--!optimize 2

local DEFAULT_OPTIONS = {
	EnabledRemarks = {
		ColdRemark = false,
		InlineRemark = true -- currently unused
	},
	DecompilerTimeout = 60, -- seconds; high-fidelity reconstruction is multi-pass
	DecompilerMode = "optdec", -- optdec/disasm
	ReaderFloatPrecision = 17, -- round-trip precision for IEEE-754 doubles
	ShowDebugInformation = true, -- show trivial function and array allocation details
	ShowProtoDebugInformation = false, -- VM internals clutter reconstructed source
	ShowInstructionLines = true, -- retained as compact source-line comments by optdec
	ShowOperationIndex = true, -- show instruction index. used in jumps #n.
	ShowOperationNames = false,
	ShowTrivialOperations = false,
	UseTypeInfo = true, -- allow adding types to function parameters (ex. p1: string, p2: number)
	ListUsedGlobals = true, -- list all (non-Roblox!!) globals used in the script as a top comment
	ReturnElapsedTime = false, -- return time it took to finish processing the bytecode
	SuppressOptdecHeader = false,
	KeepControlFlowAnnotations = false,
	EnableAnalysis = true
}

local function LoadFromUrl(x)
	local BASE_USER = "Nascube"
	local BASE_BRANCH = "main"
	local BASE_URL = "https://raw.githubusercontent.com/%s/Advanced-Decompiler/%s/%s.lua"
	local loadSuccess, loadResult = pcall(function()
		local formattedUrl = string.format(BASE_URL, BASE_USER, BASE_BRANCH, x)
		return game:HttpGet(formattedUrl, true)
	end)

	if not loadSuccess then
		warn(`({math.random()}) MОDULE FАILЕD ТO LOАD FRОM URL: {loadResult}.`)
		return
	end

	local success, result = pcall(loadstring, loadResult)
	if not success then
		warn(`({math.random()}) MОDULE FАILЕD ТO LOАDSТRING: {result}.`)
		return
	end

	if type(result) ~= "function" then
		warn(`MОDULE IS {tostring(result)} (function expected)`)
		return
	end

	return result()
end


local Implementations = LoadFromUrl("Implementations")
local Reader = LoadFromUrl("Reader")
local Strings = LoadFromUrl("Strings")
local Luau = LoadFromUrl("Luau")
local Optdec = LoadFromUrl("Optdec")
local Collector = LoadFromUrl("Collector")
local Analysis = LoadFromUrl("Analysis")
local SemanticIR = LoadFromUrl("SemanticIR")
local RegionStructurer = LoadFromUrl("RegionStructurer")
local AST = LoadFromUrl("AST")
local Decompiler = LoadFromUrl("Decompiler")


assert(Implementations, "Implementations failed to load")
assert(Reader, "Reader failed to load")
assert(Strings, "Strings failed to load")
assert(Luau, "Luau failed to load")
assert(Optdec, "Optdec failed to load")
assert(Collector, "Collector failed to load")
assert(Analysis, "Analysis failed to load")
assert(SemanticIR, "SemanticIR failed to load")
assert(RegionStructurer, "RegionStructurer failed to load")
assert(AST, "AST failed to load")
assert(Decompiler, "Decompiler failed to load")
assert(
	Decompiler.VERSION == "10.6.0-predicate-ast",
	"Wrong Decompiler module loaded; expected v10.6.0-predicate-ast, got " ..
		tostring(Decompiler.VERSION)
)
assert(
	AST.VERSION == "1.1.0",
	"Wrong AST module loaded; expected v1.1.0, got " .. tostring(AST.VERSION)
)
assert(
	RegionStructurer.VERSION == "1.2.0",
	"Wrong RegionStructurer module loaded; expected v1.2.0, got " .. tostring(RegionStructurer.VERSION)
)
assert(
	SemanticIR.VERSION == "1.2.0",
	"Wrong SemanticIR module loaded; expected v1.2.0, got " .. tostring(SemanticIR.VERSION)
)
assert(
	Analysis.VERSION == "1.0.0",
	"Wrong Analysis module loaded; expected v1.0.0, got " ..
		tostring(Analysis.VERSION)
)
assert(
	Collector.VERSION == "1.4.0",
	"Wrong Collector module loaded; expected v1.4.0, got " ..
		tostring(Collector.VERSION)
)
assert(
	Optdec.VERSION == "7.0.0",
	"Wrong Optdec module loaded; expected v7.0.0, got " ..
		tostring(Optdec.VERSION)
)

assert(
	Luau.BytecodeTag.LBC_VERSION_MAX >= 9,
	"Loaded Luau.lua does not support bytecode version 9"
)

assert(
	Luau.BytecodeTag.LBC_CONSTANT_INTEGER == 9,
	"Loaded Luau.lua lacks integer constants"
)

local requiredOpcodes = {
	GETUDATAKS = false,
	SETUDATAKS = false,
	NAMECALLUDATA = false,
}

for _, opcodeInfo in Luau.OpCode do
	if opcodeInfo and requiredOpcodes[opcodeInfo.name] ~= nil then
		requiredOpcodes[opcodeInfo.name] = true
	end
end

for opcodeName, found in requiredOpcodes do
	assert(found, "Missing opcode: " .. opcodeName)
end

local LuauOpCode = Luau.OpCode
local LuauBytecodeTag = Luau.BytecodeTag
local LuauBytecodeType = Luau.BytecodeType
local LuauCaptureType = Luau.CaptureType
local LuauBuiltinFunction = Luau.BuiltinFunction
local LuauProtoFlag = Luau.ProtoFlag

local toBoolean = Implementations.toBoolean
local toEscapedString = Implementations.toEscapedString
local formatIndexString = Implementations.formatIndexString
local padLeft = Implementations.padLeft
local padRight = Implementations.padRight
local isGlobal = Implementations.isGlobal

local LUAU_KEYWORDS = {
	["and"] = true,
	["break"] = true,
	["continue"] = true,
	["do"] = true,
	["else"] = true,
	["elseif"] = true,
	["end"] = true,
	["export"] = true,
	["false"] = true,
	["for"] = true,
	["function"] = true,
	["if"] = true,
	["in"] = true,
	["local"] = true,
	["nil"] = true,
	["not"] = true,
	["or"] = true,
	["repeat"] = true,
	["return"] = true,
	["then"] = true,
	["true"] = true,
	["type"] = true,
	["until"] = true,
	["while"] = true,
}

local function isValidIdentifier(name)
	return type(name) == "string"
		and name:match("^[%a_][%w_]*$") ~= nil
		and not LUAU_KEYWORDS[name]
end

local function Decompile(bytecode, options)
	local bytecodeVersion, typeEncodingVersion

	Reader:Set(options.ReaderFloatPrecision)

	local reader = Reader.new(bytecode)

	-- step 1: collect information from the bytecode
	local function disassemble()
		if bytecodeVersion >= 4 then
			-- type encoding did not exist before this version
			typeEncodingVersion = reader:nextByte()
		end

		local stringTable = {}
		local function readStringTable()
			local amountOfStrings = reader:nextVarInt() -- or, well, stringTable size.
			for i = 1, amountOfStrings do
				stringTable[i] = reader:nextString()
			end
		end

		local userdataTypes = {}
		local function readUserdataTypes()
			while true do
				local index = reader:nextByte()

				if index == 0 then
					break
				end

				userdataTypes[index] = reader:nextVarInt()
			end
		end

		local protoTable = {}
		local function readProtoTable()
			local amountOfProtos = reader:nextVarInt() -- or protoTable size
			for i = 1, amountOfProtos do
				local protoId = i - 1 -- account for main proto

				local proto = {
					id = protoId,

					instructions = {},
					constants = {},
					captures = {}, -- upvalue references
					innerProtos = {},

					instructionLineInfo = {}
				}
				protoTable[protoId] = proto

				-- read header
				proto.maxStackSize = reader:nextByte()
				proto.numParams = reader:nextByte()
				proto.numUpvalues = reader:nextByte()
				proto.isVarArg = toBoolean(reader:nextByte())

				-- read flags and typeInfo if bytecode version includes that information
				if bytecodeVersion >= 4 then
					proto.flags = reader:nextByte()

					-- collect type info
					local resultTypedParams = {}
					local resultTypedUpvalues = {}
					local resultTypedLocals = {}

					-- refer to: https://github.com/luau-lang/luau/blob/0.655/Compiler/src/BytecodeBuilder.cpp#L752
					local allTypeInfoSize = reader:nextVarInt()

					local hasTypeInfo = allTypeInfoSize > 0 -- we don't have any type info if the size is zero.
					proto.hasTypeInfo = hasTypeInfo

					if hasTypeInfo then
						local totalTypedParams = allTypeInfoSize
						local totalTypedUpvalues = 0
						local totalTypedLocals = 0

						if typeEncodingVersion > 1 then
							-- much more info is encoded in next versions
							totalTypedParams = reader:nextVarInt()
							totalTypedUpvalues = reader:nextVarInt()
							totalTypedLocals = reader:nextVarInt()
						end

						local function readTypedParams()
							local typedParams = resultTypedParams
							if totalTypedParams > 0 then
								typedParams = reader:nextBytes(totalTypedParams) -- array of uint8
								-- first value is always "function"
								-- we don't care about that.
								table.remove(typedParams, 1)
								-- second value is the amount of typed params
								table.remove(typedParams, 1)
							end
							return typedParams
						end
						local function readTypedUpvalues()
							local typedUpvalues = resultTypedUpvalues
							if totalTypedUpvalues > 0 then
								for i = 1, totalTypedUpvalues do
									local upvalueType = reader:nextByte()

									-- info on the upvalue at index `i`
									local info = {
										type = upvalueType
									}
									typedUpvalues[i] = info
								end
							end
							return typedUpvalues
						end
						local function readTypedLocals()
							local typedLocals = resultTypedLocals
							if totalTypedLocals > 0 then
								for i = 1, totalTypedLocals do
									local localType = reader:nextByte()
									-- Register is locals' place in the stack
									local localRegister = reader:nextByte() -- accounts for function params!
									-- PC - Program Counter
									local localStartPC = reader:nextVarInt() + 1
									-- refer to: https://github.com/luau-lang/luau/blob/0.655/Compiler/src/BytecodeBuilder.cpp#L749
									-- if you want to know why we get endPC like that
									local localEndPC = reader:nextVarInt() + localStartPC - 1

									-- info on the local at index `i`
									local info = {
										type = localType,
										register = localRegister,
										startPC = localStartPC,
										endPC = localEndPC
									}
									typedLocals[i] = info
								end
							end
							return typedLocals
						end

						resultTypedParams = readTypedParams()
						resultTypedUpvalues = readTypedUpvalues()
						resultTypedLocals = readTypedLocals()
					end

					proto.typedParams = resultTypedParams
					proto.typedUpvalues = resultTypedUpvalues
					proto.typedLocals = resultTypedLocals
				end

				-- total number of instructions
				proto.sizeInstructions = reader:nextVarInt()
				for i = 1, proto.sizeInstructions do
					local encodedInstruction = reader:nextUInt32()
					proto.instructions[i] = encodedInstruction
				end

				-- total number of constants
				proto.sizeConstants = reader:nextVarInt()
				for i = 1, proto.sizeConstants do
					local constValue

					local constType = reader:nextByte()
					if constType == LuauBytecodeTag.LBC_CONSTANT_BOOLEAN then
						-- 1 = true, 0 = false
						constValue = toBoolean(reader:nextByte())
					elseif constType == LuauBytecodeTag.LBC_CONSTANT_NUMBER then
						constValue = reader:nextDouble()
					elseif constType == LuauBytecodeTag.LBC_CONSTANT_STRING then
						local stringId = reader:nextVarInt()
						constValue = stringTable[stringId]
					elseif constType == LuauBytecodeTag.LBC_CONSTANT_IMPORT then
						-- imports are globals from the environment
						-- examples: math.random, print, coroutine.wrap

						local id = reader:nextUInt32()

						local indexCount = bit32.rshift(id, 30)

						local cacheIndex1 = bit32.band(bit32.rshift(id, 20), 0x3FF)
						local cacheIndex2 = bit32.band(bit32.rshift(id, 10), 0x3FF)
						local cacheIndex3 = bit32.band(bit32.rshift(id, 0), 0x3FF)

						local importTag = ""

						if indexCount == 1 then
							local k1 = proto.constants[cacheIndex1 + 1]
							importTag ..= tostring(k1.value)
						elseif indexCount == 2 then
							local k1 = proto.constants[cacheIndex1 + 1]
							local k2 = proto.constants[cacheIndex2 + 1]
							importTag ..= tostring(k1.value) .. "."
							importTag ..= tostring(k2.value)
						elseif indexCount == 3 then
							local k1 = proto.constants[cacheIndex1 + 1]
							local k2 = proto.constants[cacheIndex2 + 1]
							local k3 = proto.constants[cacheIndex3 + 1]
							importTag ..= tostring(k1.value) .. "."
							importTag ..= tostring(k2.value) .. "."
							importTag ..= tostring(k3.value)
						end

						constValue = importTag
				
				elseif constType == LuauBytecodeTag.LBC_CONSTANT_TABLE then
					local sizeTable = reader:nextVarInt()
					local tableKeys = {}

					for entryIndex = 1, sizeTable do
						tableKeys[entryIndex] = reader:nextVarInt() + 1
					end

					constValue = {
						size = sizeTable,
						keys = tableKeys,
						values = nil,
						prefilled = false
					}

				elseif constType == LuauBytecodeTag.LBC_CONSTANT_TABLE_WITH_CONSTANTS then
					local sizeTable = reader:nextVarInt()
					local tableKeys = {}
					local tableValues = {}

					for entryIndex = 1, sizeTable do
						tableKeys[entryIndex] = reader:nextVarInt() + 1

						local valueConstantIndex = reader:nextInt32()

						if valueConstantIndex >= 0 then
							tableValues[entryIndex] = valueConstantIndex + 1
						else
							tableValues[entryIndex] = false
						end
					end

					constValue = {
						size = sizeTable,
						keys = tableKeys,
						values = tableValues,
						prefilled = true
					}
					elseif constType == LuauBytecodeTag.LBC_CONSTANT_CLOSURE then
						local closureId = reader:nextVarInt() + 1
						constValue = closureId
					elseif constType == LuauBytecodeTag.LBC_CONSTANT_VECTOR then
						local x, y, z, w = reader:nextFloat(), reader:nextFloat(), reader:nextFloat(), reader:nextFloat()
						if w == 0 then
							constValue = "Vector3.new(".. x ..", ".. y ..", ".. z ..")"
						else
							constValue = "vector.create(".. x ..", ".. y ..", ".. z ..", ".. w ..")"
						end
						elseif constType == LuauBytecodeTag.LBC_CONSTANT_INTEGER then
						local isNegative = reader:nextByte() ~= 0
						local magnitude = reader:nextVarInt64String()

						if isNegative and magnitude ~= "0" then
							constValue = "-" .. magnitude
						else
							constValue = magnitude
						end
						elseif constType ~= LuauBytecodeTag.LBC_CONSTANT_NIL then
							error(
								string.format(
									"Unsupported constant tag %d in bytecode version %d",
									constType,
									bytecodeVersion
								)
							)
						end
					
					-- info on the constant at index `i`
					local info = {
						type = constType,
						value = constValue
					}
					proto.constants[i] = info
				end

				-- total number of protos inside this proto
				proto.sizeInnerProtos = reader:nextVarInt()
				for i = 1, proto.sizeInnerProtos do
					local protoId = reader:nextVarInt()
					proto.innerProtos[i] = protoTable[protoId]
				end

				-- lineDefined is the line function starts on
				proto.lineDefined = reader:nextVarInt()

				-- protoDebugNameId is the string id of the function's name if it is not unnamed
				local protoDebugNameId = reader:nextVarInt()
				proto.name = stringTable[protoDebugNameId]

				-- references:
				-- https://github.com/luau-lang/luau/blob/0.655/Compiler/src/BytecodeBuilder.cpp#L888
				-- https://github.com/uniquadev/LuauVM/blob/master/VM/luau/lobject.lua
				local hasLineInfo = toBoolean(reader:nextByte())
				proto.hasLineInfo = hasLineInfo

				if hasLineInfo then
					-- log2 of the line gap between instructions
					local lineGapLog2 = reader:nextByte()

					local baselineSize = bit32.rshift(proto.sizeInstructions - 1, lineGapLog2) + 1

					local lastOffset = 0
					local lastLine = 0

					-- line number as a delta from baseline for each instruction
					local smallLineInfo = {}
					-- one entry for each bit32.lshift(1, lineGapLog2) instructions
					local absLineInfo = {}
					-- ready to read line info
					local resultLineInfo = {}

					for instructionIndex in proto.instructions do
						local lineDelta = reader:nextByte()

						lastOffset = bit32.band(
							lastOffset + lineDelta,
							0xFF
						)

						smallLineInfo[instructionIndex] = lastOffset
					end

					for i = 1, baselineSize do
						-- if we read unsigned int32 here we're doomed!!!!!! for eternity!!!!!!!!!
						local largeLineChange = lastLine + reader:nextInt32()
						absLineInfo[i - 1] = largeLineChange

						lastLine = largeLineChange
					end

					for instructionIndex, relativeLine in smallLineInfo do
						local baselineIndex = bit32.rshift(
							instructionIndex - 1,
							lineGapLog2
						)

						local baselineLine = absLineInfo[baselineIndex] or 0

						resultLineInfo[instructionIndex] =
							baselineLine + relativeLine
					end

					proto.lineInfoSize = lineGapLog2
					proto.instructionLineInfo = resultLineInfo
				end

				-- debug info is not present in Roblox and that's sad
				-- no variable names...
				local hasDebugInfo = toBoolean(reader:nextByte())
				proto.hasDebugInfo = hasDebugInfo

				if hasDebugInfo then
					local totalDebugLocals = reader:nextVarInt()
					local function readDebugLocals()
						local debugLocals = {}

						for i = 1, totalDebugLocals do
							local localName = stringTable[reader:nextVarInt()]
							local localStartPC = reader:nextVarInt()
							local localEndPC = reader:nextVarInt()
							local localRegister = reader:nextByte()

							-- debug info on the local at index `i`
							local info = {
								name = localName,
								startPC = localStartPC,
								endPC = localEndPC,
								register = localRegister
							}
							debugLocals[i] = info
						end

						return debugLocals
					end
					proto.debugLocals = readDebugLocals()

					local totalDebugUpvalues = reader:nextVarInt()
					local function readDebugUpvalues()
						local debugUpvalues = {}

						for i = 1, totalDebugUpvalues do
							local upvalueName = stringTable[reader:nextVarInt()]

							-- debug info on the upvalue at index `i`
							local info = {
								name = upvalueName
							}
							debugUpvalues[i] = info
						end

						return debugUpvalues
					end
					proto.debugUpvalues = readDebugUpvalues()
				end
			end
		end

		-- read needs to be done in proper order
		readStringTable()
		if typeEncodingVersion == 3 then
			readUserdataTypes()
		end
		readProtoTable()

		if next(userdataTypes) ~= nil then
			warn("please send the bytecode to me so i can add support for userdata types. thanks!")
		end

		local mainProtoId = reader:nextVarInt()

		if options.CollectionSession then
			Collector.captureParsed(
				options.CollectionSession,
				{
					bytecodeVersion = bytecodeVersion,
					typeEncodingVersion = typeEncodingVersion,
					mainProtoId = mainProtoId,
					stringTable = stringTable,
					userdataTypes = userdataTypes,
					protoTable = protoTable,
				},
				Luau
			)
		end

		return mainProtoId, protoTable
	end
	-- step 2: organize information for decompilation
	local function organize()
		-- provides proto name and line along with the issue in a warning message
		local function reportProtoIssue(proto, issue)
			local protoIdentifier = `[{proto.name or "unnamed"}:{proto.lineDefined or -1}]`
			warn(protoIdentifier .. ": " .. issue)
		end

		local mainProtoId, protoTable = disassemble()

		local mainProto = protoTable[mainProtoId]
		mainProto.main = true

		-- collected operation data
		local registerActions = {}

		local function baseProto(proto)
			-- Prototypes can be referenced by several closure instructions (and in
			-- malformed chunks can be cyclic).  Organizing the same proto twice
			-- used to overwrite its action table and decode proto.flags a second
			-- time, at which point flags is already a table.  That caused:
			-- bit32.band(number expected, got table).
			if registerActions[proto.id] then
				return
			end

			local protoRegisterActions = {}

			-- this needs to be done here.
			local protoActionData = {
				proto = proto,
				actions = protoRegisterActions
			}
			registerActions[proto.id] = protoActionData

			local instructions = proto.instructions
			local innerProtos = proto.innerProtos
			local constants = proto.constants
			local captures = proto.captures
			local flags = proto.flags or 0

			-- collect all captures past the base instruction index
			local function collectCaptures(baseIndex, proto)
				local numUpvalues = proto.numUpvalues
				if numUpvalues > 0 then
					local _captures = proto.captures

					for i = 1, numUpvalues do
						local capture = instructions[baseIndex + i]

						local captureType = Luau:INSN_A(capture)
						local sourceRegister = Luau:INSN_B(capture)

						if captureType == LuauCaptureType.LCT_VAL or captureType == LuauCaptureType.LCT_REF then
							_captures[i - 1] = sourceRegister
						elseif captureType == LuauCaptureType.LCT_UPVAL then
							-- capture of a capture. haha..
							_captures[i - 1] = captures[sourceRegister]
						end
					end
				end
			end

			local function writeFlags()
				-- Idempotency guard for chunks that share prototype references.
				if type(flags) == "table" then
					proto.flags = flags
					return
				end

				local decodedFlags = {}

				if proto.main then
					-- what we are dealing with here is mainFlags
					-- refer to: https://github.com/luau-lang/luau/blob/0.655/Compiler/src/Compiler.cpp#L4188

					decodedFlags.native = toBoolean(bit32.band(flags, LuauProtoFlag.LPF_NATIVE_MODULE))
				else
					-- normal protoFlags
					-- refer to: https://github.com/luau-lang/luau/blob/0.655/Compiler/src/Compiler.cpp#L287

					decodedFlags.native = toBoolean(bit32.band(flags, LuauProtoFlag.LPF_NATIVE_FUNCTION))
					decodedFlags.cold = toBoolean(bit32.band(flags, LuauProtoFlag.LPF_NATIVE_COLD))
				end

				-- update flags entry
				flags = decodedFlags
				proto.flags = decodedFlags
			end
			local function writeInstructions()
				local auxSkip = false

				for index, instruction in instructions do
					if auxSkip then
						-- we are currently on an aux of a previous instruction
						-- there is no need to do any work here.
						auxSkip = false
						continue
					end

					local opCodeInfo = LuauOpCode[Luau:INSN_OP(instruction)]
					if not opCodeInfo then
						-- this is serious!
						reportProtoIssue(proto, `invalid instruction at index "{index}"!`)
						continue
					end

					local opCodeName = opCodeInfo.name
					local opCodeType = opCodeInfo.type
					local opCodeIsAux = opCodeInfo.aux == true

					-- information in the instruction that we will use
					local A, B, C
					local sD, D, E
					local aux

					-- creates an action from provided data and registers it.
					local function registerAction(usedRegisters, extraData, hide)
						local data = {
							usedRegisters = usedRegisters or {},
							extraData = extraData,
							opCode = opCodeInfo,
							hide = hide
						}
						table.insert(protoRegisterActions, data)
					end

					-- handle reading information based on the op code type
					if opCodeType == "A" then
						A = Luau:INSN_A(instruction)
					elseif opCodeType == "E" then
						E = Luau:INSN_E(instruction)
					elseif opCodeType == "AB" then
						A = Luau:INSN_A(instruction)
						B = Luau:INSN_B(instruction)
					elseif opCodeType == "AC" then
						A = Luau:INSN_A(instruction)
						C = Luau:INSN_C(instruction)
					elseif opCodeType == "ABC" then
						A = Luau:INSN_A(instruction)
						B = Luau:INSN_B(instruction)
						C = Luau:INSN_C(instruction)
					elseif opCodeType == "AD" then
						A = Luau:INSN_A(instruction)
						D = Luau:INSN_D(instruction)
					elseif opCodeType == "AsD" then
						A = Luau:INSN_A(instruction)
						sD = Luau:INSN_sD(instruction)
					elseif opCodeType == "sD" then
						sD = Luau:INSN_sD(instruction)
					end

					-- handle aux
					if opCodeIsAux then
						auxSkip = true

						-- AUX is the word immediately after the instruction.
						aux = instructions[index + 1]

						if aux == nil then
							reportProtoIssue(
								proto,
								`missing AUX word after instruction "{index}"!`
							)

							aux = 0
						end
					end

					-- it would be faster if we did this comparing opCode index
					-- rather than name, but it would be suffering to code and read
					if opCodeName == "NOP" or opCodeName == "BREAK" or opCodeName == "NATIVECALL" then
						-- empty action for these
						registerAction(nil, nil, not options.ShowTrivialOperations)
					elseif opCodeName == "LOADNIL" then
						registerAction({A})
					elseif opCodeName == "LOADB" then -- load boolean
						registerAction({A}, {B, C})
					elseif opCodeName == "LOADN" then -- load number literal
						registerAction({A}, {sD})
					elseif opCodeName == "LOADK" then -- load constant
						registerAction({A}, {D})
					elseif opCodeName == "MOVE" then
						registerAction({A, B})
					elseif opCodeName == "GETGLOBAL" or opCodeName == "SETGLOBAL" then
						-- we most likely will not ever use C here.
						registerAction({A}, {aux}) --({A}, {C, aux})
					elseif opCodeName == "GETUPVAL" or opCodeName == "SETUPVAL" then
						registerAction({A}, {B})
					elseif opCodeName == "CLOSEUPVALS" then
						registerAction({A}, nil, not options.ShowTrivialOperations)
					elseif opCodeName == "GETIMPORT" then
						registerAction({A}, {D, aux})
					elseif opCodeName == "GETTABLE"
						or opCodeName == "SETTABLE"
					then
						registerAction({A, B, C})

					elseif opCodeName == "GETTABLEKS"
						or opCodeName == "SETTABLEKS"
					then
						registerAction({A, B}, {C, aux})

					elseif opCodeName == "GETUDATAKS"
						or opCodeName == "SETUDATAKS"
					then
						local constantIndex =
							bit32.band(aux, 0xFFFF)

						local cachedSlot =
							bit32.rshift(aux, 16)

						registerAction(
							{A, B},
							{C, constantIndex, cachedSlot}
						)
					elseif opCodeName == "GETTABLEN" or opCodeName == "SETTABLEN" then
						registerAction({A, B}, {C})
					elseif opCodeName == "NEWCLOSURE" then
						registerAction({A}, {D})

						local proto = innerProtos[D + 1]
						collectCaptures(index, proto)
						baseProto(proto)
					elseif opCodeName == "DUPCLOSURE" then
						registerAction({A}, {D})

						local proto = protoTable[constants[D + 1].value - 1]
						collectCaptures(index, proto)
						baseProto(proto)
					elseif opCodeName == "NAMECALL" then
						registerAction(
							{A, B},
							{C, aux},
							not options.ShowTrivialOperations
						)

					elseif opCodeName == "NAMECALLUDATA" then
						local constantIndex =
							bit32.band(aux, 0xFFFF)

						local cachedSlot =
							bit32.rshift(aux, 16)

						registerAction(
							{A, B},
							{C, constantIndex, cachedSlot},
							not options.ShowTrivialOperations
						)
					elseif opCodeName == "CALL" then
						registerAction({A}, {B, C})
					elseif opCodeName == "RETURN" then
						registerAction({A}, {B})
					elseif opCodeName == "JUMP" or opCodeName == "JUMPBACK" then
						registerAction({}, {sD})
					elseif opCodeName == "JUMPIF" or opCodeName == "JUMPIFNOT" then
						registerAction({A}, {sD})
					elseif
						opCodeName == "JUMPIFEQ" or opCodeName == "JUMPIFLE" or opCodeName == "JUMPIFLT" or
						opCodeName == "JUMPIFNOTEQ" or opCodeName == "JUMPIFNOTLE" or opCodeName == "JUMPIFNOTLT"
					then
						registerAction({A, aux}, {sD})
					elseif
						opCodeName == "ADD" or opCodeName == "SUB" or opCodeName == "MUL" or
						opCodeName == "DIV" or opCodeName == "MOD" or opCodeName == "POW"
					then
						registerAction({A, B, C})
					elseif
						opCodeName == "ADDK" or opCodeName == "SUBK" or opCodeName == "MULK" or
						opCodeName == "DIVK" or opCodeName == "MODK" or opCodeName == "POWK"
					then
						registerAction({A, B}, {C})
					elseif opCodeName == "AND" or opCodeName == "OR" then
						registerAction({A, B, C})
					elseif opCodeName == "ANDK" or opCodeName == "ORK" then
						registerAction({A, B}, {C})
					elseif opCodeName == "CONCAT" then
						local registers = {A}
						for reg = B, C do
							table.insert(registers, reg)
						end
						registerAction(registers)
					elseif opCodeName == "NOT" or opCodeName == "MINUS" or opCodeName == "LENGTH" then
						registerAction({A, B})
					elseif opCodeName == "NEWTABLE" then
						registerAction({A}, {B, aux})
					elseif opCodeName == "DUPTABLE" then
						registerAction({A}, {D})
					elseif opCodeName == "SETLIST" then
						if C ~= 0 then
							local registers = {A, B}
							for i = 1, C - 2 do -- account for target and source registers
								table.insert(registers, A + i)
							end
							registerAction(registers, {aux, C})
						else
							registerAction({A, B}, {aux, C})
						end
					elseif opCodeName == "FORNPREP" then
						-- Numeric-for layout is [limit, step, index, variable].
						-- The old action omitted A+3 and later printed the internal
						-- index as both the destination and initial value, allowing
						-- symbolic propagation to produce invalid `for 1 = ...`.
						registerAction({A, A+1, A+2, A+3}, {sD})
					elseif opCodeName == "FORNLOOP" then
						registerAction({A}, {sD})
					elseif opCodeName == "FORGLOOP" then
						local numVariableRegisters = bit32.band(aux, 0xFF)

						local registers = {}
						-- A, A+1 and A+2 are generator/state/index. User-visible
						-- generic-for variables begin at A+3.
						for regIndex = 0, numVariableRegisters - 1 do
							table.insert(registers, A + 3 + regIndex)
						end
						registerAction(registers, {sD, aux})
					elseif opCodeName == "FORGPREP_INEXT" or opCodeName == "FORGPREP_NEXT" then
						registerAction({A, A+1})
					elseif opCodeName == "FORGPREP" then
						registerAction({A}, {sD})
					elseif opCodeName == "GETVARARGS" then
						if B ~= 0 then
							local registers = {}

							for offset = 0, B - 2 do
								registers[#registers + 1] = A + offset
							end

							registerAction(registers, {B})
						else
							registerAction({A}, {B})
						end
					elseif opCodeName == "PREPVARARGS" then
						registerAction({}, {A}, not options.ShowTrivialOperations)
					elseif opCodeName == "LOADKX" then
						registerAction({A}, {aux})
					elseif opCodeName == "JUMPX" then
						registerAction({}, {E})
					elseif opCodeName == "COVERAGE" then
						registerAction({}, {E}, not options.ShowTrivialOperations)
					elseif
						opCodeName == "JUMPXEQKNIL" or opCodeName == "JUMPXEQKB" or
						opCodeName == "JUMPXEQKN" or opCodeName == "JUMPXEQKS"
					then
						registerAction({A}, {sD, aux})
					elseif opCodeName == "CAPTURE" then
						-- empty action here
						registerAction(nil, nil, not options.ShowTrivialOperations)
					elseif opCodeName == "SUBRK" or opCodeName == "DIVRK" then -- constant sub/div
						registerAction({A, C}, {B})
					elseif opCodeName == "IDIV" then -- floor division
						registerAction({A, B, C})
					elseif opCodeName == "IDIVK" then -- floor division with 1 constant argument
						registerAction({A, B}, {C})
					elseif opCodeName == "FASTCALL" then -- reads info from the CALL instruction
						registerAction({}, {A, C}, not options.ShowTrivialOperations)
					elseif opCodeName == "FASTCALL1" then -- 1 register argument
						registerAction({B}, {A, C}, not options.ShowTrivialOperations)
					elseif opCodeName == "FASTCALL2" then -- 2 register arguments
						local sourceArgumentRegister2 = bit32.band(aux, 0xFF)

						registerAction({B, sourceArgumentRegister2}, {A, C}, not options.ShowTrivialOperations)
					elseif opCodeName == "FASTCALL2K" then -- 1 register argument and 1 constant argument
						registerAction({B}, {A, C, aux}, not options.ShowTrivialOperations)
					elseif opCodeName == "FASTCALL3" then
					local sourceArgumentRegister2 = bit32.band(aux, 0xFF)

					local sourceArgumentRegister3 = bit32.band(bit32.rshift(aux, 8), 0xFF)

						registerAction({B, sourceArgumentRegister2, sourceArgumentRegister3}, {A, C}, not options.ShowTrivialOperations)
					end
					if opCodeIsAux then
						registerAction(nil, nil, true)
					end
				end
			end

			writeFlags()
			writeInstructions()
		end
		baseProto(mainProto)

		if options.CollectionSession then
			Collector.captureOrganized(
				options.CollectionSession,
				mainProtoId,
				registerActions,
				protoTable,
				Luau
			)
			if options.EnableAnalysis ~= false then
				local analysisOk, analysisResult = pcall(
					Analysis.analyzeSession,
					options.CollectionSession
				)
				options.CollectionSession.stages.godTier = analysisOk
					and analysisResult
					or {
						schema = Analysis.SCHEMA,
						version = Analysis.VERSION,
						error = tostring(analysisResult),
					}
			end
		end

		return mainProtoId, registerActions, protoTable
	end
	-- step 3: turn the result into a string
	local function finalize(mainProtoId, registerActions, protoTable)
		local finalResult = ""

		local totalParameters = 0
		-- array of used globals for further output
		local usedGlobals = {}

		-- should `key` be logged in usedGlobals?
		local function isValidGlobal(key)
			return not table.find(usedGlobals, key) and not isGlobal(key)
		end

		-- received result. embed final things here.
		local function processResult(result)
			local embed = ""

			if options.ListUsedGlobals and #usedGlobals > 0 then
				embed ..= string.format(Strings.USED_GLOBALS, table.concat(usedGlobals, ", "))
			end

			return embed .. result
		end

		-- now proceed based off mode
		if options.DecompilerMode == "disasm" or options.DecompilerMode == "optdec" then -- shared semantic emitter
			local result = ""

			local function writeActions(protoActions)
				local actions = protoActions.actions
				local proto = protoActions.proto

				local instructionLineInfo = proto.instructionLineInfo
				local innerProtos = proto.innerProtos
				local constants = proto.constants
				local captures = proto.captures
				local flags = proto.flags

				local numParams = proto.numParams

				-- for proper `goto` handling
				local jumpMarkers = {}
				local function makeJumpMarker(index)
					local numMarkers = jumpMarkers[index] or 0
					jumpMarkers[index] = numMarkers + 1
				end

				-- for easier parameter differentiation
				totalParameters += numParams

				-- support for mainFlags
				if proto.main then
					-- if there is a possible way to check for --!optimize please let me know
					if flags.native then
						result ..= "--!native" .. "\n"
					end
				end

				for i, action in actions do
					if not action then
						result ..=
							"-- missing action at index #" ..
							tostring(i) ..
							"\n"

						continue
					end

					if action.hide then
						continue
					end

					local usedRegisters =
						action.usedRegisters or {}

					local extraData = action.extraData
					local opCodeInfo = action.opCode

					if not opCodeInfo
						or type(opCodeInfo.name) ~= "string"
					then
						result ..=
							"-- malformed action at index #" ..
							tostring(i) ..
							"\n"

						continue
					end

					local opCodeName = opCodeInfo.name

					local function handleJumpMarkers()
						local numJumpMarkers = jumpMarkers[i]
						if numJumpMarkers then
							jumpMarkers[i] = nil

							--if string.find(opCodeName, "JUMP") then
							-- it's much more complicated
							--	result ..= "else\n"

							--	local newJumpOffset = i + extraData[1] + 1
							--	makeJumpMarker(newJumpOffset)
							--else
							-- it's just a one way condition
							for i = 1, numJumpMarkers do
								result ..= "end\n"
							end
							--end
						end
					end

					local function writeHeader()
						local index
						if options.ShowOperationIndex then
							index = "[".. padLeft(i, "0", 3) .."]"
						else
							index = ""
						end

						local name
						if options.ShowOperationNames then
							name = padRight(opCodeName, " ", 15)
						else
							name = ""
						end

						local line = ""

						if options.ShowInstructionLines then
							local sourceLine =
								instructionLineInfo[i]
								or proto.lineDefined
								or 0

							line = ":" .. padLeft(sourceLine, "0", 3) .. ":"
						end
						result ..= index .." ".. line .. name
					end
					local function writeOperationBody()
						local function findDebugLocal(register, instructionIndex)
							if not proto.debugLocals then
								return nil
							end

							for _, localInfo in proto.debugLocals do
								if localInfo.register == register
									and instructionIndex >= localInfo.startPC
									and instructionIndex < localInfo.endPC
								then
									return localInfo.name
								end
							end

							return nil
						end

						local function formatRegister(register)
							local parameterRegister = register + 1

							if parameterRegister <= numParams then
								return "p" .. parameterRegister
							end

							local debugName = findDebugLocal(register, i)

							if isValidIdentifier(debugName) then
								return debugName
							end

							return "v" .. (register - numParams)
						end

						local function formatUpvalue(upvalueIndex)
							-- Debug upvalue names are the only source-faithful names
							-- available here. `captures` stores parent registers and must
							-- not be formatted in the child function's register space.
							local debugUpvalues = proto.debugUpvalues
							local debugName = debugUpvalues
								and debugUpvalues[upvalueIndex + 1]

							if type(debugName) == "table" then
								debugName = debugName.name
							end

							if isValidIdentifier(debugName) then
								return debugName
							end

							return "upvalue_" .. tostring(upvalueIndex)
						end

						local function formatProto(proto)
							local name = proto.name
							local numParams = proto.numParams
							local isVarArg = proto.isVarArg
							local isTyped = proto.hasTypeInfo and options.UseTypeInfo
							local flags = proto.flags or {
								native = false,
								cold = false
							}
							local typedParams = proto.typedParams

							local protoBody = ""

							-- attribute support
							local prefix = ""

							if flags.native then
								if flags.cold and options.EnabledRemarks.ColdRemark then
									prefix ..= string.format(
										Strings.DECOMPILER_REMARK,
										"This function is marked cold and is not compiled natively"
									)
								end

								prefix ..= "@native "
							end

							if name then
								protoBody = prefix .. "local function " .. name
							else
								protoBody = prefix .. "function"
							end
							-- now build parameters
							protoBody ..= "("

							for index = 1, numParams do
								local parameterBody = "p" .. index

								-- Prefer debug-local parameter names when the compiler
								-- retained them. Parameters occupy registers 0..n-1.
								if proto.debugLocals then
									for _, localInfo in proto.debugLocals do
										if localInfo.register == index - 1
											and isValidIdentifier(localInfo.name)
										then
											parameterBody = localInfo.name
											break
										end
									end
								end
								-- if has type info, apply it
								if isTyped then
									local parameterType = typedParams[index]
									-- not sure if parameterType always exists
									if parameterType then
										parameterBody ..= ": ".. Luau:GetBaseTypeString(parameterType, true)
									end
								end
								-- if not last parameter
								if index ~= numParams then
									parameterBody ..= ", "
								end
								protoBody ..= parameterBody
							end

							if isVarArg then
								if numParams > 0 then
									-- top it off with ...
									protoBody ..= ", ..."
								else
									protoBody ..= "..."
								end
							end

							protoBody ..= ")\n"

							-- additional debug information
							if options.ShowDebugInformation
								and options.ShowProtoDebugInformation
							then
								protoBody ..= "-- proto pool id: ".. proto.id .. "\n"
								protoBody ..= "-- num upvalues: ".. proto.numUpvalues .. "\n"
								protoBody ..= "-- num inner protos: ".. proto.sizeInnerProtos .. "\n"
								protoBody ..= "-- size instructions: ".. proto.sizeInstructions .. "\n"
								protoBody ..= "-- size constants: ".. proto.sizeConstants .. "\n"
								protoBody ..= "-- lineinfo gap: ".. proto.lineInfoSize .. "\n"
								protoBody ..= "-- max stack size: ".. proto.maxStackSize .. "\n"
								protoBody ..= "-- is typed: ".. tostring(proto.hasTypeInfo) .. "\n"
							end

							return protoBody
						end

						local function formatConstantValue(k)
							if not k then
								return "nil --[[missing constant]]"
							end

							if k.type == LuauBytecodeTag.LBC_CONSTANT_VECTOR then
								return k.value
							elseif k.type == LuauBytecodeTag.LBC_CONSTANT_INTEGER then
								-- Keep the exact decimal representation. Do not pass it
								-- through tonumber, which may lose 64-bit precision.
								return k.value
							else
								if type(tonumber(k.value)) == "number" then
									return tonumber(string.format(`%0.{options.ReaderFloatPrecision}f`, k.value))
								else
									return toEscapedString(k.value)
								end
							end
						end

						local function writeProto(register, proto)
							local protoBody = formatProto(proto)

							local name = proto.name
							if name then
								result ..= "\n".. protoBody
								writeActions(registerActions[proto.id])
								result ..= "end\n".. formatRegister(register) .." = ".. name
							else
								result ..= formatRegister(register) .." = ".. protoBody
								writeActions(registerActions[proto.id])
								result ..= "end"
							end
						end

						if opCodeName == "LOADNIL" then
							local targetRegister = usedRegisters[1]

							result ..= formatRegister(targetRegister) .." = nil"
						elseif opCodeName == "LOADB" then -- load boolean
							local targetRegister = usedRegisters[1]

							local value = toBoolean(extraData[1])
							local jumpOffset = extraData[2]

							result ..= formatRegister(targetRegister) .." = ".. toEscapedString(value)

							if jumpOffset ~= 0 and options.ShowTrivialOperations then
								-- C is a PC skip, never arithmetic. Preserve it as
								-- metadata until SSA/phi reconstruction consumes it.
								result ..= string.format(
									" --[[ LOADB skips %i instruction(s) ]]",
									jumpOffset
								)
							end
						elseif opCodeName == "LOADN" then -- load number literal
							local targetRegister = usedRegisters[1]

							local value = extraData[1]

							result ..= formatRegister(targetRegister) .." = ".. value
						elseif opCodeName == "LOADK" then -- load constant
							local targetRegister = usedRegisters[1]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. value
						elseif opCodeName == "MOVE" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(sourceRegister)
						elseif opCodeName == "GETGLOBAL" then
							local targetRegister = usedRegisters[1]

							-- formatConstantValue uses toEscapedString which we don't want here
							local globalKey = tostring(constants[extraData[1] + 1].value)

							if options.ListUsedGlobals and isValidGlobal(globalKey) then
								table.insert(usedGlobals, globalKey)
							end

							result ..= formatRegister(targetRegister) .." = ".. globalKey
						elseif opCodeName == "SETGLOBAL" then
							local sourceRegister = usedRegisters[1]

							local globalKey = tostring(constants[extraData[1] + 1].value)

							if options.ListUsedGlobals and isValidGlobal(globalKey) then
								table.insert(usedGlobals, globalKey)
							end

							result ..= globalKey .." = ".. formatRegister(sourceRegister)
						elseif opCodeName == "GETUPVAL" then
							local targetRegister = usedRegisters[1]

							local upvalueIndex = extraData[1]

							result ..= formatRegister(targetRegister) .." = ".. formatUpvalue(upvalueIndex)
						elseif opCodeName == "SETUPVAL" then
							local sourceRegister = usedRegisters[1]

							local upvalueIndex = extraData[1]

							result ..= formatUpvalue(upvalueIndex) .." = ".. formatRegister(sourceRegister)
						elseif opCodeName == "CLOSEUPVALS" then
							local targetRegister = usedRegisters[1]

							result ..= "-- clear captures from back until: ".. targetRegister
						elseif opCodeName == "GETIMPORT" then
							local targetRegister = usedRegisters[1]

							local importIndex = extraData[1]
							local importIndices = extraData[2]

							-- we load imports into constants
							local import = tostring(constants[importIndex + 1].value)

							local totalIndices = bit32.rshift(importIndices, 30)
							if totalIndices == 1 then
								if options.ListUsedGlobals and isValidGlobal(import) then
									-- it is a non-Roblox global that we need to log
									table.insert(usedGlobals, import)
								end
							end

							result ..= formatRegister(targetRegister) .." = ".. import
						elseif opCodeName == "GETTABLE" then
							local targetRegister = usedRegisters[1]
							local tableRegister = usedRegisters[2]
							local indexRegister = usedRegisters[3]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(tableRegister) .."[".. formatRegister(indexRegister) .."]"
						elseif opCodeName == "SETTABLE" then
							local sourceRegister = usedRegisters[1]
							local tableRegister = usedRegisters[2]
							local indexRegister = usedRegisters[3]

							result ..= formatRegister(tableRegister) .."[".. formatRegister(indexRegister) .."]" .." = ".. formatRegister(sourceRegister)
						elseif opCodeName == "GETTABLEKS" then
							local targetRegister = usedRegisters[1]
							local tableRegister = usedRegisters[2]

							--local slotIndex = extraData[1]
							local key = constants[extraData[2] + 1].value

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(tableRegister) .. formatIndexString(key)
						elseif opCodeName == "SETTABLEKS" then
							local sourceRegister = usedRegisters[1]
							local tableRegister = usedRegisters[2]

							--local slotIndex = extraData[1]
							local key = constants[extraData[2] + 1].value

							result ..= formatRegister(tableRegister) .. formatIndexString(key) .." = ".. formatRegister(sourceRegister)
						elseif opCodeName == "GETTABLEN" then
							local targetRegister = usedRegisters[1]
							local tableRegister = usedRegisters[2]

							local index = extraData[1] + 1

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(tableRegister) .."[".. index .."]"
						elseif opCodeName == "SETTABLEN" then
							local sourceRegister = usedRegisters[1]
							local tableRegister = usedRegisters[2]

							local index = extraData[1] + 1

							result ..= formatRegister(tableRegister) .."[".. index .."] = ".. formatRegister(sourceRegister)
						elseif opCodeName == "NEWCLOSURE" then
							local targetRegister = usedRegisters[1]

							local protoIndex = extraData[1] + 1
							local nextProto = innerProtos[protoIndex]

							writeProto(targetRegister, nextProto)
						elseif opCodeName == "DUPCLOSURE" then
							local targetRegister = usedRegisters[1]

							local protoIndex = extraData[1] + 1
							local nextProto = protoTable[constants[protoIndex].value - 1]

							writeProto(targetRegister, nextProto)
						elseif opCodeName == "NAMECALL"
							or opCodeName == "NAMECALLUDATA"
						then
							local constantIndex =
								extraData
								and extraData[2]

							if type(constantIndex) ~= "number" then
								result ..=
									"-- malformed " ..
									opCodeName ..
									" at instruction #" ..
									tostring(i)

								return
							end

							local constant =
								constants
								and constants[constantIndex + 1]

							local method =
								constant and tostring(constant.value)
								or ("missing_constant_" .. constantIndex)

							result ..= "-- :" .. method
						elseif opCodeName == "GETUDATAKS" then
							local targetRegister = usedRegisters[1]
							local userdataRegister = usedRegisters[2]
							local constantIndex = extraData[2]

							local constant = constants[constantIndex + 1]
							local key =
								constant and constant.value
								or ("missing_constant_" .. constantIndex)

							result ..=
								formatRegister(targetRegister) ..
								" = " ..
								formatRegister(userdataRegister) ..
								formatIndexString(key)
							elseif opCodeName == "SETUDATAKS" then
								local sourceRegister = usedRegisters[1]
								local userdataRegister = usedRegisters[2]
								local constantIndex = extraData[2]

								local constant = constants[constantIndex + 1]
								local key =
									constant and constant.value
									or ("missing_constant_" .. constantIndex)

								result ..=
									formatRegister(userdataRegister) ..
									formatIndexString(key) ..
									" = " ..
									formatRegister(sourceRegister)
							elseif opCodeName == "CALL" then
								local baseRegister = usedRegisters
									and usedRegisters[1]

								local encodedArguments = extraData
									and extraData[1]

								local encodedResults = extraData
									and extraData[2]

								-- Do not let malformed or misaligned actions crash the
								-- entire decompilation.
								if type(baseRegister) ~= "number"
									or type(encodedArguments) ~= "number"
									or type(encodedResults) ~= "number"
								then
									result ..= string.format(
										"-- malformed CALL action at instruction #%d " ..
										"(base=%s, args=%s, results=%s)",
										i,
										tostring(baseRegister),
										tostring(encodedArguments),
										tostring(encodedResults)
									)

									return
								end

								local numArguments = encodedArguments - 1
								local numResults = encodedResults - 1

								local namecallMethod = ""
								local argumentOffset = 0
								local callReceiverRegister = baseRegister

								-- NAMECALL and CALL are separated by a hidden AUX action.
								-- NAMECALL itself can also be hidden when trivial VM
								-- operations are suppressed, so searching only visible
								-- actions loses every method call and turns
								-- `game:GetService(x)` into the invalid `game(r, x)`.
								local precedingAction = nil

								for precedingIndex = i - 1, 1, -1 do
									local candidate = actions[precedingIndex]
									local candidateOpcode = candidate
										and candidate.opCode
									local candidateName = candidateOpcode
										and candidateOpcode.name

									if candidateName == "NAMECALL"
										or candidateName == "NAMECALLUDATA"
									then
										local data = candidate.extraData
										local registers = candidate.usedRegisters
										if type(data) == "table"
											and type(data[2]) == "number"
											and type(registers) == "table"
											and type(registers[2]) == "number"
										then
											precedingAction = candidate
											break
										end
									elseif candidate and candidate.hide ~= true then
										-- A different visible instruction means this CALL is
										-- not paired with a NAMECALL.
										break
									end
								end

								if precedingAction then
									local precedingOpCode =
										precedingAction.opCode

									local precedingExtraData =
										precedingAction.extraData

									local precedingName =
										precedingOpCode
										and precedingOpCode.name

									local isNamecall =
										precedingName == "NAMECALL"
										or precedingName == "NAMECALLUDATA"

									if isNamecall
										and type(precedingExtraData) == "table"
										and type(precedingExtraData[2]) == "number"
									then
										local constantIndex =
											precedingExtraData[2]

										local methodConstant =
											constants
											and constants[constantIndex + 1]

										local methodName

										if methodConstant
											and methodConstant.value ~= nil
										then
											methodName =
												tostring(methodConstant.value)
										else
											methodName =
												"missing_constant_" ..
												tostring(constantIndex)
										end

										namecallMethod = ":" .. methodName

										-- NAMECALL A B stores the callable in A but the
										-- source object (`self`) is register B. Emitting A as
										-- the receiver produced calls such as v0:Stop()
										-- instead of self:Stop().
										local precedingRegisters = precedingAction.usedRegisters
										if precedingRegisters
											and type(precedingRegisters[2]) == "number"
										then
											callReceiverRegister = precedingRegisters[2]
										end

										-- Encoded NAMECALL arguments include self.
										-- Colon syntax supplies self implicitly.
										if numArguments > 0 then
											numArguments -= 1
										end

										argumentOffset = 1
									end
								end

								local callBody = ""

								-- Build destination registers.
								if numResults == -1 then
					-- Luau MULTRET has no direct assignment syntax. Keep the
					-- first register as the symbolic tuple head instead of
					-- emitting the invalid statement `... = call()`.
					callBody ..= formatRegister(baseRegister) .. " = "
								elseif numResults > 0 then
									local outputRegisters = {}

									for resultIndex = 0, numResults - 1 do
										outputRegisters[#outputRegisters + 1] =
											formatRegister(
												baseRegister + resultIndex
											)
									end

									callBody ..=
										table.concat(outputRegisters, ", ") ..
										" = "
								end

								-- Build the function/method expression.
								callBody ..=
									formatRegister(callReceiverRegister) ..
									namecallMethod ..
									"("

								-- Build arguments.
								if numArguments == -1 then
									callBody ..= "..."
								elseif numArguments > 0 then
									local arguments = {}

									for argumentIndex = 1, numArguments do
										arguments[#arguments + 1] =
											formatRegister(
												baseRegister +
												argumentIndex +
												argumentOffset
											)
									end

									callBody ..=
										table.concat(arguments, ", ")
								end

								callBody ..= ")"
								result ..= callBody
						elseif opCodeName == "RETURN" then
							local baseRegister = usedRegisters[1]

							local retBody = ""

							local totalValues = extraData[1] - 2
							if totalValues == -2 then -- MULTRET
								retBody ..= " ".. formatRegister(baseRegister) ..", ..."
							elseif totalValues > -1 then
								retBody ..= " "

								for i = 0, totalValues do
									retBody ..= formatRegister(baseRegister + i)

									if i ~= totalValues then
										retBody ..= ", "
									end
								end
							end

							result ..= "return".. retBody
						elseif opCodeName == "JUMP" then
							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							--makeJumpMarker(endIndex)

							result ..= "-- jump to #" .. endIndex
						elseif opCodeName == "JUMPBACK" then
							local jumpOffset = extraData[1] + 1

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							--makeJumpMarker(endIndex)

							result ..= "-- jump back to #" .. endIndex
						elseif opCodeName == "JUMPIF" then
							local sourceRegister = usedRegisters[1]

							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if not ".. formatRegister(sourceRegister) .." then -- goto #".. endIndex
						elseif opCodeName == "JUMPIFNOT" then
							local sourceRegister = usedRegisters[1]

							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(sourceRegister) .." then -- goto #".. endIndex
						elseif opCodeName == "JUMPIFEQ" then
							local leftRegister = usedRegisters[1]
							local rightRegister = usedRegisters[2]

							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(leftRegister) .." ~= ".. formatRegister(rightRegister) .." then -- goto #".. endIndex
						elseif opCodeName == "JUMPIFLE" then
							local leftRegister = usedRegisters[1]
							local rightRegister = usedRegisters[2]

							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(leftRegister) .." > ".. formatRegister(rightRegister) .." then -- goto #".. endIndex
						elseif opCodeName == "JUMPIFLT" then -- may be wrong
							local leftRegister = usedRegisters[1]
							local rightRegister = usedRegisters[2]

							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(leftRegister) .." >= ".. formatRegister(rightRegister) .." then -- goto #".. endIndex
						elseif opCodeName == "JUMPIFNOTEQ" then
							local leftRegister = usedRegisters[1]
							local rightRegister = usedRegisters[2]

							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(leftRegister) .." == ".. formatRegister(rightRegister) .." then -- goto #".. endIndex
						elseif opCodeName == "JUMPIFNOTLE" then
							local leftRegister = usedRegisters[1]
							local rightRegister = usedRegisters[2]

							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(leftRegister) .." <= ".. formatRegister(rightRegister) .." then -- goto #".. endIndex
						elseif opCodeName == "JUMPIFNOTLT" then
							local leftRegister = usedRegisters[1]
							local rightRegister = usedRegisters[2]

							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(leftRegister) .." < ".. formatRegister(rightRegister) .." then -- goto #".. endIndex
						elseif opCodeName == "ADD" then
							local targetRegister = usedRegisters[1]
							local leftRegister = usedRegisters[2]
							local rightRegister = usedRegisters[3]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(leftRegister) .." + ".. formatRegister(rightRegister)
						elseif opCodeName == "SUB" then
							local targetRegister = usedRegisters[1]
							local leftRegister = usedRegisters[2]
							local rightRegister = usedRegisters[3]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(leftRegister) .." - ".. formatRegister(rightRegister)
						elseif opCodeName == "MUL" then
							local targetRegister = usedRegisters[1]
							local leftRegister = usedRegisters[2]
							local rightRegister = usedRegisters[3]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(leftRegister) .." * ".. formatRegister(rightRegister)
						elseif opCodeName == "DIV" then
							local targetRegister = usedRegisters[1]
							local leftRegister = usedRegisters[2]
							local rightRegister = usedRegisters[3]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(leftRegister) .." / ".. formatRegister(rightRegister)
						elseif opCodeName == "MOD" then
							local targetRegister = usedRegisters[1]
							local leftRegister = usedRegisters[2]
							local rightRegister = usedRegisters[3]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(leftRegister) .." % ".. formatRegister(rightRegister)
						elseif opCodeName == "POW" then
							local targetRegister = usedRegisters[1]
							local leftRegister = usedRegisters[2]
							local rightRegister = usedRegisters[3]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(leftRegister) .." ^ ".. formatRegister(rightRegister)
						elseif opCodeName == "ADDK" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(sourceRegister) .." + ".. value
						elseif opCodeName == "SUBK" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(sourceRegister) .." - ".. value
						elseif opCodeName == "MULK" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(sourceRegister) .." * ".. value
						elseif opCodeName == "DIVK" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(sourceRegister) .." / ".. value
						elseif opCodeName == "MODK" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(sourceRegister) .." % ".. value
						elseif opCodeName == "POWK" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(sourceRegister) .." ^ ".. value
						elseif opCodeName == "AND" then
							local targetRegister = usedRegisters[1]
							local leftRegister = usedRegisters[2]
							local rightRegister = usedRegisters[3]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(leftRegister) .." and ".. formatRegister(rightRegister)
						elseif opCodeName == "OR" then
							local targetRegister = usedRegisters[1]
							local leftRegister = usedRegisters[2]
							local rightRegister = usedRegisters[3]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(leftRegister) .." or ".. formatRegister(rightRegister)
						elseif opCodeName == "ANDK" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]
							local value =
								formatConstantValue(constants[extraData[1] + 1])

							result ..=
								formatRegister(targetRegister) ..
								" = " ..
								formatRegister(sourceRegister) ..
								" and " ..
								value

						elseif opCodeName == "ORK" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]
							local value =
								formatConstantValue(constants[extraData[1] + 1])

							result ..=
								formatRegister(targetRegister) ..
								" = " ..
								formatRegister(sourceRegister) ..
								" or " ..
								value
						elseif opCodeName == "CONCAT" then
							local targetRegister = table.remove(usedRegisters, 1)

							local totalRegisters = #usedRegisters

							local concatBody = ""
							for i = 1, totalRegisters do
								local register = usedRegisters[i]
								concatBody ..= formatRegister(register)

								if i ~= totalRegisters then
									concatBody ..= " .. "
								end
							end
							result ..= formatRegister(targetRegister) .." = ".. concatBody
						elseif opCodeName == "NOT" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							result ..= formatRegister(targetRegister) .." = not ".. formatRegister(sourceRegister)
						elseif opCodeName == "MINUS" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							result ..= formatRegister(targetRegister) .." = -".. formatRegister(sourceRegister)
						elseif opCodeName == "LENGTH" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							result ..= formatRegister(targetRegister) .." = #".. formatRegister(sourceRegister)
						elseif opCodeName == "NEWTABLE" then
							local targetRegister = usedRegisters[1]

							--local tableHashSize = extraData[1]
							local arraySize = extraData[2]

							result ..= formatRegister(targetRegister) .." = {}"

							if options.ShowDebugInformation and arraySize > 0 then
								result ..= " --[[".. arraySize .." preallocated indexes]]"
							end
					elseif opCodeName == "DUPTABLE" then
						local targetRegister = usedRegisters[1]
						local template = constants[extraData[1] + 1].value

						local entries = {}

						for entryIndex = 1, template.size do
							local keyConstantIndex = template.keys[entryIndex]
							local keyText =
								formatConstantValue(constants[keyConstantIndex])

							local valueText = "0"

							if template.prefilled and template.values then
								local valueConstantIndex =
									template.values[entryIndex]

								if valueConstantIndex then
									valueText = formatConstantValue(
										constants[valueConstantIndex]
									)
								end
							end

							entries[entryIndex] =
								"[" .. tostring(keyText) .. "] = " ..
								tostring(valueText)
						end

						result ..=
							formatRegister(targetRegister) ..
							" = {" ..
							table.concat(entries, ", ") ..
							"}"
						elseif opCodeName == "SETLIST" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]
							local startIndex = extraData[1]
							local encodedCount = extraData[2]

							if encodedCount == 0 then
								result ..=
									formatRegister(targetRegister) ..
									"[" .. startIndex .. "] = ..."
							else
								local valueCount = encodedCount - 1
								local assignments = {}

								for offset = 0, valueCount - 1 do
									assignments[#assignments + 1] =
										formatRegister(targetRegister) ..
										"[" .. (startIndex + offset) .. "] = " ..
										formatRegister(sourceRegister + offset)
								end

								result ..= table.concat(assignments, "\n")
							end
						elseif opCodeName == "FORNPREP" then
							local limitRegister = usedRegisters[1]
							local stepRegister = usedRegisters[2]
							local indexRegister = usedRegisters[3]
							local variableRegister = usedRegisters[4]

							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							-- we have FORNLOOP
							--makeJumpMarker(endIndex)

							local numericStartBody =
								"for " .. formatRegister(variableRegister) ..
								" = " .. formatRegister(indexRegister) ..
								", " .. formatRegister(limitRegister) ..
								", " .. formatRegister(stepRegister) ..
								" do -- end at #" .. endIndex
							result ..= numericStartBody
						elseif opCodeName == "FORNLOOP" then
							local targetRegister = usedRegisters[1]

							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							local numericEndBody = "end -- iterate + jump to #".. endIndex
							result ..= numericEndBody
						elseif opCodeName == "FORGLOOP" then
							local jumpOffset = extraData[1]
							--local aux = extraData[2]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							local genericEndBody = "end -- iterate + jump to #".. endIndex
							result ..= genericEndBody
						elseif opCodeName == "FORGPREP_INEXT" then
							local targetRegister = usedRegisters[1] + 1

							local variablesBody = formatRegister(targetRegister + 2) ..", ".. formatRegister(targetRegister + 3)

							result ..= "for ".. variablesBody .." in ipairs(".. formatRegister(targetRegister) ..") do"
						elseif opCodeName == "FORGPREP_NEXT" then
							local targetRegister = usedRegisters[1] + 1

							local variablesBody = formatRegister(targetRegister + 2) ..", ".. formatRegister(targetRegister + 3)

							result ..= "for ".. variablesBody .." in pairs(".. formatRegister(targetRegister) ..") do -- could be doing next, t"
						elseif opCodeName == "FORGPREP" then
							local targetRegister = usedRegisters[1]

							-- D targets the FORGLOOP instruction. The previous +2
							-- landed on FORGLOOP's AUX word, whose action has no
							-- registers, producing `for  in ... do`.
							local jumpOffset = extraData[1] + 1

							-- where the FORGLOOP instruction resides
							local endIndex = i + jumpOffset

							local endAction = actions[endIndex]
							local endUsedRegisters = endAction
								and endAction.usedRegisters
								or {}

							local variablesBody = ""

							local totalRegisters = #endUsedRegisters
							for i, register in endUsedRegisters do
								variablesBody ..= formatRegister(register)

								if i ~= totalRegisters then
									variablesBody ..= ", "
								end
							end

							result ..= "for ".. variablesBody .." in ".. formatRegister(targetRegister) .." do -- end at #".. endIndex
						elseif opCodeName == "GETVARARGS" then
							local variableCount = extraData[1] - 1

							local retBody = ""
							if variableCount == -1 then -- MULTRET
								-- i don't know about this
								local targetRegister = usedRegisters[1]
								retBody = formatRegister(targetRegister)
							else
								for i = 1, variableCount do
									local register = usedRegisters[i]
									retBody ..= formatRegister(register)

									if i ~= variableCount then
										retBody ..= ", "
									end
								end
							end
							retBody ..= " = ..."

							result ..= retBody
						elseif opCodeName == "PREPVARARGS" then
							local numParams = extraData[1]

							result ..= "-- ... ; number of fixed args: ".. numParams
						elseif opCodeName == "LOADKX" then
							local targetRegister = usedRegisters[1]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. value
						elseif opCodeName == "JUMPX" then -- the cooler jump
							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							--makeJumpMarker(endIndex)

							result ..= "-- jump to #" .. endIndex
						elseif opCodeName == "COVERAGE" then
							local hitCount = extraData[1]

							result ..= "-- coverage (".. hitCount ..")"
						elseif opCodeName == "JUMPXEQKNIL" then
							local sourceRegister = usedRegisters[1]

							local jumpOffset = extraData[1] -- if 1 then don't jump
							local aux = extraData[2]

							local reverse = bit32.rshift(aux, 0x1F) ~= 1
							local sign = if reverse then "~=" else "=="

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(sourceRegister) .." ".. sign .." nil then -- goto #".. endIndex
						elseif opCodeName == "JUMPXEQKB" then
							local sourceRegister = usedRegisters[1]

							local jumpOffset = extraData[1] -- if 1 then don't jump
							local aux = extraData[2]

							local value = tostring(toBoolean(bit32.band(aux, 1)))

							local reverse = bit32.rshift(aux, 0x1F) ~= 1
							local sign = if reverse then "~=" else "=="

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(sourceRegister) .." ".. sign .." ".. value .." then -- goto #".. endIndex
						elseif opCodeName == "JUMPXEQKN" then
							local sourceRegister = usedRegisters[1]

							local jumpOffset = extraData[1] -- if 1 then don't jump
							local aux = extraData[2]

							local value = formatConstantValue(constants[bit32.band(aux, 0xFFFFFF) + 1])

							local reverse = bit32.rshift(aux, 0x1F) ~= 1
							local sign = if reverse then "~=" else "=="

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(sourceRegister) .." ".. sign .." ".. value .." then -- goto #".. endIndex
						elseif opCodeName == "JUMPXEQKS" then
							local sourceRegister = usedRegisters[1]

							local jumpOffset = extraData[1] -- if 1 then don't jump
							local aux = extraData[2]

							local value = formatConstantValue(constants[bit32.band(aux, 0xFFFFFF) + 1])

							local reverse = bit32.rshift(aux, 0x1F) ~= 1
							local sign = if reverse then "~=" else "=="

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(sourceRegister) .." ".. sign .." ".. value .." then -- goto #".. endIndex
						elseif opCodeName == "CAPTURE" then
							result ..= "-- upvalue capture"
						elseif opCodeName == "SUBRK" then -- constant sub (reverse SUBK)
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. value .." - ".. formatRegister(sourceRegister)
						elseif opCodeName == "DIVRK" then -- constant div (reverse DIVK)
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. value .." / ".. formatRegister(sourceRegister)
						elseif opCodeName == "IDIV" then -- floor division
							local targetRegister = usedRegisters[1]
							local sourceLeftRegister = usedRegisters[2]
							local sourceRightRegister = usedRegisters[3]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(sourceLeftRegister) .." // ".. formatRegister(sourceRightRegister)
						elseif opCodeName == "IDIVK" then -- floor division with 1 constant argument
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(sourceRegister) .." // ".. value
						elseif opCodeName == "FASTCALL" then -- reads info from the CALL instruction
							local bfid = extraData[1] -- builtin function id
							--local jumpOffset = extraData[2]

							-- where for CALL resides
							--local callIndex = i + jumpOffset

							--local callAction = actions[callIndex]
							--local callUsedRegisters = callAction.usedRegisters
							--local callExtraData = callAction.extraData

							result ..= "-- FASTCALL; ".. Luau:GetBuiltinInfo(bfid) .."()"
						elseif opCodeName == "FASTCALL1" then -- 1 register argument
							local sourceArgumentRegister = usedRegisters[1]

							local bfid = extraData[1] -- builtin function id
							--local jumpOffset = extraData[2]

							result ..= "-- FASTCALL1; ".. Luau:GetBuiltinInfo(bfid) .."(".. formatRegister(sourceArgumentRegister) ..")"
						elseif opCodeName == "FASTCALL2" then -- 2 register arguments
							local sourceArgumentRegister = usedRegisters[1]
							local sourceArgumentRegister2 = usedRegisters[2]

							local bfid = extraData[1] -- builtin function id
							--local jumpOffset = extraData[2]

							result ..= "-- FASTCALL2; ".. Luau:GetBuiltinInfo(bfid) .."(".. formatRegister(sourceArgumentRegister) ..", ".. formatRegister(sourceArgumentRegister2) ..")"
						elseif opCodeName == "FASTCALL2K" then -- 1 register argument and 1 constant argument
							local sourceArgumentRegister = usedRegisters[1]

							local bfid = extraData[1] -- builtin function id
							--local jumpOffset = extraData[2]
							local value = formatConstantValue(constants[extraData[3] + 1])

							result ..= "-- FASTCALL2K; ".. Luau:GetBuiltinInfo(bfid) .."(".. formatRegister(sourceArgumentRegister) ..", ".. value ..")"
						elseif opCodeName == "FASTCALL3" then
							local sourceArgumentRegister = usedRegisters[1]
							local sourceArgumentRegister2 = usedRegisters[2]
							local sourceArgumentRegister3 = usedRegisters[3]
							local bfid = extraData[1]

							result ..=
								"-- FASTCALL3; " ..
								Luau:GetBuiltinInfo(bfid) ..
								"(" ..
								formatRegister(sourceArgumentRegister) ..
								", " ..
								formatRegister(sourceArgumentRegister2) ..
								", " ..
								formatRegister(sourceArgumentRegister3) ..
								")"
						end
					end
					local function writeFooter()
						result ..= "\n"
					end

					writeHeader()

					local bodySuccess, bodyError = xpcall(
						writeOperationBody,
						function(err)
							if debug and debug.traceback then
								return debug.traceback(
									tostring(err),
									2
								)
							end

							return tostring(err)
						end
					)

					if not bodySuccess then
						result ..= string.format(
							"--[[ DECOMPILER OPCODE ERROR\n" ..
							"Build: %s\n" ..
							"Proto: %s\n" ..
							"Instruction: %s\n" ..
							"Opcode: %s\n" ..
							"Used registers: %s\n" ..
							"Extra data: %s\n" ..
							"Error: %s\n" ..
							"]] ",
							BUILD_ID,
							tostring(proto.name or proto.id),
							tostring(i),
							tostring(opCodeName),
							usedRegisters
								and table.concat(usedRegisters, ",")
								or "nil",
							extraData
								and table.concat(extraData, ",")
								or "nil",
							tostring(bodyError)
						)
					end

					writeFooter()
					handleJumpMarkers()
				end
			end
			writeActions(registerActions[mainProtoId])

			if options.DecompilerMode == "optdec" then
				-- Keep the proven decoder/emitter and run the dedicated reconstruction
				-- pipeline as a final pass. This preserves the existing architecture.
				local optimizeSuccess, optimized = xpcall(
					function()
						return Optdec.optimize(result, options)
					end,
					function(err)
						if debug and debug.traceback then
							return debug.traceback(tostring(err), 2)
						end
						return tostring(err)
					end
				)

				if optimizeSuccess then
					result = optimized
				else
					-- Never lose a valid low-level reconstruction because an
					-- optional readability pass encountered an edge case.
					result = "--[[ optdec optimizer fallback: " .. optimized .. " ]]\n" .. result
				end
			end

			finalResult = processResult(result)
		else
			finalResult = processResult(
				"-- unsupported decompiler mode: " .. tostring(options.DecompilerMode)
			)
		end

		return finalResult
	end

	local function manager(proceed, issue)
		if not proceed then
			if issue == "COMPILATION_FAILURE" then
				local errorMessageLength = reader:len() - 1
				local errorMessage =
					reader:nextString(errorMessageLength)

				return string.format(
					Strings.COMPILATION_FAILURE,
					errorMessage
				)
			end

			return Strings.UNSUPPORTED_LBC_VERSION
		end

		local startTime = os.clock()
		local result
		local internalError
		local completed = false

		task.spawn(function()
			local success, value = xpcall(
				function()
					return finalize(organize())
				end,
				function(err)
					if debug and debug.traceback then
						return debug.traceback(tostring(err), 2)
					end

					return tostring(err)
				end
			)

			if success then
				result = value
			else
				internalError = value
			end

			completed = true
		end)

		while not completed
			and os.clock() - startTime < options.DecompilerTimeout
		do
			task.wait()
		end

		local elapsedTime = os.clock() - startTime

		if internalError then
			return string.format(
				"-- DECOMPILER INTERNAL ERROR\n%s",
				internalError
			), elapsedTime
		end

		if not completed then
			return Strings.TIMEOUT, elapsedTime
		end

		return string.format(
			Strings.SUCCESS,
			result
		), elapsedTime
	end

	bytecodeVersion = reader:nextByte()
	warn(
		"[Advanced Decompiler] Bytecode version:",
		bytecodeVersion,
		"supported:",
		LuauBytecodeTag.LBC_VERSION_MIN,
		"to",
		LuauBytecodeTag.LBC_VERSION_MAX
	)
if bytecodeVersion == 0 then
	return manager(false, "COMPILATION_FAILURE")
end

if bytecodeVersion < LuauBytecodeTag.LBC_VERSION_MIN then
	return string.format(
		"-- BYTECODE VERSION %d IS TOO OLD; SUPPORTED RANGE IS %d..%d",
		bytecodeVersion,
		LuauBytecodeTag.LBC_VERSION_MIN,
		LuauBytecodeTag.LBC_VERSION_MAX
	)
end

if bytecodeVersion > LuauBytecodeTag.LBC_VERSION_MAX then
	return string.format(
		"-- BYTECODE VERSION %d IS TOO NEW; SUPPORTED RANGE IS %d..%d",
		bytecodeVersion,
		LuauBytecodeTag.LBC_VERSION_MIN,
		LuauBytecodeTag.LBC_VERSION_MAX
	)
end

return manager(true)
end

local _ENV = (getgenv or getrenv or getfenv)()

-- Direct bytecode entry point added by OPTDEC v5. This complements the
-- existing Instance-based decompile API without replacing it.
_ENV.optdec = function(bytecode, customOptions)
	if type(bytecode) ~= "string" then
		error("invalid argument #1 to 'optdec' (Luau bytecode string expected)", 2)
	end

	local options = table.clone(DEFAULT_OPTIONS)
	options.DecompilerMode = "optdec"

	if customOptions ~= nil then
		if type(customOptions) ~= "table" then
			error("invalid argument #2 to 'optdec' (table expected)", 2)
		end
		for key, value in customOptions do
			options[key] = value
		end
		-- This entry point always runs the high-fidelity reconstruction pass.
		options.DecompilerMode = "optdec"
	end

	local output, elapsedTime = Decompile(bytecode, options)
	if options.ReturnElapsedTime then
		return output, elapsedTime
	end
	return output
end

-- Lossless local collection mode for building and regression-testing future
-- decompiler versions. Collection never performs an HTTP request or upload.
-- It returns JSON and optionally writes it when the host exposes writefile.
_ENV.collectoptdec = function(bytecode, config)
	if type(bytecode) ~= "string" then
		error("invalid argument #1 to 'collectoptdec' (Luau bytecode string expected)", 2)
	end

	config = config or {}
	if type(config) ~= "table" then
		error("invalid argument #2 to 'collectoptdec' (table expected)", 2)
	end

	local options = table.clone(DEFAULT_OPTIONS)
	options.DecompilerTimeout = config.DecompilerTimeout or 300
	options.DecompilerMode = config.DecompilerMode or "disasm"
	options.ShowInstructionLines = true
	options.ShowOperationIndex = true
	options.ShowOperationNames = true
	options.ShowTrivialOperations = true
	options.ShowDebugInformation = true
	options.ShowProtoDebugInformation = true
	options.UseTypeInfo = true
	options.ListUsedGlobals = true
	options.ReturnElapsedTime = true
	options.KeepControlFlowAnnotations = true

	local session = Collector.begin(bytecode, {
		label = config.Label,
		notes = config.Notes,
		originalSource = config.OriginalSource,
		dexSourceOutput = config.DexSourceOutput,
		instanceSnapshot = config.InstanceSnapshot,
		externalArtifacts = config.ExternalArtifacts,
		compilerMetadata = config.CompilerMetadata,
		options = options,
	})
	options.CollectionSession = session

	Collector.event(session, "decompile-start", {
		mode = options.DecompilerMode,
	})

	local output, elapsed = Decompile(bytecode, options)
	local result = {
		primaryMode = options.DecompilerMode,
		primaryOutput = output,
		primaryElapsed = elapsed,
	}

	-- Collect both views by default. The second run intentionally has no
	-- CollectionSession because parsed/organized IR is already captured.
	if config.IncludeBothOutputs ~= false then
		local secondaryOptions = table.clone(options)
		secondaryOptions.CollectionSession = nil
		secondaryOptions.DecompilerMode = if options.DecompilerMode == "disasm"
			then "optdec"
			else "disasm"

		local secondaryOutput, secondaryElapsed =
			Decompile(bytecode, secondaryOptions)

		result.secondaryMode = secondaryOptions.DecompilerMode
		result.secondaryOutput = secondaryOutput
		result.secondaryElapsed = secondaryElapsed
	end

	if not session.stages.semanticIR then
		local semanticOk, semanticResult = pcall(SemanticIR.buildSession, session)
		session.stages.semanticIR = semanticOk and semanticResult or {
			schema = SemanticIR.SCHEMA,
			version = SemanticIR.VERSION,
			error = tostring(semanticResult),
		}
	end

	if not session.stages.regionTree then
		local regionOk, regionResult = pcall(RegionStructurer.buildSession, session)
		session.stages.regionTree = regionOk and regionResult or {
			schema = RegionStructurer.SCHEMA,
			version = RegionStructurer.VERSION,
			error = tostring(regionResult),
		}
	end

	if not session.stages.ast then
		local astOk, astResult = pcall(AST.buildSession, session)
		session.stages.ast = astOk and astResult or {
			schema = AST.SCHEMA,
			version = AST.VERSION,
			error = tostring(astResult),
		}
	end

	if config.IncludeV10Output ~= false then
		local v10Ok, v10Output, v10Metadata = pcall(
			Decompiler.decompileSession,
			session
		)
		if v10Ok then
			result.v10Output = v10Output
			result.v10Metadata = v10Metadata
		else
			result.v10Error = tostring(v10Output)
		end
	end

	Collector.event(session, "decompile-finish", {
		primaryElapsed = elapsed,
		primaryLength = #tostring(output),
		secondaryLength = result.secondaryOutput
			and #tostring(result.secondaryOutput)
			or nil,
	})

	Collector.finish(session, result)

	local path
	local encoded
	if config.SaveToFile ~= false then
		path, encoded = Collector.save(session, config.Path)
	else
		encoded = Collector.encode(session)
	end

	return encoded, path, session.raw.fnv1a32
end

_ENV.optdecv10 = function(bytecode, config)
	config = table.clone(config or {})
	config.SaveToFile = false
	config.IncludeV10Output = true
	local encoded = _ENV.collectoptdec(bytecode, config)
	local decoded = game:GetService("HttpService"):JSONDecode(encoded)
	if decoded.result.v10Error then
		error("OPTDEC V10 failed: " .. decoded.result.v10Error, 2)
	end
	return decoded.result.v10Output, decoded.result.v10Metadata
end

_ENV.collectscript = function(scriptObject, config)
	if not getscriptbytecode then
		error("collectscript requires getscriptbytecode", 2)
	end
	if typeof(scriptObject) ~= "Instance" then
		error("invalid argument #1 to 'collectscript' (Instance expected)", 2)
	end

	local success, bytecode = pcall(getscriptbytecode, scriptObject)
	if not success or type(bytecode) ~= "string" then
		error("failed to obtain script bytecode: " .. tostring(bytecode), 2)
	end

	config = config or {}
	if config.Label == nil then
		config.Label = scriptObject:GetFullName()
	end
	if config.InstanceSnapshot == nil then
		config.InstanceSnapshot = Collector.inspectScript(
			scriptObject,
			config
		)
	end
	return _ENV.collectoptdec(bytecode, config)
end

_ENV.decompile = function(script, x, ...)
	if not getscriptbytecode then
		error("decompile is not enabled. (getscriptbytecode is missing)", 2)
		return
	end

	if typeof(script) ~= "Instance" then
		error("invalid argument #1 to 'decompile' (Instance expected)", 2)
		return
	end

	local function isScriptValid()
		local class = script.ClassName
		if class == "Script" then
			return script.RunContext == Enum.RunContext.Client
		else
			return class == "LocalScript" or class == "ModuleScript"
		end
	end
	if not isScriptValid() then
		error("invalid argument #1 to 'decompile' (Instance<LocalScript, ModuleScript> expected)", 2)
		return
	end

	local success, result = pcall(getscriptbytecode, script)
	if not success or type(result) ~= "string" then
		error(`decompile failed to grab script bytecode: {tostring(result)}`, 2)
		return
	end

	local options
	if x then
		options = table.clone(DEFAULT_OPTIONS)

		local varType = type(x)
		if varType == "table" then -- a dictionary of options
			for k, v in x do
				options[k] = v
			end
		elseif varType == "string" then -- mode
			options.DecompilerMode = x

			local timeout = ...
			if timeout then
				if type(timeout) ~= "number" then
					error("invalid argument #3 to 'decompile' (number expected)", 2)
				end

				options.DecompilerTimeout = timeout
			end
		else
			error("invalid argument #2 to 'decompile' (table/string expected)", 2)
		end
	else
		options = DEFAULT_OPTIONS
	end

	local output, elapsedTime = Decompile(result, options)

	if options.ReturnElapsedTime then
		return output, elapsedTime
	else
		return output
	end
end
