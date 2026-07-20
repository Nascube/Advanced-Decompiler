--!optimize 2
-- OPTDEC Collection Mode v1
-- Collects local diagnostic/training data only. It never uploads or transmits.

local Collector = {}
Collector.VERSION = "1.4.0"
Collector.SCHEMA = "optdec-collection-v1.4"

local function copyArray(input)
    local output = {}
    if type(input) == "table" then
        for index, value in input do
            output[index] = value
        end
    end
    return output
end

local function safeString(value, limit)
    local text = tostring(value)
    limit = limit or 1000000
    if #text > limit then
        return text:sub(1, limit) .. "--[[TRUNCATED]]"
    end
    return text
end

local function fnv1a(bytes)
    local hash = 2166136261
    for index = 1, #bytes do
        hash = bit32.bxor(hash, string.byte(bytes, index))

		-- FNV prime = 0x01000193. A direct multiplication can exceed
		-- the exact integer range of a double and produced incorrect hashes
		-- for large bytecode. Multiply as two 16-bit limbs instead.
		local low = bit32.band(hash, 0xFFFF)
		local high = bit32.rshift(hash, 16)
		local lowProduct = low * 0x0193
		local resultLow = lowProduct % 0x10000
		local carry = math.floor(lowProduct / 0x10000)
		local resultHigh =
			(high * 0x0193 + low * 0x0100 + carry) % 0x10000

		hash = resultHigh * 0x10000 + resultLow
    end
    return string.format("%08x", hash)
end

local function bytesToHex(bytes)
    local output = table.create(#bytes)
    for index = 1, #bytes do
        output[index] = string.format("%02x", string.byte(bytes, index))
    end
    return table.concat(output)
end

local function detectCapabilities()
    local names = {
        "buffer", "debug", "getscriptbytecode", "getfunctionbytecode",
        "getgc", "getgenv", "getrenv", "getfenv", "setfenv", "loadstring",
        "readfile", "writefile", "appendfile", "isfile", "makefolder",
        "isfolder", "setclipboard", "cloneref", "gethui",
    }
    local environment = (getgenv and getgenv()) or (getfenv and getfenv()) or _G
    local result = {}
    for _, name in names do
        local value = environment and environment[name]
        result[name] = type(value)
    end
    result.task = type(task)
    result.game = if typeof then typeof(game) else type(game)
    return result
end

local function sanitize(value, seen, depth)
    local valueType = type(value)
    if valueType == "nil" or valueType == "boolean" or valueType == "string" then
        return value
    elseif valueType == "number" then
        if value ~= value then return "NaN" end
        if value == math.huge then return "Infinity" end
        if value == -math.huge then return "-Infinity" end
        return value
    elseif valueType ~= "table" then
        return `<{valueType}:{safeString(value, 1000)}>`
    end

    seen = seen or {}
    depth = depth or 0
    if seen[value] then
        return `<cycle:{seen[value]}>`
    end
    if depth >= 32 then
        return "<max-depth>"
    end

    local id = tostring(#seen + 1)
    seen[value] = id
    local output = {}
    local count = 0
    for key, child in value do
        count += 1
        if count > 1000000 then
            output.__truncated = true
            break
        end
        local safeKey = if type(key) == "string" or type(key) == "number"
            then key
            else safeString(key, 1000)
        output[safeKey] = sanitize(child, seen, depth + 1)
    end
    return output
end

local function jsonEscape(text)
    return text:gsub("\\", "\\\\")
        :gsub('"', '\\"')
        :gsub("\b", "\\b")
        :gsub("\f", "\\f")
        :gsub("\n", "\\n")
        :gsub("\r", "\\r")
        :gsub("\t", "\\t")
end

local function isArray(value)
    local maxIndex = 0
    local count = 0
    for key in value do
        if type(key) ~= "number" or key < 1 or key % 1 ~= 0 then
            return false, 0
        end
        maxIndex = math.max(maxIndex, key)
        count += 1
    end
    return maxIndex == count, maxIndex
end

local function encodeJson(value, stack)
    local valueType = type(value)
    if value == nil then return "null" end
    if valueType == "boolean" or valueType == "number" then return tostring(value) end
    if valueType == "string" then return '"' .. jsonEscape(value) .. '"' end
    if valueType ~= "table" then return '"' .. jsonEscape(tostring(value)) .. '"' end

    stack = stack or {}
    if stack[value] then return '"<cycle>"' end
    stack[value] = true

    local array, size = isArray(value)
    local output = {}
    if array then
        for index = 1, size do
            output[index] = encodeJson(value[index], stack)
        end
        stack[value] = nil
        return "[" .. table.concat(output, ",") .. "]"
    end

    local keys = {}
    for key in value do keys[#keys + 1] = tostring(key) end
    table.sort(keys)
    for _, key in keys do
        output[#output + 1] = '"' .. jsonEscape(key) .. '":' .. encodeJson(value[key], stack)
    end
    stack[value] = nil
    return "{" .. table.concat(output, ",") .. "}"
end

local function constantSnapshot(constant)
    if type(constant) ~= "table" then return sanitize(constant) end
    return {
        type = constant.type,
        value = sanitize(constant.value),
    }
end

local function protoSnapshot(proto, luau)
    local instructions = {}
    local auxiliaryOwnerPc = nil
    for pc, word in proto.instructions or {} do
        if auxiliaryOwnerPc then
            instructions[#instructions + 1] = {
                pc = pc,
                wordKind = "AUX",
                ownerPc = auxiliaryOwnerPc,
                raw = word,
                rawHex = string.format("%08x", word),
                line = proto.instructionLineInfo and proto.instructionLineInfo[pc] or nil,
            }
            auxiliaryOwnerPc = nil
            continue
        end

        local opcodeNumber = luau:INSN_OP(word)
        local opcode = luau.OpCode[opcodeNumber]
        instructions[#instructions + 1] = {
            pc = pc,
            wordKind = "INSTRUCTION",
            raw = word,
            rawHex = string.format("%08x", word),
            opcodeNumber = opcodeNumber,
            opcode = opcode and opcode.name or "INVALID",
            encoding = opcode and opcode.type or nil,
            hasAux = opcode and opcode.aux == true or false,
            A = luau:INSN_A(word),
            B = luau:INSN_B(word),
            C = luau:INSN_C(word),
            D = luau:INSN_D(word),
            sD = luau:INSN_sD(word),
            E = luau:INSN_E(word),
            line = proto.instructionLineInfo and proto.instructionLineInfo[pc] or nil,
        }

        if opcode and opcode.aux == true then
            auxiliaryOwnerPc = pc
        end
    end

    local constants = {}
    for index, constant in proto.constants or {} do
        constants[index] = constantSnapshot(constant)
    end

    local childIds = {}
    for index, child in proto.innerProtos or {} do
        childIds[index] = type(child) == "table" and child.id or child
    end

    return {
        id = proto.id,
        main = proto.main,
        name = proto.name,
        source = proto.source,
        lineDefined = proto.lineDefined,
        maxStackSize = proto.maxStackSize,
        numParams = proto.numParams,
        numUpvalues = proto.numUpvalues,
        isVarArg = proto.isVarArg,
        flags = sanitize(proto.flags),
        hasTypeInfo = proto.hasTypeInfo,
        typedParams = sanitize(proto.typedParams),
        typedUpvalues = sanitize(proto.typedUpvalues),
        typedLocals = sanitize(proto.typedLocals),
        typeInfo = sanitize(proto.typeInfo),
        sizeInstructions = proto.sizeInstructions,
        sizeConstants = proto.sizeConstants,
        sizeInnerProtos = proto.sizeInnerProtos,
        lineInfoSize = proto.lineInfoSize,
        instructions = instructions,
        constants = constants,
        childProtoIds = childIds,
        captures = sanitize(proto.captures),
        debugLocals = sanitize(proto.debugLocals),
        debugUpvalues = sanitize(proto.debugUpvalues),
        instructionLineInfo = sanitize(proto.instructionLineInfo),
    }
end

-- Build a lossless first-pass control-flow graph from raw executable PCs.
-- These are CFG seeds only; dominators/regions are intentionally deferred to
-- the future SSA/AST decompiler.
local function cfgSeedSnapshot(proto)
    local rawInstructionPcs = {}
    local captureDescriptorPcs = {}
    local executable = {}
    local executableSet = {}

    for _, instruction in proto.instructions or {} do
        if instruction.wordKind == "INSTRUCTION" then
            rawInstructionPcs[#rawInstructionPcs + 1] = instruction.pc
            if instruction.opcode == "CAPTURE" then
                captureDescriptorPcs[#captureDescriptorPcs + 1] = instruction.pc
            else
                executable[#executable + 1] = instruction
                executableSet[instruction.pc] = true
            end
        end
    end

    local nextPc = {}
    for index, instruction in executable do
        nextPc[instruction.pc] = executable[index + 1]
            and executable[index + 1].pc or nil
    end

    local leaders = {}
    if executable[1] then leaders[executable[1].pc] = true end
    local edges, edgeKinds = {}, {}
    local invalidTargetCount = 0

    local function addEdge(fromPc, toPc, kind, markLeader)
        if type(toPc) ~= "number" then return end
        local valid = executableSet[toPc] == true
        if not valid then invalidTargetCount += 1 end
        edges[#edges + 1] = {
            from = fromPc,
            to = toPc,
            kind = kind,
            targetIsExecutable = valid,
        }
        edgeKinds[kind] = (edgeKinds[kind] or 0) + 1
        if markLeader then leaders[toPc] = true end
    end

    local conditional = {
        JUMPIF = true, JUMPIFNOT = true,
        JUMPIFEQ = true, JUMPIFLE = true, JUMPIFLT = true,
        JUMPIFNOTEQ = true, JUMPIFNOTLE = true, JUMPIFNOTLT = true,
        JUMPXEQKNIL = true, JUMPXEQKB = true,
        JUMPXEQKN = true, JUMPXEQKS = true,
        FORNPREP = true, FORNLOOP = true, FORGLOOP = true,
    }
    local genericPrep = {
        FORGPREP = true,
        FORGPREP_INEXT = true,
        FORGPREP_NEXT = true,
    }
    local fastcall = {
        FASTCALL = true, FASTCALL1 = true, FASTCALL2 = true,
        FASTCALL2K = true, FASTCALL3 = true,
    }

    for _, instruction in executable do
        local pc = instruction.pc
        local name = instruction.opcode
        local fallthrough = nextPc[pc]
        local dTarget = pc + 1 + instruction.sD
        local cTarget = pc + 1 + instruction.C

        if conditional[name] then
            addEdge(pc, dTarget, "branch", true)
            addEdge(pc, fallthrough, "fallthrough", true)
        elseif genericPrep[name] then
            addEdge(pc, dTarget, "loop-prep", true)
            if fallthrough then leaders[fallthrough] = true end
        elseif name == "LOADB" and instruction.C ~= 0 then
            addEdge(pc, cTarget, "skip", true)
            if fallthrough then leaders[fallthrough] = true end
        elseif fastcall[name] then
            addEdge(pc, cTarget, "fastpath", true)
            addEdge(pc, fallthrough, "fallback", true)
        elseif name == "JUMP" or name == "JUMPBACK" then
            addEdge(
                pc,
                dTarget,
                name == "JUMPBACK" and "backedge" or "jump",
                true
            )
            if fallthrough then leaders[fallthrough] = true end
        elseif name == "JUMPX" then
            addEdge(pc, pc + 1 + instruction.E, "jump", true)
            if fallthrough then leaders[fallthrough] = true end
        elseif name == "RETURN" then
            if fallthrough then leaders[fallthrough] = true end
        else
            addEdge(pc, fallthrough, "next", false)
        end
    end

    local leaderList = {}
    for pc in leaders do
        if executableSet[pc] then leaderList[#leaderList + 1] = pc end
    end
    table.sort(leaderList)

    local executablePcs = {}
    for index, instruction in executable do
        executablePcs[index] = instruction.pc
    end

    local blocks = {}
    local pcToBlock = {}
    local current = nil
    for _, instruction in executable do
        if leaders[instruction.pc] or not current then
            current = {
                id = #blocks + 1,
                startPc = instruction.pc,
                endPc = instruction.pc,
                instructionPcs = {},
                predecessors = {},
                successors = {},
                reachable = false,
            }
            blocks[#blocks + 1] = current
        end
        current.instructionPcs[#current.instructionPcs + 1] = instruction.pc
        current.endPc = instruction.pc
        current.terminatorPc = instruction.pc
        pcToBlock[instruction.pc] = current.id
    end

    local blockEdgeSet = {}
    local blockEdges = {}
    for _, edge in edges do
        local fromBlock = pcToBlock[edge.from]
        local toBlock = pcToBlock[edge.to]
        if fromBlock and toBlock then
            local key = tostring(fromBlock) .. ":" .. tostring(toBlock)
            if not blockEdgeSet[key] then
                blockEdgeSet[key] = true
                blockEdges[#blockEdges + 1] = {
                    fromBlock = fromBlock,
                    toBlock = toBlock,
                }
                local successors = blocks[fromBlock].successors
                successors[#successors + 1] = toBlock
                local predecessors = blocks[toBlock].predecessors
                predecessors[#predecessors + 1] = fromBlock
            end
        end
    end

    if blocks[1] then
        local queue, head = {1}, 1
        blocks[1].reachable = true
        while head <= #queue do
            local id = queue[head]
            head += 1
            for _, successor in blocks[id].successors do
                if not blocks[successor].reachable then
                    blocks[successor].reachable = true
                    queue[#queue + 1] = successor
                end
            end
        end
    end

    local unreachableBlocks = {}
    for _, block in blocks do
        table.sort(block.predecessors)
        table.sort(block.successors)
        if not block.reachable then
            unreachableBlocks[#unreachableBlocks + 1] = block.id
        end
    end

    return {
        rawInstructionPcs = rawInstructionPcs,
        executablePcs = executablePcs,
        captureDescriptorPcs = captureDescriptorPcs,
        leaders = leaderList,
        edges = edges,
        blocks = blocks,
        blockEdges = blockEdges,
        unreachableBlocks = unreachableBlocks,
        summary = {
            rawInstructionCount = #rawInstructionPcs,
            executableNodeCount = #executablePcs,
            captureDescriptorCount = #captureDescriptorPcs,
            leaderCount = #leaderList,
            blockCount = #blocks,
            edgeCount = #edges,
            blockEdgeCount = #blockEdges,
            invalidTargetCount = invalidTargetCount,
            unreachableBlockCount = #unreachableBlocks,
            edgeKinds = edgeKinds,
        },
    }
end
local function captureCompleteness(protos, originalSource)
    local report = {
        hasOriginalSource = type(originalSource) == "string" and #originalSource > 0,
        prototypeCount = 0,
        instructionWordCount = 0,
        instructionCount = 0,
        auxiliaryWordCount = 0,
        invalidOpcodeCount = 0,
        constantCount = 0,
        debugLocalCount = 0,
        debugUpvalueCount = 0,
        typedPrototypeCount = 0,
        namedPrototypeCount = 0,
        capturedUpvalueCount = 0,
    }

    for _, proto in protos do
        report.prototypeCount += 1
        if proto.name then report.namedPrototypeCount += 1 end
        if proto.hasTypeInfo then report.typedPrototypeCount += 1 end
        report.constantCount += #(proto.constants or {})
        report.debugLocalCount += #(proto.debugLocals or {})
        report.debugUpvalueCount += #(proto.debugUpvalues or {})
        report.capturedUpvalueCount += #(proto.captures or {})

        for _, instruction in proto.instructions or {} do
            report.instructionWordCount += 1
            if instruction.wordKind == "AUX" then
                report.auxiliaryWordCount += 1
            else
                report.instructionCount += 1
                if instruction.opcode == "INVALID" then
                    report.invalidOpcodeCount += 1
                end
            end
        end
    end

    report.hasDebugNames =
        report.debugLocalCount > 0 or report.debugUpvalueCount > 0
    report.canRecoverNamesDirectly = report.hasDebugNames
    -- Ground-truth source enables supervised name-recovery research even
    -- when the bytecode contains no debug local/upvalue names.
    report.canTrainNameRecovery = report.hasOriginalSource
    report.canTrainStructureRecovery = report.hasOriginalSource
    return report
end

local function resolveRuntimeFunction(name)
	local environment = (getgenv and getgenv())
		or (getfenv and getfenv())
		or _G
	local value = environment and environment[name]
	if type(value) == "function" then return value end
	value = debug and debug[name]
	if type(value) == "function" then return value end
	return nil
end

local function inspectClosure(rootClosure, limits)
	limits = limits or {}
	local maxFunctions = limits.MaxRuntimeFunctions or 5000
	local maxDepth = limits.MaxRuntimeProtoDepth or 64
	local getInfo = resolveRuntimeFunction("getinfo")
	local getConstants = resolveRuntimeFunction("getconstants")
	local getProtos = resolveRuntimeFunction("getprotos")
	local getUpvalues = resolveRuntimeFunction("getupvalues")
	local seen = {}
	local total = 0

	local function visit(fn, depth)
		if type(fn) ~= "function" then return sanitize(fn) end
		if seen[fn] then return {reference = seen[fn]} end
		if total >= maxFunctions then return {truncated = "function-limit"} end
		if depth > maxDepth then return {truncated = "depth-limit"} end

		total += 1
		local id = total
		seen[fn] = id
		local output = {id = id, depth = depth}

		if getInfo then
			local ok, value = pcall(getInfo, fn)
			if ok then output.info = sanitize(value) end
		end
		if getConstants then
			local ok, value = pcall(getConstants, fn)
			if ok then output.constants = sanitize(value) end
		end
		if getUpvalues then
			local ok, value = pcall(getUpvalues, fn)
			if ok then output.upvalues = sanitize(value) end
		end
		if getProtos then
			local ok, value = pcall(getProtos, fn)
			if ok and type(value) == "table" then
				output.protos = {}
				for index, child in value do
					output.protos[index] = visit(child, depth + 1)
				end
			end
		end
		return output
	end

	return {
		root = visit(rootClosure, 0),
		functionCount = total,
		limits = {
			maxFunctions = maxFunctions,
			maxDepth = maxDepth,
		},
	}
end

function Collector.inspectScript(scriptObject, config)
	config = config or {}
	local result = {
		typeof = typeof and typeof(scriptObject) or type(scriptObject),
		properties = {},
		ancestry = {},
		introspectionAttempts = {},
	}

	local function captureProperty(name)
		local ok, value = pcall(function() return scriptObject[name] end)
		result.introspectionAttempts["property:" .. name] = {
			ok = ok,
			error = ok and nil or safeString(value, 4096),
		}
		if ok then result.properties[name] = sanitize(value) end
	end

	for _, name in {
		"Name", "ClassName", "Archivable", "Disabled", "Enabled",
		"RunContext", "LinkedSource", "SourceAssetId", "ScriptGuid",
		"UniqueId", "Sandboxed",
	} do
		captureProperty(name)
	end

	local ok, value = pcall(function() return scriptObject:GetFullName() end)
	if ok then result.fullName = value end
	local okParent, parent = pcall(function() return scriptObject.Parent end)
	if okParent and parent then
		local okName, parentName = pcall(function() return parent:GetFullName() end)
		result.parentFullName = okName and parentName or tostring(parent)
	end

	local current = scriptObject
	for depth = 0, 63 do
		if not current then break end
		local entry = {depth = depth}
		pcall(function() entry.name = current.Name end)
		pcall(function() entry.className = current.ClassName end)
		pcall(function() entry.fullName = current:GetFullName() end)
		result.ancestry[#result.ancestry + 1] = entry
		local ok, nextParent = pcall(function() return current.Parent end)
		if not ok then break end
		current = nextParent
	end

	if okParent and parent then
		pcall(function()
			result.siblingIndex = table.find(parent:GetChildren(), scriptObject)
		end)
	end
	local okDebugId, debugId = pcall(function()
		return scriptObject:GetDebugId(0)
	end)
	result.introspectionAttempts.GetDebugId = {
		ok = okDebugId,
		error = okDebugId and nil or safeString(debugId, 4096),
	}
	if okDebugId then result.debugId = debugId end

	local okAttributes, attributes = pcall(function()
		return scriptObject:GetAttributes()
	end)
	if okAttributes then result.attributes = sanitize(attributes) end

	local okTags, tags = pcall(function()
		return game:GetService("CollectionService"):GetTags(scriptObject)
	end)
	if okTags then result.tags = sanitize(tags) end

	local okSource, source = pcall(function() return scriptObject.Source end)
	result.sourceReadable = okSource and type(source) == "string"
	if result.sourceReadable and config.IncludeReadableSource ~= false then
		result.readableSource = source
	end

	local getScriptHash = resolveRuntimeFunction("getscripthash")
	if getScriptHash then
		local ok, value = pcall(getScriptHash, scriptObject)
		result.introspectionAttempts.getscripthash = {
			ok = ok,
			error = ok and nil or safeString(value, 4096),
		}
		if ok then result.scriptHash = sanitize(value) end
	end

	local getEnv = resolveRuntimeFunction("getsenv")
	if getEnv then
		local envOk, scriptEnvironment = pcall(getEnv, scriptObject)
		result.introspectionAttempts.getsenv = {
			ok = envOk,
			error = envOk and nil or safeString(scriptEnvironment, 4096),
		}
		if envOk and type(scriptEnvironment) == "table" then
			local environmentSnapshot = {}
			for key, envValue in scriptEnvironment do
				environmentSnapshot[tostring(key)] = {
					type = typeof and typeof(envValue) or type(envValue),
					value = (type(envValue) == "nil"
						or type(envValue) == "boolean"
						or type(envValue) == "number"
						or type(envValue) == "string")
						and envValue
						or nil,
				}
			end
			result.environment = environmentSnapshot
		end
	end

	local getClosure = resolveRuntimeFunction("getscriptclosure")
	if getClosure and config.IncludeRuntimeClosure ~= false then
		local closureOk, closure = pcall(getClosure, scriptObject)
		result.introspectionAttempts.getscriptclosure = {
			ok = closureOk,
			error = closureOk and nil or safeString(closure, 4096),
		}
		result.runtimeClosureAvailable = closureOk and type(closure) == "function"
		if result.runtimeClosureAvailable then
			result.runtimeClosure = inspectClosure(closure, config)
		end
	end

	return result
end

function Collector.begin(bytecode, metadata)
    local session = {
        schema = Collector.SCHEMA,
        collectorVersion = Collector.VERSION,
        createdUnix = os.time(),
        createdClock = os.clock(),
        label = metadata and metadata.label or nil,
        notes = metadata and metadata.notes or nil,
        environment = {
            capabilities = detectCapabilities(),
            placeId = game and game.PlaceId or nil,
            gameId = game and game.GameId or nil,
            jobId = game and game.JobId or nil,
        },
        raw = {
            byteLength = #bytecode,
            checksumAlgorithm = "FNV-1a-32/u32-limbs",
            fnv1a32 = fnv1a(bytecode),
            bytecodeHex = bytesToHex(bytecode),
        },
        originalSource = metadata and metadata.originalSource or nil,
		dexSourceOutput = metadata and metadata.dexSourceOutput or nil,
		instanceSnapshot = sanitize(metadata and metadata.instanceSnapshot),
		externalArtifacts = sanitize(metadata and metadata.externalArtifacts),
		compilerMetadata = sanitize(metadata and metadata.compilerMetadata),
        options = sanitize(metadata and metadata.options or {}),
        fingerprints = {
            bytecode = {byteLength = #bytecode, fnv1a32 = fnv1a(bytecode)},
            originalSource = type(metadata and metadata.originalSource) == "string" and {
                byteLength = #(metadata.originalSource),
                fnv1a32 = fnv1a(metadata.originalSource),
                lineCount = select(2, string.gsub(metadata.originalSource, "\n", "")) + 1,
            } or nil,
            dexSourceOutput = type(metadata and metadata.dexSourceOutput) == "string" and {
                byteLength = #(metadata.dexSourceOutput),
                fnv1a32 = fnv1a(metadata.dexSourceOutput),
                lineCount = select(2, string.gsub(metadata.dexSourceOutput, "\n", "")) + 1,
            } or nil,
        },
        stages = {},
        events = {},
    }
    local identify = resolveRuntimeFunction("identifyexecutor")
        or resolveRuntimeFunction("getexecutorname")
    if identify then
        local ok, name, version = pcall(identify)
        session.environment.executor = {
            ok = ok,
            name = ok and sanitize(name) or nil,
            version = ok and sanitize(version) or nil,
            error = ok and nil or safeString(name, 4096),
        }
    end
    return session
end

function Collector.event(session, kind, data)
    session.events[#session.events + 1] = {
        clock = os.clock(),
        kind = kind,
        data = sanitize(data),
    }
end

function Collector.captureParsed(session, data, luau)
    local protos = {}
	local cfgSeeds = {}
    for id, proto in data.protoTable or {} do
		local snapshot = protoSnapshot(proto, luau)
        protos[tostring(id)] = snapshot
		cfgSeeds[tostring(id)] = cfgSeedSnapshot(snapshot)
    end
    session.bytecodeVersion = data.bytecodeVersion
    session.typeEncodingVersion = data.typeEncodingVersion
    session.mainProtoId = data.mainProtoId
    session.stringTable = sanitize(data.stringTable)
    session.userdataTypes = sanitize(data.userdataTypes)
    session.stages.parsed = {
		protos = protos,
		cfgSeeds = cfgSeeds,
	}
    session.completeness = captureCompleteness(
        protos,
        session.originalSource
    )
    local cfgSummary = {
        prototypeCount = 0, rawInstructionCount = 0,
        executableNodeCount = 0, captureDescriptorCount = 0,
        leaderCount = 0, blockCount = 0, edgeCount = 0,
        blockEdgeCount = 0, invalidTargetCount = 0,
        unreachableBlockCount = 0, edgeKinds = {},
    }
    for _, seed in cfgSeeds do
        cfgSummary.prototypeCount += 1
        for key, value in seed.summary do
            if type(value) == "number" and cfgSummary[key] ~= nil then
                cfgSummary[key] += value
            end
        end
        for kind, count in seed.summary.edgeKinds do
            cfgSummary.edgeKinds[kind] =
                (cfgSummary.edgeKinds[kind] or 0) + count
        end
    end
    session.completeness.cfg = cfgSummary
end

function Collector.captureOrganized(
    session,
    mainProtoId,
    registerActions,
    protoTable,
    luau
)
    local actions = {}
    for protoId, protoActions in registerActions or {} do
        local protoOutput = {}
        for index, action in protoActions.actions or {} do
            protoOutput[index] = {
                opcode = action.opCode and action.opCode.name or nil,
                encoding = action.opCode and action.opCode.type or nil,
                hasAux = action.opCode and action.opCode.aux == true or false,
                usedRegisters = copyArray(action.usedRegisters),
                extraData = sanitize(action.extraData),
                hidden = action.hide == true,
            }
        end
        actions[tostring(protoId)] = protoOutput
    end
    session.stages.organized = {
        mainProtoId = mainProtoId,
        actions = actions,
    }

    -- collectCaptures runs during organization, so this stage contains the
    -- resolved child-upvalue → parent-register mappings that are unavailable
    -- in the initial parsed snapshot.
    local resolvedCaptures = {}
    local closureSites = {}
	local captureDescriptorCount = 0
	local captureTypes = {}
    for protoId, proto in protoTable or {} do
        resolvedCaptures[tostring(protoId)] = sanitize(proto.captures)

        local sites = {}
        local pc = 1
        while pc <= #(proto.instructions or {}) do
            local word = proto.instructions[pc]
            local opcode = luau.OpCode[luau:INSN_OP(word)]
            local opcodeName = opcode and opcode.name or "INVALID"

            if opcodeName == "NEWCLOSURE" or opcodeName == "DUPCLOSURE" then
                local childProto = nil
                local D = luau:INSN_D(word)
                if opcodeName == "NEWCLOSURE" then
                    childProto = proto.innerProtos and proto.innerProtos[D + 1]
                else
                    local constant = proto.constants and proto.constants[D + 1]
                    local childId = constant and constant.value
                    if type(childId) == "number" then
                        childProto = protoTable[childId - 1]
                    end
                end

                local descriptors = {}
                local captureCount = childProto and childProto.numUpvalues or 0
                for offset = 1, captureCount do
                    local captureWord = proto.instructions[pc + offset]
                    if captureWord then
						captureDescriptorCount += 1
						local captureType = luau:INSN_A(captureWord)
						captureTypes[tostring(captureType)] =
							(captureTypes[tostring(captureType)] or 0) + 1
                        descriptors[offset] = {
                            pc = pc + offset,
                            raw = captureWord,
                            rawHex = string.format("%08x", captureWord),
							captureType = captureType,
                            source = luau:INSN_B(captureWord),
                        }
                    end
                end

                sites[#sites + 1] = {
                    pc = pc,
                    opcode = opcodeName,
                    targetRegister = luau:INSN_A(word),
                    operandD = D,
                    childProtoId = childProto and childProto.id or nil,
                    descriptors = descriptors,
                }
            end

            pc += if opcode and opcode.aux == true then 2 else 1
        end
        closureSites[tostring(protoId)] = sites
    end

    session.stages.organized.resolvedCaptures = resolvedCaptures
    session.stages.organized.closureSites = closureSites
    local parsedCfgCompleteness = session.completeness.cfg
    session.completeness = captureCompleteness(
        session.stages.parsed.protos,
        session.originalSource
    )
    session.completeness.cfg = parsedCfgCompleteness
    session.completeness.resolvedCapturePrototypeCount = 0
    session.completeness.closureSiteCount = 0
	session.completeness.capturedUpvalueCount = captureDescriptorCount
	session.completeness.captureTypes = captureTypes
    for _, captures in resolvedCaptures do
        if next(captures) ~= nil then
            session.completeness.resolvedCapturePrototypeCount += 1
        end
    end
    for _, sites in closureSites do
        session.completeness.closureSiteCount += #sites
    end
end

function Collector.finish(session, result)
    session.finishedClock = os.clock()
    session.elapsedCollection = session.finishedClock - session.createdClock
    session.result = sanitize(result)
    session.fingerprints.outputs = {}
    for name, value in result or {} do
        if type(value) == "string" then
            session.fingerprints.outputs[name] = {
                byteLength = #value,
                fnv1a32 = fnv1a(value),
                lineCount = select(2, string.gsub(value, "\n", "")) + 1,
            }
        end
    end
    return session
end

function Collector.encode(session)
    local sanitized = sanitize(session)
    if game and game.GetService then
        local ok, encoded = pcall(function()
            return game:GetService("HttpService"):JSONEncode(sanitized)
        end)
        if ok then return encoded end
    end
    return encodeJson(sanitized)
end

function Collector.save(session, path)
    local encoded = Collector.encode(session)
    path = path or (`optdec-collection-{session.raw.fnv1a32}.json`)
    if type(writefile) == "function" then
        writefile(path, encoded)
        return path, encoded
    end
    return nil, encoded
end

return Collector
