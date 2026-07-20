--!optimize 2

local V10 = {}
V10.VERSION = "10.6.0-predicate-ast"
V10.SCHEMA = "optdec-v10-source-v7"

local function sortedValues(t)
    local entries = {}
    for key, value in t or {} do entries[#entries + 1] = {key=key, value=value} end
    table.sort(entries, function(a,b)
        local an,bn=tonumber(a.key),tonumber(b.key)
        if an and bn then return an<bn end
        return tostring(a.key)<tostring(b.key)
    end)
    local out={}; for i,e in entries do out[i]=e.value end; return out
end

local function quote(value)
    if value == nil then return "nil" end
    local kind = type(value)
    if kind == "string" then return string.format("%q", value) end
    if kind == "number" then
        if value ~= value then return "(0/0)" end
        if value == math.huge then return "math.huge" end
        if value == -math.huge then return "-math.huge" end
        return tostring(value)
    end
    if kind == "boolean" then return tostring(value) end
    return "nil --[[unsupported constant: " .. kind .. "]]"
end

local function constantValue(proto, index)
    local constants = proto.constants or {}
    local constant = constants[index] or constants[tostring(index)]
    if type(constant) ~= "table" then return constant end
    if constant.value ~= nil then return constant.value end
    if constant.string ~= nil then return constant.string end
    if constant.number ~= nil then return constant.number end
    if constant.boolean ~= nil then return constant.boolean end
    return nil
end

local binary = {
    ADD="+", SUB="-", MUL="*", DIV="/", IDIV="//", MOD="%", POW="^",
    AND="and", OR="or", ADDK="+", SUBK="-", MULK="*", DIVK="/",
    IDIVK="//", MODK="%", POWK="^", ANDK="and", ORK="or",
}

local function reg(index) return "R[" .. tostring(index or 0) .. "]" end

local function indexedValue(values, index)
    if type(values) ~= "table" or type(index) ~= "number" then return nil end
    if values[index + 1] ~= nil then return values[index + 1] end
    return values[index]
end

local function resolveClosureProtoId(proto, instruction)
    if instruction.opcode == "NEWCLOSURE" then
        return indexedValue(proto.childProtoIds, instruction.D)
    elseif instruction.opcode == "DUPCLOSURE" then
        local constant = indexedValue(proto.constants, instruction.D)
        if type(constant) == "table" and constant.type == 6 then return constant.value end
    end
    return nil
end

local function instructionLine(proto, instruction)
    local op,A,B,C,D = instruction.opcode,instruction.A,instruction.B,instruction.C,instruction.D
    if op == "LOADNIL" then return reg(A).." = nil"
    elseif op == "LOADB" then return reg(A).." = "..tostring(B ~= 0)
    elseif op == "LOADN" then return reg(A).." = "..tostring(D or 0)
    elseif op == "LOADK" or op == "LOADKX" then return reg(A).." = "..quote(constantValue(proto,D))
    elseif op == "MOVE" then return reg(A).." = "..reg(B)
    elseif op == "GETUPVAL" then return reg(A).." = UP["..tostring(B).."]"
    elseif op == "SETUPVAL" then return "UP["..tostring(B).."] = "..reg(A)
    elseif op == "NEWTABLE" or op == "DUPTABLE" then return reg(A).." = {}"
    elseif op == "NOT" then return reg(A).." = not "..reg(B)
    elseif op == "MINUS" then return reg(A).." = -"..reg(B)
    elseif op == "LENGTH" then return reg(A).." = #"..reg(B)
    elseif binary[op] then
        local right = string.sub(op,-1)=="K" and quote(constantValue(proto,C)) or reg(C)
        return reg(A).." = "..reg(B).." "..binary[op].." "..right
    elseif op == "GETTABLE" then return reg(A).." = "..reg(B).."["..reg(C).."]"
    elseif op == "GETTABLEKS" then return reg(A).." = "..reg(B).."["..quote(constantValue(proto,instruction.aux)).."]"
    elseif op == "SETTABLE" then return reg(B).."["..reg(C).."] = "..reg(A)
    elseif op == "SETTABLEKS" then return reg(B).."["..quote(constantValue(proto,instruction.aux)).."] = "..reg(A)
    elseif op == "CONCAT" then
        local parts={}; for i=B,C do parts[#parts+1]=reg(i) end
        return reg(A).." = "..table.concat(parts," .. ")
    elseif op == "CALL" then
        local args={}
        if B and B>1 then for i=A+1,A+B-1 do args[#args+1]=reg(i) end
        elseif B==0 then args[1]="... --[[open arguments]]" end
        local call=reg(A).."("..table.concat(args,", ")..")"
        if C==1 then return call
        elseif C==0 then return reg(A).." = "..call.." --[[MULTRET]]"
        else
            local lhs={}; for i=A,A+C-2 do lhs[#lhs+1]=reg(i) end
            return table.concat(lhs,", ").." = "..call
        end
    elseif op == "RETURN" then
        if B==0 then return "return ... --[[open return tuple]]" end
        local values={}; for i=A,A+(B or 1)-2 do values[#values+1]=reg(i) end
        return "return "..table.concat(values,", ")
    elseif op == "GETVARARGS" then
        if B==0 then return reg(A).." = ... --[[MULTRET]]" end
        local lhs={}; for i=A,A+B-2 do lhs[#lhs+1]=reg(i) end
        return table.concat(lhs,", ").." = ..."
    elseif op == "NEWCLOSURE" or op == "DUPCLOSURE" then
        local childId=resolveClosureProtoId(proto,instruction)
        return reg(A).." = PROTO["..tostring(childId or 0).."] --[[resolved closure]]"
    elseif op == "GETGLOBAL" then
        return reg(A).." = ENV["..quote(constantValue(proto,instruction.aux)).."]"
    elseif op == "SETGLOBAL" then
        return "ENV["..quote(constantValue(proto,instruction.aux)).."] = "..reg(A)
    elseif op == "GETIMPORT" then
        return reg(A).." = __getimport("..quote(instruction.aux)..")"
    elseif op == "NAMECALL" then
        local key=quote(constantValue(proto,instruction.aux))
        return reg(A+1).." = "..reg(B).."; "..reg(A).." = "..reg(B).."["..key.."]"
    elseif op == "SETTABLEN" then
        return reg(B).."["..tostring((C or 0)+1).."] = "..reg(A)
    elseif op == "GETTABLEN" then
        return reg(A).." = "..reg(B).."["..tostring((C or 0)+1).."]"
    elseif op == "SETLIST" then
        return "__setlist("..reg(A)..", "..reg(B)..", "..tostring(C or 0)..")"
    elseif op == "CLOSEUPVALS" then
        return "__closeupvalues("..tostring(A or 0)..")"
    elseif op == "PREPVARARGS" then
        return "-- vararg frame prepared"
    elseif string.sub(tostring(op),1,8) == "FASTCALL" then
        return "-- "..tostring(op).." fast path; paired CALL preserves fallback semantics"
    elseif op == "JUMP" or op == "JUMPBACK" or op == "JUMPX"
        or string.sub(tostring(op),1,6) == "JUMPIF"
        or string.sub(tostring(op),1,5) == "JUMPX"
        or op == "FORNPREP" or op == "FORNLOOP"
        or string.sub(tostring(op),1,8) == "FORGPREP" or op == "FORGLOOP" then
        return "__control("..quote(op)..", "..tostring(instruction.pc)..", "
            ..tostring(A or 0)..", "..tostring(B or 0)..", "..tostring(C or 0)
            ..", "..tostring(D or instruction.sD or 0)..")"
    end
    return "__opcode("..quote(op)..", "..tostring(instruction.pc)..", "
        ..tostring(A or 0)..", "..tostring(B or 0)..", "..tostring(C or 0)
        ..", "..tostring(D or 0)..", "..tostring(instruction.aux or 0)..")"
end

local function maxRegister(proto)
    local maximum = (proto.maxStackSize or proto.maxstacksize or 1)-1
    for _,ins in sortedValues(proto.instructions) do
        if type(ins)=="table" then
            for _,key in {"A","B","C"} do
                local value=ins[key]; if type(value)=="number" and value<256 then maximum=math.max(maximum,value) end
            end
        end
    end
    return math.min(maximum,255)
end

local function emitPrototype(proto, seed, analysis)
    local lines={}
    local id=proto.id or 0
    lines[#lines+1]="PROTO["..tostring(id).."] = function(...)"
    lines[#lines+1]="    -- reconstructed prototype "..tostring(id)
    local maxReg=maxRegister(proto)
    lines[#lines+1]="    local R = table.create("..tostring(maxReg + 1)..")"
    lines[#lines+1]="    local UP = {}"
    local instructionByPc={}
    for _,ins in sortedValues(proto.instructions) do
        if type(ins)=="table" and ins.wordKind=="INSTRUCTION" and ins.opcode~="CAPTURE" then instructionByPc[ins.pc]=ins end
    end
    for _,block in sortedValues(seed.blocks) do
        lines[#lines+1]="    do --[[block "..tostring(block.id).." pc "..tostring(block.startPc)..".."..tostring(block.endPc).."]]"
        for _,pc in block.instructionPcs or {} do
            local ins=instructionByPc[pc]
            if ins then lines[#lines+1]="        "..instructionLine(proto,ins) end
        end
        lines[#lines+1]="    end"
    end
    lines[#lines+1]="end"
    return table.concat(lines,"\n")
end

function V10.decompileSession(session)
    local parsed=assert(session.stages and session.stages.parsed,"parsed stage missing")
    local analysisStage=assert(session.stages.godTier,"godTier stage missing")
    local protos,seeds,analyses=sortedValues(parsed.protos),sortedValues(parsed.cfgSeeds),sortedValues(analysisStage.prototypes)
    local analysisById={}; for _,a in analyses do analysisById[a.protoId]=a end
    local chunks={
        "--!nocheck",
        "-- OPTDEC V10 structural developer output",
        "-- analysis schema: "..tostring(analysisStage.schema),
        "-- semantic IR schema: "..tostring(session.stages.semanticIR and session.stages.semanticIR.schema or "unavailable"),
        "-- region tree schema: "..tostring(session.stages.regionTree and session.stages.regionTree.schema or "unavailable"),
        "-- AST schema: "..tostring(session.stages.ast and session.stages.ast.schema or "unavailable"),
        "-- exact original lexical identity is not implied",
        "local PROTO = {}",
        "local ENV = {}",
        "local function __getimport(path) return ENV[path] end",
        "local function __setlist(target, base, count) return target, base, count end",
        "local function __closeupvalues(base) return base end",
        "local function __control(...) return ... end",
        "local function __opcode(...) return ... end",
        "",
    }
    local seedByIndex=seeds
    for index,proto in protos do
        chunks[#chunks+1]=emitPrototype(proto,seedByIndex[index],analysisById[proto.id])
        chunks[#chunks+1]=""
    end
    chunks[#chunks+1]="return PROTO["..tostring(session.mainProtoId).."](...)"
    return table.concat(chunks,"\n"), {
        schema=V10.SCHEMA, version=V10.VERSION,
        prototypeCount=#protos, mainProtoId=session.mainProtoId,
        semanticIR=session.stages.semanticIR and session.stages.semanticIR.summary or nil,
        regionTree=session.stages.regionTree and session.stages.regionTree.summary or nil,
        ast=session.stages.ast and session.stages.ast.summary or nil,
        limitations={
            "irreducible and unresolved regions use low-level block form",
            "erased local identifiers cannot be recovered literally",
        },
    }
end

return V10
