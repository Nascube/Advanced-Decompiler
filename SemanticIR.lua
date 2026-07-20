--!optimize 2

local SemanticIR = {}
SemanticIR.VERSION = "1.2.0"
SemanticIR.SCHEMA = "optdec-semantic-ir-v1"

local function sortedValues(t)
    local out = {}
    for key, value in t or {} do
        if type(value) == "table" then out[#out + 1] = { key = key, value = value } end
    end
    table.sort(out, function(a, b)
        local ai = tonumber(a.value.id or a.value.protoId or a.key) or 0
        local bi = tonumber(b.value.id or b.value.protoId or b.key) or 0
        return ai < bi
    end)
    local values = {}
    for _, item in out do values[#values + 1] = item.value end
    return values
end

local function category(op)
    if op == "RETURN" then return "return" end
    if string.sub(op, 1, 8) == "FASTCALL" then return "fastcall" end
    if string.sub(op, 1, 4) == "FORN" or string.sub(op, 1, 4) == "FORG" then return "loop" end
    if op == "JUMPBACK" then return "loop" end
    if op == "JUMP" or op == "JUMPX" then return "jump" end
    if string.sub(op, 1, 4) == "JUMP" then return "branch" end
    return nil
end

local function normalizedControl(instruction, seed)
    local op = tostring(instruction.opcode)
    local kind = category(op)
    if not kind then return nil end
    local successors = {}
    for _, edge in sortedValues(seed.edges) do
        if edge.from == instruction.pc and edge.kind ~= "next" then
            successors[#successors + 1] = {
                targetPc = edge.to,
                edgeKind = edge.kind,
            }
        end
    end
    table.sort(successors, function(a, b)
        if a.targetPc == b.targetPc then return tostring(a.edgeKind) < tostring(b.edgeKind) end
        return (a.targetPc or 0) < (b.targetPc or 0)
    end)
    return {
        sourcePc = instruction.pc,
        opcode = op,
        category = kind,
        inverted = string.find(op, "NOT", 1, true) ~= nil,
        operands = {
            A = instruction.A, B = instruction.B, C = instruction.C,
            D = instruction.D, sD = instruction.sD,
            E = instruction.E, aux = instruction.aux,
        },
        successors = successors,
        hasExplicitSuccessors = #successors > 0,
    }
end

function SemanticIR.buildSession(session)
    local parsed = assert(session.stages and session.stages.parsed, "parsed stage missing")
    local godTier = assert(session.stages.godTier, "godTier stage missing")
    assert(not godTier.error, "godTier analysis failed: " .. tostring(godTier.error))
    local protos, seeds, analyses = sortedValues(parsed.protos), sortedValues(parsed.cfgSeeds), sortedValues(godTier.prototypes)
    local analysisById = {}
    for _, item in analyses do analysisById[item.protoId] = item end
    local result = {
        schema = SemanticIR.SCHEMA,
        version = SemanticIR.VERSION,
        prototypes = {},
        summary = {
            prototypeCount = #protos,
            controlCount = 0,
            branchCount = 0,
            jumpCount = 0,
            loopControlCount = 0,
            fastcallCount = 0,
            returnCount = 0,
            explicitSuccessorCount = 0,
            unresolvedControlCount = 0,
            regionSeedCount = 0,
        },
    }
    for index, proto in protos do
        local seed = seeds[index] or { edges = {}, blocks = {} }
        local analysis = analysisById[proto.id] or {}
        local item = {
            protoId = proto.id,
            controls = {},
            blocks = {},
            blockOrder = {},
            naturalLoops = analysis.naturalLoops or {},
            regionSeeds = analysis.regionSeeds or {},
        }
        for _, block in sortedValues(seed.blocks) do
            item.blockOrder[#item.blockOrder + 1] = block.id
            item.blocks[#item.blocks + 1] = {
                id = block.id,
                startPc = block.startPc,
                endPc = block.endPc,
                terminatorPc = block.terminatorPc,
                predecessors = block.predecessors,
                successors = block.successors,
                reachable = block.reachable,
            }
        end
        for _, instruction in sortedValues(proto.instructions) do
            if instruction.wordKind == "INSTRUCTION" and instruction.opcode ~= "CAPTURE" then
                local control = normalizedControl(instruction, seed)
                if control then
                    item.controls[#item.controls + 1] = control
                    local summary = result.summary
                    summary.controlCount += 1
                    local field = ({ branch = "branchCount", jump = "jumpCount", loop = "loopControlCount", fastcall = "fastcallCount", ["return"] = "returnCount" })[control.category]
                    if field then summary[field] += 1 end
                    if control.hasExplicitSuccessors or control.category == "return" then summary.explicitSuccessorCount += 1 else summary.unresolvedControlCount += 1 end
                end
            end
        end
        result.summary.regionSeedCount += #item.regionSeeds
        result.prototypes[#result.prototypes + 1] = item
    end
    return result
end

return SemanticIR
