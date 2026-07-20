--!optimize 2

local Structurer = {}
Structurer.VERSION = "1.2.0"
Structurer.SCHEMA = "optdec-region-tree-v1"

local function values(t)
    local out = {}
    for _, value in t or {} do if type(value) == "table" then out[#out + 1] = value end end
    return out
end

local function intervalForRegion(region)
    if region.kind == "naturalLoop" then
        local first, last = nil, nil
        for _, blockId in region.nodes do
            first = first and math.min(first, blockId) or blockId
            last = last and math.max(last, blockId) or blockId
        end
        return first or region.header, last or region.header
    end
    local numbers = {}
    for _, value in { region.header, region.thenBlock, region.elseBlock, region.join } do
        if type(value) == "number" then numbers[#numbers + 1] = value end
    end
    if #numbers == 0 then return 0, 0 end
    local first, last = numbers[1], numbers[1]
    for index = 2, #numbers do
        first = math.min(first, numbers[index])
        last = math.max(last, numbers[index])
    end
    return first, last
end

local function contains(outer, inner)
    return outer.startBlock <= inner.startBlock and outer.endBlock >= inner.endBlock
        and (outer.startBlock < inner.startBlock or outer.endBlock > inner.endBlock)
end

local function constructPrototype(semanticProto, analysisProto)
    local regions, nextId = {}, 1
    for _, seed in values(analysisProto.regionSeeds) do
        local complete = type(seed.header) == "number"
            and type(seed.thenBlock) == "number"
            and type(seed.elseBlock) == "number"
        local kind = complete and (seed.elseBlock == seed.join and "if" or "ifElse")
            or "conditionalFallback"
        local node = {
            id = nextId, kind = kind, confidence = seed.confidence,
            header = seed.header, thenBlock = seed.thenBlock,
            elseBlock = seed.elseBlock, join = seed.join, children = {},
        }
        node.startBlock, node.endBlock = intervalForRegion(node)
        regions[#regions + 1], nextId = node, nextId + 1
    end
    for _, loop in values(analysisProto.naturalLoops) do
        local node = {
            id = nextId, kind = "naturalLoop", confidence = "structural",
            header = loop.header, latch = loop.latch, nodes = loop.nodes or {},
            sourcePc = loop.sourcePc, targetPc = loop.targetPc,
            edgeKind = loop.edgeKind, children = {},
        }
        node.startBlock, node.endBlock = intervalForRegion(node)
        regions[#regions + 1], nextId = node, nextId + 1
    end
    -- Assign each region to the smallest strictly containing interval.
    for _, child in regions do
        local parent, parentSpan = nil, nil
        for _, candidate in regions do
            if candidate ~= child and contains(candidate, child) then
                local span = candidate.endBlock - candidate.startBlock
                if parentSpan == nil or span < parentSpan then parent, parentSpan = candidate, span end
            end
        end
        child.parentId = parent and parent.id or nil
        if parent then parent.children[#parent.children + 1] = child.id end
    end
    table.sort(regions, function(a, b)
        if a.startBlock == b.startBlock then
            if a.endBlock == b.endBlock then return a.id < b.id end
            return a.endBlock > b.endBlock
        end
        return a.startBlock < b.startBlock
    end)
    local roots = {}
    for _, region in regions do if region.parentId == nil then roots[#roots + 1] = region.id end end
    return {
        protoId = semanticProto.protoId,
        blockOrder = semanticProto.blockOrder,
        blocks = semanticProto.blocks,
        controls = semanticProto.controls,
        regions = regions,
        roots = roots,
    }
end

function Structurer.buildSession(session)
    local semantic = assert(session.stages and session.stages.semanticIR, "semanticIR stage missing")
    assert(not semantic.error, "semanticIR failed: " .. tostring(semantic.error))
    local analysis = assert(session.stages.godTier, "godTier stage missing")
    assert(not analysis.error, "godTier failed: " .. tostring(analysis.error))
    local analysisById = {}
    for _, proto in values(analysis.prototypes) do analysisById[proto.protoId] = proto end
    local result = {
        schema = Structurer.SCHEMA, version = Structurer.VERSION,
        prototypes = {}, summary = {
            prototypeCount = 0, regionCount = 0, conditionalCount = 0,
            ifCount = 0, ifElseCount = 0, naturalLoopCount = 0,
            nestedRegionCount = 0, rootRegionCount = 0,
            malformedRegionCount = 0,
        },
    }
    for _, semanticProto in values(semantic.prototypes) do
        local proto = constructPrototype(semanticProto, analysisById[semanticProto.protoId] or {})
        result.prototypes[#result.prototypes + 1] = proto
        result.summary.prototypeCount += 1
        result.summary.rootRegionCount += #proto.roots
        for _, region in proto.regions do
            result.summary.regionCount += 1
            if region.parentId then result.summary.nestedRegionCount += 1 end
            if region.kind == "naturalLoop" then
                result.summary.naturalLoopCount += 1
            else
                result.summary.conditionalCount += 1
                if region.kind == "if" then
                    result.summary.ifCount += 1
                elseif region.kind == "ifElse" then
                    result.summary.ifElseCount += 1
                else
                    result.summary.malformedRegionCount += 1
                end
            end
        end
    end
    return result
end

return Structurer
