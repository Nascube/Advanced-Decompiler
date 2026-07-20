--!optimize 2

-- guess source text; every result is derived from bytecode control/data flow.
local Analysis = {}
Analysis.VERSION = "1.0.0"
Analysis.SCHEMA = "optdec-god-tier-analysis-v1"

local function sortedValues(t)
    local result = {}
    for key, value in t or {} do
        result[#result + 1] = {key = key, value = value}
    end
    table.sort(result, function(a, b)
        local an, bn = tonumber(a.key), tonumber(b.key)
        if an and bn then return an < bn end
        return tostring(a.key) < tostring(b.key)
    end)
    local values = {}
    for index, entry in result do values[index] = entry.value end
    return values
end

local function cloneSet(source)
    local result = {}
    for key in source or {} do result[key] = true end
    return result
end

local function setEquals(a, b)
    for key in a do if not b[key] then return false end end
    for key in b do if not a[key] then return false end end
    return true
end

local function intersect(a, b)
    local result = {}
    for key in a do if b[key] then result[key] = true end end
    return result
end

local function setArray(set)
    local result = {}
    for value in set or {} do result[#result + 1] = value end
    table.sort(result)
    return result
end

local function setSize(set)
    local count = 0
    for _ in set or {} do count += 1 end
    return count
end

local function computeDominators(blocks)
    local active, all = {}, {}
    for _, block in blocks do
        if block.reachable then
            active[#active + 1] = block.id
            all[block.id] = true
        end
    end
    if #active == 0 then return {}, {}, {} end
    local entry = active[1]
    local dom = {}
    for _, id in active do dom[id] = id == entry and {[id] = true} or cloneSet(all) end

    local changed = true
    while changed do
        changed = false
        for _, id in active do
            if id ~= entry then
                local block = blocks[id]
                local nextSet = nil
                for _, predecessor in block.predecessors or {} do
                    if dom[predecessor] then
                        nextSet = nextSet and intersect(nextSet, dom[predecessor])
                            or cloneSet(dom[predecessor])
                    end
                end
                nextSet = nextSet or {}
                nextSet[id] = true
                if not setEquals(nextSet, dom[id]) then dom[id], changed = nextSet, true end
            end
        end
    end

    local idom = {}
    for _, id in active do
        if id ~= entry then
            local best, bestDepth = nil, -1
            for candidate in dom[id] do
                if candidate ~= id then
                    local depth = setSize(dom[candidate])
                    if depth > bestDepth then best, bestDepth = candidate, depth end
                end
            end
            idom[id] = best
        end
    end

    local frontierSets = {}
    for _, id in active do frontierSets[id] = {} end
    for _, id in active do
        local predecessors = blocks[id].predecessors or {}
        if #predecessors >= 2 then
            for _, predecessor in predecessors do
                local runner = predecessor
                while runner and runner ~= idom[id] do
                    frontierSets[runner][id] = true
                    runner = idom[runner]
                end
            end
        end
    end
    return dom, idom, frontierSets
end

local function computePostDominators(blocks)
    local active, all, exits = {}, {}, {}
    for _, block in blocks do
        if block.reachable then
            active[#active + 1] = block.id
            all[block.id] = true
            local liveSuccessors = 0
            for _, successor in block.successors or {} do
                if blocks[successor] and blocks[successor].reachable then liveSuccessors += 1 end
            end
            if liveSuccessors == 0 then exits[block.id] = true end
        end
    end
    local post = {}
    for _, id in active do post[id] = exits[id] and {[id] = true} or cloneSet(all) end
    local changed = true
    while changed do
        changed = false
        for _, id in active do
            if not exits[id] then
                local nextSet = nil
                for _, successor in blocks[id].successors or {} do
                    if post[successor] then
                        nextSet = nextSet and intersect(nextSet, post[successor])
                            or cloneSet(post[successor])
                    end
                end
                if nextSet then
                    nextSet[id] = true
                    if not setEquals(nextSet, post[id]) then post[id], changed = nextSet, true end
                end
            end
        end
    end
    local ipdom = {}
    for _, id in active do
        if not exits[id] then
            local best, bestDepth = nil, -1
            for candidate in post[id] do
                if candidate ~= id then
                    local depth = setSize(post[candidate])
                    if depth > bestDepth then best, bestDepth = candidate, depth end
                end
            end
            ipdom[id] = best
        end
    end
    return post, ipdom, setArray(exits)
end

local function computeNaturalLoops(blocks, dom, instructionEdges)
    local pcToBlock = {}
    for _, block in blocks do
        for _, pc in block.instructionPcs do pcToBlock[pc] = block.id end
    end
    local loops, seen = {}, {}
    for _, edge in instructionEdges or {} do
        local tail, header = pcToBlock[edge.from], pcToBlock[edge.to]
        local transfersBackward = type(edge.from) == "number"
            and type(edge.to) == "number" and edge.to <= edge.from
        local realTransfer = edge.kind ~= "next"
            and edge.kind ~= "fallthrough"
            and edge.kind ~= "fallback"
            and edge.kind ~= "fastpath"
            and edge.kind ~= "loop-prep"
        if tail and header and tail ~= header and transfersBackward and realTransfer
            and dom[tail] and dom[tail][header] then
            local key = tostring(tail) .. ":" .. tostring(header)
            if not seen[key] then
                seen[key] = true
                local nodes, stack = {[header]=true, [tail]=true}, {tail}
                while #stack > 0 do
                    local node = table.remove(stack)
                    for _, predecessor in blocks[node].predecessors or {} do
                        if not nodes[predecessor] then
                            nodes[predecessor] = true
                            if predecessor ~= header then stack[#stack + 1] = predecessor end
                        end
                    end
                end
                loops[#loops + 1] = {
                    header=header, latch=tail, nodes=setArray(nodes),
                    sourcePc=edge.from, targetPc=edge.to, edgeKind=edge.kind,
                }
            end
        end
    end
    return loops
end

local DEFINES_A = {
    LOADNIL=true, LOADB=true, LOADN=true, LOADK=true, LOADKX=true,
    MOVE=true, GETGLOBAL=true, GETUPVAL=true, GETIMPORT=true,
    GETTABLE=true, GETTABLEKS=true, GETTABLEN=true, NEWCLOSURE=true,
    DUPCLOSURE=true, NEWTABLE=true, DUPTABLE=true, ADD=true, SUB=true,
    MUL=true, DIV=true, MOD=true, POW=true, ADDK=true, SUBK=true,
    MULK=true, DIVK=true, MODK=true, POWK=true, AND=true, OR=true,
    ANDK=true, ORK=true, CONCAT=true, NOT=true, MINUS=true, LENGTH=true,
    GETVARARGS=true, PREPVARARGS=true, IDIV=true, IDIVK=true,
    GETUDATAKS=true, NAMECALLUDATA=true,
}
local USES_B = {
    MOVE=true, GETTABLE=true, GETTABLEKS=true, GETTABLEN=true,
    ADD=true, SUB=true, MUL=true, DIV=true, MOD=true, POW=true,
    ADDK=true, SUBK=true, MULK=true, DIVK=true, MODK=true, POWK=true,
    AND=true, OR=true, ANDK=true, ORK=true, NOT=true, MINUS=true,
    LENGTH=true, SETTABLE=true, SETTABLEKS=true, SETTABLEN=true,
    SETGLOBAL=true, SETUPVAL=true, JUMPIF=true, JUMPIFNOT=true,
    JUMPIFEQ=true, JUMPIFLE=true, JUMPIFLT=true, JUMPIFNOTEQ=true,
    JUMPIFNOTLE=true, JUMPIFNOTLT=true, FASTCALL1=true, FASTCALL2=true,
    FASTCALL2K=true, FASTCALL3=true, GETUDATAKS=true, SETUDATAKS=true,
}
local USES_C = {
    GETTABLE=true, ADD=true, SUB=true, MUL=true, DIV=true, MOD=true,
    POW=true, AND=true, OR=true, SETTABLE=true, JUMPIFEQ=true,
    JUMPIFLE=true, JUMPIFLT=true, JUMPIFNOTEQ=true,
    JUMPIFNOTLE=true, JUMPIFNOTLT=true,
}

local function registerEffects(instruction)
    local name = instruction.opcode
    local uses, defs = {}, {}
    if DEFINES_A[name] and type(instruction.A) == "number" then defs[instruction.A] = true end
    if USES_B[name] and type(instruction.B) == "number" then uses[instruction.B] = true end
    if USES_C[name] and type(instruction.C) == "number" then uses[instruction.C] = true end
    if name == "NAMECALL" then uses[instruction.B], defs[instruction.A], defs[instruction.A + 1] = true, true, true end
    if name == "CALL" then
        uses[instruction.A] = true
        if instruction.B and instruction.B > 1 then
            for register = instruction.A + 1, instruction.A + instruction.B - 1 do uses[register] = true end
        end
        if instruction.C and instruction.C > 1 then
            for register = instruction.A, instruction.A + instruction.C - 2 do defs[register] = true end
        end
    elseif name == "RETURN" then
        local count = instruction.B or 0
        if count > 1 then for register = instruction.A, instruction.A + count - 2 do uses[register] = true end end
    elseif name == "SETTABLEKS" or name == "SETTABLEN" or name == "SETUDATAKS" then
        uses[instruction.A], uses[instruction.B] = true, true
    elseif name == "CONCAT" then
        for register = instruction.B, instruction.C do uses[register] = true end
    elseif name == "FORNPREP" or name == "FORNLOOP" then
        for register = instruction.A, instruction.A + 3 do uses[register] = true end
        defs[instruction.A + 3] = true
    elseif name == "FORGLOOP" then
        uses[instruction.A] = true
        local count = instruction.C or 0
        for register = instruction.A + 3, instruction.A + 2 + count do defs[register] = true end
    end
    return uses, defs
end

local function computeDataFlow(proto, seed, frontier)
    local instructionByPc = {}
    for _, instruction in sortedValues(proto.instructions) do
        if instruction.wordKind == "INSTRUCTION" and instruction.opcode ~= "CAPTURE" then
            instructionByPc[instruction.pc] = instruction
        end
    end
    local blockUse, blockDef = {}, {}
    local definitionBlocks = {}
    for _, block in seed.blocks do
        local uses, defs = {}, {}
        for _, pc in block.instructionPcs do
            local instruction = instructionByPc[pc]
            if instruction then
                local instructionUses, instructionDefs = registerEffects(instruction)
                for register in instructionUses do if not defs[register] then uses[register] = true end end
                for register in instructionDefs do
                    defs[register] = true
                    definitionBlocks[register] = definitionBlocks[register] or {}
                    definitionBlocks[register][block.id] = true
                end
            end
        end
        blockUse[block.id], blockDef[block.id] = uses, defs
    end
    local liveIn, liveOut = {}, {}
    for _, block in seed.blocks do liveIn[block.id], liveOut[block.id] = {}, {} end
    local changed = true
    while changed do
        changed = false
        for index = #seed.blocks, 1, -1 do
            local block = seed.blocks[index]
            local out = {}
            for _, successor in block.successors do
                for register in liveIn[successor] do out[register] = true end
            end
            local inside = cloneSet(blockUse[block.id])
            for register in out do if not blockDef[block.id][register] then inside[register] = true end end
            if not setEquals(out, liveOut[block.id]) or not setEquals(inside, liveIn[block.id]) then
                liveOut[block.id], liveIn[block.id], changed = out, inside, true
            end
        end
    end
    local phi = {}
    for register, defBlocks in definitionBlocks do
        local work, seen = setArray(defBlocks), cloneSet(defBlocks)
        local head = 1
        while head <= #work do
            local block = work[head]; head += 1
            for frontierBlock in frontier[block] or {} do
                phi[frontierBlock] = phi[frontierBlock] or {}
                if liveIn[frontierBlock] and liveIn[frontierBlock][register]
                    and not phi[frontierBlock][register] then
                    phi[frontierBlock][register] = true
                    if not seen[frontierBlock] then
                        seen[frontierBlock] = true
                        work[#work + 1] = frontierBlock
                    end
                end
            end
        end
    end
    local output, phiCount = {}, 0
    for _, block in seed.blocks do
        local phis = setArray(phi[block.id] or {})
        phiCount += #phis
        output[block.id] = {
            use = setArray(blockUse[block.id]), def = setArray(blockDef[block.id]),
            liveIn = setArray(liveIn[block.id]), liveOut = setArray(liveOut[block.id]),
            phiRegisters = phis,
        }
    end
    return output, phiCount
end

local function computeSSA(proto, blocks, idom, dataFlow)
    local instructionByPc = {}
    for _, instruction in sortedValues(proto.instructions) do
        if instruction.wordKind == "INSTRUCTION" and instruction.opcode ~= "CAPTURE" then
            instructionByPc[instruction.pc] = instruction
        end
    end
    local children = {}
    for _, block in blocks do children[block.id] = {} end
    for blockId, parentId in idom do
        children[parentId][#children[parentId] + 1] = blockId
    end
    for _, list in children do table.sort(list) end

    local stacks, counters, output = {}, {}, {}
    local function top(register)
        local stack = stacks[register]
        return stack and stack[#stack] or 0
    end
    local function define(register)
        counters[register] = (counters[register] or 0) + 1
        stacks[register] = stacks[register] or {0}
        stacks[register][#stacks[register] + 1] = counters[register]
        return counters[register]
    end
    local function rename(blockId)
        local block, pushed = blocks[blockId], {}
        local record = {phis = {}, instructions = {}, phiInputs = {}}
        output[blockId] = record
        for _, register in dataFlow[blockId].phiRegisters do
            local version = define(register)
            pushed[#pushed + 1] = register
            record.phis[#record.phis + 1] = {register=register, version=version, inputs={}}
        end
        for _, pc in block.instructionPcs do
            local instruction = instructionByPc[pc]
            if instruction then
                local uses, defs = registerEffects(instruction)
                local entry = {pc=pc, opcode=instruction.opcode, uses={}, defs={}}
                for _, register in setArray(uses) do
                    entry.uses[#entry.uses + 1] = {register=register, version=top(register)}
                end
                for _, register in setArray(defs) do
                    local version = define(register)
                    pushed[#pushed + 1] = register
                    entry.defs[#entry.defs + 1] = {register=register, version=version}
                end
                record.instructions[#record.instructions + 1] = entry
            end
        end
        for _, successor in block.successors do
            local successorFlow = dataFlow[successor]
            if successorFlow then
                record.phiInputs[successor] = {}
                for _, register in successorFlow.phiRegisters do
                    record.phiInputs[successor][#record.phiInputs[successor] + 1] = {
                        register=register, version=top(register), predecessor=blockId,
                    }
                end
            end
        end
        for _, child in children[blockId] do rename(child) end
        for index = #pushed, 1, -1 do
            local stack = stacks[pushed[index]]
            stack[#stack] = nil
        end
    end
    if blocks[1] then rename(blocks[1].id) end
    local valueCount = 0
    for _, count in counters do valueCount += count end
    return output, valueCount
end

local function computeTupleIR(proto)
    local tuples, openTupleCount = {}, 0
    for _, instruction in sortedValues(proto.instructions) do
        if instruction.wordKind == "INSTRUCTION" then
            local name = instruction.opcode
            local tuple = nil
            if name == "CALL" then
                tuple = {
                    pc=instruction.pc, kind="call", base=instruction.A,
                    argumentCount=instruction.B == 0 and "open" or instruction.B - 1,
                    resultCount=instruction.C == 0 and "open" or instruction.C - 1,
                    consumesTop=instruction.B == 0, producesTop=instruction.C == 0,
                }
            elseif name == "RETURN" then
                tuple = {
                    pc=instruction.pc, kind="return", base=instruction.A,
                    valueCount=instruction.B == 0 and "open" or instruction.B - 1,
                    consumesTop=instruction.B == 0,
                }
            elseif name == "GETVARARGS" then
                tuple = {
                    pc=instruction.pc, kind="varargs", base=instruction.A,
                    resultCount=instruction.B == 0 and "open" or instruction.B - 1,
                    producesTop=instruction.B == 0,
                }
            elseif name == "SETLIST" then
                tuple = {
                    pc=instruction.pc, kind="setlist", base=instruction.A,
                    valueCount=instruction.B == 0 and "open" or instruction.B,
                    consumesTop=instruction.B == 0,
                }
            end
            if tuple then
                if tuple.consumesTop or tuple.producesTop then openTupleCount += 1 end
                tuples[#tuples + 1] = tuple
            end
        end
    end
    return tuples, openTupleCount
end

local function propagateTupleFlow(tuples, blocks)
    local byPc, links = {}, {}
    for _, tuple in tuples do byPc[tuple.pc] = tuple end
    for _, block in blocks do
        local currentProducer = nil
        for _, pc in block.instructionPcs do
            local tuple = byPc[pc]
            if tuple then
                if tuple.consumesTop and currentProducer then
                    tuple.openInputProducerPc = currentProducer.pc
                    links[#links + 1] = {
                        producerPc=currentProducer.pc, consumerPc=tuple.pc,
                        producerKind=currentProducer.kind, consumerKind=tuple.kind,
                    }
                end
                if tuple.producesTop then currentProducer = tuple
                elseif tuple.kind == "call" and not tuple.producesTop then currentProducer = nil end
            end
        end
    end
    return links
end

local function computeClosureIR(proto, ssa)
    local instructions = sortedValues(proto.instructions)
    local closures, captureCount = {}, 0
    for index, instruction in instructions do
        if instruction.wordKind == "INSTRUCTION"
            and (instruction.opcode == "NEWCLOSURE" or instruction.opcode == "DUPCLOSURE") then
            local closure = {
                pc=instruction.pc, opcode=instruction.opcode,
                targetRegister=instruction.A, childReference=instruction.D,
                captures={},
            }
            local cursor = index + 1
            while instructions[cursor] and instructions[cursor].opcode == "CAPTURE" do
                local capture = instructions[cursor]
                closure.captures[#closure.captures + 1] = {
                    pc=capture.pc, captureType=capture.A, source=capture.B,
                    mode=capture.A == 0 and "value"
                        or capture.A == 1 and "reference"
                        or capture.A == 2 and "upvalue"
                        or "unknown",
                    environmentCell = capture.A == 1
                        and ("register-cell:" .. tostring(capture.B))
                        or capture.A == 2
                        and ("upvalue-cell:" .. tostring(capture.B))
                        or nil,
                }
                captureCount += 1
                cursor += 1
            end
            closures[#closures + 1] = closure
        end
    end
    return closures, captureCount
end

local function computeRegionSeeds(blocks, loops, blockAnalysis)
    local regions, loopHeaders = {}, {}
    for _, loop in loops do
        loopHeaders[loop.header] = true
        regions[#regions + 1] = {
            kind="loop", header=loop.header, latch=loop.latch,
            nodes=loop.nodes, exit=blockAnalysis[loop.header]
                and blockAnalysis[loop.header].immediatePostDominator or nil,
            confidence="structural",
        }
    end
    for _, block in blocks do
        if block.reachable and #block.successors == 2 and not loopHeaders[block.id] then
            regions[#regions + 1] = {
                kind="conditional", header=block.id,
                thenBlock=block.successors[1], elseBlock=block.successors[2],
                join=blockAnalysis[block.id]
                    and blockAnalysis[block.id].immediatePostDominator or nil,
                confidence="structural",
            }
        end
    end
    return regions
end

function Analysis.analyzePrototype(proto, seed)
    local blocks = sortedValues(seed.blocks)
    local dom, idom, frontier = computeDominators(blocks)
    local post, ipdom, exits = computePostDominators(blocks)
    local loops = computeNaturalLoops(blocks, dom, sortedValues(seed.edges))
    local dataFlow, phiCount = computeDataFlow(proto, {blocks=blocks}, frontier)
    local ssa, ssaValueCount = computeSSA(proto, blocks, idom, dataFlow)
    local tuples, openTupleCount = computeTupleIR(proto)
    local tupleLinks = propagateTupleFlow(tuples, blocks)
    local closures, closureCaptureCount = computeClosureIR(proto, ssa)
    local blockAnalysis = {}
    for _, block in blocks do
        blockAnalysis[block.id] = {
            dominators = setArray(dom[block.id] or {}), immediateDominator = idom[block.id],
            dominanceFrontier = setArray(frontier[block.id] or {}),
            postDominators = setArray(post[block.id] or {}), immediatePostDominator = ipdom[block.id],
            dataFlow = dataFlow[block.id],
            ssa = ssa[block.id],
        }
    end
    local regions = computeRegionSeeds(blocks, loops, blockAnalysis)
    return {
        protoId = proto.id,
        blockAnalysis = blockAnalysis,
        exitBlocks = exits,
        naturalLoops = loops,
        tupleIR = tuples,
        tupleFlow = tupleLinks,
        closureIR = closures,
        regionSeeds = regions,
        phiCount = phiCount,
        ssaValueCount = ssaValueCount,
        summary = {
            blockCount=#blocks, loopCount=#loops, phiCount=phiCount,
            ssaValueCount=ssaValueCount, tupleCount=#tuples,
            openTupleCount=openTupleCount, tupleLinkCount=#tupleLinks,
            closureCount=#closures,
            closureCaptureCount=closureCaptureCount, regionCount=#regions,
        },
    }
end

function Analysis.analyzeSession(session)
    local parsed = assert(session.stages and session.stages.parsed, "parsed stage missing")
    local protos, seeds = sortedValues(parsed.protos), sortedValues(parsed.cfgSeeds)
    assert(#protos == #seeds, "prototype/CFG seed count mismatch")
    local result = {
        schema = Analysis.SCHEMA, version = Analysis.VERSION,
        prototypes = {}, summary = {
            prototypeCount=#protos, blockCount=0, loopCount=0, phiCount=0,
            ssaValueCount=0, tupleCount=0, openTupleCount=0, tupleLinkCount=0,
            closureCount=0, closureCaptureCount=0, regionCount=0,
        },
    }
    for index, proto in protos do
        local analysis = Analysis.analyzePrototype(proto, seeds[index])
        result.prototypes[#result.prototypes + 1] = analysis
        result.summary.blockCount += analysis.summary.blockCount
        result.summary.loopCount += analysis.summary.loopCount
        result.summary.phiCount += analysis.summary.phiCount
        result.summary.ssaValueCount += analysis.summary.ssaValueCount
        result.summary.tupleCount += analysis.summary.tupleCount
        result.summary.openTupleCount += analysis.summary.openTupleCount
        result.summary.tupleLinkCount += analysis.summary.tupleLinkCount
        result.summary.closureCount += analysis.summary.closureCount
        result.summary.closureCaptureCount += analysis.summary.closureCaptureCount
        result.summary.regionCount += analysis.summary.regionCount
    end
    return result
end

return Analysis
