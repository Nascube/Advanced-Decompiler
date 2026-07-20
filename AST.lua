--!optimize 2

local AST = {}
AST.VERSION = "1.1.0"
AST.SCHEMA = "optdec-ast-v1"

local function values(t)
    local out = {}
    for _, value in t or {} do if type(value) == "table" then out[#out + 1] = value end end
    return out
end

local function indexById(items, field)
    local out = {}
    for _, item in values(items) do out[item[field]] = item end
    return out
end

local function registerExpression(index)
    return { type = "RegisterExpression", register = index }
end

local function expressionForControl(control)
    local op, operands = control.opcode, control.operands or {}
    if op == "JUMPIF" or op == "JUMPIFNOT" then
        return {
            type = "TruthinessExpression",
            value = registerExpression(operands.A),
            negated = op == "JUMPIFNOT",
        }
    end
    local operators = {
        JUMPIFEQ = "==", JUMPIFNOTEQ = "~=",
        JUMPIFLT = "<", JUMPIFLE = "<=",
        JUMPIFNOTLT = ">=", JUMPIFNOTLE = ">",
    }
    if operators[op] then
        return {
            type = "BinaryExpression", operator = operators[op],
            left = registerExpression(operands.A),
            right = registerExpression(operands.aux or operands.B),
        }
    end
    if string.sub(op, 1, 7) == "JUMPXEQ" then
        return {
            type = "ConstantComparisonExpression",
            operator = control.inverted and "~=" or "==",
            left = registerExpression(operands.A),
            constantKind = string.sub(op, 8),
            encodedConstant = operands.aux,
        }
    end
    return {
        type = "BytecodePredicateExpression", opcode = op,
        operands = operands, successors = control.successors,
    }
end

local function predicateFor(region, blockById, controlByPc)
    local block = blockById[region.header]
    local control = block and controlByPc[block.terminatorPc] or nil
    if not control then return { type = "UnknownPredicate", headerBlockId = region.header }, false end
    return {
        type = "ControlPredicate",
        opcode = control.opcode,
        sourcePc = control.sourcePc,
        inverted = control.inverted,
        operands = control.operands,
        successors = control.successors,
        expression = expressionForControl(control),
    }, true
end

local function astNode(region, blockById, controlByPc)
    local predicate, resolved = predicateFor(region, blockById, controlByPc)
    if region.kind == "if" or region.kind == "ifElse" then
        return {
            type = "IfStatement", regionId = region.id,
            condition = predicate, conditionResolved = resolved,
            thenBody = { type = "BlockStatement", entryBlockId = region.thenBlock },
            elseBody = region.kind == "ifElse"
                and { type = "BlockStatement", entryBlockId = region.elseBlock }
                or nil,
            joinBlockId = region.join, children = region.children,
        }
    elseif region.kind == "naturalLoop" then
        return {
            type = "LoopStatement", loopKind = "NaturalLoop", regionId = region.id,
            condition = predicate, conditionResolved = resolved,
            headerBlockId = region.header, latchBlockId = region.latch,
            bodyBlockIds = region.nodes, children = region.children,
        }
    end
    return {
        type = "UnstructuredRegion", regionId = region.id,
        startBlockId = region.startBlock, endBlockId = region.endBlock,
        children = region.children, reason = "incomplete structural operands",
    }
end

function AST.buildSession(session)
    local tree = assert(session.stages and session.stages.regionTree, "regionTree stage missing")
    assert(not tree.error, "regionTree failed: " .. tostring(tree.error))
    local treeProtos = values(tree.prototypes)
    local result = {
        schema = AST.SCHEMA, version = AST.VERSION, prototypes = {},
        summary = {
            prototypeCount = 0, astNodeCount = 0, ifStatementCount = 0,
            ifElseStatementCount = 0, loopStatementCount = 0,
            unstructuredRegionCount = 0, resolvedConditionCount = 0,
            unresolvedConditionCount = 0, typedPredicateCount = 0,
        },
    }
    for index, treeProto in treeProtos do
        local blockById = indexById(treeProto.blocks, "id")
        local controlByPc = indexById(treeProto.controls, "sourcePc")
        local proto = { protoId = treeProto.protoId, body = {}, roots = treeProto.roots }
        for _, region in values(treeProto.regions) do
            local node = astNode(region, blockById, controlByPc)
            proto.body[#proto.body + 1] = node
            result.summary.astNodeCount += 1
            if node.type == "IfStatement" then
                result.summary.ifStatementCount += 1
                if node.elseBody then result.summary.ifElseStatementCount += 1 end
            elseif node.type == "LoopStatement" then
                result.summary.loopStatementCount += 1
            else
                result.summary.unstructuredRegionCount += 1
            end
            if node.condition and node.condition.expression then
                result.summary.typedPredicateCount += 1
            end
            if node.conditionResolved == true then
                result.summary.resolvedConditionCount += 1
            elseif node.conditionResolved == false then
                result.summary.unresolvedConditionCount += 1
            end
        end
        result.prototypes[#result.prototypes + 1] = proto
        result.summary.prototypeCount += 1
    end
    return result
end

return AST
