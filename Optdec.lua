--!optimize 2
-- OPTDEC v5 optimization/reconstruction pass.
-- This module intentionally sits on top of the existing decoder/emitter; it
-- does not replace Reader, Luau, Implementations, or the bytecode parser.

local Optdec = {}
Optdec.VERSION = "7.0.0"

local KEYWORDS = {
    ["and"] = true, ["break"] = true, ["continue"] = true, ["do"] = true,
    ["else"] = true, ["elseif"] = true, ["end"] = true, ["export"] = true,
    ["false"] = true, ["for"] = true, ["function"] = true, ["if"] = true,
    ["in"] = true, ["local"] = true, ["nil"] = true, ["not"] = true,
    ["or"] = true, ["repeat"] = true, ["return"] = true, ["then"] = true,
    ["true"] = true, ["type"] = true, ["until"] = true, ["while"] = true,
}

local function trim(value)
    return (value:gsub("^%s+", ""):gsub("%s+$", ""))
end

local function splitLines(source)
    local lines = {}
    source = source:gsub("\r\n", "\n"):gsub("\r", "\n")
    if source:sub(-1) ~= "\n" then
        source ..= "\n"
    end
    for line in source:gmatch("(.-)\n") do
        lines[#lines + 1] = line
    end
    return lines
end

local function isIdentifier(value)
    return value:match("^[%a_][%w_]*$") ~= nil and not KEYWORDS[value]
end

local function isTemporary(name)
    return name:match("^v%d+$") ~= nil
end

local function stripDisassemblyPrefix(line)
    -- [001] :023:GETIMPORT      body
    line = line:gsub("^%s*%[%d+%]%s*", "")
    line = line:gsub("^:%d+:%s*", "")
    line = line:gsub("^[A-Z][A-Z0-9_]*%s+", "")
    return trim(line)
end

-- Replaces identifiers while leaving quoted strings and comments untouched.
local function rewriteIdentifiers(text, resolver)
    local output = table.create(#text)
    local index = 1
    local length = #text
    local quote = nil

    while index <= length do
        local char = text:sub(index, index)
        local nextChar = text:sub(index + 1, index + 1)

        if quote then
            output[#output + 1] = char
            if char == "\\" then
                if index < length then
                    output[#output + 1] = nextChar
                    index += 2
                    continue
                end
            elseif char == quote then
                quote = nil
            end
            index += 1
        elseif char == '"' or char == "'" or char == "`" then
            quote = char
            output[#output + 1] = char
            index += 1
        elseif char == "-" and nextChar == "-" then
            output[#output + 1] = text:sub(index)
            break
        elseif char:match("[%a_]") then
            local finish = index + 1
            while finish <= length and text:sub(finish, finish):match("[%w_]") do
                finish += 1
            end
            local name = text:sub(index, finish - 1)
            output[#output + 1] = resolver(name) or name
            index = finish
        else
            output[#output + 1] = char
            index += 1
        end
    end

    return table.concat(output)
end

local function countIdentifier(text, wanted)
    local count = 0
    rewriteIdentifiers(text, function(name)
        if name == wanted then
            count += 1
        end
        return nil
    end)
    return count
end

local function parenthesize(expression)
    expression = trim(expression)
    if expression:match("^[%a_][%w_%.%[%]\"']*$")
        or expression:match("^%-?%d+%.?%d*$")
        or expression:match('^".*"$')
        or expression:match("^'.*'$")
        or expression == "nil" or expression == "true" or expression == "false"
    then
        return expression
    end
    return "(" .. expression .. ")"
end

local function isSafeDeferredExpression(expression)
    -- Calls, table construction, varargs, and function literals have observable
    -- timing/identity. Keep them as statements instead of moving them.
    if expression:find("%f[%w]function%f[%W]")
        or expression:find("...", 1, true)
        or expression:find("[{}]")
        or expression:find("[%a_][%w_%.%[%]\"']*%s*%(")
    then
        return false
    end
    return true
end

local function isBlockBoundary(line)
    return line:match("^if%s") ~= nil
        or line:match("^elseif%s") ~= nil
        or line == "else"
        or line:match("^else%s") ~= nil
        or line:match("^for%s") ~= nil
        or line:match("^while%s") ~= nil
        or line == "repeat"
        or line:match("^until%s") ~= nil
        or line == "end"
        or line:match("^end%s") ~= nil
        or line:match("^return") ~= nil
        or line:match("^break") ~= nil
        or line:match("^continue") ~= nil
        or line:match("^local function%s") ~= nil
        or line:match("^function%s") ~= nil
end

local function collectUseCounts(lines)
    local counts = {}
    for _, line in lines do
        rewriteIdentifiers(line, function(name)
            if isTemporary(name) then
                counts[name] = (counts[name] or 0) + 1
            end
            return nil
        end)
        local lhs = line:match("^([%a_][%w_]*)%s*=")
        if lhs and isTemporary(lhs) then
            counts[lhs] = math.max(0, (counts[lhs] or 0) - 1)
        end
    end
    return counts
end

local function symbolicPass(lines)
    -- Register-aware symbolic propagation. Luau reuses register numbers, so a
    -- global use-count is incorrect; every assignment creates a new version.
    local pending = {}
    local output = {}
    local declared = {}
    local semanticDeclared = {}

    local function resolve(name, stack, consumed)
        local expression = pending[name]
        if not expression then
            return nil
        end

        stack = stack or {}
        consumed = consumed or {}
        if stack[name] then
            return name
        end

        stack[name] = true
        consumed[name] = true
        local rewritten = rewriteIdentifiers(expression, function(inner)
            local value = resolve(inner, stack, consumed)
            return value and parenthesize(value) or nil
        end)
        stack[name] = nil
        return rewritten
    end

    local function rewriteWithPending(text)
        local consumed = {}
        local cache = {}
        local rewritten = rewriteIdentifiers(text, function(name)
            if cache[name] ~= nil then
                return cache[name] ~= false and cache[name] or nil
            end
            local value = resolve(name, nil, consumed)
            cache[name] = value or false
            return value and parenthesize(value) or nil
        end)
        for name in consumed do
            pending[name] = nil
        end
        return rewritten
    end

    local function flushPending(reason)
        local names = {}
        for name in pending do
            names[#names + 1] = name
        end
        table.sort(names, function(a, b)
            local an = tonumber(a:match("%d+")) or math.huge
            local bn = tonumber(b:match("%d+")) or math.huge
            return an < bn
        end)
        for _, name in names do
            local expression = pending[name]
            if expression
                and expression ~= name
                and not semanticDeclared[expression]
            then
                local prefix = declared[name] and "" or "local "
                declared[name] = true
                output[#output + 1] = prefix .. name .. " = " .. expression
                if reason then
                    output[#output + 1] = "--[[ optdec: register value crosses " .. reason .. " ]]"
                end
            end
        end
        table.clear(pending)
    end

    local function semanticName(expression)
        -- Parentheses inserted by an earlier conservative pass are accepted
        -- so `game:GetService(("Players"))` can still recover `Players`.
        local service = expression:match(
            '^game:GetService%(%(*["\']([%a_][%w_]*)["\']%)*%)$'
        )
        if service and isIdentifier(service) then
            return service
        end
        return nil
    end

    for _, original in lines do
        local line = trim(original)
        if line == "" then
            continue
        end

        -- VM scaffolding already represented by the semantic CALL/closure.
        if line:match("^%-%-%s*:")
            or line:match("^%-%-%s*FASTCALL")
            or line:match("^%-%-%s*upvalue capture")
            or line:match("^%-%-%s*clear captures")
            or line:match("^%-%-%s*%.%.%.")
        then
            continue
        end

        if isBlockBoundary(line) then
            line = rewriteWithPending(line)
            flushPending("control flow")
            output[#output + 1] = line
            continue
        end

        -- Multi-result CALLs must never rewrite destination registers through
        -- the current symbolic environment. Doing so produced assignments to
        -- upvalues, e.g. `upvalue_0, v1 = GetPlayers()`.
        local multiLhs, multiRhs = line:match(
            "^([%a_][%w_]*%s*,%s*[%a_][%w_,%s]*)%s*=%s*(.+)$"
        )
        if multiLhs and multiRhs then
            multiRhs = rewriteWithPending(multiRhs)
            local destinations = {}
            for name in multiLhs:gmatch("[%a_][%w_]*") do
                destinations[#destinations + 1] = name
                pending[name] = nil
            end
            output[#output + 1] = table.concat(destinations, ", ") .. " = " .. multiRhs
            continue
        end

        local lhs, rhs = line:match("^([%a_][%w_]*)%s*=%s*(.+)$")
        if lhs and rhs and not line:match("^local%s") then
            -- Resolve the old version before replacing lhs with its new value.
            rhs = rewriteWithPending(rhs)
            pending[lhs] = nil

            if isTemporary(lhs) and isSafeDeferredExpression(rhs) then
                pending[lhs] = rhs
                continue
            end

            local inferredName = isTemporary(lhs) and semanticName(rhs) or nil
            if inferredName then
                local prefix = semanticDeclared[inferredName] and "" or "local "
                semanticDeclared[inferredName] = true
                output[#output + 1] = prefix .. inferredName .. " = " .. rhs
                pending[lhs] = inferredName
                continue
            end

            if not declared[lhs] and isTemporary(lhs) then
                line = "local " .. lhs .. " = " .. rhs
                declared[lhs] = true
            else
                line = lhs .. " = " .. rhs
            end
            output[#output + 1] = line
            continue
        end

        line = rewriteWithPending(line)
        output[#output + 1] = line
    end

    flushPending(nil)
    return output
end

local function removeDeadMoves(lines)
    local output = {}
    for _, line in lines do
        local lhs, rhs = line:match("^%s*([%a_][%w_]*)%s*=%s*([%a_][%w_]*)%s*$")
        if lhs and lhs == rhs then
            continue
        end
        output[#output + 1] = line
    end
    return output
end

local function recoverMultretArguments(lines)
    -- Rejoin an immediately-produced MULTRET value with the following call.
    -- This reconstructs nested calls such as
    -- self:_addConnection(signal:Connect(callback)).
    local removed = {}

    for index, line in lines do
        if not line:find("...", 1, true) then
            continue
        end

        local producerIndex = index - 1
        while producerIndex >= 1
            and trim(lines[producerIndex]):match("^%-%-")
        do
            producerIndex -= 1
        end

        if producerIndex < 1 then
            continue
        end

        local producer = trim(lines[producerIndex])
        local register, expression = producer:match(
            "^local%s+(v%d+)%s*=%s*(.+)$"
        )
        if not register then
            register, expression = producer:match("^(v%d+)%s*=%s*(.+)$")
        end

        if register and expression
            and expression:find("%(")
            and not expression:find("function", 1, true)
        then
            -- gsub replacement strings interpret `%` as capture syntax. Luau
            -- expressions frequently contain modulo operators and patterns
            -- such as "%1 %2", so passing the reconstructed expression as a
            -- replacement string crashes with "invalid use of '%'". A
            -- replacement callback returns the text literally.
            lines[index] = line:gsub(
                "%.%.%.",
                function()
                    return parenthesize(expression)
                end,
                1
            )
            removed[producerIndex] = true
        end
    end

    local output = {}
    for index, line in lines do
        if not removed[index] then
            output[#output + 1] = line
        end
    end
    return output
end

local function reconstructNamedFunctions(lines)
    -- The bytecode stores `function T:m()` as a closure followed by
    -- `T.m = closure`. Rejoin that canonical pattern after register cleanup.
    local removed = {}
    local index = 1

    local function opensBlock(line)
        return line:match("^local function%s") ~= nil
            or line:match("^function%s") ~= nil
            or line:match("=%s*function%s*%b()%s*$") ~= nil
            or line:find(" then", 1, true) ~= nil
            or line:find(" do", 1, true) ~= nil
            or line == "repeat"
    end

    while index <= #lines do
        local functionName, parameters = lines[index]:match(
            "^local function%s+([%a_][%w_]*)%s*%((.*)%)%s*$"
        )

        if not functionName then
            index += 1
            continue
        end

        local depth = 1
        local finish = index + 1
        while finish <= #lines and depth > 0 do
            local line = trim(lines[finish])
            if line == "end" or line:match("^end%s") or line:match("^until%s") then
                depth -= 1
            end
            if opensBlock(line)
                and not line:match("^elseif%s")
                and not line:match("^else")
            then
                depth += 1
            end
            finish += 1
        end

        local assignmentIndex = nil
        local owner = nil
        for candidate = finish, math.min(#lines, finish + 8) do
            local line = trim(lines[candidate])
            local possibleOwner, field, value = line:match(
                "^([%a_][%w_%.%[%]\"']*)%.([%a_][%w_]*)%s*=%s*([%a_][%w_]*)$"
            )
            if possibleOwner and field == functionName and value == functionName then
                assignmentIndex = candidate
                owner = possibleOwner
                break
            end
        end

        if assignmentIndex and owner then
            local first, rest = parameters:match("^%s*([^,]+)%s*,%s*(.*)$")
            first = first or trim(parameters)
            rest = rest or ""
            local firstName = first:match("^([%a_][%w_]*)")
            local isMethod = firstName == "self" or firstName == "p1"

            if isMethod then
                lines[index] = "function " .. owner .. ":" .. functionName .. "(" .. rest .. ")"
                if firstName ~= "self" then
                    for bodyIndex = index + 1, finish - 2 do
                        lines[bodyIndex] = rewriteIdentifiers(lines[bodyIndex], function(name)
                            return name == firstName and "self" or nil
                        end)
                    end
                end
            else
                lines[index] = "function " .. owner .. "." .. functionName .. "(" .. parameters .. ")"
            end

            removed[assignmentIndex] = true
        end

        index = math.max(index + 1, finish)
    end

    local output = {}
    for lineIndex, line in lines do
        if not removed[lineIndex] then
            output[#output + 1] = line
        end
    end
    return output
end

local function recoverGenericForCalls(lines)
    -- CALL with MULTRET is commonly followed by FORGPREP. Rejoin
    -- `r0, r1, r2 = expr(); for k, v in r0 do` into the source-level loop.
    local removed = {}

    for index, line in lines do
        local destinations, expression = trim(line):match(
            "^([%a_][%w_]*%s*,%s*[%a_][%w_,%s]*)%s*=%s*(.+)$"
        )
        if not destinations then
            continue
        end

        local iteratorRegister = destinations:match("^%s*([%a_][%w_]*)")
        if not iteratorRegister then
            continue
        end

        for candidate = index + 1, math.min(#lines, index + 5) do
            local candidateLine = trim(lines[candidate])
            if candidateLine:match("^%-%-") then
                continue
            end

            local variables, iterator = candidateLine:match(
                "^for%s+(.+)%s+in%s+([%a_][%w_]*)%s+do"
            )
            if variables and iterator == iteratorRegister then
                lines[candidate] = "for " .. trim(variables) .. " in " .. expression .. " do"
                removed[index] = true
            end
            break
        end
    end

    local output = {}
    for index, line in lines do
        if not removed[index] then
            output[#output + 1] = line
        end
    end
    return output
end

local function inferLoopNames(lines)
    -- Use iterator semantics only when the role is unambiguous. Debug names
    -- always win; these names replace compiler temporaries only.
    for index, line in lines do
        local variables, iterator = trim(line):match("^for%s+(.+)%s+in%s+(.+)%s+do")
        if not variables or not iterator then
            continue
        end

        local original = {}
        for name in variables:gmatch("[%a_][%w_]*") do
            original[#original + 1] = name
        end
        if #original == 0 then
            continue
        end

        local inferred = nil
        if iterator:find("GetPlayers", 1, true) then
            inferred = {"_", "player"}
        elseif iterator:find("_playerConnections", 1, true) then
            inferred = {"player"}
        elseif iterator:find("_connections", 1, true) then
            inferred = {"_", "connection"}
        elseif iterator:find("GetDescendants", 1, true) then
            inferred = {"_", "descendant"}
        elseif iterator:find("GetChildren", 1, true) then
            inferred = {"_", "child"}
        end

        if not inferred then
            continue
        end

        local rename = {}
        for position, oldName in original do
            if isTemporary(oldName) and inferred[position] then
                rename[oldName] = inferred[position]
            end
        end
        if next(rename) == nil then
            continue
        end

        lines[index] = rewriteIdentifiers(lines[index], function(name)
            return rename[name]
        end)

        local depth = 1
        for bodyIndex = index + 1, #lines do
            local body = trim(lines[bodyIndex])
            if body:match("^end") or body:match("^until%s") then
                depth -= 1
                if depth == 0 then
                    break
                end
            end

            lines[bodyIndex] = rewriteIdentifiers(lines[bodyIndex], function(name)
                return rename[name]
            end)

            if body:match("^local function%s")
                or body:match("^function%s")
                or body:find(" then", 1, true)
                or body:find(" do", 1, true)
                or body == "repeat"
            then
                depth += 1
            end
        end
    end
    return lines
end

local METHOD_PARAMETERS = {
    FixCharacter = {"player", "character"},
    _setupPlayer = {"player"},
    _applyAccessoryFix = {"player", "character"},
    _addConnection = {"connection"},
    _cleanupPlayer = {"player"},
}

local function normalizeMethodSelf(lines)
    local depth = 0
    local active = nil

    for index, line in lines do
        local owner, method, parameters = trim(line):match(
            "^function%s+([%a_][%w_%.]*)%:([%a_][%w_]*)%((.*)%)"
        )
        if owner then
            active = {depth = depth + 1, method = method}

            local names = METHOD_PARAMETERS[method]
            if names then
                local parts = {}
                for part in parameters:gmatch("[^,]+") do
                    parts[#parts + 1] = trim(part)
                end
                for position, semanticName in names do
                    local part = parts[position]
                    if part then
                        parts[position] = part:gsub("^[%a_][%w_]*", semanticName, 1)
                    end
                end
                lines[index] = "function " .. owner .. ":" .. method .. "(" .. table.concat(parts, ", ") .. ")"
            end
        end

        if active and index > 1 then
            lines[index] = rewriteIdentifiers(lines[index], function(name)
                return name == "p1" and "self" or nil
            end)
        end

        local body = trim(lines[index])
        if body:match("^end") or body:match("^until%s") then
            depth = math.max(0, depth - 1)
            if active and depth < active.depth then
                active = nil
            end
        end
        if body:match("^local function%s")
            or body:match("^function%s")
            or body:find(" then", 1, true)
            or body:find(" do", 1, true)
            or body == "repeat"
        then
            depth += 1
        end
    end
    return lines
end

local function cleanSourceAnnotations(lines, options)
    if options and options.KeepControlFlowAnnotations then
        return lines
    end

    local output = {}
    for _, line in lines do
        local body = trim(line)
        if body:match("^%-%- jump to #")
            or body:match("^%-%- jump back to #")
            or body:match("^%-%-%[%[ optdec: register value crosses")
        then
            continue
        end

        line = line:gsub("%s*%-%- goto #%d+", "")
        line = line:gsub("%s*%-%- end at #%d+", "")
        line = line:gsub("%s*%-%- iterate %+ jump to #%d+", "")
        output[#output + 1] = line
    end
    return output
end

local function indent(lines)
    local output = {}
    local depth = 0

    for _, raw in lines do
        local line = trim(raw)
        local closes = line == "end"
            or line:match("^end%s")
            or line == "else"
            or line:match("^else%s")
            or line:match("^elseif%s")
            or line:match("^until%s")

        if closes then
            depth = math.max(0, depth - 1)
        end

        output[#output + 1] = string.rep("    ", depth) .. line

        local opens = line:find(" then", 1, true) ~= nil
            or line:find(" do", 1, true) ~= nil
            or line == "repeat"
            or line:match("^local function%s.*%)%s*$") ~= nil
            or line:match("^function%s.*%)%s*$") ~= nil
            or line:match("=%s*function%s*%b()%s*$") ~= nil

        if opens and not line:match("^%-%-") then
            depth += 1
        end
        if line == "else" or line:match("^else%s") or line:match("^elseif%s") then
            depth += 1
        end
    end

    return output
end

local function addFidelityHeader(lines, options)
    if options and options.SuppressOptdecHeader then
        return lines
    end
    table.insert(lines, 1, "--[[ optdec v7: high-fidelity reconstruction; erased comments and stripped names are unrecoverable. ]]")
    return lines
end

function Optdec.optimize(source, options)
    assert(type(source) == "string", "Optdec.optimize expects emitted source")

    local rawLines = splitLines(source)
    local lines = {}
    local previousSourceLine = nil
    for _, line in rawLines do
        local sourceLine = line:match("^%s*%[%d+%]%s*:(%d+):")
            or line:match("^%s*:(%d+):")
        local body = stripDisassemblyPrefix(line)

        if options and options.ShowInstructionLines
            and sourceLine
            and sourceLine ~= "0"
            and sourceLine ~= previousSourceLine
        then
            lines[#lines + 1] = "--[[ source line " .. tostring(tonumber(sourceLine)) .. " ]]"
            previousSourceLine = sourceLine
        end

        lines[#lines + 1] = body
    end

    lines = symbolicPass(lines)
    lines = recoverMultretArguments(lines)
    lines = removeDeadMoves(lines)
    lines = reconstructNamedFunctions(lines)
    lines = recoverGenericForCalls(lines)
    lines = inferLoopNames(lines)
    lines = normalizeMethodSelf(lines)
    lines = cleanSourceAnnotations(lines, options)
    lines = indent(lines)
    lines = addFidelityHeader(lines, options)

    return table.concat(lines, "\n")
end

return Optdec
