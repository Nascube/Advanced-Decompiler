--!optimize 2

local DexCollectionIntegration = {}
DexCollectionIntegration.VERSION = "1.0.0"

local function resolveCollector(env)
    if env and type(env.collectscript) == "function" then
        return env.collectscript
    end
    local global = (getgenv and getgenv()) or (getfenv and getfenv()) or _G
    return global and global.collectscript
end

function DexCollectionIntegration.IsAvailable(env)
    return type(resolveCollector(env)) == "function"
end

local function safeFileName(value)
    value = tostring(value)
    value = value:gsub("[^%w%._%-]", "_")
    if #value > 180 then value = value:sub(1, 180) end
    return value
end

function DexCollectionIntegration.Register(context, selection, env, gameObject)
    assert(context and type(context.Register) == "function", "Dex context expected")
    assert(selection and type(selection) == "table", "Dex selection expected")

    context:Register("SAVE_OPTDEC_COLLECTION", {
        Name = "Save OPTDEC Collection",
        OnClick = function()
            local collectscript = resolveCollector(env)
            if type(collectscript) ~= "function" then
                warn("[OPTDEC] collectscript is not installed")
                return
            end

            local write = env and env.writefile or writefile
            local decompile = env and env.decompile or decompile
            local getBytecode = env and env.getscriptbytecode or getscriptbytecode
            local selected = selection.List or {}

            for _, node in next, selected do
                local object = node.Obj
                if object
                    and object:IsA("LuaSourceContainer")
                    and (not env.isViableDecompileScript
                        or env.isViableDecompileScript(object))
                then
                    local fullName = object:GetFullName()
                    local baseName = string.format(
                        "%i.%s.%s",
                        gameObject.PlaceId,
                        object.ClassName,
                        safeFileName(env.parsefile and env.parsefile(object.Name) or object.Name)
                    )

                    local bytecodePath = baseName .. ".Bytecode.bin"
                    local dexSourcePath = baseName .. ".DexDecompiled.lua"
                    local collectionPath = baseName .. ".Collection.v1.4.json"
                    local dexSource = nil

                    if type(decompile) == "function" then
                        local ok, result = pcall(decompile, object)
                        if ok and type(result) == "string" then
                            dexSource = result
                            if type(write) == "function" then
                                write(dexSourcePath, result)
                            end
                        end
                    end

                    if type(getBytecode) == "function" and type(write) == "function" then
                        local ok, bytecode = pcall(getBytecode, object)
                        if ok and type(bytecode) == "string" then
                            write(bytecodePath, bytecode)
                        end
                    end

                    local ok, jsonOrError, savedPath, checksum = pcall(
                        collectscript,
                        object,
                        {
                            Label = fullName,
                            Notes = [[
Collected from Dex Explorer.
Dex decompiled source is a baseline artifact, not ground truth.
Raw bytecode and collection JSON are canonical.
]],
                            DexSourceOutput = dexSource,
                            DecompilerTimeout = 900,
                            DecompilerMode = "disasm",
                            IncludeBothOutputs = true,
                            IncludeReadableSource = true,
                            IncludeRuntimeClosure = true,
                            MaxRuntimeFunctions = 10000,
                            MaxRuntimeProtoDepth = 128,
                            SaveToFile = true,
                            Path = collectionPath,
                            ExternalArtifacts = {
                                bytecode = bytecodePath,
                                dexDecompiledSource = dexSourcePath,
                                collection = collectionPath,
                            },
                            CompilerMetadata = {
                                acquisition = "Dex Explorer",
                                instanceClass = object.ClassName,
                                instanceFullName = fullName,
                            },
                        }
                    )

                    if ok then
                        print(
                            "[OPTDEC] Collection saved:",
                            savedPath or collectionPath,
                            "checksum:",
                            checksum
                        )
                    else
                        warn(
                            "[OPTDEC] Collection failed for " ..
                            fullName .. ": " .. tostring(jsonOrError)
                        )
                    end

                    task.wait(0.2)
                end
            end
        end,
    })
end

return DexCollectionIntegration
