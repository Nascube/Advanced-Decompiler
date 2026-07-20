-- Not using slow metatables here because we need it fast
local FLOAT_PRECISION = 24

local Reader = {}

local function decimalMultiplyAdd(decimal, multiplier, addition)
	local carry = addition
	local output = table.create(#decimal + 4)

	for index = #decimal, 1, -1 do
		local digit = string.byte(decimal, index) - 48
		local value = digit * multiplier + carry

		output[index] = tostring(value % 10)
		carry = math.floor(value / 10)
	end

	local prefix = ""

	while carry > 0 do
		prefix = tostring(carry % 10) .. prefix
		carry = math.floor(carry / 10)
	end

	return prefix .. table.concat(output)
end

function Reader.new(bytecode)
	local stream = buffer.fromstring(bytecode)
	local cursor = 0
	--
	local self = {}

	function self:len()
		return buffer.len(stream)
	end

	function self:nextByte()
		local result = buffer.readu8(stream, cursor)
		cursor += 1
		return result
	end
	function self:nextSignedByte()
		local result = buffer.readi8(stream, cursor)
		cursor += 1
		return result
	end
	function self:nextBytes(count)
		local result = {}
		for i = 1, count do
			table.insert(result, self:nextByte())
		end
		return result
	end

	function self:nextChar()
		local result = string.char(self:nextByte())
		return result
	end

	function self:nextUInt32()
		local result = buffer.readu32(stream, cursor)
		cursor += 4
		return result
	end
	function self:nextInt32()
		local result = buffer.readi32(stream, cursor)
		cursor += 4
		return result
	end

	function self:nextFloat()
		local result = buffer.readf32(stream, cursor)
		cursor += 4
		return tonumber(string.format(`%0.{FLOAT_PRECISION}f`, result))
	end

	function self:nextVarInt()
		local result = 0
		for i = 0, 4 do
			local b = self:nextByte()
			result = bit32.bor(result, bit32.lshift(bit32.band(b, 0x7F), i * 7))
			if not bit32.btest(b, 0x80) then
				break
			end
		end
		return result
	end
	
	function self:nextVarInt64String()
	local chunks = {}
	local terminated = false

	-- An unsigned 64-bit varint needs at most ten bytes.
	for index = 1, 10 do
		local byte = self:nextByte()

		chunks[index] = bit32.band(byte, 0x7F)

		if not bit32.btest(byte, 0x80) then
			terminated = true
			break
		end
	end

	if not terminated then
		error("Malformed 64-bit varint", 2)
	end

	-- Convert the little-endian base-128 representation to an
	-- exact decimal string without passing through a double.
	local decimal = "0"

	for index = #chunks, 1, -1 do
		decimal = decimalMultiplyAdd(
			decimal,
			128,
			chunks[index]
		)
	end

	return decimal
end

	function self:nextString(len)
		len = len or self:nextVarInt()
		if len == 0 then
			return ""
		else
			local result = buffer.readstring(stream, cursor, len)
			cursor += len
			return result
		end
	end

	function self:nextDouble()
		local result = buffer.readf64(stream, cursor)
		cursor += 8
		return result
	end

	return self
end

function Reader:Set(...)
	FLOAT_PRECISION = ...
end

return Reader
