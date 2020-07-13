local expr = {
	sym = {};
	Scode = {};
	Seval = {};
}
expr.mt = {
	__add = function(l, r)
		l = expr.coerce(l)
		r = expr.coerce(r)
		local e = {
			[expr.sym] = true;
			[expr.Scode] = ('(+ %s %s)'):format(l[expr.Scode], r[expr.Scode]);
			[expr.Seval] = function() return l[expr.Seval]() + r[expr.Seval]() end;
		}
		setmetatable(e, expr.mt)
		return e
	end;
	__sub = function(l, r)
		l = expr.coerce(l)
		r = expr.coerce(r)
		local e = {
			[expr.sym] = true;
			[expr.Scode] = ('(- %s %s)'):format(l[expr.Scode], r[expr.Scode]);
			[expr.Seval] = function() return l[expr.Seval]() - r[expr.Seval]() end;
		}
		setmetatable(e, expr.mt)
		return e
	end;
	__mul = function(l, r)
		l = expr.coerce(l)
		r = expr.coerce(r)
		local e = {
			[expr.sym] = true;
			[expr.Scode] = ('(* %s %s)'):format(l[expr.Scode], r[expr.Scode]);
			[expr.Seval] = function() return l[expr.Seval]() * r[expr.Seval]() end;
		}
		setmetatable(e, expr.mt)
		return e
	end;
	__div = function(l, r)
		l = expr.coerce(l)
		r = expr.coerce(r)
		local e = {
			[expr.sym] = true;
			[expr.Scode] = ('(/ %s %s)'):format(l[expr.Scode], r[expr.Scode]);
			[expr.Seval] = function() return l[expr.Seval]() / r[expr.Seval]() end;
		}
		setmetatable(e, expr.mt)
		return e
	end;
	__pow = function(l, r)
		l = expr.coerce(l)
		r = expr.coerce(r)
		local e = {
			[expr.sym] = true;
			[expr.Scode] = ('(^ %s %s)'):format(l[expr.Scode], r[expr.Scode]);
			[expr.Seval] = function() return l[expr.Seval]() ^ r[expr.Seval]() end;
		}
		setmetatable(e, expr.mt)
		return e
	end;
}
function expr.coerce(e)
	if type(e) == 'table' and e[expr.sym] then
		return e
	elseif type(e) == 'number' then
		local e = {
			[expr.sym] = true;
			[expr.Scode] = tostring(e);
		}
		setmetatable(e, expr.mt)
		return e
	else
		error(('todo: %s'):format(e))
	end
end
function expr.eval(...)
	local res = {}
	for i = 1, select('#', ...) do
		res[i] = expr.coerce(select(i, ...))[expr.Seval]()
	end
	return table.unpack(res, 1, select('#', ...))
end
local function satisfy(body)
	local h = io.open('test.smt2', 'w')
	h:write '(set-logic QF_NRA)\n'
	local vars = {}
	local function var(label)
		local name = label:gsub('[^a-z]', function(c)
			return '_' .. tostring(c:byte()) .. '_'
		end)
		local i = nil
		while vars[name .. tostring(i)] do
			i = (i or 0) + 1
		end
		if i then
			name = name .. tostring(i)
		end
		h:write(('(declare-fun %s () Real)\n'):format(name))
		local var; var = {
			[expr.sym] = true;
			[expr.Scode] = name;
			[expr.Seval] = function() return var.val end;
			label = label;
			name = name;
		}
		vars[name] = var
		setmetatable(var, expr.mt)
		return var
	end
	local function equal(...)
		for i = 2, select('#', ...) do
			h:write(('(assert (= %s %s))\n'):format(expr.coerce(select(i - 1, ...))[expr.Scode], expr.coerce(select(i, ...))[expr.Scode]))
		end
	end
	local res = body(var, equal)
	h:write '(check-sat)\n'
	for name, var in pairs(vars) do
		h:write(('(get-value (%s))\n'):format(name))
	end
	h:close()

	h = io.popen('z3 test.smt2', 'r')
	while true do
		local line = h:read '*l'
		if not line then
			break
		end
		repeat
			if line == 'sat' then
				break
			end

			local name, val = line:match '^%(%(([^ %(%)]+) (%d+%.?%d*)%)%)$'
			if name then
				vars[name].val = tonumber(val)
				break
			end

			local name, val = line:match '^%(%(([^ %(%)]+) %(%- (%d+%.?%d*)%)%)%)$'
			if name then
				vars[name].val = -tonumber(val)
				break
			end

			error(('todo: %q'):format(line))
		until true
	end
	h:close()
	return res
end

local res = satisfy(function(var, equal)
	local foo = var 'foo'
	equal(foo, 2)
	return foo
end)
print(expr.eval(res))
