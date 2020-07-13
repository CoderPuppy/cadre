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
	__unm = function(self)
		local e = {
			[expr.sym] = true;
			[expr.Scode] = ('(- %s)'):format(self[expr.Scode]);
			[expr.Seval] = function() return -self[expr.Seval]() end;
		}
		setmetatable(e, expr.mt)
		return e
	end;
}
function expr.coerce(e)
	if type(e) == 'table' and e[expr.sym] then
		return e
	elseif type(e) == 'number' then
		local v = e
		local e = {
			[expr.sym] = true;
			[expr.Scode] = tostring(v);
			[expr.Seval] = function() return v end;
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
function expr.and_(...)
	local args = table.pack(...)
	for i = 1, args.n do
		args[i] = expr.coerce(args[i])
	end
	local e = {
		[expr.sym] = true;
		[expr.Seval] = function()
			for i = 1, args.n do
				if not args[i][expr.Seval]() then
					return false
				end
			end
			return true
		end;
	}
	e[expr.Scode] = '(and'
	for i = 1, args.n do
		e[expr.Scode] = e[expr.Scode] .. ' ' .. args[i][expr.Scode]
	end
	e[expr.Scode] = e[expr.Scode] .. ')'
	setmetatable(e, expr.mt)
	return e
end
function expr.or_(...)
	local args = table.pack(...)
	for i = 1, args.n do
		args[i] = expr.coerce(args[i])
	end
	local e = {
		[expr.sym] = true;
		[expr.Seval] = function()
			for i = 1, args.n do
				if args[i][expr.Seval]() then
					return true
				end
			end
			return false
		end;
	}
	e[expr.Scode] = '(or'
	for i = 1, args.n do
		e[expr.Scode] = e[expr.Scode] .. ' ' .. args[i][expr.Scode]
	end
	e[expr.Scode] = e[expr.Scode] .. ')'
	setmetatable(e, expr.mt)
	return e
end
function expr.equal(...)
	local args = table.pack(...)
	for i = 1, args.n do
		args[i] = expr.coerce(args[i])
	end
	local e = {
		[expr.sym] = true;
		[expr.Seval] = function()
			for i = 2, args.n do
				if args[i - 1][expr.Seval]() ~= args[i][expr.Seval]() then
					return false
				end
			end
			return true
		end;
	}
	e[expr.Scode] = '(='
	for i = 1, args.n do
		e[expr.Scode] = e[expr.Scode] .. ' ' .. args[i][expr.Scode]
	end
	e[expr.Scode] = e[expr.Scode] .. ')'
	setmetatable(e, expr.mt)
	return e
end
function expr.strictly_decreasing(...)
	local args = table.pack(...)
	for i = 1, args.n do
		args[i] = expr.coerce(args[i])
	end
	local e = {
		[expr.sym] = true;
		[expr.Seval] = function()
			local v = args[1][expr.Seval]()
			for i = 2, args.n do
				local v_ = args[i][expr.Seval]()
				if v <= v_ then
					return false
				end
				v = v_
			end
			return true
		end;
	}
	e[expr.Scode] = '(>'
	for i = 1, args.n do
		e[expr.Scode] = e[expr.Scode] .. ' ' .. args[i][expr.Scode]
	end
	e[expr.Scode] = e[expr.Scode] .. ')'
	setmetatable(e, expr.mt)
	return e
end
function expr.strictly_increasing(...)
	local args = table.pack(...)
	for i = 1, args.n do
		args[i] = expr.coerce(args[i])
	end
	local e = {
		[expr.sym] = true;
		[expr.Seval] = function()
			local v = args[1][expr.Seval]()
			for i = 2, args.n do
				local v_ = args[i][expr.Seval]()
				if v >= v_ then
					return false
				end
				v = v_
			end
			return true
		end;
	}
	e[expr.Scode] = '(<'
	for i = 1, args.n do
		e[expr.Scode] = e[expr.Scode] .. ' ' .. args[i][expr.Scode]
	end
	e[expr.Scode] = e[expr.Scode] .. ')'
	setmetatable(e, expr.mt)
	return e
end
function expr.decreasing(...)
	local args = table.pack(...)
	for i = 1, args.n do
		args[i] = expr.coerce(args[i])
	end
	local e = {
		[expr.sym] = true;
		[expr.Seval] = function()
			local v = args[1][expr.Seval]()
			for i = 2, args.n do
				local v_ = args[i][expr.Seval]()
				if v < v_ then
					return false
				end
				v = v_
			end
			return true
		end;
	}
	e[expr.Scode] = '(>='
	for i = 1, args.n do
		e[expr.Scode] = e[expr.Scode] .. ' ' .. args[i][expr.Scode]
	end
	e[expr.Scode] = e[expr.Scode] .. ')'
	setmetatable(e, expr.mt)
	return e
end
function expr.increasing(...)
	local args = table.pack(...)
	for i = 1, args.n do
		args[i] = expr.coerce(args[i])
	end
	local e = {
		[expr.sym] = true;
		[expr.Seval] = function()
			local v = args[1][expr.Seval]()
			for i = 2, args.n do
				local v_ = args[i][expr.Seval]()
				if v > v_ then
					return false
				end
				v = v_
			end
			return true
		end;
	}
	e[expr.Scode] = '(<='
	for i = 1, args.n do
		e[expr.Scode] = e[expr.Scode] .. ' ' .. args[i][expr.Scode]
	end
	e[expr.Scode] = e[expr.Scode] .. ')'
	setmetatable(e, expr.mt)
	return e
end
function expr.not_(e_)
	e_ = expr.coerce(e_)
	local e = {
		[expr.sym] = true;
		[expr.Scode] = ('(not %s)'):format(e_[expr.Scode]);
		[expr.Seval] = function() return not e_[expr.Seval]() end;
	}
	setmetatable(e, expr.mt)
	return e
end
local function satisfy(body)
	local h = io.open('test.smt2', 'w')
	h:write '(set-logic QF_NRA)\n'
	local vars = {}
	local function var(label)
		local name = label:gsub('[ _%(%)]', function(c)
			return '_' .. tostring(c:byte()) .. '_'
		end)
		local i = nil
		while vars[name .. (i and tostring(i) or '')] do
			i = (i or 0) + 1
		end
		name = name .. (i and tostring(i) or '')
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
	local function ensure(...)
		for i = 1, select('#', ...) do
			h:write(('(assert %s)\n'):format(expr.coerce(select(i, ...))[expr.Scode]))
		end
	end
	local res = body(var, ensure)
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
				print(name, tonumber(val))
				vars[name].val = tonumber(val)
				break
			end

			local name, val = line:match '^%(%(([^ %(%)]+) %(%- (%d+%.?%d*)%)%)%)$'
			if name then
				print(name, -tonumber(val))
				vars[name].val = -tonumber(val)
				break
			end

			local name, num, den = line:match '^%(%(([^ %(%)]+) %(/ (%d+%.?%d*) (%d+%.?%d*)%)%)%)$'
			if name then
				print(name, tonumber(num)/tonumber(den))
				vars[name].val = tonumber(num)/tonumber(den)
				break
			end

			local name, num, den = line:match '^%(%(([^ %(%)]+) %(%- %(/ (%d+%.?%d*) (%d+%.?%d*)%)%)%)%)$'
			if name then
				print(name, -tonumber(num)/tonumber(den))
				vars[name].val = -tonumber(num)/tonumber(den)
				break
			end

			error(('todo: %q'):format(line))
		until true
	end
	h:close()
	return res
end

local res = satisfy(function(var, ensure)
	local function parallel(...)
		local parts_c, parts_x, parts_y = {}, {}, {}
		local n = select('#', ...)
		for i = 1, n do
			local l = select(i, ...)
			local c = var('parallel ' .. l.name)
			parts_c[i] = expr.not_(expr.equal(c, 0))
			parts_x[i] = c * l.x_coef
			parts_y[i] = c * l.y_coef
		end
		return expr.and_(
			expr.and_(table.unpack(parts_c, 1, n)),
			expr.equal(table.unpack(parts_x, 1, n)),
			expr.equal(table.unpack(parts_y, 1, n))
		)
	end
	local function perpendicular(a, b)
		local c = var('perpendicular')
		return expr.and_(
			expr.not_(expr.equal(c, 0)),
			expr.equal(a.x_coef, -c * b.y_coef),
			expr.equal(a.y_coef,  c * b.x_coef)
		)
	end
	local shape = {
		sym = {};
		Scontains = {};
		all = {};
	}
	shape.mt = {
		__call = function(self, opts)
			for k, v in pairs(opts) do
				local prop = self[k]
				repeat
					if type(prop) == 'table' then
						if prop[shape.sym] then
							prop(v)
							break
						elseif prop[expr.sym] then
							ensure(expr.equal(prop, v))
							break
						end
					end
					error(('todo: %s (%s) = %s'):format(k, prop, v))
				until true
			end
			return self
		end;
	}
	function shape.point(name, opts)
		local point = {
			[shape.sym] = true;
			name = name;
			x = var(name .. ' x');
			y = var(name .. ' y');
		}
		point[shape.Scontains] = function(x, y)
			return expr.equal(x, point.x) and expr.equal(y, point.y)
		end
		function point.on(s)
			return s[shape.Scontains](point.x, point.y)
		end
		setmetatable(point, shape.mt)
		shape.all[point] = true
		if opts then
			point(opts)
		end
		return point
	end
	function shape.intersect(name, ...)
		local p = shape.point(name)
		for i = 1, select('#', ...) do
			local arg = select(i, ...)
			if type(arg) == 'table' and arg[shape.sym] then
				p.on(arg)
			else
				assert(i == select('#', ...))
				p(arg)
			end
		end
		return p
	end
	function shape.line(name, opts)
		local line = {
			[shape.sym] = true;
			name = name;
			x_coef = var(name .. ' x coef');
			y_coef = var(name .. ' y coef');
			const = var(name .. ' const');
		}
		ensure(expr.not_(expr.and_(expr.equal(line.x_coef, 0), expr.equal(line.y_coef, 0))))
		line[shape.Scontains] = function(x, y)
			return expr.equal(line.x_coef * x + line.y_coef * y, line.const)
		end
		function line.pos(x, y)
			return -line.y_coef * x + line.x_coef * y
		end
		setmetatable(line, shape.mt)
		shape.all[line] = true
		if opts then
			line(opts)
		end
		return line
	end
	function shape.line_segment(name, opts)
		local segment = {
			[shape.sym] = true;
			name = name;
			line = shape.line(name .. ' line');
		}
		segment.p1 = shape.intersect(name .. ' p1', segment.line)
		segment.p2 = shape.intersect(name .. ' p2', segment.line);
		ensure(expr.increasing(
			segment.line.pos(segment.p1.x, segment.p1.y),
			segment.line.pos(segment.p2.x, segment.p2.y)
		))
		segment.len = ((segment.p1.x - segment.p2.x)^2 + (segment.p1.y - segment.p2.y)^2)^0.5
		segment[shape.Scontains] = function(x, y) return expr.and_(
			segment.line[shape.Scontains](x, y),
			expr.increasing(
				segment.line.pos(segment.p1.x, segment.p1.y),
				segment.line.pos(x, y),
				segment.line.pos(segment.p2.x, segment.p2.y)
			)
		) end
		setmetatable(segment, shape.mt)
		shape.all[segment] = true
		if opts then
			segment(opts)
		end
		return segment
	end
	function shape.rect(name, opts)
		local rect = {
			[shape.sym] = true;
			name = name;
			top = shape.line_segment(name .. ' top');
			right = shape.line_segment(name .. ' right');
			bottom = shape.line_segment(name .. ' bottom');
			left = shape.line_segment(name .. ' left');
		}
		ensure(parallel(rect.top.line, rect.bottom.line))
		ensure(parallel(rect.left.line, rect.right.line))
		ensure(perpendicular(rect.top.line, rect.left.line))
		ensure(expr.equal(rect.top.p2.x, rect.right.p1.x))
		ensure(expr.equal(rect.top.p2.y, rect.right.p1.y))
		ensure(expr.equal(rect.right.p2.x, rect.bottom.p1.x))
		ensure(expr.equal(rect.right.p2.y, rect.bottom.p1.y))
		ensure(expr.equal(rect.bottom.p2.x, rect.left.p1.x))
		ensure(expr.equal(rect.bottom.p2.y, rect.left.p1.y))
		ensure(expr.equal(rect.left.p2.x, rect.top.p1.x))
		ensure(expr.equal(rect.left.p2.y, rect.top.p1.y))
		rect[shape.Scontains] = function(x, y) return expr.or_(
			rect.top[shape.Scontains](x, y),
			rect.right[shape.Scontains](x, y),
			rect.bottom[shape.Scontains](x, y),
			rect.left[shape.Scontains](x, y)
		) end
		setmetatable(rect, shape.mt)
		shape.all[rect] = true
		if opts then
			rect(opts)
		end
		return rect
	end

	local ground = shape.line 'ground' {
		x_coef = 0;
		y_coef = 1;
		const = 0;
	}

	local r = shape.rect 'r'
	ensure(parallel(ground, r.top.line))
end)
