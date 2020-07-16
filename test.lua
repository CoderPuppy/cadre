local pl = require 'pl.import_into' ()
local bit = require 'bit'

local function symbolify(name)
	return name:gsub('[^a-zA-Z0-9%-]', function(c)
		return '_' .. tostring(c:byte()) .. '_'
	end)
end
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
function expr.env()
	local env = {
		vars = {};
		ensures = {};
	}
	function env.var(label)
		local name = symbolify(label)
		local i = nil
		while env.vars[name .. (i and tostring(i) or '')] do
			i = (i or 0) + 1
		end
		name = name .. (i and tostring(i) or '')
		local var; var = {
			[expr.sym] = true;
			[expr.Scode] = name;
			[expr.Seval] = function() return var.val end;
			label = label;
			name = name;
		}
		env.vars[name] = var
		setmetatable(var, expr.mt)
		return var
	end
	function env.ensure(label, prop)
		assert(label)
		assert(prop)
		local name = symbolify(label)
		local i = nil
		while env.ensures[name .. (i and tostring(i) or '')] do
			i = (i or 0) + 1
		end
		name = name .. (i and tostring(i) or '')
		env.ensures[name] = {
			name = name;
			prop = expr.coerce(prop);
		}
	end
	function env.satisfy()
		-- local filename = os.tmpname()
		local filename = 'test.smt2'
		print(filename)
		local h = io.open(filename, 'w')
		h:write '(set-logic QF_LRA)\n'
		h:write '(set-option :produce-unsat-cores true)\n'
		for _, var in pairs(env.vars) do
			h:write(('(declare-fun %s () Real)\n'):format(var.name))
		end
		for _, e in pairs(env.ensures) do
			h:write(('(assert (! %s :named %s))\n'):format(
				e.prop[expr.Scode],
				symbolify(e.name)
			))
		end
		h:write '(check-sat)\n'
		for name, var in pairs(env.vars) do
			h:write(('(get-value (%s))\n'):format(name))
		end
		h:write '(get-unsat-core)\n'
		h:close()

		h = io.popen('z3 ' .. filename, 'r')
		local function got_var_val(line, name, val)
			print(name, val, line)
			env.vars[name].val = val
		end
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
					got_var_val(line, name, tonumber(val))
					break
				end

				local name, val = line:match '^%(%(([^ %(%)]+) %(%- (%d+%.?%d*)%)%)%)$'
				if name then
					got_var_val(line, name, -tonumber(val))
					break
				end

				local name, num, den = line:match '^%(%(([^ %(%)]+) %(/ (%d+%.?%d*) (%d+%.?%d*)%)%)%)$'
				if name then
					got_var_val(line, name, tonumber(num)/tonumber(den))
					break
				end

				local name, num, den = line:match '^%(%(([^ %(%)]+) %(%- %(/ (%d+%.?%d*) (%d+%.?%d*)%)%)%)%)$'
				if name then
					got_var_val(line, name, -tonumber(num)/tonumber(den))
					break
				end

				print(line)
				-- error(('todo: %q'):format(line))
			until true
		end
		h:close()
	end
	return env
end

local function make_dxf()
	local dxf = {
		next_handle = 0x30;
		styles = {};
		entities = {n = 0;};
	}
	function dxf.make_handle()
		local h = dxf.next_handle
		dxf.next_handle = dxf.next_handle + 1
		return h
	end
	function dxf.make_style(opts)
		local style = {
			handle = dxf.make_handle();
			name = assert(opts.name);
		}
		dxf.styles[style.name] = style
		return style
	end
	dxf.make_style {
		name = 'Standard';
	}
	function dxf.make_entity(opts)
		local entity = {
			handle = dxf.make_handle();
			type = assert(opts.type);
			fn = assert(opts.fn);
		}
		dxf.entities.n = dxf.entities.n + 1
		dxf.entities[dxf.entities.n] = entity
		return entity
	end
	function dxf.write(write)
		write('999\ncadre\n')

		do -- HEADER
			write('0\nSECTION\n')
			write('2\nHEADER\n')
			for k, v in pairs {
				['$ACADVAR'] = '1\nAC1015\n'; -- autocad version - autocad 2000
				['$HANDSEED'] = ('5\n%x\n'):format(dxf.next_handle); -- next available handle
				['$DIMADEC'] = '70\n0\n'; -- angle dimension precision
				['$DIMASZ'] = '40\n2.5\n'; -- dimension arrow size
				['$DIMAUNIT'] = '70\n0\n'; -- angle dimension unit - 0 = decimal degrees
				['$DIMAZIN'] = '70\n2\n'; -- angle dimension zero suppression - 2 = suppress trailing
				['$DIMDEC'] = '70\n4\n'; -- linear dimension precision
				['$DIMDLI'] = '70\n5\n'; -- dimension line increment NEEDS_RESEARCH
				['$DIMDSEP'] = '70\n46\n'; -- decimal separator - 46 = '.'
				['$DIMEXE'] = '40\n1.25\n'; -- extension line extension NEEDS_RESEARCH
				['$DIMEXO'] = '40\n0.625\n'; -- extension line offset NEEDS_RESEARCH
				['$DIMGAP'] = '40\n0.625\n'; -- dimension line gap NEEDS_RESEARCH
				['$DIMLUNIT'] = '70\n4\n'; -- linear dimension unit - 4 = architectural
				['$DIMSCALE'] = '40\n1.0\n'; -- dimension scale NEEDS_RESEARCH
				['$DIMTSZ'] = '40\n0.0\n'; -- dimension tick size - 0 = no ticks NEEDS_RESEARCH
				['$DIMTXT'] = '40\n2.5\n'; -- dimension text size - TODO: probably needs to adjust
				['$DIMZIN'] = '70\n8\n'; -- linear dimension zero suppression - 8 = NEEDS_RESEARCH
				['$DWGCODEPAGE'] = '3\nUTF-8\n'; -- encoding
				['$INSUNITS'] = '70\n1\n'; -- default unit for blocks - 1 = inches
				['$LTSCALE'] = '40\n1.0\n'; -- global linetype scale NEEDS_RESEARCH
				['$MAXACTVP'] = '70\n64\n'; -- maximum number of viewports to be regenerated NEEDS_RESEARCH
				['$MEASUREMENT'] = '70\n0\n'; -- drawing units - 0 = english
				['$PDMODE'] = '70\n0\n'; -- point display mode NEEDS_RESEARCH
				['$PDSIZE'] = '40\n0.0\n'; -- point display size NEEDS_RESEARCH
			} do
				write(('9\n%s\n%s'):format(k, v))
			end
			write('0\nENDSEC\n')
		end

		do -- TABLES
			write('0\nSECTION\n')
			write('2\nTABLES\n')
			do -- VPORT
				write('0\nTABLE\n')
				write('2\nVPORT\n')
				write('5\n8\n') -- handle
				write('330\n0\n') -- owner = none
				write('100\nAcDbSymbolTable\n')
				write('70\n1\n') -- number of viewports
				do
					write('0\nVPORT\n')
					write('5\n30\n') -- handle
					write('330\n8\n') -- owner = VPORT table
					write('100\nAcDbSymbolTableRecord\n')
					write('100\nAcDbViewportTableRecord\n')
					write('2\n*Active\n') -- name
					write('70\n0\n') -- flags
					write('10\n0.0\n') -- left x
					write('20\n0.0\n') -- lower y
					write('11\n1.0\n') -- right x
					write('21\n1.0\n') -- upper y
					write('12\n0.0\n') -- center x
					write('22\n0.0\n') -- center y
					write('13\n0.0\n') -- snap base x
					write('23\n0.0\n') -- snap base y
					write('14\n10.0\n') -- snap spacing x
					write('24\n10.0\n') -- snap spacing y
					write('15\n10.0\n') -- grid spacing x
					write('25\n10.0\n') -- grid spacing y
					write('16\n0.0\n') -- view direction (from target) x NEEDS_RESEARCH
					write('26\n0.0\n') -- view direction (from target) y NEEDS_RESEARCH
					write('36\n1.0\n') -- view direction (from target) z NEEDS_RESEARCH
					write('17\n0.0\n') -- view target x NEEDS_RESEARCH
					write('27\n0.0\n') -- view target y NEEDS_RESEARCH
					write('37\n0.0\n') -- view target z NEEDS_RESEARCH
					write('40\n297.0\n') -- view height TODO
					write('41\n1.9\n') -- view ratio TODO
					write('42\n50.0\n') -- lens length in mm
					write('43\n0.0\n') -- front clipping plane (relative to target point)
					write('44\n0.0\n') -- back clipping plane (relative to target point)
					write('50\n0.0\n') -- snap angle NEEDS_RESEARCH
					write('51\n0.0\n') -- view twist angle NEEDS_RESEARCH
					write('71\n0\n') -- view mode - see https://knowledge.autodesk.com/support/autocad/learn-explore/caas/CloudHelp/cloudhelp/2021/ENU/AutoCAD-Core/files/GUID-01F9D6D3-0A43-4BCB-AA5C-65459D4BBC78-htm.html?st=VIEWMODE
					write('72\n100\n') -- circle zoom percent NEEDS_RESEARCH
					write('73\n1\n') -- fast zoom NEEDS_RESEARCH
					write('74\n3\n') -- user coordinate system icon - 3 = on, display at origin - see https://knowledge.autodesk.com/support/autocad/learn-explore/caas/CloudHelp/cloudhelp/2019/ENU/AutoCAD-Core/files/GUID-BCC7DA63-7F74-4F61-8605-E36A010FD33A-htm.html
					write('75\n1\n') -- snap on/off - 1 = on
					write('76\n1\n') -- grid on/off - 1 = on
					write('77\n0\n') -- snap style NEEDS_RESEARCH
					write('78\n0\n') -- snap isopair NEEDS_RESEARCH
					write('281\n0\n') -- render mode - 0 = 2D optimized
					write('65\n1\n') -- UCSVP - 1 = UCS icon displays this viewport's UCS - see https://knowledge.autodesk.com/support/autocad/learn-explore/caas/CloudHelp/cloudhelp/2019/ENU/AutoCAD-Core/files/GUID-F71044DB-48DE-4D02-89E4-B1C2BC4C64A0-htm.html
					write('110\n0.0\n') -- UCS origin x
					write('120\n0.0\n') -- UCS origin y
					write('130\n0.0\n') -- UCS origin z
					write('111\n1.0\n') -- UCS x x
					write('121\n0.0\n') -- UCS x y
					write('131\n0.0\n') -- UCS x z
					write('112\n0.0\n') -- UCS y x
					write('122\n1.0\n') -- UCS y y
					write('132\n0.0\n') -- UCS y z
					write('79\n0\n') -- UCS orthographic type - 0 = not orthographic
					write('146\n0.0\n') -- elevation
					-- TODO: https://github.com/LibreCAD/libdxfrw/blob/0b08abc3198fb44d6f91744f467d47443703b52b/src/libdxfrw.cpp#L418
				end
				write('0\nENDTAB\n')
			end
			do -- LTYPE
				write('0\nTABLE\n')
				write('2\nLTYPE\n')
				write('5\n5\n')
				write('330\n0\n') -- owner = none
				write('100\nAcDbSymbolTable\n')
				write('70\n3\n') -- number of linetypes
				do
					write('0\nLTYPE\n')
					write('5\n14\n') -- handle
					write('330\n5\n') -- owner = LTYPE table
					write('100\nAcDbSymbolTableRecord\n')
					write('100\nAcDbLinetypeTableRecord\n')
					write('2\nByBlock\n') -- name
					write('70\n0\n') -- flags
					write('3\n\n') -- description
					write('72\n65\n') -- alignment code - 65 = 'A'
					write('73\n0\n') -- number of elements
					write('40\n0.0\n') -- length
				end
				do
					write('0\nLTYPE\n')
					write('5\n15\n') -- handle
					write('330\n5\n') -- owner = LTYPE table
					write('100\nAcDbSymbolTableRecord\n')
					write('100\nAcDbLinetypeTableRecord\n')
					write('2\nByLayer\n') -- name
					write('70\n0\n') -- flags
					write('3\n\n') -- description
					write('72\n65\n') -- alignment code - 65 = 'A'
					write('73\n0\n') -- number of elements
					write('40\n0.0\n') -- length
				end
				do
					write('0\nLTYPE\n')
					write('5\n16\n') -- handle TODO
					write('330\n5\n') -- owner = LTYPE table
					write('100\nAcDbSymbolTableRecord\n')
					write('100\nAcDbLinetypeTableRecord\n')
					write('2\nContinuous\n') -- name
					write('70\n0\n') -- flags
					write('3\nSolid line\n') -- description
					write('72\n65\n') -- alignment code - 65 = 'A'
					write('73\n0\n') -- number of elements
					write('40\n0.0\n') -- length
				end
				write('0\nENDTAB\n')
			end
			do -- LAYER
				write('0\nTABLE\n')
				write('2\nLAYER\n')
				write('5\n2\n')
				write('330\n0\n') -- owner = none
				write('100\nAcDbSymbolTable\n')
				write('70\n1\n') -- number of layers
				do
					write('0\nLAYER\n')
					write('5\n10\n') -- handle
					write('330\n2\n') -- owner = LAYER table
					write('100\nAcDbSymbolTableRecord\n')
					write('100\nAcDbLayerTableRecord\n')
					write('2\n0\n') -- name
					write('70\n0\n') -- flags
					write('62\n7\n') -- color NEEDS_RESEARCH
					-- TODO: 420 (24 bit color?)
					write('6\nContinuous\n') -- linetype
					write('370\n25\n') -- line width
					write('390\nF\n') -- PlotStyleName NEEDS_RESEARCH
				end
				write('0\nENDTAB\n')
			end
			do -- STYLE
				write('0\nTABLE\n')
				write('2\nSTYLE\n')
				write('5\n3\n') -- handle
				write('330\n0\n') -- owner = none
				write('100\nAcDbSymbolTable\n')
				write('70\n1\n') -- number of styles
				for _, style in pairs(dxf.styles) do
					write('0\nSTYLE\n')
					write(('5\n%x\n'):format(style.handle)) -- handle
					write('330\n3\n') -- owner = STYLE table
					write('100\nAcDbSymbolTableRecord\n')
					write('100\nAcDbTextStyleTableRecord\n')
					write(('2\n%s\n'):format(style.name)) -- name
					write('70\n0\n') -- flags
					write('40\n0.0\n') -- fixed text height NEEDS_RESEARCH
					write('41\n1.0\n') -- width factor NEEDS_RESEARCH
					write('50\n0.0\n') -- oblique angle NEEDS_RESEARCH
					write('71\n0\n') -- text generation flags
					write('42\n2.5\n') -- last height used NEEDS_RESEARCH
					write('3\n\n') -- font filename
					write('4\n\n') -- big font filename
					write('1071\n0\n') -- font family (italic, bold)
				end
				write('0\nENDTAB\n')
			end
			do -- VIEW
				write('0\nTABLE\n')
				write('2\nVIEW\n')
				write('5\n6\n') -- handle
				write('330\n0\n') -- owner = none
				write('100\nAcDbSymbolTable\n')
				write('70\n0\n') -- number of views
				write('0\nENDTAB\n')
			end
			do -- UCS
				write('0\nTABLE\n')
				write('2\nUCS\n')
				write('5\n7\n') -- handle
				write('330\n0\n') -- owner = none
				write('100\nAcDbSymbolTable\n')
				write('70\n0\n') -- number of UCSs
				write('0\nENDTAB\n')
			end
			do -- APPID
				write('0\nTABLE\n')
				write('2\nAPPID\n')
				write('5\n9\n') -- handle
				write('330\n0\n') -- owner = none
				write('100\nAcDbSymbolTable\n')
				write('70\n1\n') -- number of appids
				do
					write('0\nAPPID\n')
					write('5\n12\n') -- handle
					write('330\n9\n') -- owner = APPID table
					write('100\nAcDbSymbolTableRecord\n')
					write('100\nAcDbRegAppTableRecord\n')
					write('2\nACAD\n') -- name
					write('70\n0\n') -- flags
				end
				write('0\nENDTAB\n')
			end
			do -- DIMSTYLE
				write('0\nTABLE\n')
				write('2\nDIMSTYLE\n')
				write('5\nA\n') -- handle
				write('330\n0\n') -- owner = none
				write('100\nAcDbSymbolTable\n')
				write('70\n1\n') -- number of dimstyles
				write('100\nAcDbDimStyleTable\n')
				write('71\n1\n') -- NEEDS_RESEARCH
				do
					write('0\nDIMSTYLE\n')
					write('105\n27\n') -- handle
					write('330\nA\n') -- owner = DIMSTYLE table
					write('100\nAcDbSymbolTableRecord\n')
					write('100\nAcDbDimStyleTableRecord\n')
					write('2\nStandard\n') -- name
					write('41\n2.5\n') -- DIMASZ - arrow size
					write('42\n0.625\n') -- DIMEXO - extension offset
					write('43\n3.75\n') -- DIMDLI
					write('44\n1.25\n') -- DIMEXE - extension extension
					write('70\n0\n') -- flags? NEEDS_RESEARCH
					write('73\n0\n') -- DIMTIH - force horizontal text (inside) - 0 = no
					write('74\n0\n') -- DIMTOH - force horizontal text (outside) - 0 = no
					write('77\n1\n') -- DIMTAD - vertical position of text - 1 = above except when forced horizontal
					write('78\n8\n') -- DIMZIN - zero suppression - 8 = suppress trailing zeros
					write('140\n2.5\n') -- DIMTXT - text height
					write('141\n2.5\n') -- DIMCEN - relative location for center marks or lines for circles and arcs
					write('143\n0.03937007874016\n') -- DIMALTF - factor for converting to alternate unit
					write('147\n0.625\n') -- DIMGAP
					write('171\n3\n') -- DIMALTD - precision in alternate unit
					write('172\n1\n') -- DIMTOFL
					write('271\n2\n') -- DIMDEC - precision
					write('272\n2\n') -- DIMTDEC - precision for tolerances
					write('274\n3\n') -- DIMALTTD - precision for tolerances in alternate unit
					write('278\n46\n') -- DIMDSEP - decimal separator
					write('283\n0\n') -- DIMTOU - vertical justification for tolerances - 0 = bottom
					write('284\n8\n') -- DIMTZIN - zero suppression in tolerances - 8 = suppress trailing zeros
					write(('340\n%x\n'):format(dxf.styles.Standard.handle)) -- DIMTXSTY_HANDLE = Standard
				end
				write('0\nENDTAB\n')
			end
			do -- BLOCK_RECORD
				write('0\nTABLE\n')
				write('2\nBLOCK_RECORD\n')
				write('5\n1\n') -- handle
				write('330\n0\n') -- owner = none
				write('100\nAcDbSymbolTable\n')
				write('70\n2\n') -- number of block records
				do
					write('0\nBLOCK_RECORD\n')
					write('5\n1F\n') -- handle
					write('330\n1\n') -- owner = BLOCK_RECORD table
					write('100\nAcDbSymbolTableRecord\n')
					write('100\nAcDbBlockTableRecord\n')
					write('2\n*Model_Space\n') -- name
					write('340\n22\n') -- layout reference
				end
				do
					write('0\nBLOCK_RECORD\n')
					write('5\n1B\n') -- handle
					write('330\n1\n') -- owner = BLOCK_RECORD table
					write('100\nAcDbSymbolTableRecord\n')
					write('100\nAcDbBlockTableRecord\n')
					write('2\n*Paper_Space\n') -- name
					write('340\n1E\n') -- layout reference
				end
				write('0\nENDTAB\n')
			end
		end

		do -- BLOCKS
			write('0\nSECTION\n')
			write('2\nBLOCKS\n')
			do
				write('0\nBLOCK\n')
				write('5\n20\n') -- handle
				write('330\n1F\n') -- owner = *Model_Space BLOCK_RECORD
				write('100\nAcDbEntity\n')
				write('8\n0\n') -- layer
				write('100\nAcDbBlockBegin\n')
				write('2\n*Model_Space\n') -- name
				write('70\n0\n') -- flags
				write('10\n0.0\n') -- base point x
				write('20\n0.0\n') -- base point y
				write('30\n0.0\n') -- base point z
				write('3\n*Model_Space\n') -- name
				write('1\n\n') -- xref path name NEEDS_RESEARCH
				write('0\nENDBLK\n')
				write('5\n21\n') -- handle
				write('330\n1F\n') -- owner = *Model_Space BLOCK_RECORD
				write('100\nAcDbEntity\n')
				write('8\n0\n') -- layer
				write('100\nAcDbBlockEnd\n')
			end
			do
				write('0\nBLOCK\n')
				write('5\n1C\n') -- handle
				write('330\n1B\n') -- owner = *Paper_Space BLOCK_RECORD
				write('100\nAcDbEntity\n')
				write('8\n0\n') -- layer
				-- write('67\n1\n') -- TODO NEEDS_RESEARCH
				write('100\nAcDbBlockBegin\n')
				write('2\n*Paper_Space\n') -- name
				write('70\n0\n') -- flags
				write('10\n0.0\n') -- base point x
				write('20\n0.0\n') -- base point y
				write('30\n0.0\n') -- base point z
				write('3\n*Paper_Space\n') -- name
				write('1\n\n') -- xref path name NEEDS_RESEARCH
				write('0\nENDBLK\n')
				write('5\n1D\n') -- handle
				write('330\n1B\n') -- owner = *Paper_Space BLOCK_RECORD
				write('100\nAcDbEntity\n')
				write('8\n0\n') -- layer
				write('100\nAcDbBlockEnd\n')
			end
			write('0\nENDSEC\n')
		end

		do -- ENTITIES
			write('0\nSECTION\n')
			write('2\nENTITIES\n')
			for i = 1, dxf.entities.n do
				local entity = dxf.entities[i]
				write(('0\n%s\n'):format(entity.type))
				write(('5\n%x\n'):format(entity.handle)) -- handle
				write('100\nAcDbEntity\n')
				write('8\n0\n') -- layer
				write('62\n256\n') -- color - 256 = ByLayer
				write('370\n-1\n') -- lineweight - -1 = ByLayer
				write('48\n1.0\n') -- linetype scale
				write('6\nByLayer\n') -- linetype name
				entity.fn(write)
			end
			write('0\nENDSEC\n')
		end

		do -- OBJECTS
			write('0\nSECTION\n')
			write('2\nOBJECTS\n')
			do -- root
				write('0\nDICTIONARY\n')
				write('5\nC\n') -- handle
				write('330\n0\n') -- owner = none
				write('100\nAcDbDictionary\n')
				write('280\n0\n') -- hard own elements - 0 = no
				write('281\n1\n') -- duplicate handling - 1 = keep existing
				do
					write('3\nACAD_GROUP\n') -- entry name
					write('350\nD\n') -- entry value handle = ACAD_GROUP
				end
				do
					write('3\nACAD_LAYOUT\n') -- entry name
					write('350\n1a\n') -- entry value handle = ACAD_LAYOUT
				end
			end
			do -- ACAD_GROUP
				write('0\nDICTIONARY\n')
				write('5\nD\n') -- handle
				write('330\nC\n') -- owner = root
				write('100\nAcDbDictionary\n')
				write('280\n0\n') -- hard own elements - 0 = no
				write('281\n1\n') -- duplicate handling - 1 = keep existing
			end
			do -- ACAD_LAYOUT
				write('0\nDICTIONARY\n')
				write('5\nD\n') -- handle
				write('330\nC\n') -- owner = root
				write('100\nAcDbDictionary\n')
				write('280\n0\n') -- hard own elements - 0 = no
				write('281\n1\n') -- duplicate handling - 1 = keep existing
				do
					write('3\nModel\n') -- entry name
					write('350\n22\n') -- entry value handle = ACAD_LAYOUT.Model
				end
			end
			do -- ACAD_LAYOUT.Model
				write('0\nLAYOUT\n')
				write('5\n22\n') -- handle
				write('330\n1F\n') -- owner = *Model_Space BLOCK_RECORD
				do -- plot
					write('100\nAcDbPlotSetting\n')
					write('1\n\n') -- name
					write('2\nnone_device\n') -- printer name
					write('4\n\n') -- paper size
					write('6\n\n') -- plot view name
					write('40\n0.0\n') -- left margin in millimeters
					write('41\n0.0\n') -- bottom margin in millimeters
					write('42\n0.0\n') -- right margin in millimeters
					write('43\n0.0\n') -- top margin in millimeters
					write('44\n0.0\n') -- paper width in millimeters
					write('45\n0.0\n') -- paper height in millimeters
					write('46\n0.0\n') -- plot origin x in millimeters
					write('47\n0.0\n') -- plot origin y in millimeters
					write('48\n0.0\n') -- plot window left x
					write('49\n0.0\n') -- plot window bottom y
					write('140\n0.0\n') -- plot window right x
					write('141\n0.0\n') -- plot window top y
					write('142\n1.0\n') -- numerator of scale, paper units
					write('143\n1.0\n') -- denominator of scale, drawing units
					write('70\n1712\n') -- flags - 1024 = ModelType, 512 = DrawViewportsFirst, 128 = PrintLineweights, 32 = PlotPlotStyles, 16 = UseStandardScale - NEEDS_RESEARCH
					write('72\n0\n') -- paper units - 0 = inches
					write('73\n0\n') -- rotation - 0 = none
					write('74\n0\n') -- type - 0 = last screen display
					write('7\n\n') -- current style sheet
					write('75\n0\n') -- standard scale type - 0 = scaled to fit
					write('147\n1.0\n') -- standard scale value
					write('148\n0.0\n') -- image origin x
					write('149\n0.0\n') -- image origin y
				end
				write('100\nAcDbLayout\n')
				write('1\nModel\n') -- name
				write('70\n1\n') -- flags - 1 = PSLTSCALE is current
				write('71\n0\n') -- tab order
				write('10\n0.0\n') -- grid left x
				write('20\n0.0\n') -- grid bottom y
				write('11\n12.0\n') -- grid right x TODO
				write('21\n9.0\n') -- grid top y TODO
				write('12\n0.0\n') -- insertion base x
				write('22\n0.0\n') -- insertion base y
				write('32\n0.0\n') -- insertion base z
				write('14\n0.0\n') -- min extent x
				write('24\n0.0\n') -- min extent y
				write('34\n0.0\n') -- min extent z
				write('15\n0.0\n') -- max extent x
				write('25\n0.0\n') -- max extent y
				write('35\n0.0\n') -- max extent z
				write('146\n0.0\n') -- elevation NEEDS_RESEARCH
				write('13\n0.0\n') -- UCS origin x
				write('23\n0.0\n') -- UCS origin y
				write('33\n0.0\n') -- UCS origin z
				write('16\n1.0\n') -- UCS x x
				write('26\n0.0\n') -- UCS x y
				write('36\n0.0\n') -- UCS x z
				write('17\n0.0\n') -- UCS y x
				write('27\n1.0\n') -- UCS y y
				write('37\n0.0\n') -- UCS y z
				write('76\n0\n') -- orthographic type - 0 = not orthographic
			end
			do -- ACAD_LAYOUT.Layout1
				write('0\nLAYOUT\n')
				write('5\n1E\n') -- handle
				write('330\n1B\n') -- owner = *Model_Space BLOCK_RECORD
				do -- plot
					write('100\nAcDbPlotSetting\n')
					write('1\n\n') -- name
					write('2\nnone_device\n') -- printer name
					write('4\n\n') -- paper size
					write('6\n\n') -- plot view name
					write('40\n0.0\n') -- left margin in millimeters
					write('41\n0.0\n') -- bottom margin in millimeters
					write('42\n0.0\n') -- right margin in millimeters
					write('43\n0.0\n') -- top margin in millimeters
					write('44\n0.0\n') -- paper width in millimeters
					write('45\n0.0\n') -- paper height in millimeters
					write('46\n0.0\n') -- plot origin x in millimeters
					write('47\n0.0\n') -- plot origin y in millimeters
					write('48\n0.0\n') -- plot window left x
					write('49\n0.0\n') -- plot window bottom y
					write('140\n0.0\n') -- plot window right x
					write('141\n0.0\n') -- plot window top y
					write('142\n1.0\n') -- numerator of scale, paper units
					write('143\n1.0\n') -- denominator of scale, drawing units
					write('70\n688\n') -- flags - 512 = DrawViewportsFirst, 128 = PrintLineweights, 32 = PlotPlotStyles, 16 = UseStandardScale - NEEDS_RESEARCH
					write('72\n0\n') -- paper units - 0 = inches
					write('73\n0\n') -- rotation - 0 = none
					write('74\n5\n') -- type - 5 = layout information
					write('7\n\n') -- current style sheet
					write('75\n16\n') -- standard scale type - 16 = 1:1
					write('147\n1.0\n') -- standard scale value
					write('148\n0.0\n') -- image origin x
					write('149\n0.0\n') -- image origin y
				end
				write('100\nAcDbLayout\n')
				write('1\nLayout1\n') -- name
				write('70\n1\n') -- flags - 1 = PSLTSCALE is current
				write('71\n1\n') -- tab order
				write('10\n0.0\n') -- grid left x
				write('20\n0.0\n') -- grid bottom y
				write('11\n420.0\n') -- grid right x TODO
				write('21\n297.0\n') -- grid top y TODO
				write('12\n0.0\n') -- insertion base x
				write('22\n0.0\n') -- insertion base y
				write('32\n0.0\n') -- insertion base z
				write('14\n100000000000000000000.0\n') -- min extent x TODO
				write('24\n100000000000000000000.0\n') -- min extent y TODO
				write('34\n100000000000000000000.0\n') -- min extent z TODO
				write('15\n-100000000000000000000.0\n') -- max extent x TODO
				write('25\n-100000000000000000000.0\n') -- max extent y TODO
				write('35\n-100000000000000000000.0\n') -- max extent z TODO
				write('146\n0.0\n') -- elevation NEEDS_RESEARCH
				write('13\n0.0\n') -- UCS origin x
				write('23\n0.0\n') -- UCS origin y
				write('33\n0.0\n') -- UCS origin z
				write('16\n1.0\n') -- UCS x x
				write('26\n0.0\n') -- UCS x y
				write('36\n0.0\n') -- UCS x z
				write('17\n0.0\n') -- UCS y x
				write('27\n1.0\n') -- UCS y y
				write('37\n0.0\n') -- UCS y z
				write('76\n0\n') -- orthographic type - 0 = not orthographic
			end
			write('0\nENDSEC\n')
		end

		-- TODO: CLASSES

		write('0\nEOF\n')
	end
	return dxf
end

local env = expr.env()
local function parallel(...)
	local parts_c, parts_x, parts_y = {}, {}, {}
	local n = select('#', ...)
	for i = 1, n do
		local l = select(i, ...)
		local c = env.var('parallel ' .. l.name)
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
	local c = env.var('perpendicular')
	return expr.and_(
		expr.not_(expr.equal(c, 0)),
		expr.equal(a.x_coef, -c * b.y_coef),
		expr.equal(a.y_coef,  c * b.x_coef)
	)
end
local shape = {
	sym = {};
	Stype = {};
	Scontains = {};
	Sequal = {};
	Sdxf = {};
	all = {};
}
local function apply_opts(name, self, opts)
	if opts[shape.sym] then
		assert(self[shape.Stype] == opts[shape.Stype])
		env.ensure(('%s equal %s'):format(name, opts.name), self[shape.Sequal](opts))
		return self
	end
	for k, v in pairs(opts) do
		local prop = self[k]
		repeat
			if type(prop) == 'table' then
				if prop[shape.sym] then
					prop(v)
					break
				end

				if prop[expr.sym] then
					env.ensure(('%s opts %s'):format(name, k), expr.equal(prop, v))
					break
				end

				apply_opts(('%s opts %s'):format(name, k), prop, v)
				break
			end

			if type(prop) == 'function' then
				local res = prop(v)
				repeat
					if res == nil then
						break
					end
					if type(res) == 'table' then
						if res[expr.sym] then
							env.ensure(res)
							break
						end
					end
					error(('todo: res = %s'):format(res))
				until true
				break
			end

			error(('todo: %s (%s) = %s'):format(k, prop, v))
		until true
	end
	return self
end
shape.mt = {
	__call = function(self, opts)
		return apply_opts(self.name, self, opts)
	end;
}
function shape.make(s, opts)
	assert(s[shape.sym])
	assert(s[shape.Stype])
	assert(s[shape.Scontains])
	assert(s[shape.Sequal])
	assert(s[shape.Sdxf])
	setmetatable(s, shape.mt)
	shape.all[s] = true
	if opts then
		s(opts)
	end
	return s
end
function shape.point(name, opts)
	local point = {
		[shape.sym] = true;
		[shape.Stype] = 'point';
		name = name;
		x = env.var(name .. ' x');
		y = env.var(name .. ' y');
	}
	point[shape.Scontains] = function(x, y)
		return expr.equal(x, point.x) and expr.equal(y, point.y)
	end
	point[shape.Sequal] = function(other)
		return expr.and_(expr.equal(point.x, other.x), expr.equal(point.y, other.y))
	end
	point[shape.Sdxf] = function(dxf)
		return dxf.make_entity {
			type = 'POINT';
			fn = function(write)
				write('100\nAcDbPoint\n')
				write(('10\n%g\n'):format(expr.eval(point.x)))
				write(('20\n%g\n'):format(expr.eval(point.y)))
				write('30\n0\n')
			end;
		}
	end
	function point.on(s)
		return s[shape.Scontains](point.x, point.y)
	end
	shape.make(point, opts)
	return point
end
function shape.line(name, x_coef, y_coef, opts)
	local line = {
		[shape.sym] = true;
		[shape.Stype] = 'line';
		name = name;
		x_coef = x_coef;
		y_coef = y_coef;
		const = env.var(name .. ' const');
	}
	env.ensure(('%s real'):format(name), expr.not_(expr.and_(expr.equal(line.x_coef, 0), expr.equal(line.y_coef, 0))))
	line[shape.Scontains] = function(x, y)
		return expr.equal(line.x_coef * x + line.y_coef * y, line.const)
	end
	line[shape.Sequal] = function(other)
		local c = env.var('line equal: ' .. line.name .. ' =? ' .. other.name)
		return expr.and_(
			expr.not_(expr.equal(c, 0)),
			expr.equal(line.x_coef, c * other.x_coef),
			expr.equal(line.y_coef, c * other.y_coef),
			expr.equal(line.const, c * other.const)
		)
	end
	do
		local x = env.var(name .. ' base x')
		local y = env.var(name .. ' base y')
		env.ensure(('%s base point'):format(name), line[shape.Scontains](x, y))
		line[shape.Sdxf] = function(dxf)
			return dxf.make_entity {
				type = 'XLINE';
				fn = function(write)
					write('100\nAcDbXline\n')
					write(('10\n%g\n'):format(expr.eval(x)))
					write(('20\n%g\n'):format(expr.eval(y)))
					write('30\n0\n')
					write(('11\n%g\n'):format(expr.eval(-line.y_coef)))
					write(('21\n%g\n'):format(expr.eval(line.x_coef)))
					write('31\n0\n')
				end;
			}
		end
	end
	function line.pos(x, y)
		return -line.y_coef * x + line.x_coef * y
	end
	shape.make(line, opts)
	return line
end
local x_axis = shape.line('x axis', 0, 1) {
	const = 0;
}
local y_axis = shape.line('y axis', 1, 0) {
	const = 0;
}
function shape.line_segment(name, x_coef, y_coef, opts)
	local segment = {
		[shape.sym] = true;
		[shape.Stype] = 'line_segment';
		name = name;
		line = shape.line(name .. ' line', x_coef, y_coef);
	}
	segment.segments = { n = 1; segment; }
	segment.points = {
		n = 2;
		shape.point(name .. ' p1');
		shape.point(name .. ' p2');
	}
	env.ensure(('%s p1 on line'):format(name), segment.points[1].on(segment.line))
	env.ensure(('%s p2 on line'):format(name), segment.points[2].on(segment.line))
	env.ensure(('%s p1 < p2'):format(name), expr.increasing(
		segment.line.pos(segment.points[1].x, segment.points[1].y),
		segment.line.pos(segment.points[2].x, segment.points[2].y)
	))
	segment.len = (
		(segment.points[1].x - segment.points[2].x)^2 +
		(segment.points[1].y - segment.points[2].y)^2
	)^0.5
	segment[shape.Scontains] = function(x, y) return expr.and_(
		segment.line[shape.Scontains](x, y),
		expr.increasing(
			segment.line.pos(segment.points[1].x, segment.points[1].y),
			segment.line.pos(x, y),
			segment.line.pos(segment.points[2].x, segment.points[2].y)
		)
	) end
	segment[shape.Sequal] = function(other) return expr.and_(
		segment.points[1][shape.Sequal](other.points[1]),
		segment.points[2][shape.Sequal](other.points[2])
	) end
	segment[shape.Sdxf] = function(dxf)
		return dxf.make_entity {
			type = 'LINE';
			fn = function(write)
				write('100\nAcDbLine\n')
				write(('10\n%g\n'):format(expr.eval(segment.points[1].x)))
				write(('20\n%g\n'):format(expr.eval(segment.points[1].y)))
				write('30\n0\n')
				write(('11\n%g\n'):format(expr.eval(segment.points[2].x)))
				write(('21\n%g\n'):format(expr.eval(segment.points[2].y)))
				write('31\n0\n')
			end;
		}
	end
	function segment.point(t)
		return shape.point(('%s point %g'):format(name, t)) {
			x = segment.points[1].x * (1 - t) + segment.points[2].x * t;
			y = segment.points[1].y * (1 - t) + segment.points[2].y * t;
		}
	end
	function segment.ends_on(other)
		return expr.and_(
			segment.points[1].on(other),
			segment.points[2].on(other)
		)
	end
	shape.make(segment, opts)
	return segment
end
function shape.poly(name, n, closed, ...)
	local poly = {
		[shape.sym] = true;
		[shape.Stype] = 'poly';
		closed = closed;
		segments = { n = n - (closed and 0 or 1); };
		points = { n = n; };
	}
	for i = 1, n do
		poly.points[i] = shape.point(name .. ' p' .. tostring(i))
	end
	for i = 1, n - 1 do
		poly.segments[i] = shape.line_segment(name .. ' s' .. tostring(i), select(i * 2 - 1, ...), select(i * 2, ...), {
			points = {
				poly.points[i];
				poly.points[i + 1];
			};
		})
	end
	if closed then
		poly.segments[n] = shape.line_segment(name .. ' s' .. tostring(n), select(n * 2 - 1, ...), select(n * 2, ...), {
			points = {
				poly.points[n];
				poly.points[1];
			};
		})
	end
	poly[shape.Scontains] = function(x, y)
		local props = {}
		for i = 1, poly.segments.n do
			props[i] = poly.segments[i][shape.Scontains](x, y)
		end
		return expr.or_(table.unpack(props, 1, poly.segments.n))
	end
	poly[shape.Sequal] = function(other)
		local props = {
			n = poly.points.n + 2;
			expr.equal(poly.closed, other.closed);
			expr.equal(poly.points.n, other.points.n);
		}
		for i = 1, poly.points.n do
			props[i + 2] = poly.points[i][shape.Sequal](other.points[i])
		end
		return expr.and_(table.unpack(props, 1, props.n))
	end
	poly[shape.Sdxf] = function(dxf)
		return dxf.make_entity {
			type = 'LWPOLYLINE';
			fn = function(write)
				write('100\nAcDbPolyline\n')
				write('90\n4\n') -- number of vertices
				write(('70\n%d\n'):format(bit.bor( -- flags
					closed and 1 or 0, -- 1 = closed
					128 -- 128 = pattern continues through vertices
				)))
				for i = 1, poly.points.n do
					local point = poly.points[i]
					write(('10\n%g\n'):format(expr.eval(point.x))) -- vertex x
					write(('20\n%g\n'):format(expr.eval(point.y))) -- vertex y
				end
			end;
		}
	end
	shape.make(poly, nil) -- TODO: opts
	return poly
end
function shape.rect(name, opts)
	local rect = {
		[shape.sym] = true;
		[shape.Stype] = 'rect';
		name = name;
		poly = shape.poly(name .. ' poly', 4, true, 0, -1, -1, 0, 0, 1, 1, 0);
	}
	rect.top = rect.poly.segments[1]
	rect.right = rect.poly.segments[2]
	rect.bottom = rect.poly.segments[3]
	rect.left = rect.poly.segments[4]
	env.ensure(('%s top || bottom'):format(name), parallel(rect.top.line, rect.bottom.line))
	env.ensure(('%s left || right'):format(name), parallel(rect.left.line, rect.right.line))
	env.ensure(('%s top _|_ left'):format(name), perpendicular(rect.top.line, rect.left.line))
	rect.top_left = rect.poly.points[1]
	rect.top_right = rect.poly.points[2]
	rect.bottom_right = rect.poly.points[3]
	rect.bottom_left = rect.poly.points[4]
	rect[shape.Scontains] = rect.poly[shape.Scontains]
	rect[shape.Sequal] = function(other) return rect.poly[shape.Sequal](other.poly) end
	rect[shape.Sdxf] = rect.poly[shape.Sdxf]
	shape.make(rect, opts)
	return rect
end
function shape.arect(name, opts)
	local rect = shape.rect(name)
	env.ensure(('%s top horizontal'):format(name), expr.equal(rect.top_left.y, rect.top_right.y))
	env.ensure(('%s bottom horizontal'):format(name), expr.equal(rect.bottom_left.y, rect.bottom_right.y))
	env.ensure(('%s left vertical'):format(name), expr.equal(rect.top_left.x, rect.bottom_left.x))
	env.ensure(('%s right vertical'):format(name), expr.equal(rect.top_right.x, rect.bottom_right.x))
	rect.top.y = rect.top_left.y
	rect.bottom.y = rect.bottom_left.y
	rect.left.x = rect.top_left.x
	rect.right.x = rect.top_right.x
	rect.width = rect.right.x - rect.left.x
	rect.height = rect.top.y - rect.bottom.y
	env.ensure(('%s width > 0'):format(name), expr.strictly_decreasing(rect.width, 0))
	env.ensure(('%s height > 0'):format(name), expr.strictly_decreasing(rect.height, 0))
	if opts then
		rect(opts)
	end
	return rect
end

local dxf, d

if true then
	d = {
		beams = {};
		joists = {};
		ledgers = {};
	}
	d.house = shape.arect 'house' {
		top_left = { x = 0; y = 0; };
		width = 30 * 12;
		height = 30 * 12;
	}
	d.ledgers[1] = shape.arect 'ledger' {
		height = 1.5;
	}
	env.ensure('ledger 1 (bottom left) on house top', d.ledgers[1].bottom_left.on(d.house.top))
	env.ensure('ledger 1 (bottom right) on house top', d.ledgers[1].bottom_right.on(d.house.top))
	d.beams[1] = shape.arect 'beam 1' {
		height = 2 * 1.5;
	}
	local function make_joists(name, from, to, n, max_spacing)
		local joists = {n = n;}
		for i = 1, n do
			local j = shape.arect(('joist %s %d'):format(name, i)) {
				width = 1.5;
			}
			joists[i] = j
			env.ensure(('joist %s %d bot left on from top'):format(name, i), j.bottom_left.on(from.top))
			env.ensure(('joist %s %d bot right on from top'):format(name, i), j.bottom_right.on(from.top))
			env.ensure(('joist %s %d top left on to bottom'):format(name, i), j.top_left.on(to.bottom))
			env.ensure(('joist %s %d top right on to bottom'):format(name, i), j.top_right.on(to.bottom))
		end
		for i = 1, n - 1 do
			local l, r = joists[i], joists[i + 1]
			env.ensure(('joists %s %d and %d not overlap'):format(name, i, i + 1), expr.increasing(l.right.x, r.left.x))
			env.ensure(('joists %s %d and %d max spacing'):format(name, i, i + 1), expr.increasing(r.top.point(0.5).x - l.top.point(0.5).x, max_spacing))
		end
		return joists
	end
	d.joists[1] = make_joists('1', d.ledgers[1], d.beams[1], 1, 16)
	env.ensure('beam 1 dist from house', expr.equal(d.beams[1].top.y - d.house.top.y, 11 * 12 + 6))
	env.satisfy()
	-- print(pl.pretty.write(d))
end

if true then
	local h = io.open('test.dxf', 'w')
	dxf = make_dxf()
	if d then
		local function display(s)
			print(s.name, s[shape.Sdxf](dxf).handle)
		end
		-- display(x_axis)
		-- display(y_axis)
		display(d.house)
		display(d.ledgers[1])
		display(d.beams[1])
		for i = 1, d.joists[1].n do
			display(d.joists[1][i])
		end
	end
	dxf.write(function(s)
		h:write(s)
	end)
	h:close()
end
