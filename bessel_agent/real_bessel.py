"""Closed real J/Y/cross-product targets with explicitly scoped diagnostics.

Version 2 never promotes numerical or conditional algebraic evidence to a proof
of a theorem about Bessel Y. Version 1 keeps its existing Lean semantics.
"""
from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import json
import re
from typing import Any

from .core import InputError, NeedsConditions, _keys, _expr, _constant, _run_lean, _save_json, _sha, environment

VARIABLES = {'n', 'x', 'z', 'lambda', 's', 'w', 't'}
RELATIONS = {'gt': '>', 'ge': '>=', 'lt': '<', 'le': '<=', 'eq': '=', 'ne': '!='}
CROSS_DEFINITION = 'X_nm(s,t) = J_n(s)*Y_m(t) - Y_n(s)*J_m(t)'
TEMPLATE = Path(__file__).with_name('templates') / 'cross_product.lean'


def is_extended(data: Any) -> bool:
    return isinstance(data, dict) and type(data.get('schema_version')) is int and data['schema_version'] == 2


def _walk(node):
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from _walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from _walk(value)


def _convert(node):
    from .parser import _order
    op = node['op']
    if op in {'int', 'var'}:
        return node
    if op in {'add', 'sub', 'mul', 'div'}:
        return {'op': op, 'args': [_convert(a) for a in node['args']]}
    if op == 'neg':
        return {'op': op, 'arg': _convert(node['arg'])}
    if op in {'bessel_j', 'bessel_y'}:
        return {'op': op, 'order': _order(node['order']), 'arg': _convert(node['arg'])}
    if op == 'bessel_cross':
        return {'op': op, 'orders': [_order(a) for a in node['orders']], 'args': [_convert(a) for a in node['args']]}
    if op == 'power':
        exponent = _order(node['exponent'])
        if exponent['op'] == 'int' and 0 <= exponent['value'] <= 12:
            return {'op': 'pow', 'base': _convert(node['base']), 'exponent': exponent['value']}
    raise InputError('Real J/Y diagnostics support arithmetic, powers 0..12, and Bessel J/Y/X; derivatives, integrals and other powers need a separate supported profile.')


def _parts(raw):
    if isinstance(raw, list) and all(isinstance(item, str) for item in raw):
        raw = ','.join(raw)
    if not isinstance(raw, str) or not raw.strip():
        raise NeedsConditions('State the real domain, for example x > 0 or 0 < lambda < 1, z > 0.')
    if len(raw) > 8192:
        raise InputError('Conditions exceed the text length limit.')
    raw = raw.replace(r'\lambda', 'lambda').replace('λ', 'lambda').replace('、', ',').replace('，', ',')
    for old, new in [(r'\geq', '>='), (r'\leq', '<='), (r'\neq', '!='), (r'\ge', '>='), (r'\le', '<='), (r'\ne', '!='), ('≥', '>='), ('≤', '<='), ('≠', '!=')]:
        raw = raw.replace(old, new)
    raw = re.sub(r'\b(?:and|where|for)\b|かつ', ',', raw)
    raw = re.sub(r'\\(?:frac|dfrac|tfrac)\s*\{(-?[0-9]+)\}\s*\{([0-9]+)\}', r'\1/\2', raw)
    stack, start, parts = [], 0, []
    for i, char in enumerate(raw):
        if char in '({':
            stack.append(char)
        elif char in ')}':
            if not stack or stack.pop() != {')': '(', '}': '{'}[char]:
                raise InputError('Unbalanced condition parentheses.')
        elif char == ',' and not stack:
            parts.append(raw[start:i].strip())
            start = i + 1
    if stack:
        raise InputError('Unbalanced condition parentheses.')
    return [p for p in parts + [raw[start:].strip()] if p]


def parse_target(text, conditions):
    from .parser import _Parser
    lhs, rhs = _Parser(text, extended=True).equation()
    assumptions = []
    integer_stated = False
    for part in _parts(conditions):
        compact = re.sub(r'\s+', '', part)
        if compact in {'ninteger', 'ninZ', 'nは整数'}:
            integer_stated = True
            continue
        tokens = re.split(r'(>=|<=|!=|>|<|=)', part)
        if len(tokens) not in {3, 5}:
            raise NeedsConditions('State scalar comparisons or a Bessel expression equal/non-equal to zero.')
        for i in range(0, len(tokens)-2, 2):
            left, relation, right = (p.strip() for p in tokens[i:i+3])
            operator = next(key for key, value in RELATIONS.items() if value == relation)
            if left in VARIABLES or right in VARIABLES:
                if right in VARIABLES:
                    left, right = right, left
                    operator = {'gt': 'lt', 'ge': 'le', 'lt': 'gt', 'le': 'ge', 'eq': 'eq', 'ne': 'ne'}[operator]
                if not re.fullmatch(r'[+-]?[0-9]+(?:/[0-9]+)?', right):
                    raise NeedsConditions('Scalar comparisons require an exact rational constant.')
                try:
                    q = Fraction(right)
                except ZeroDivisionError as exc:
                    raise NeedsConditions('A condition constant has a zero denominator.') from exc
                atom = {'op': 'compare', 'variable': left, 'relation': operator,
                        'value': {'numerator': q.numerator, 'denominator': q.denominator}}
            else:
                if operator not in {'eq', 'ne'} or right != '0' or len(tokens) != 3:
                    raise NeedsConditions('Function-value conditions have the form expression = 0 or expression != 0.')
                parser = _Parser(left, extended=True)
                expr = parser.expression()
                if parser.peek() is not None:
                    raise InputError('Unexpected token in a function-value condition.')
                atom = {'op': 'expr_compare', 'lhs': _convert(expr), 'relation': operator, 'rhs': {'op': 'int', 'value': 0}}
            if atom not in assumptions:
                assumptions.append(atom)
    lhs, rhs = _convert(lhs), _convert(rhs)
    names = {n['name'] for n in _walk([lhs, rhs, assumptions]) if n.get('op') == 'var'}
    names |= {a['variable'] for a in assumptions if a['op'] == 'compare'}
    if 'n' in names and not integer_stated:
        raise NeedsConditions('State n integer for an integer-order variable.')
    target = {'schema_version': 2, 'variables': {name: 'int' if name == 'n' else 'real' for name in sorted(names)},
              'assumptions': assumptions, 'lhs': lhs, 'rhs': rhs}
    validate(target, require_proof=False)
    return target


def _validate_expr(node, variables, depth=0, budget=None, scalar=False):
    budget = [1200] if budget is None else budget
    budget[0] -= 1
    if depth > 24 or budget[0] < 0 or not isinstance(node, dict):
        raise InputError('Real expression exceeds the supported size or depth.')
    op = node.get('op')
    if not isinstance(op, str):
        raise InputError('Every real expression must have an op string.')
    child = lambda n, s=scalar: _validate_expr(n, variables, depth+1, budget, s)
    if op == 'int':
        _keys(node, {'op', 'value'})
        if type(node['value']) is not int or abs(node['value']) > 1000:
            raise InputError('Integer literals must be between -1000 and 1000.')
    elif op == 'var':
        _keys(node, {'op', 'name'})
        if not isinstance(node['name'], str) or node['name'] not in variables:
            raise InputError('Every variable must have an explicit real/integer declaration.')
    elif op == 'neg':
        _keys(node, {'op', 'arg'}); child(node['arg'])
    elif op in {'add', 'sub', 'mul', 'div'}:
        _keys(node, {'op', 'args'})
        if not isinstance(node['args'], list) or len(node['args']) != 2:
            raise InputError('Binary operations require two arguments.')
        for arg in node['args']:
            child(arg)
        if op == 'div' and _constant(node['args'][1]) == 0:
            raise NeedsConditions('A denominator is identically zero.')
    elif op == 'pow':
        _keys(node, {'op', 'base', 'exponent'})
        if type(node['exponent']) is not int or not 0 <= node['exponent'] <= 12:
            raise InputError('Real diagnostics support powers 0..12.')
        child(node['base'])
    elif op in {'bessel_j', 'bessel_y', 'bessel_cross'} and not scalar:
        cross = op == 'bessel_cross'
        _keys(node, {'op', 'orders', 'args'} if cross else {'op', 'order', 'arg'})
        orders, args = (node['orders'], node['args']) if cross else ([node['order']], [node['arg']])
        if not isinstance(orders, list) or not isinstance(args, list) or len(orders) != (2 if cross else 1) or len(args) != len(orders):
            raise InputError('Bessel operators require the documented number of orders and arguments.')
        for order in orders:
            if isinstance(order, dict) and order.get('op') == 'rational':
                from .core import _fixed_exponent
                _fixed_exponent(order)
            else:
                _expr(order, 'int')
            if any(n.get('op') == 'var' and n.get('name') not in variables for n in _walk(order)):
                raise InputError('Declare the integer order variable n.')
        for arg in args:
            child(arg, True)
    else:
        raise InputError(f'Unsupported real diagnostic operation {op!r}.')


def domains(data):
    result = {name: [None, None, set()] for name in data['variables']}
    for atom in data['assumptions']:
        if atom['op'] != 'compare':
            continue
        domain = result[atom['variable']]
        q = Fraction(atom['value']['numerator'], atom['value']['denominator'])
        relation = atom['relation']
        if relation == 'ne':
            domain[2].add(q)
        if relation in {'gt', 'ge', 'eq'}:
            edge = q, relation == 'gt'
            if domain[0] is None or edge > domain[0]:
                domain[0] = edge
        if relation in {'lt', 'le', 'eq'}:
            edge = q, relation == 'lt'
            if domain[1] is None or (q, not edge[1]) < (domain[1][0], not domain[1][1]):
                domain[1] = edge
    for name, (lo, hi, excluded) in result.items():
        if data['variables'][name] == 'int':
            if lo:
                lo = (Fraction(lo[0].numerator//lo[0].denominator+1) if lo[1] else Fraction(-(-lo[0].numerator//lo[0].denominator)), False)
            if hi:
                hi = (Fraction(-(-hi[0].numerator//hi[0].denominator)-1) if hi[1] else Fraction(hi[0].numerator//hi[0].denominator), False)
            if lo:
                while lo[0] in excluded: lo = lo[0]+1, False
            if hi:
                while hi[0] in excluded: hi = hi[0]-1, False
            result[name] = [lo, hi, excluded]
        if lo and hi and (lo[0] > hi[0] or (lo[0] == hi[0] and (lo[1] or hi[1] or lo[0] in excluded))):
            raise NeedsConditions(f'Contradictory scalar conditions for {name}.')
    return result


def validate(data, require_proof=True):
    _keys(data, {'schema_version', 'variables', 'assumptions', 'lhs', 'rhs'} | ({'proof'} if require_proof else set()), set() if require_proof else {'proof'})
    if not is_extended(data) or not isinstance(data['variables'], dict) or not 1 <= len(data['variables']) <= 4:
        raise InputError('Version 2 requires one to four typed variables.')
    variables = data['variables']
    if any(name not in VARIABLES or kind != ('int' if name == 'n' else 'real') for name, kind in variables.items()):
        raise InputError('Real variables: x, z, lambda, s, w, t; integer-order variable: n.')
    if sum(kind == 'real' for kind in variables.values()) > 3:
        raise InputError('At most three real variables are supported in a diagnostic target.')
    for side in ['lhs', 'rhs']:
        _validate_expr(data[side], variables)
    assumptions = data['assumptions']
    if not isinstance(assumptions, list) or not 1 <= len(assumptions) <= 12:
        raise NeedsConditions('State one to twelve explicit domain/root conditions.')
    seen = set()
    for atom in assumptions:
        if isinstance(atom, dict) and atom.get('op') == 'compare':
            _keys(atom, {'op', 'variable', 'relation', 'value'})
            if not isinstance(atom['variable'], str) or atom['variable'] not in variables or not isinstance(atom['relation'], str) or atom['relation'] not in RELATIONS:
                raise InputError('A comparison needs a declared variable and supported relation.')
            _keys(atom['value'], {'numerator', 'denominator'})
            p, q = atom['value']['numerator'], atom['value']['denominator']
            if type(p) is not int or type(q) is not int or abs(p) > 1000 or not 1 <= q <= 1000 or Fraction(p, q).denominator != q:
                raise InputError('Condition constants must be reduced exact rationals bounded by 1000.')
        else:
            _keys(atom, {'op', 'lhs', 'relation', 'rhs'})
            if atom['op'] != 'expr_compare' or atom['relation'] not in ['eq', 'ne'] or atom['rhs'] != {'op': 'int', 'value': 0}:
                raise InputError('Function conditions compare an expression to zero with = or !=.')
            _validate_expr(atom['lhs'], variables)
            if atom['relation'] == 'eq' and ((atom['lhs'] == data['lhs'] and atom['rhs'] == data['rhs']) or (atom['lhs'] == data['rhs'] and atom['rhs'] == data['lhs'])):
                raise NeedsConditions('The target equality is itself an assumption; choose an independent target.')
        key = json.dumps(atom, sort_keys=True)
        if key in seen:
            raise InputError('Conditions must be distinct.')
        seen.add(key)
    for atom in assumptions:
        if atom['op'] == 'expr_compare' and {**atom, 'relation': 'ne' if atom['relation'] == 'eq' else 'eq'} in assumptions:
            raise NeedsConditions('A function expression cannot be both zero and nonzero.')
    domains(data)
    if 'proof' in data and data['proof'] != {'mode': 'diagnostic'}:
        raise InputError('Version 2 uses proof mode diagnostic; direct/steps recipes apply to version 1.')
    return data


def display(node):
    op = node['op']
    if op == 'int': return str(node['value'])
    if op == 'var': return node['name']
    if op == 'rational': return str(Fraction(node['numerator'], node['denominator']))
    if op == 'neg': return f'(-{display(node["arg"])})'
    if op in {'add', 'sub', 'mul', 'div'}:
        return '(' + display(node['args'][0]) + {'add': '+', 'sub': '-', 'mul': '*', 'div': '/'}[op] + display(node['args'][1]) + ')'
    if op == 'pow': return f'({display(node["base"])}^{node["exponent"]})'
    if op in {'bessel_j', 'bessel_y'}:
        return f'{"J" if op == "bessel_j" else "Y"}_{{{display(node["order"])}}}({display(node["arg"])})'
    if op == 'bessel_cross':
        return f'X_{{{display(node["orders"][0])},{display(node["orders"][1])}}}({display(node["args"][0])},{display(node["args"][1])})'
    raise InputError('Cannot display an unknown real expression.')


def labels(data):
    result = [f'{name} is {kind}' for name, kind in sorted(data['variables'].items())]
    for a in data['assumptions']:
        if a['op'] == 'compare':
            result.append(f'{a["variable"]} {RELATIONS[a["relation"]]} {Fraction(a["value"]["numerator"], a["value"]["denominator"])}')
        else:
            result.append(f'{display(a["lhs"])} {RELATIONS[a["relation"]]} 0')
    return result


def _positive(node, bounds):
    value = _constant(node)
    if value is not None: return value > 0
    if node['op'] == 'var':
        lo = bounds[node['name']][0]
        return lo is not None and (lo[0] > 0 or (lo[0] == 0 and lo[1]))
    if node['op'] in {'add', 'mul', 'div'}: return all(_positive(n, bounds) for n in node['args'])
    if node['op'] == 'pow': return node['exponent'] == 0 or _positive(node['base'], bounds)
    return False


def template_match(data):
    """Match the documented root identity without changing the fixed target."""
    from .parser import _Parser
    bounds = domains(data)
    for variable in ['z', 'x']:
        if set(data['variables']) != {'lambda', variable}:
            continue
        lo, hi, _ = bounds['lambda']
        vlo = bounds[variable][0]
        if not (lo and (lo[0] > 0 or lo == (0, True)) and hi and (hi[0] < 1 or hi == (1, True)) and vlo and (vlo[0] > 0 or vlo == (0, True))):
            continue
        A = f'X_00({variable},lambda*{variable})'
        B = f'X_11({variable},lambda*{variable})'
        C = f'X_02({variable},lambda*{variable})'
        Q = f'X_01({variable},{variable})'
        left = f'{A}^2/({Q}^2+lambda^2*{A}*{C})'
        root = _convert(_Parser(f'X_01({variable},lambda*{variable})', extended=True).expression())
        if {'op': 'expr_compare', 'lhs': root, 'relation': 'eq', 'rhs': {'op': 'int', 'value': 0}} not in data['assumptions']:
            continue
        for right in [f'(1/lambda)*{A}/({B}-lambda*{A})', f'(1/lambda)*({A}/({B}-lambda*{A}))']:
            lhs, rhs = map(_convert, _Parser(left+'='+right, extended=True).equation())
            if (data['lhs'], data['rhs']) in [(lhs, rhs), (rhs, lhs)]:
                return {'id': 'cross_product_root_fraction', 'root_variable': variable,
                        'substitutions': {'lam': 'lambda', 'A': A, 'B': B, 'C': C, 'Q': Q},
                        'assumptions': ['0 < lam', 'Q != 0', 'C = -A', 'lam*A*B = Q^2', '0 < Q^2-lam^2*A^2'],
                        'steps': ['次数2の漸化式と根条件より C=-A。', f'交差積の行列式とWronskianより lam*A*B=Q^2、Q=-2/(pi*{variable})。',
                                  f'u(t)=X_00({variable},t) のBessel方程式を積分すると Q^2-lam^2*A^2=(2/{variable}^2)*integral(lam*{variable},{variable},t*u(t)^2) > 0。',
                                  '分母を lam*A*(B-lam*A) に因数分解し、非零性を用いて約分する。'],
                        'sources': ['https://dlmf.nist.gov/10.6.E1', 'https://dlmf.nist.gov/10.6.E10', 'https://dlmf.nist.gov/10.5.E2', 'https://dlmf.nist.gov/10.2.E1'],
                        'formal_obligations': ['Bessel Y and X definitions', 'root recurrence', 'Wronskian scaling', 'positive energy integral']}
    return None


def domain_obligations(data, template):
    bounds = domains(data)
    explicit = [a['lhs'] for a in data['assumptions'] if a['op'] == 'expr_compare' and a['relation'] == 'ne']
    pending = []
    derived_denominators = [n['args'][1] for n in _walk([data['lhs'], data['rhs']]) if n.get('op') == 'div'] if template else []
    def nonzero(n):
        value = _constant(n)
        if value is not None: return value != 0
        if n in explicit or _positive(n, bounds): return True
        if n['op'] == 'var': return 0 in bounds[n['name']][2]
        if n['op'] == 'neg': return nonzero(n['arg'])
        if n['op'] in {'mul', 'div'}: return all(nonzero(a) for a in n['args'])
        if n['op'] == 'pow': return n['exponent'] == 0 or nonzero(n['base'])
        return False
    for node in _walk([data['lhs'], data['rhs'], data['assumptions']]):
        if node.get('op') in {'bessel_j', 'bessel_y', 'bessel_cross'}:
            for arg in node['args'] if node['op'] == 'bessel_cross' else [node['arg']]:
                if not _positive(arg, bounds):
                    pending.append(display(arg)+' > 0')
        if node.get('op') == 'div' and not nonzero(node['args'][1]) and node['args'][1] not in derived_denominators:
            pending.append(display(node['args'][1])+' != 0')
    # The exact template supplies an analytic proof of its two denominators.
    return sorted(set(pending))


def conditional_source():
    return TEMPLATE.read_text(encoding='utf-8')


def verify_diagnostic(data, output_dir, timeout):
    from .real_numeric import diagnose
    template = template_match(data)
    pending = domain_obligations(data, template)
    numeric = diagnose(data)
    conditional = {'accepted': False, 'reason': 'no_matching_analytic_template'}
    if template:
        source = conditional_source()
        path = output_dir / 'conditional_certificate.lean'
        path.write_text(source, encoding='utf-8')
        conditional = {**_run_lean(path, timeout), 'scope': 'algebra_under_explicit_bessel_hypotheses',
                       'assumptions': template['assumptions'], 'sha256': _sha(source.encode())}
    result = {'status': 'needs_conditions' if pending else 'unresolved',
              'reason': 'domain_conditions_required' if pending else 'bessel_y_formalization_pending',
              'statement': display(data['lhs'])+' = '+display(data['rhs']), 'conditions': labels(data),
              'definitions': {'bessel_cross': CROSS_DEFINITION}, 'environment': environment(),
              'full_bessel_proof': False, 'pending_domain_conditions': pending,
              'analysis': template, 'conditional_lean': conditional, 'numerical': numeric,
              'request_sha256': _sha((output_dir/'request.json').read_bytes())}
    _save_json(output_dir/'analysis.json', template or {'status': 'no_matching_template'})
    _save_json(output_dir/'numerical.json', numeric)
    _save_json(output_dir/'result.json', result)
    lines = ['# 正実数のBessel診断', '', result['statement'], '', '条件：'+'、'.join(labels(data)), '',
             '状態：'+result['status']+'。Bessel Yの形式的定義と解析公式への接続が残っています。', '',
             '数値診断：'+numeric['diagnostic']+'。有限標本の結果を numerical.json に保存しました。']
    if template:
        lines += ['', '## 解析テンプレート', *template['steps'], '', '## 条件付きLean',
                  '代数検査：'+str(conditional['accepted'])+'。仮定：'+'、'.join(template['assumptions']),
                  '残る形式化：'+'、'.join(template['formal_obligations'])]
    if pending:
        lines += ['', '確認する定義域条件：'+'、'.join(pending)]
    (output_dir/'report.md').write_text('\n'.join(lines)+'\n', encoding='utf-8')
    return result


def replay_diagnostic(data, result, output_dir, timeout):
    if result.get('status') not in {'unresolved', 'needs_conditions'} or result.get('full_bessel_proof') is not False:
        raise InputError('A version 2 diagnostic cannot carry proved/refuted status.')
    if result.get('request_sha256') != _sha((output_dir/'request.json').read_bytes()) or result.get('environment') != environment():
        raise InputError('The saved target or mathematical environment changed.')
    template = template_match(data)
    if not template or result.get('analysis') != template:
        raise InputError('This target has no matching conditional certificate.')
    source = conditional_source()
    path = output_dir/'conditional_certificate.lean'
    if path.read_text(encoding='utf-8') != source or result.get('conditional_lean', {}).get('sha256') != _sha(source.encode()):
        raise InputError('The conditional certificate differs from the fixed template.')
    checked = _run_lean(path, timeout)
    return {'status': result['status'], 'replayed': False, 'conditional_replayed': checked['accepted'],
            'full_bessel_proof': False, 'verification': checked}
