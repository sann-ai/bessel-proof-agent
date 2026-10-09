"""Bounded numerical diagnostics using an already available mpmath runtime."""
from __future__ import annotations

from fractions import Fraction
import importlib
from itertools import product
import time

from .core import InputError
from .real_bessel import _walk, domains, validate


def _scalar_holds(atom, values):
    actual = values[atom['variable']]
    q = Fraction(atom['value']['numerator'], atom['value']['denominator'])
    return {'gt': actual > q, 'ge': actual >= q, 'lt': actual < q, 'le': actual <= q,
            'eq': actual == q, 'ne': actual != q}[atom['relation']]


def diagnose(data):
    validate(data, require_proof=False)
    report = {'status': 'unresolved', 'diagnostic': 'backend_unavailable', 'backend': 'mpmath',
              'full_bessel_proof': False, 'precision_digits': 60, 'checked_samples': 0,
              'samples': [], 'candidates': [], 'skipped_reasons': [], 'excluded_by_conditions': 0,
              'root_search': {'method': 'bounded_sign_changes_then_secant', 'interval_cap': 60,
                              'grid_step': '0.5', 'roots_per_parameter_sample': 3,
                              'exhaustive': False},
              'max_samples': 27, 'rigorous_interval_enclosures': False,
              'max_root_grid_points': 720, 'time_limit_seconds': 30,
              'comparison_relative_tolerance': '1e-30', 'root_residual_tolerance': '1e-35',
              'explanation': '明示条件内の有限標本を計算します。根は符号変化から精密化し、根条件と全追加条件を再確認します。数値一致と差の候補を保存し、元命題の形式的な証明状態は未解決です。'}
    try:
        mp = importlib.import_module('mpmath')
    except ImportError:
        report['skipped_reasons'] = ['mpmath is not available in this Python environment; no package was installed.']
        return report
    report['backend_version'] = mp.__version__
    roots = [a for a in data['assumptions'] if a['op'] == 'expr_compare' and a['relation'] == 'eq']
    if len(roots) > 1:
        report.update(diagnostic='unsupported_root_system', skipped_reasons=['Automatic sampling supports one function-value root equation.'])
        return report
    bounds = domains(data)
    names = sorted(data['variables'])
    root_name = None
    if roots:
        root_vars = {n['name'] for n in _walk(roots[0]['lhs']) if n.get('op') == 'var' and data['variables'][n['name']] == 'real'}
        root_name = next((n for n in ['z', 'x'] if n in root_vars), None)
        if root_name is None and len(root_vars) == 1:
            root_name = next(iter(root_vars))
        if root_name is None:
            report.update(diagnostic='unsupported_root_binding', skipped_reasons=['Name the root variable z or x, or use one real root variable.'])
            return report
    report['root_search']['variable'] = root_name
    scalar = [a for a in data['assumptions'] if a['op'] == 'compare']
    def eligible(name, value):
        return all(_scalar_holds(a, {name: value}) for a in scalar if a['variable'] == name)
    def values_for(name):
        lo, hi, _ = bounds[name]
        values = [Fraction(-1), Fraction(0), Fraction(1)] if name == 'n' else [Fraction(1,5), Fraction(1,2), Fraction(4,5)] if name == 'lambda' else [Fraction(1,2), Fraction(1), Fraction(2)]
        if lo and hi:
            values += [(lo[0]+hi[0])/2]
        elif lo:
            values += [lo[0]+1]
        elif hi:
            values += [hi[0]-1]
        if data['variables'][name] == 'int':
            values = [Fraction(int(v)) for v in values]
        return list(dict.fromkeys(v for v in values if eligible(name, v)))[:3]
    skipped = set()
    deadline = time.monotonic() + report['time_limit_seconds']
    grid_remaining = [report['max_root_grid_points']]
    def evaluate(node, values, budget):
        if time.monotonic() > deadline:
            raise ValueError('Numerical diagnostic time limit reached.')
        budget[0] -= 1
        if budget[0] < 0: raise ValueError('Expression evaluation budget exceeded.')
        op = node['op']
        ev = lambda n: evaluate(n, values, budget)
        if op == 'int': return mp.mpf(node['value'])
        if op == 'var': return values[node['name']]
        if op == 'rational': return mp.mpf(node['numerator'])/node['denominator']
        if op == 'neg': return -ev(node['arg'])
        if op == 'pow': return ev(node['base'])**node['exponent']
        if op in {'add', 'sub', 'mul', 'div'}:
            a,b = map(ev,node['args'])
            if op == 'div' and abs(b) < mp.mpf('1e-40'): raise ValueError('Sample denominator is zero or below the diagnostic threshold.')
            return {'add': lambda:a+b,'sub':lambda:a-b,'mul':lambda:a*b,'div':lambda:a/b}[op]()
        if op in {'bessel_j', 'bessel_y', 'bessel_cross'}:
            def bessel(family, order, arg):
                if abs(order)>20 or not 0<arg<=60: raise ValueError('Numerical Bessel scope: |order| <= 20 and 0 < argument <= 60.')
                return (mp.besselj if family=='j' else mp.bessely)(order,arg)
            if op != 'bessel_cross': return bessel('j' if op=='bessel_j' else 'y',ev(node['order']),ev(node['arg']))
            n,m = map(ev,node['orders']); s,t = map(ev,node['args'])
            return bessel('j',n,s)*bessel('y',m,t)-bessel('y',n,s)*bessel('j',m,t)
        raise ValueError('Unsupported numerical expression.')
    def ev(node, values): return evaluate(node, values, [10000])
    def mvalue(q): return mp.mpf(q.numerator)/q.denominator
    def locate(values):
        lo,hi,_ = bounds[root_name]
        lower = max(mp.mpf('0.000001'),mvalue(lo[0]) if lo else mp.mpf('0.000001'))
        upper = min(mp.mpf(60),mvalue(hi[0]) if hi else mp.mpf(60))
        if lower>=upper: return []
        found=[]
        fn=lambda v:ev(roots[0]['lhs'],{**values,root_name:v})
        a=lower
        try:
            with mp.workdps(20): fa=fn(a)
        except (ValueError, ArithmeticError) as exc:
            skipped.add(str(exc)); fa=None
        while a<upper and len(found)<3 and grid_remaining[0] > 0 and time.monotonic() <= deadline:
            grid_remaining[0] -= 1
            b=min(a+mp.mpf('0.5'),upper)
            try:
                with mp.workdps(20): fb=fn(b)
                if fa is not None and mp.isfinite(fa) and mp.isfinite(fb) and fa*fb<=0:
                    r=mp.findroot(fn,(a,b),tol=mp.mpf('1e-45'),maxsteps=50)
                    if mp.isfinite(r) and a<=r<=b and abs(fn(r))<mp.mpf('1e-35') and all(abs(r-old)>mp.mpf('1e-20') for old in found):
                        found.append(r)
                fa=fb
            except (ValueError, ArithmeticError) as exc:
                skipped.add(str(exc)[:200]); fa=None
            a=b
        return found
    with mp.workdps(60):
        params=[name for name in names if name!=root_name]
        grids=[values_for(name) for name in params]
        for values_tuple in product(*grids):
            if time.monotonic() > deadline:
                skipped.add('Numerical diagnostic time limit reached.')
                break
            exact=dict(zip(params,values_tuple))
            values={name:mvalue(value) for name,value in exact.items()}
            root_values=locate(values) if root_name else [None]
            if root_name and not root_values: skipped.add('No root found in the bounded sign-change search for a parameter sample.')
            for root in root_values:
                if report['checked_samples']>=report['max_samples']: break
                at={**values,root_name:root} if root_name else values
                try:
                    # Scalar bounds are compared exactly for parameters; roots
                    # retain their high precision approximation for comparisons.
                    scalar_values = {**exact, root_name: Fraction(str(root))} if root_name else exact
                    if any(not _scalar_holds(a, scalar_values) for a in scalar):
                        report['excluded_by_conditions']+=1; continue
                    residuals=[]
                    accepted=True
                    for condition in data['assumptions']:
                        if condition['op']!='expr_compare': continue
                        value=ev(condition['lhs'],at)
                        if not mp.isfinite(value): raise ValueError('A condition evaluated to a nonfinite value.')
                        residuals.append({'condition': condition, 'absolute_value':mp.nstr(abs(value),48)})
                        if condition['relation']=='eq' and abs(value)>mp.mpf('1e-35'): accepted=False
                        if condition['relation']=='ne' and abs(value)<mp.mpf('1e-35'): accepted=False
                    if not accepted: report['excluded_by_conditions']+=1; continue
                    lhs,rhs=ev(data['lhs'],at),ev(data['rhs'],at)
                    if not mp.isfinite(lhs) or not mp.isfinite(rhs): raise ValueError('A target evaluated to a nonfinite value.')
                    error=abs(lhs-rhs); tolerance=mp.mpf('1e-30')*max(1,abs(lhs),abs(rhs))
                    sample={'values':{name:mp.nstr(value,48) for name,value in at.items()},
                            'lhs':mp.nstr(lhs,48),'rhs':mp.nstr(rhs,48),'absolute_difference':mp.nstr(error,48),
                            'comparison_tolerance':mp.nstr(tolerance,48),'condition_residuals':residuals}
                    report['samples'].append(sample); report['checked_samples']+=1
                    if error>tolerance: report['candidates'].append(sample)
                except (ValueError,ArithmeticError) as exc:
                    skipped.add(str(exc)[:200])
            if report['checked_samples']>=report['max_samples']: break
    report['skipped_reasons']=sorted(skipped)
    if grid_remaining[0] == 0:
        report['skipped_reasons'].append('Root grid evaluation limit reached.')
    if time.monotonic() > deadline and 'Numerical diagnostic time limit reached.' not in report['skipped_reasons']:
        report['skipped_reasons'].append('Numerical diagnostic time limit reached.')
    report['diagnostic']='counterexample_candidates' if report['candidates'] else 'no_mismatch_found' if report['checked_samples'] else 'no_eligible_samples'
    return report
