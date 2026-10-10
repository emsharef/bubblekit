"""Claim 032: supplied Gaussian components, not estimated/certified budgets."""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp

spec=spec_from_file_location('paths027',Path(__file__).resolve().parents[1]/'027/budget.py')
paths=module_from_spec(spec)
spec.loader.exec_module(paths)


def component(durations, drifts, scales, nulls, trapped=False):
    nulls=tuple(nulls)
    if not nulls:
        raise ValueError('nonempty reference catalogue required')
    values=tuple(paths.component_budget(durations,drifts,scales,b,k) for b,k in nulls)
    return mp.mpf(0) if trapped else min(values)


def mixture(weights, components):
    return paths.mixture_budget(weights,components)
