"""Fixed diagnostics for the local-lognormal predictable forecast; no simulation."""
from fractions import Fraction as F
import importlib.util
from pathlib import Path
import sys

from mpmath import mp
from forecast import Candidate, evaluate, row_interval

mp.dps = 80


def real(x):
    return mp.mpf(x.numerator)/x.denominator


def integral(candidate, t, source, label, start, tick):
    variance = candidate.scale**2*(source/start)**int(2*candidate.power-2)*candidate.clock[t]
    mean, sd = mp.log(real(source))-real(variance)/2, mp.sqrt(real(variance))
    lo, hi = tick*max(F(0),label-F(1,2)), tick*(label+F(1,2))
    a = -mp.inf if lo == 0 else (mp.log(real(lo))-mean)/sd
    b = (mp.log(real(hi))-mean)/sd
    cuts = sorted({a,b,*[mp.mpf(v) for v in (-12,-6,0,6,12) if a < v < b]})
    return mp.quad(lambda z: mp.exp(-z*z/2)/mp.sqrt(2*mp.pi), cuts)


def main():
    count = 0
    for power in (F(1), F(3,2), F(2)):
        for scale in (F(7,10), F(3)):
            c = Candidate(power,scale,(F(1,5),))
            for label in (0,2,5,8):
                ref = integral(c,0,F(6,5),label,F(1),F(1,5))
                for bits in (48,128):
                    low,high = row_interval(c,0,F(6,5),label,F(1),F(1,5),bits)
                    assert real(low) <= ref <= real(high), (power,scale,label,bits,ref)
                    count += 1
    # A complete finite partition plus its unbounded tail; no truncation renormalization.
    c = Candidate(F(2),F(3),(F(1,5),))
    bounds = [row_interval(c,0,F(1),z,F(1),F(1,5),128) for z in range(21)]
    var = mp.mpf(9)/5
    edge = mp.log(mp.mpf('4.1'))
    tail = mp.erfc((edge+var/2)/mp.sqrt(2*var))/2
    assert real(sum(a for a,_ in bounds))+tail <= 1 <= real(sum(b for _,b in bounds))+tail
    # Exact-start and representative-zero conventions both yield nonzero rows.
    assert row_interval(c,0,F(1,20),0,F(1),F(1,5),128)[1] > 0

    labels = (10,10,11,10,12,15,20,15,10,6,12)
    catalogue = tuple(Candidate(p,k,(F(1,10),)*len(labels))
                      for p in (F(1),F(3,2),F(2)) for k in (F(1,5),F(7,10),F(3)))
    out = evaluate(labels,catalogue,F(1),F(1,10),3)
    assert len({step.choice for step in out}) > 1
    for length in range(4,len(labels)+1):
        prefix = evaluate(labels[:length],catalogue,F(1),F(1,10),3)
        assert prefix == out[:length-3]
    for replacement in (0,2,100):
        changed = evaluate(labels[:-1]+(replacement,),catalogue,F(1),F(1,10),3)
        assert changed[:-1] == out[:-1]
        assert changed[-1].choice == out[-1].choice
    frozen = evaluate(labels,catalogue,F(1),F(1,10),3,frozen=True)
    assert len({s.choice for s in frozen}) == 1
    for result in (out,frozen):
        lower, reference = F(1),mp.mpf(1)
        for step in result:
            j = step.prefix_length-1
            source = F(labels[j-1],10) if labels[j-1] else F(1,40)
            mass = integral(catalogue[step.choice],j,source,labels[j],F(1),F(1,10))
            lower *= step.lower
            reference *= mass
            assert step.joint_lower == lower
            assert real(lower) <= reference

    # Short integration with the reviewed D19 denominator; no stochastic run.
    spec = importlib.util.spec_from_file_location('d22_forecast_denominator',
        Path(__file__).resolve().parents[1]/'038/certify.py')
    cert = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = cert
    spec.loader.exec_module(cert)
    observed, gaps = labels[:4], (F(1,10),)*4
    denominator = cert.enclose(observed,gaps,(gaps,),F(1,10),F(1),
        (F(-1,5),F(1,5),F(1,25),F(9,25)),3,
        count=4,max_count=16,max_evaluations=8,factor=F(2))
    assert 0 < denominator.upper <= 1
    score_lower = out[0].joint_lower/denominator.upper
    assert score_lower >= 0
    print('Cell integration enclosures:',count,'; complete partition plus tail passes.')
    print('Predictable choices:',[step.choice for step in out],'; frozen:',frozen[0].choice)
    print('Prefix immutability, current-label blindness, lower products and D19 composition pass.')
    print('Fixed-record denominator status:',denominator.status,'; no power or runtime conclusion.')
    for action in (lambda: evaluate(labels,catalogue,F(1),F(0),3),
                   lambda: evaluate(labels,catalogue,F(1),F(1,10),0),
                   lambda: row_interval(c,0,F(1),-1,F(1),F(1,5)),
                   lambda: evaluate(labels,catalogue,F(1),F(1,10),3,bits=8)):
        try:
            action()
        except ValueError:
            pass
        else:
            raise AssertionError('invalid input accepted')


if __name__ == '__main__':
    main()
    from compare_check import main as compare_checks
    compare_checks()
    from restart_check import main as restart_checks
    restart_checks()
