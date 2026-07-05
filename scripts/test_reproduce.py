"""
test_reproduce.py -- pytest suite that independently re-derives the
finite_diagnostic numerical claims that have a script in THIS repo
(causal-quantum-gravity). The probe_*.py scripts referenced elsewhere in
SUPPLEMENT.md SS12.3 live in the sibling private repo
(research_universal_solver/scripts/), which has its own test_reproduce.py
covering those.

Standing rule (this project, as of this file): no numerical claim enters
SUPPLEMENT.md or the companion note without a checked-in, runnable test
that reproduces it -- prose alone is not sufficient, and a claim reported
in conversation is not trusted until it passes here.

Run: python3 -m pytest scripts/test_reproduce.py -v
"""
import sys
import os

sys.path.insert(0, os.path.dirname(__file__))


def test_qnm_frequency_convergence():
    """SUPPLEMENT.md SS13 Schwarzschild addendum: M*omega converges to the
    literature scalar l=2, n=0 fundamental QNM frequency."""
    from verify_quantum_gravity_root_bridge import qnm_eigenvalue, TARGET

    w, d = qnm_eigenvalue(1600, rs_min=-30.0, rs_max=80.0, sigma_max=2.0, order=4)
    assert d < 0.005, f"QNM frequency {w} too far from target {TARGET} (|diff|={d})"
    assert abs(w.real - TARGET.real) < 0.001
    assert abs(w.imag - TARGET.imag) < 0.002
