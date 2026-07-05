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


def test_price_tail_time_symmetric_exponent_near_8():
    """HANDOFF_SW_BRIDGE.md SS5/SS6-T2: the late-time tail of a
    time-symmetric (psidot=0) l=2 scalar perturbation has local slope
    near -8, steepening (not approaching -7) across the measurement
    windows -- do not let this drift toward the generic Price -(2l+3)=-7
    value without the T1 control run distinguishing the two families."""
    from price_tail import evolve, windowed_slope

    t_arr, obs_arr = evolve(mode="time_symmetric")
    windows = [(250, 450), (450, 650), (650, 850)]
    slopes = [windowed_slope(t_arr, obs_arr, lo, hi) for lo, hi in windows]

    for s in slopes:
        assert -8.5 < s < -7.5, f"time-symmetric slope {s} outside expected -8 family"
    # steepening, not approaching -7 (guards against silently "fixing" toward textbook)
    assert slopes[-1] < slopes[0] + 0.3, f"slopes {slopes} unexpectedly flattening toward -7"


def test_price_tail_t1_control_family_split():
    """HANDOFF_SW_BRIDGE.md SS6-T1 (required): momentum-type (psi=0,
    psidot=Gaussian) initial data must give an exponent distinguishable
    from the time-symmetric family by roughly 1 unit -- confirming the
    split is a real initial-data effect, not a lattice/observer artifact.
    If this ever fails (both families converge to the same exponent),
    HANDOFF_SW_BRIDGE.md SS6-T1's escalation applies: do not report a
    pinned exponent."""
    from price_tail import evolve, windowed_slope

    t_ts, obs_ts = evolve(mode="time_symmetric")
    t_mom, obs_mom = evolve(mode="momentum")

    slope_ts = windowed_slope(t_ts, obs_ts, 650, 850)
    slope_mom = windowed_slope(t_mom, obs_mom, 650, 850)

    assert -7.5 < slope_mom < -6.5, f"momentum-family slope {slope_mom} not near classic -7"
    diff = abs(slope_ts - slope_mom)
    assert 0.7 < diff < 1.3, (
        f"family split {diff} not near the expected ~1 unit -- "
        "escalate per HANDOFF_SW_BRIDGE.md SS6-T1 rather than pinning an exponent"
    )
