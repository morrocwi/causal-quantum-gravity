"""Telegraph analyser: exact rational theorem values + float spectrum sorting."""

from fractions import Fraction

import numpy as np
import pytest

from spine_pde import DECAY, OSCILLATORY, CRITICAL, Telegraph


def test_disc_1111_is_minus_three_exact():
    tg = Telegraph(1, 1, 1)          # all int -> exact mode
    assert tg.exact
    assert tg.discriminant(1) == Fraction(-3)
    assert tg.regime(1) == OSCILLATORY


def test_mass_and_tau_c_native_units():
    tg = Telegraph(Fraction(1), Fraction(3), Fraction(2))
    # mass = D/(2M) = 3/2 ; tau_c = M/D = 1/3 ; mass == 1/(2 tau_c)
    assert tg.mass() == Fraction(3, 2)
    assert tg.tau_c() == Fraction(1, 3)
    assert tg.mass() == 1 / (2 * tg.tau_c())


def test_mass_is_one_over_2M_when_D_equals_one():
    tg = Telegraph(Fraction(5), Fraction(1), Fraction(1))
    assert tg.mass() == Fraction(1, 10)  # 1/(2M)


def test_crossover_and_regime_switch():
    tg = Telegraph(Fraction(1), Fraction(2), Fraction(1))
    lam_c = tg.crossover()             # D^2/(4MK) = 1
    assert lam_c == Fraction(1)
    assert tg.regime(lam_c) == CRITICAL
    assert tg.regime(lam_c - Fraction(1, 2)) == DECAY        # lam < lam_c
    assert tg.regime(lam_c + Fraction(1, 2)) == OSCILLATORY  # lam > lam_c


def test_decoherence_rate():
    tg = Telegraph(Fraction(1), Fraction(2), Fraction(3))
    # Gamma = K lam / D = 3*4/2 = 6
    assert tg.decoherence_rate(4) == Fraction(6)


def test_zero_damping_gives_infinite_tau_and_no_decoherence():
    tg = Telegraph(1.0, 0.0, 1.0)
    assert tg.tau_c() == float("inf")
    assert tg.decoherence_rate(3.0) == float("inf")
    assert tg.mass() == 0.0


def test_roots_complex_when_underdamped():
    tg = Telegraph(1.0, 1.0, 1.0)
    r1, r2 = tg.roots(1.0)       # disc = -3 < 0
    assert abs(r1.imag) > 0 and abs(r2.imag) > 0
    # product of roots == K lam / M = 1
    assert np.isclose((r1 * r2).real, 1.0)


def test_classify_spectrum_vectorised():
    tg = Telegraph(1.0, 2.0, 1.0)   # lam_c = 1
    lam = np.linspace(0, 5, 5001)
    info = tg.classify_spectrum(lam)
    assert info["lam_c"] == 1.0
    # every lam > 1 is oscillatory, every lam < 1 is decay
    assert np.all(info["oscillatory"] == (lam > 1.0))
    assert np.all(info["decay"] == (lam < 1.0))
    assert info["n_oscillatory"] + info["n_decay"] <= lam.size


def test_validation():
    with pytest.raises(ValueError):
        Telegraph(0, 1, 1)   # M must be > 0
    with pytest.raises(ValueError):
        Telegraph(1, 1, 0)   # K must be > 0
