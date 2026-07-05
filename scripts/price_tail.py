#!/usr/bin/env python3
"""
price_tail.py -- Regge-Wheeler time-domain evolution on Schwarzschild,
measuring the late-time power-law ("Price") tail of a scalar (l=2)
perturbation. finite_diagnostic reproduce script for the Schwarzschild-
bridge "shadow" currency (HANDOFF_SW_BRIDGE.md SS5/SS6-T1/T2).

Physical content (standard, textbook; not claimed as new): the
Regge-Wheeler equation
    d^2(psi)/dt^2 - d^2(psi)/drs^2 + V(r) psi = 0
    V(r) = f(r) * [ l(l+1)/r^2 + 2M/r^3 ],   f(r) = 1 - 2M/r
on the same potential already Coq-verified (InfoAnalysisLift.v's `schw`),
evolved by explicit leapfrog on a uniform tortoise-coordinate grid, no PML
(the window is chosen short enough that boundary reflections have not yet
reached the observer).

Two initial-data families, exactly as specified in the handoff:
    time-symmetric:  psi = exp(-(rs-20)^2/18), psidot = 0
    momentum-type:   psi = 0,                  psidot = exp(-(rs-20)^2/18)
(T1 control run: if the two families give indistinguishable exponents,
that itself is the reportable finding, not a route to force a textbook
number.)

Run: python3 scripts/price_tail.py
"""
import numpy as np
from scipy.special import lambertw

M = 1.0
L_ANGULAR = 2


def f(r):
    return 1.0 - 2.0 * M / r


def r_of_tortoise(rs):
    """Exact inverse of rs = r + 2M ln(r/2M - 1) via the Lambert W branch
    used in the handoff: r = 2M(1 + W(exp(rs/(2M) - 1)))."""
    w = lambertw(np.exp(rs / (2.0 * M) - 1.0))
    return (2.0 * M * (1.0 + w)).real


def potential(rs, l=L_ANGULAR):
    r = r_of_tortoise(rs)
    return f(r) * (l * (l + 1) / r**2 + 2.0 * M / r**3)


def evolve(rs_min=-600.0, rs_max=600.0, N=6001, dt=0.1, steps=9000,
           observer_rs=10.0, mode="time_symmetric"):
    rs = np.linspace(rs_min, rs_max, N)
    h = rs[1] - rs[0]
    V = potential(rs)
    obs_idx = np.argmin(np.abs(rs - observer_rs))

    if mode == "time_symmetric":
        psi = np.exp(-((rs - 20.0) ** 2) / 18.0)
        psidot = np.zeros(N)
    elif mode == "momentum":
        psi = np.zeros(N)
        psidot = np.exp(-((rs - 20.0) ** 2) / 18.0)
    else:
        raise ValueError(mode)

    def laplacian(p):
        lap = np.zeros_like(p)
        lap[1:-1] = (p[2:] - 2 * p[1:-1] + p[:-2]) / h**2
        return lap

    psi_prev = psi - dt * psidot + 0.5 * dt**2 * (laplacian(psi) - V * psi)
    psi_curr = psi.copy()

    t_arr = np.zeros(steps)
    obs_arr = np.zeros(steps)

    for n in range(steps):
        lap = laplacian(psi_curr)
        psi_next = 2 * psi_curr - psi_prev + dt**2 * (lap - V * psi_curr)
        psi_next[0] = 0.0
        psi_next[-1] = 0.0
        t_arr[n] = (n + 1) * dt
        obs_arr[n] = psi_next[obs_idx]
        psi_prev, psi_curr = psi_curr, psi_next

    return t_arr, obs_arr


def windowed_slope(t_arr, obs_arr, t_lo, t_hi):
    mask = (t_arr >= t_lo) & (t_arr <= t_hi) & (np.abs(obs_arr) > 0)
    tt = t_arr[mask]
    yy = np.abs(obs_arr[mask])
    log_t = np.log(tt)
    log_y = np.log(yy)
    slope, intercept = np.polyfit(log_t, log_y, 1)
    return slope


def main():
    print("Single-mode pre-flight (health check, per handoff SS4's permanent rule):")
    t_pf, obs_pf = evolve(rs_min=-100.0, rs_max=100.0, N=1001, dt=0.1, steps=500,
                           observer_rs=10.0, mode="time_symmetric")
    max_amp = np.abs(obs_pf).max()
    growing = np.abs(obs_pf[-50:]).max() > 2 * np.abs(obs_pf[:50]).max()
    print(f"  max|psi| at observer = {max_amp:.4f}, late/early amplitude blowing up: {growing}")
    if growing:
        print("  FAIL: amplitude growing -- sign error suspected, aborting.")
        return

    print("\nTime-symmetric initial data (psi=Gaussian, psidot=0):")
    t_arr, obs_arr = evolve(mode="time_symmetric")
    windows = [(250, 450), (450, 650), (650, 850)]
    slopes_ts = []
    for lo, hi in windows:
        s = windowed_slope(t_arr, obs_arr, lo, hi)
        slopes_ts.append(s)
        print(f"  window [{lo},{hi}]: local slope = {s:.2f}")

    print("\nMomentum-type initial data (psi=0, psidot=Gaussian) -- T1 control:")
    t_arr2, obs_arr2 = evolve(mode="momentum")
    slopes_mom = []
    for lo, hi in windows:
        s = windowed_slope(t_arr2, obs_arr2, lo, hi)
        slopes_mom.append(s)
        print(f"  window [{lo},{hi}]: local slope = {s:.2f}")

    split = abs(slopes_ts[-1] - slopes_mom[-1])
    print(f"\nT1 acceptance check: |slope_ts - slope_mom| at last window "
          f"= {split:.2f} "
          f"(expect ~1 if families are genuinely distinct; if both ~ -8, "
          f"escalate per handoff SS6-T1 rather than reporting a pinned exponent)")

    ts_in_family = all(-8.5 < s < -7.5 for s in slopes_ts)
    mom_in_family = all(-7.5 < s < -6.5 for s in slopes_mom)
    steepening = slopes_ts[-1] <= slopes_ts[0] + 0.3
    split_ok = 0.7 < split < 1.3
    ok = ts_in_family and mom_in_family and steepening and split_ok

    print()
    if ok:
        print("PASS: time-symmetric tail in the -8 family (steepening, not "
              "approaching -7), momentum-type control in the classic -7 "
              "family, family split ~1 unit -- T1 acceptance test satisfied.")
    else:
        print("FAIL: one or more acceptance conditions not met -- "
              f"ts_in_family={ts_in_family} mom_in_family={mom_in_family} "
              f"steepening={steepening} split_ok={split_ok}. "
              "Escalate per HANDOFF_SW_BRIDGE.md SS6-T1 rather than "
              "reporting a pinned exponent.")


if __name__ == "__main__":
    main()
