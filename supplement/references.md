# References — Causal Quantum Gravity

> Split out of `SUPPLEMENT.md`. Every external equation used in this journal, by branch.

## References — every external equation used in this journal, by branch

> Peer-review pass (2026-07-05): every formula quoted above is listed here
> with its original source. Nothing in this list is claimed as this
> project's own result; each entry is cited exactly where its formula is
> used in §§3–7 above.

**Branch 1 — Quantum mechanics**

- M. Planck, "Über das Gesetz der Energieverteilung im Normalspectrum,"
  *Annalen der Physik*, 1900; A. Einstein, "Über einen die Erzeugung und
  Verwandlung des Lichtes betreffenden heuristischen Gesichtspunkt,"
  *Annalen der Physik*, 1905a. — jointly the source of the
  Planck–Einstein relation `E=ħω` used to compose §3's dispersion relation
  into an energy spectrum.
- E. Hückel, "Quantentheoretische Beiträge zum Benzolproblem,"
  *Zeitschrift für Physik*, 1931. — Hückel molecular-orbital theory, the
  §3.1 validation target (adjacency spectrum, resonance energy `2β`).

**Branch 2 — Special relativity**

- H. A. Lorentz, "Electromagnetic phenomena in a system moving with any
  velocity smaller than that of light," *Proc. Acad. Science Amsterdam*,
  1904; A. Einstein, "Zur Elektrodynamik bewegter Körper,"
  *Annalen der Physik*, 1905b. — jointly the source of the Lorentz boost
  transformation `boost_t(γ,v,t,x)=γ(t−vx)`, `γ²(1−v²)=1`, used (and
  honestly marked as *imported*, not derived) in `InfoLorentzInvariance`/
  `InfoLorentzTaylor`, §4.

**Branch 3 — General relativity / gravity**

- K. Schwarzschild, "Über das Gravitationsfeld eines Massenpunktes nach der
  Einsteinschen Theorie," *Sitzungsberichte der Königlich Preußischen
  Akademie der Wissenschaften*, 1916. — source of the metric factor
  `f(r)=1−2GM/rc²` imported by `SchwarzWeak`/`InfoGR` and by this journal's
  §6 Regge-Wheeler potential.
- A. Einstein, "Die Feldgleichungen der Gravitation," *Sitzungsberichte der
  Königlich Preußischen Akademie der Wissenschaften*, 1915. — source of the
  field equations `G_μν=8πG/c⁴ T_μν` referenced (not derived) by
  `InfoEinsteinTensor`/`InfoJacobianCovariance`, §5.1; also the historical
  source of the Mercury 43″/century perihelion-precession prediction
  reproduced numerically by the §5.1/§6 companion script.
- W. Unruh, "Notes on black-hole evaporation," *Phys. Rev. D*, 1976. —
  source of the Unruh temperature `T=ħκ/2πk_B` imported by `InfoJacobson`,
  §5.1.
- J. D. Bekenstein, "Black holes and entropy," *Phys. Rev. D*, 1973; S. W.
  Hawking, "Particle creation by black holes," *Commun. Math. Phys.*, 1975.
  — jointly the source of the Bekenstein-Hawking entropy `S=k_Bc³A/4Għ`
  imported by `InfoJacobson`, §5.1.
- T. Jacobson, "Thermodynamics of spacetime: the Einstein equation of
  state," *Phys. Rev. Lett.*, 1995. — source of the overall
  Clausius/Unruh/Bekenstein derivation *strategy* `InfoJacobson` follows
  (the algebraic core reused there is Jacobson's route, not this
  project's).
- C. W. Misner, K. S. Thorne, J. A. Wheeler, *Gravitation*, W. H. Freeman,
  1973. — standard reference for the generic tensor-algebra identities
  (trace-reversal, vacuum=Ricci-flat, Bianchi/covariance) formalized,
  without connection to `L_R`, in `InfoEinsteinTensor`/`InfoChristoffel`/
  `InfoJacobianCovariance`, §5.1.
- T. Regge, "General relativity without coordinates," *Il Nuovo Cimento*,
  1961. — Regge calculus, the prior-art discrete-spacetime geodesic
  computation cited in the §8 novelty audit.
- L. Bombelli, J. Lee, D. Meyer, R. Sorkin, "Space-time as a causal set,"
  *Phys. Rev. Lett.*, 1987. — Causal Set Theory, cited in the §8 novelty
  audit as prior art for "discrete graph substrate underlies physics."
- S. Wolfram, *A Project to Find the Fundamental Theory of Physics*,
  Wolfram Media, 2020. — the Wolfram Physics Project, cited in the §8
  novelty audit as prior art for the same claim.
- (anonymous / unresolved at time of writing), arXiv:2510.00057,
  *Phys. Rev. D*, Sept./Oct. 2025 — peer-reviewed minimal-length quantum
  speed limit test via matter-wave interferometry, cited in the §8 novelty
  audit as a stronger, peer-reviewed competitor to this project's own
  τ_c-floor claim.

**Bridge — QNM numerics (§6)**

- T. Regge, J. A. Wheeler, "Stability of a Schwarzschild singularity,"
  *Phys. Rev.*, 1957. — source of the Regge-Wheeler equation
  `d²ψ/dr*²+[ω²−V(r)]ψ=0` discretized in §6.
- E. Leaver, "An analytic representation for the quasi-normal modes of
  Kerr black holes," *Proc. R. Soc. Lond. A*, 1985. — source of the
  literature target QNM value `Mω≈0.4836−0.0968i` used for comparison
  throughout §6.
- E. Berti, V. Cardoso, A. O. Starinets, "Quasinormal modes of black holes
  and black branes," *Class. Quantum Grav.*, 2009. — review consolidating
  the same QNM literature values.
- A. Zenginoğlu, "A geometric framework for black hole perturbations,"
  *Phys. Rev. D*, 2011. — hyperboloidal-slicing method attempted (and
  found to hit a genuine essential singularity) in §5.2, attempt 6–7.
- J.-P. Bérenger, "A perfectly matched layer for the absorption of
  electromagnetic waves," *J. Comput. Phys.*, 1994. — source of the
  Perfectly Matched Layer (PML) absorbing-boundary method used in §6's
  successful, converged numerical bridge.

**Branch 4 — Discrete graph curvature**

- R. Forman, "Bochner's method for cell complexes and combinatorial Ricci
  curvature," *Discrete & Computational Geometry*, 2003. — source of the
  Forman-Ricci curvature formula `F(u,v)=4−deg(u)−deg(v)` used in §7.
- Y. Ollivier, "Ricci curvature of Markov chains on metric spaces,"
  *Journal of Functional Analysis*, 2009. — source of Ollivier-Ricci
  curvature, the optimal-transport-based alternative raised as an open
  question, §10.

**This project's own priority record**

- Y. Lahtee, "The Yaoharee Proposal" (working title), SSRN, posted 17 Oct
  2025 — cited in the §8 novelty audit as this project's own earliest
  verifiable timestamp, predating the June 2026 bioRxiv competitor
  identified in the same audit.
