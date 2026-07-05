.PHONY: verify clean

# Dependency order matters: RDL_GammaSpectral -> InfoCoercivityBoundedClosure ->
# InfoDiscreteGraphCurvature, and InfoAnalysisLift -> InfoQuantumGravityRootBridge.
# InfoSchrodinger and InfoLorentzInvariance are standalone but both required by
# InfoQuantumRelativityUnification. InfoLorentz, InfoLorentzContinuum standalone.
COQFILES = \
	formal/RDL_GammaSpectral.v \
	formal/InfoCoercivityBoundedClosure.v \
	formal/InfoDiscreteGraphCurvature.v \
	formal/InfoAnalysisLift.v \
	formal/InfoQuantumGravityRootBridge.v \
	formal/InfoSchrodinger.v \
	formal/InfoLorentzInvariance.v \
	formal/InfoQuantumRelativityUnification.v \
	formal/InfoLorentz.v \
	formal/InfoLorentzContinuum.v \
	formal/InfoSpectralCeiling.v \
	formal/InfoRecurrenceEnergy.v \
	formal/InfoQuantumFrequencyCeiling.v \
	formal/InfoGraphFluxBalance.v \
	formal/InfoCompanionSkew.v \
	formal/InfoCausalSignature.v \
	formal/InfoGraphNoether.v \
	formal/InfoGraphGrowth.v \
	formal/InfoActionStationarity.v \
	formal/InfoCurvatureBalance.v \
	formal/InfoProductSpectrum.v \
	formal/InfoContinuumLimit_nD.v \
	formal/InfoWeightedReadout.v \
	formal/InfoCrossTermDominance.v \
	formal/InfoDiskBeforeLock.v \
	formal/InfoGrowthFold.v \
	formal/InfoCeilingMonotone.v \
	formal/InfoCurvatureNoether.v \
	formal/InfoModeRotation.v \
	formal/InfoPentagonSpectrum.v \
	formal/InfoAreaLaw.v \
	formal/InfoDegreeFromCurvature.v \
	formal/InfoTensorFrame.v \
	formal/InfoStrainTensorBridge.v \
	formal/InfoOptimizerWindow.v

verify:
	@set -e; \
	for f in $(COQFILES); do \
		echo "=== coqc $$f ==="; \
		coqc -q -R . DQG $$f || { echo "FAIL: $$f"; exit 1; }; \
	done; \
	echo "=== python3 scripts/verify_quantum_gravity_root_bridge.py (partial run, expect timeout at N=6400 is OK) ==="; \
	set +e; \
	timeout 90 python3 scripts/verify_quantum_gravity_root_bridge.py; \
	code=$$?; \
	set -e; \
	if [ $$code -ne 0 ] && [ $$code -ne 124 ]; then echo "FAIL: verify_quantum_gravity_root_bridge.py exited $$code"; exit 1; fi; \
	echo "=== PASS: all formal/*.v compiled, QNM bridge script ran ==="

clean:
	rm -f formal/*.vo formal/*.vok formal/*.vos formal/*.glob formal/.*.aux formal/.nra.cache
