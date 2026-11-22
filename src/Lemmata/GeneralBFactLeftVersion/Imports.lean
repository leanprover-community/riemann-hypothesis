module

public import Mathlib
public import Formalism.SharpRestriction.GrowthBounds.ObjPol
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalRingCardinality.DataArith
public import Formalism.LocalRingCardinality.DataKernels
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.SharpRestriction.CuspSpanNormBounds.DataS
public import Formalism.SharpRestriction.GrowthBounds.DataG
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.FrobeniusOrbits.DiscrMaximalRealCyclotomic
public import Formalism.FrobeniusOrbits.HostOrbitsPlaces
public import Formalism.FrobeniusOrbits.HostDiffSupport
public import Formalism.FrobeniusOrbits.HostThickExists
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.CoboundaryTransfers.Statement
public import Formalism.DegreeFormula.FlagDegFormula
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Formalism.SharpRestriction.GrowthBounds.DataGChain
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.RealCyclotomicSubfield
public import Formalism.LocalRingCardinality.DataLevel
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.FrobeniusOrbits.Statement
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Formalism.TameInertiaTowers.CentralOrderTwo.OrderOfThreeUnitsTwoPow
public import Formalism.TameInertiaTowers.CentralOrderTwo.TwoAdic
public import Formalism.TameInertiaTowers.CentralOrderTwo.MemDecompositionSubgroupIff
public import Formalism.TameInertiaTowers.CentralOrderTwo.NegOneNeOneUnitsZmodFour
public import Formalism.TameInertiaTowers.CentralOrderTwo.Groups
public import Formalism.TameInertiaTowers.CentralOrderTwo.NormalOrderTwoCentral
public import Formalism.TameInertiaTowers.CentralOrderTwo.Galois
public import Formalism.TameInertiaTowers.CentralOrderTwo.ConjEqInvOfPowEqOne
public import Formalism.FormalDegreeBessel.StatementBF
public import Formalism.FormalDegreeBessel.StatementWR
public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
public import Formalism.RealPlaceAnalysis.StatementU
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
public import Formalism.RealPlaceAnalysis.StatementA
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuadraticInequalityBoundHolds
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.SumOfSquaresIdentityHolds
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CasKHW
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.HWDiag
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.TrPowSumFilterZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet
public import Formalism.RealPlaceAnalysis.SmoothOnG
public import Formalism.RealPlaceAnalysis.StatementC

@[expose] public section

namespace Bl.general_b_fact_left_version

open Formalism.MainNotions.G in
theorem goal1
    {O : Type} [inst : CommRing O] [inst_1 : IsDomain O] {V : Type}
    [inst_2 : AddCommGroup V] [inst_3 : Module (KK O) V] [inst_4 : Module O V]
    [inst_5 : IsScalarTower O (KK O) V] (M : Submodule O V) :
    MQ (K := KK O) M = ⊤ → ∀ x : V, ∃ a : O, a ≠ 0 ∧ a • x ∈ M := by
  intro hM x
  have hx : x ∈ Submodule.span (KK O) (M : Set V) := by
    change x ∈ MQ (K := KK O) M
    rw [hM]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact M.smul_mem b hay
    · rw [mul_smul]
      exact M.smul_mem a hbz
  | smul k y _ hy =>
    obtain ⟨b, hb, hby⟩ := hy
    obtain ⟨⟨n, d⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) k
    have hd : (d : O) ≠ 0 := nonZeroDivisors.coe_ne_zero d
    refine ⟨b * d, mul_ne_zero hb hd, ?_⟩
    have key : (d : O) • (IsLocalization.mk' (Formalism.MainNotions.G.KK O) n d • y) = n • y := by
      rw [← smul_assoc, Algebra.smul_def, IsLocalization.mk'_spec', algebraMap_smul]
    rw [mul_smul, key, smul_comm]
    exact M.smul_mem n hby

end Bl.general_b_fact_left_version
