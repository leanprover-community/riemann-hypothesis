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

namespace Bl.general_b_fact_left_alt_form

open Formalism.MainNotions.G in
theorem goal1
    {O : Type} [inst : CommRing O] [inst_1 : IsDomain O] [IsDiscreteValuationRing O]
    {W : Type} [inst_3 : AddCommGroup W] [inst_4 : Module (KK O) W] [inst_5 : Module O W]
    [inst_6 : IsScalarTower O (KK O) W] (M : Submodule O W) (y : W) :
    y ∈ MQ (K := KK O) M → ∃ a : O, a ≠ 0 ∧ a • y ∈ M := by
  intro hy
  rw [Formalism.MainNotions.G.MQ] at hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem b hax
    · rw [mul_smul]; exact M.smul_mem a hbz
  | smul c x _ hx =>
    obtain ⟨b, hb, hbx⟩ := hx
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors O) c
    refine ⟨(s : O) * b, mul_ne_zero (nonZeroDivisors.ne_zero s.2) hb, ?_⟩
    have key : ((s : O) * b) • (c • x) = r • (b • x) := by
      rw [← algebraMap_smul (Formalism.MainNotions.G.KK O) ((s : O) * b) (c • x), smul_smul,
        ← algebraMap_smul (Formalism.MainNotions.G.KK O) r (b • x), ← algebraMap_smul (Formalism.MainNotions.G.KK O) b x, smul_smul]
      congr 1
      rw [map_mul, ← hrs]
      ring
    rw [key]
    exact M.smul_mem r hbx

end Bl.general_b_fact_left_alt_form
