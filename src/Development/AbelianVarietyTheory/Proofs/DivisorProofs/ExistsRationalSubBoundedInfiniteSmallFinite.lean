module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompactAdele
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrowthOfTame
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.ReductionBlock
import GroundTheory.GlobalFields.KummerTheory.LocalIndex

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.AdeleApprox

theorem exists_compact_integral (E : Type) [Field E] [NumberField E] :
    ∃ C : Set (InfiniteAdeleRing E), IsCompact C ∧
      ∀ x : Ad E, ∃ a : E, (x - algebraMap E (Ad E) a).1 ∈ C ∧
        ∀ v, (x - algebraMap E (Ad E) a).2 v ∈ v.adicCompletionIntegers E := by
  obtain ⟨C, hC, hCy⟩ := Formalism.IndefR.Eqv.G5.adl_inf_cocompact (F := E)
  refine ⟨C, hC, fun x => ?_⟩
  obtain ⟨u, hu⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem_intAd x.2
  obtain ⟨r, hr⟩ := hCy (x.1 - algebraMap E _ u)
  refine ⟨u + r, ?_, ?_⟩
  · show x.1 - algebraMap E (InfiniteAdeleRing E) (u + r) ∈ C
    rw [map_add (f := _), ← sub_sub]
    exact hr
  · have : x.2 - algebraMap E (Af E) (u + r) =
        (x.2 - algebraMap E _ u) - algebraMap E _ (r : E) := by rw [map_add (f := _), sub_sub]
    show ∀ v, (x.2 - algebraMap E (Af E) (u + r)) v ∈ _
    rw [this]
    exact sub_mem hu (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.algebraMap_mem_intAd r)

theorem exists_rat_sub_bounded_small :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (U : Set (Af E)), U ∈ nhds (0 : Af E) →
      ∃ R : ℝ, 0 ≤ R ∧ ∀ x : Ad E, ∃ ξ : E, ‖pInf E (x - algebraMap E (Ad E) ξ)‖ ≤ R ∧
        pFin E (x - algebraMap E (Ad E) ξ) ∈ U := by
  intro E _ _ _ U hU
  obtain ⟨C, hC, hcov⟩ := exists_compact_integral E
  obtain ⟨N, hN, hNU⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele E U hU
  have hc : Continuous (infEq E).symm := by
    refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (hC.image hc).isBounded
  refine ⟨N * max B 0, by positivity, fun x => ?_⟩
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  obtain ⟨a, h1, h2⟩ := hcov (algebraMap E (Ad E) (N : E)⁻¹ * x)
  set k := algebraMap E (Ad E) (N : E)⁻¹ * x - algebraMap E (Ad E) a with hk
  have e : x - algebraMap E (Ad E) ((N : E) * a) = N • k := by
    rw [hk, nsmul_eq_mul, ← map_natCast (algebraMap E (Ad E)) N, mul_sub, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ hN', map_one, one_mul, map_mul]
  refine ⟨(N : E) * a, ?_, ?_⟩
  · rw [e, map_nsmul]
    have hb : ‖pInf E k‖ ≤ max B 0 := (hB _ ⟨k.1, h1, rfl⟩).trans (le_max_left _ _)
    exact (norm_nsmul_le).trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
  · rw [e, map_nsmul]
    exact hNU _ h2

end GlobalTheory.AdeleApprox
