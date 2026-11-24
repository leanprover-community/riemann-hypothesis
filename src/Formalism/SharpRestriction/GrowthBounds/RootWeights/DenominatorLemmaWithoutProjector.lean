module

public import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantDenominatorLinftyBound
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.CasimirPowerScaledInsertDividedPower
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.CommutatorTripleProductLeibniz
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.DvrFractionFieldCharZeroPrime
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionDenominatorBound
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightDifferenceLeEllOfRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

private theorem degreeZeroWeightsBounded_ellOf {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [CharZero K] [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) :
    DegreeZeroWeightsBounded E (ellOf E (⊤ : Submodule K V)) := by
  intro ν hsum hne a
  have hsplit : ν a + ∑ i ∈ Finset.univ.erase a, ν i = 0 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ a)]; exact hsum
  have hell : (0 : ℤ) ≤ (ellOf E (⊤ : Submodule K V) : ℤ) := by positivity
  rw [abs_le]
  constructor
  · by_cases h0 : 0 ≤ ν a
    · linarith
    · push_neg at h0
      obtain ⟨b, hb, hbpos⟩ : ∃ b ∈ Finset.univ.erase a, 0 < ν b := by
        by_contra hc
        push_neg at hc
        have := Finset.sum_nonpos hc
        linarith
      have hba : b ≠ a := Finset.ne_of_mem_erase hb
      have := weight_difference_le_ell_of_rep hE ν hne b a hba (by linarith)
      linarith
  · by_cases h0 : ν a ≤ 0
    · linarith
    · push_neg at h0
      obtain ⟨b, hb, hbneg⟩ : ∃ b ∈ Finset.univ.erase a, ν b < 0 := by
        by_contra hc
        push_neg at hc
        have := Finset.sum_nonneg hc
        linarith
      have hab : a ≠ b := (Finset.ne_of_mem_erase hb).symm
      have := weight_difference_le_ell_of_rep hE ν hne a b hab (by linarith)
      linarith

private theorem degreeZeroWeightsBounded_linf {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [CharZero K] [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) :
    DegreeZeroWeightsBounded E (linf E (⊤ : Submodule K V)) := by
  intro ν hsum hne a
  have hmem : (ν a).natAbs ∈ {k | ∃ nu ∈ wtsOf E (⊤ : Submodule K V), (∑ b, nu b = 0) ∧
      ∃ b, k = (nu b).natAbs} :=
    ⟨ν, by simpa [wtsOf] using hne, hsum, a, rfl⟩
  have hbdd : BddAbove {k | ∃ nu ∈ wtsOf E (⊤ : Submodule K V), (∑ b, nu b = 0) ∧
      ∃ b, k = (nu b).natAbs} := by
    refine ⟨ellOf E (⊤ : Submodule K V), ?_⟩
    rintro k ⟨nu, hnu, hs, b, rfl⟩
    have hne' : weightSp E nu ≠ ⊥ := by simpa [wtsOf] using hnu
    have h := degreeZeroWeightsBounded_ellOf hE nu hs hne' b
    rw [Int.abs_eq_natAbs] at h
    exact_mod_cast h
  have hle : (ν a).natAbs ≤ linf E (⊤ : Submodule K V) := by
    unfold linf
    exact le_csSup hbdd hmem
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hle

theorem linf_lemma_without_projector (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : InvariantDenominatorLinftyBound := by
  intro p n' O _ _ _ S hG n V _ _ _ _ _ E hE M hM hMQ Inv hInv x hx
  haveI : CharZero (KK O) := dvr_fraction_field_charZero_prime S hG.prime
  rw [hMQ]
  exact invariant_projection_denominator_bound D h2 p O n V E hE M hM.1 Inv hInv _ _
    (fun c u hu0 hu => extremal_projector_properties hE c _ (degreeZeroWeightsBounded_linf hE) u hu0 hu)
    (fun c y hy => extremalProjector_denominator_bound S hG.prime hE hM.1 c _ y hy) x hx

theorem denominator_lemma_without_projector (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : InvariantProjectionDenominator := by
  intro p n' O _ _ _ S hG n V _ _ _ _ _ E hE M hM hMQ Inv hInv x hx
  haveI : CharZero (KK O) := dvr_fraction_field_charZero_prime S hG.prime
  rw [hMQ]
  exact invariant_projection_denominator_bound D h2 p O n V E hE M hM.1 Inv hInv _ _
    (fun c u hu0 hu => extremal_projector_properties hE c _ (degreeZeroWeightsBounded_ellOf hE) u hu0 hu)
    (fun c y hy => extremalProjector_denominator_bound S hG.prime hE hM.1 c _ y hy) x hx

end Formalism.MainNotions.G.GLWeightTheory
