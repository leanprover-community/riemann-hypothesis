module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPMorphismOfFlatAlgebra
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Mathlib.RingTheory.Flat.Basic
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ChooseFac
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.DpOfPre
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsLiftAndAug
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.PreOfGens
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Flat.EquationalCriterion

@[expose] public section

set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

open PowerSeries

theorem uniformBell_comp_coeff (m : ℕ) {n N : ℕ} (hn : n ≠ 0) (hN : N ≠ 0) :
    n.uniformBell N ^ m * m.uniformBell (n * N) = m.uniformBell n * (m * n).uniformBell N := by
  have h1 := Nat.uniformBell_mul_eq n hN
  have h2 := Nat.uniformBell_mul_eq m (Nat.mul_ne_zero hn hN)
  have h3 := Nat.uniformBell_mul_eq m hn
  have h4 := Nat.uniformBell_mul_eq (m * n) hN
  have hpos : 0 < N.factorial ^ (m * n) * n.factorial ^ m * m.factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  have e1 : n.uniformBell N ^ m * m.uniformBell (n * N)
      * (N.factorial ^ (m * n) * n.factorial ^ m * m.factorial) = (m * (n * N)).factorial := by
    rw [← h2, ← h1]
    ring
  have e2 : m.uniformBell n * (m * n).uniformBell N
      * (N.factorial ^ (m * n) * n.factorial ^ m * m.factorial) = (m * n * N).factorial := by
    rw [← h4, ← h3]
    ring
  rw [e1, e2, mul_assoc]

theorem exists_dividedPowers_aug : ∀ (B : Type) [CommRing B] (Q : PDPoly B),
    ∃ η : DividedPowers Q.aug, ∀ n : ℕ, η.dpow n (Q.e 1) = Q.e n := by
  intro B _ Q
  obtain ⟨η, hpre, hη⟩ := pre_aug B Q
  obtain ⟨δ, hδ⟩ := dp_of_pre Q.P Q.aug η (Set.range fun n : ℕ => Q.e (n + 1)) hpre rfl (by
    rintro x ⟨k, rfl⟩ m n hn
    show η m (η n (Q.e (k + 1))) = _ * η (m * n) (Q.e (k + 1))
    obtain ⟨j, hj⟩ : ∃ j, n * (k + 1) = j + 1 :=
      ⟨n * (k + 1) - 1, by
        have : 0 < n * (k + 1) := Nat.mul_pos (Nat.pos_of_ne_zero hn) k.succ_pos
        omega⟩
    have hc := congrArg (Nat.cast : ℕ → Q.P) (uniformBell_comp_coeff m hn (N := k + 1) (by omega))
    push_cast at hc
    rw [hη n k, hj, hpre.mul m _ _ (Q.e_succ_mem_aug j), hη m j, hη (m * n) k, ← hj,
      show m * (n * (k + 1)) = m * n * (k + 1) by ring, ← mul_assoc, ← mul_assoc, hc])
  refine ⟨δ, fun n => ?_⟩
  rw [hδ]
  simpa [Nat.uniformBell_one_right] using hη n 0

private theorem dpowSeries_add_base_eq_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) {r : R} (hr : r ∈ I) (a b : A) :
    (PowerSeries.mk fun n => (a + b) ^ n * algebraMap R A (κ.dpow n r)) =
      (PowerSeries.mk fun n => a ^ n * algebraMap R A (κ.dpow n r)) *
        PowerSeries.mk fun n => b ^ n * algebraMap R A (κ.dpow n r) := by
  ext n
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  rw [(Commute.all a b).add_pow', Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
  have h := κ.mul_dpow (m := k.1) (n := k.2) hr
  rw [hk] at h
  rw [show a ^ k.1 * algebraMap R A (κ.dpow k.1 r) * (b ^ k.2 * algebraMap R A (κ.dpow k.2 r))
      = a ^ k.1 * b ^ k.2 * algebraMap R A (κ.dpow k.1 r * κ.dpow k.2 r) by rw [map_mul]; ring,
    h, map_mul, map_natCast, nsmul_eq_mul]
  ring

private theorem dpowSeries_algebraMap_mul_base_eq_smul_arg {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) {r : R} (hr : r ∈ I) (s : R) (y : A) :
    (PowerSeries.mk fun n => (algebraMap R A s * y) ^ n * algebraMap R A (κ.dpow n r)) =
      PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n (s * r)) := by
  ext n
  simp only [PowerSeries.coeff_mk]
  rw [κ.dpow_mul hr, map_mul, map_pow]
  ring

private theorem dpowSeries_add_arg_eq_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) {r r' : R} (hr : r ∈ I) (hr' : r' ∈ I) (y : A) :
    (PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n (r + r'))) =
      (PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n r)) *
        PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n r') := by
  ext n
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul]

  rw [κ.dpow_add hr hr', map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
  rw [← hk, pow_add, map_mul]
  ring

private theorem dpowSeries_zero_arg_eq_one {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) (y : A) :
    (PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n 0)) = 1 := by
  ext n
  rcases n with _ | n
  · simp [κ.dpow_zero I.zero_mem]
  · simp [κ.dpow_eval_zero (Nat.succ_ne_zero n)]

private theorem dpowSeries_zero_base_eq_one {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) {r : R} (hr : r ∈ I) :
    (PowerSeries.mk fun n => (0 : A) ^ n * algebraMap R A (κ.dpow n r)) = 1 := by
  ext n
  rcases n with _ | n
  · simp [κ.dpow_zero hr]
  · simp

private theorem dpowSeries_sum_base_eq_prod {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) {r : R} (hr : r ∈ I) {ι : Type} (s : Finset ι) (v : ι → A) :
    (PowerSeries.mk fun n => (∑ j ∈ s, v j) ^ n * algebraMap R A (κ.dpow n r)) =
      ∏ j ∈ s, PowerSeries.mk fun n => v j ^ n * algebraMap R A (κ.dpow n r) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dpowSeries_zero_base_eq_one κ hr
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, dpowSeries_add_base_eq_mul κ hr, ih]

private theorem dpowSeries_sum_arg_eq_prod {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) (y : A) {ι : Type} (s : Finset ι) (v : ι → R) (hv : ∀ i, v i ∈ I) :
    (PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n (∑ i ∈ s, v i))) =
      ∏ i ∈ s, PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n (v i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dpowSeries_zero_arg_eq_one κ y
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj,
      dpowSeries_add_arg_eq_mul κ (hv j) (I.sum_mem fun i _ => hv i), ih]

theorem flatExt (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] (I : Ideal R)
    (κ : DividedPowers I) : ∃ δ : DividedPowers (I.map (algebraMap R A)), IsDPMorphism κ δ (algebraMap R A) := by
  apply GlobalTheory.DPFlat.exists_isDPMorphism_of_flat <;> assumption

theorem exists_std (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) :
    ∃ η : DividedPowers (Q.ext J), Q.IsStd δ η := by
  obtain ⟨η, hη⟩ := exists_dividedPowers_aug B Q
  obtain ⟨-, ε, hε⟩ := exists_lift_and_aug B Q
  obtain ⟨θ, hθ, hθη⟩ := dp_split B J δ Q.P ε Q.aug η hε
  refine ⟨θ, ⟨hθ, fun n => ?_⟩⟩
  rw [hθη n _ (Q.e_succ_mem_aug 0)]
  exact hη n

end FubiniStudyChowHeightFormula₂.Adr
