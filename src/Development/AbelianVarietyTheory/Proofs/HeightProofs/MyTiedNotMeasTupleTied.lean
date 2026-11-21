import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedMY
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.UnramifiedMeasureTuples
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.IsEmptyPlacesReferenceTuple

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta IsDedekindDomain NumberField GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedMeasureTuples Formalism.UG.P

namespace GlobalTheory.MeasTupleEq


theorem map_residue_surjective (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue O)) := by
  intro g
  classical
  let M : Matrix (Fin n) (Fin n) O := fun a b =>
    Function.surjInv (IsLocalRing.residue_surjective (R := O)) ((g : Matrix (Fin n) (Fin n) _) a b)
  have hM : M.map (IsLocalRing.residue O) = (g : Matrix (Fin n) (Fin n) _) := by
    ext a b
    simp only [M]
    exact Function.surjInv_eq _ _
  have hdet : IsUnit M.det := by
    have h1 : IsUnit (IsLocalRing.residue O M.det) := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using (Matrix.GeneralLinearGroup.det g).isUnit
    exact (isUnit_map_iff (IsLocalRing.residue O) _).1 h1
  refine ⟨Matrix.GeneralLinearGroup.mk'' M hdet, Units.ext ?_⟩
  exact hM


def glT {k : Type} [Field k] {n : ℕ} (g : GL (Fin n) k) : GL (Fin n) k :=
  ⟨(g : Matrix (Fin n) (Fin n) k).transpose, ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose,
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩

theorem index_upper_eq_lower (k : Type) [Field k] [Fintype k] (r d : ℕ) :
    (parahoric (⊥ : Ideal k) r d).index = (tjcosets_par (𝔽 := k) (r + d) r).index := by
  classical
  have hc : Nat.card (parahoric (⊥ : Ideal k) r d) = Nat.card (tjcosets_par (𝔽 := k) (r + d) r) :=
    Nat.card_congr
      { toFun := fun g => ⟨glT g.1, fun a b ha hb => Ideal.mem_bot.1 (g.2 b a hb ha)⟩
        invFun := fun g => ⟨glT g.1, fun a b ha hb => Ideal.mem_bot.2 (g.2 b a hb ha)⟩
        left_inv := fun g => Subtype.ext (Units.ext rfl)
        right_inv := fun g => Subtype.ext (Units.ext rfl) }
  have h1 := (parahoric (⊥ : Ideal k) r d).index_mul_card
  have h2 := (tjcosets_par (𝔽 := k) (r + d) r).index_mul_card
  rw [hc, ← h2] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1

theorem prod_one_sub {q : ℝ} (hq : q ≠ 0) (n : ℕ) :
    (∏ i ∈ Finset.Icc 1 n, (1 - (q ^ i)⁻¹)) * q ^ (∑ i ∈ Finset.range n, (i + 1)) =
      ∏ i ∈ Finset.range n, (q ^ (i + 1) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), Finset.sum_range_succ, Finset.prod_range_succ, ← ih,
      pow_add q (∑ i ∈ Finset.range n, (i + 1))]
    have : (1 - (q ^ (n + 1))⁻¹) * q ^ (n + 1) = q ^ (n + 1) - 1 := by field_simp
    rw [← this]; ring

theorem sum_add (r d : ℕ) : ∑ i ∈ Finset.range (r + d), (i + 1) =
    r * d + (∑ i ∈ Finset.range r, (i + 1) + ∑ i ∈ Finset.range d, (i + 1)) := by
  induction d with
  | zero => simp
  | succ d ih => rw [← add_assoc, Finset.sum_range_succ, ih, Finset.sum_range_succ]; ring

theorem eq_indexValue {q : ℝ} (hq : 1 < q) (r d : ℕ) (C : ℝ)
    (h : C * (∏ i ∈ Finset.range r, (q ^ (i + 1) - 1)) * ∏ i ∈ Finset.range d, (q ^ (i + 1) - 1) =
      ∏ i ∈ Finset.range (r + d), (q ^ (i + 1) - 1)) : C = indexValue q r d := by
  have h0 : q ≠ 0 := by linarith
  have hp : ∀ n, (∏ i ∈ Finset.Icc 1 n, (1 - (q ^ i)⁻¹)) ≠ 0 := fun n => by
    have := (GlobalTheory.MeasTuple.prod_pos' hq n).ne'
    simpa only [zpow_neg, zpow_natCast] using this
  rw [← prod_one_sub h0, ← prod_one_sub h0, ← prod_one_sub h0, sum_add, pow_add, pow_add] at h
  unfold indexValue
  rw [eq_div_iff (mul_ne_zero (hp r) (hp d))]
  apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero (∑ i ∈ Finset.range r, (i + 1)) h0)
    (pow_ne_zero (∑ i ∈ Finset.range d, (i + 1)) h0))
  linear_combination h

theorem index_field (k : Type) [Field k] [Fintype k] (r d : ℕ) :
    ((parahoric (⊥ : Ideal k) r d).index : ℝ) = indexValue (Fintype.card k : ℝ) r d := by
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have h := tjcosets_arith _ (r + d) r _ hq (by omega) (tjcosets_ff_count (𝔽 := k) (r + d) r (by omega))
  have h2 := tjcosets_prod_shift (Fintype.card k : ℤ) d r
  rw [add_comm d r, ← h, ← index_upper_eq_lower, mul_comm] at h2
  apply eq_indexValue (by exact_mod_cast hq)
  exact_mod_cast h2



variable {D : D7} {X : ThetaX D}








end GlobalTheory.MeasTupleEq

end
