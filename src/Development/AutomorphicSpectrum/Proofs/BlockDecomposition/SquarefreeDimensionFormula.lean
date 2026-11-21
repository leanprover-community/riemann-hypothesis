import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarishChandraDimension

section
section
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace GlobalTheory.CompanionTheory.FinGL

theorem prod_pow_sub (q : ℤ) (n : ℕ) :
    ∏ i ∈ Finset.range n, (q ^ n - q ^ i) =
      q ^ n.choose 2 * ∏ i ∈ Finset.Icc 1 n, (q ^ i - 1) := by
  have h1 : ∀ i ∈ Finset.range n, q ^ n - q ^ i = q ^ i * (q ^ (n - i) - 1) := by
    intro i hi
    have hin : i ≤ n := (Finset.mem_range.mp hi).le
    rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hin, mul_one]
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_range_id, Nat.choose_two_right]
  congr 1
  refine Finset.prod_nbij' (fun i => n - i) (fun j => n - j) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range, Finset.mem_Icc] at hi ⊢
    omega
  · intro j hj
    simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    show n - (n - i) = i
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    show n - (n - j) = j
    omega
  · intro i _
    rfl

theorem two_choose_add (m : ℕ) : 2 * m.choose 2 + m = m * m := by
  induction m with
  | zero => simp
  | succ k ih =>
    have h : (k + 1).choose 2 = k + k.choose 2 := by
      rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right]
    rw [h]
    nlinarith

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

theorem card_GL_int (ι : Type) [Fintype ι] [DecidableEq ι] :
    (Nat.card (GL ι K) : ℤ) = (Fintype.card K : ℤ) ^ (Fintype.card ι).choose 2 *
      ∏ i ∈ Finset.Icc 1 (Fintype.card ι), ((Fintype.card K : ℤ) ^ i - 1) := by
  rw [Nat.card_congr (glEquiv K (Fintype.equivFin ι)).toEquiv, Matrix.card_GL_field,
    ← prod_pow_sub, Fin.prod_univ_eq_prod_range (fun i => Fintype.card K ^ Fintype.card ι - Fintype.card K ^ i),
    Nat.cast_prod]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hq : 0 < Fintype.card K := Fintype.card_pos
  have hle : Fintype.card K ^ i ≤ Fintype.card K ^ Fintype.card ι :=
    Nat.pow_le_pow_right hq (Finset.mem_range.mp hi).le
  push_cast [Nat.cast_sub hle]
  rfl

section Parab

variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)

def parabCoord (p : parab K b) :
    ({p : ι × ι // b p.1 < b p.2} → K) × (∀ c, GL {i // b i = c} K) :=
  (fun x => (p.1 : Matrix ι ι K) x.1.1 x.1.2, fun c => levi K b c p)

theorem parabCoord_injective : Function.Injective (parabCoord K b) := by
  intro x y h
  have h1 := congrFun (congrArg Prod.fst h)
  have h2 := fun c => congrArg (fun g : GL {i // b i = c} K => (g : Matrix {i // b i = c} {i // b i = c} K))
    (congrFun (congrArg Prod.snd h) c)
  apply Subtype.ext
  apply Units.ext
  ext i j
  rcases lt_trichotomy (b i) (b j) with hij | hij | hij
  · exact h1 ⟨(i, j), hij⟩
  · exact congrFun (congrFun (h2 (b j)) ⟨i, hij⟩) ⟨j, rfl⟩
  · rw [x.2.1 i j hij, y.2.1 i j hij]

theorem parabCoord_surjective : Function.Surjective (parabCoord K b) := by
  rintro ⟨u, g⟩
  let M : Matrix ι ι K := fun i j =>
    if h : b i < b j then u ⟨(i, j), h⟩
    else if h' : b i = b j then (g (b j)).1 ⟨i, h'⟩ ⟨j, rfl⟩ else 0
  have hM : IsBlockUT K b M := by
    intro i j h
    simp [M, not_lt_of_gt h, h.ne']
  have hT : M.BlockTriangular b := fun i j h => hM i j h
  have hblk : ∀ c, M.toSquareBlock b c = (g c).1 := by
    intro c
    ext ⟨i, hi⟩ ⟨j, hj⟩
    subst hj
    have h0 : ¬ b i < b j := by rw [hi]; exact lt_irrefl _
    show M i j = _
    simp only [M]
    rw [dif_neg h0, dif_pos hi]
  have hdet : M.det ≠ 0 := by
    rw [hT.det]
    refine Finset.prod_ne_zero_iff.mpr fun c _ => ?_
    rw [hblk]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (g c).isUnit).ne_zero
  haveI : Invertible M := Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.mpr hdet)
  let G : GL ι K := Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet
  have hG : (G : Matrix ι ι K) = M := rfl
  have hGi : IsBlockUT K b ((G⁻¹ : GL ι K) : Matrix ι ι K) := by
    rw [Matrix.coe_units_inv, hG]
    exact fun i j h => Matrix.blockTriangular_inv_of_blockTriangular hT h
  refine ⟨⟨G, hM, hGi⟩, ?_⟩
  refine Prod.ext ?_ ?_
  · funext x
    show M x.1.1 x.1.2 = u x
    simp [M, x.2]
  · funext c
    apply Units.ext
    exact hblk c

theorem card_parab : Nat.card (parab K b) =
    Fintype.card K ^ Fintype.card {p : ι × ι // b p.1 < b p.2} *
      ∏ c, Nat.card (GL {i // b i = c} K) := by
  rw [Nat.card_eq_of_bijective _ ⟨parabCoord_injective K b, parabCoord_surjective K b⟩,
    Nat.card_prod, Nat.card_fun, Nat.card_pi, Nat.card_eq_fintype_card (α := K),
    Nat.card_eq_fintype_card (α := {p : ι × ι // b p.1 < b p.2})]

theorem card_eq_sum_blocks :
    Fintype.card ι = ∑ c, Fintype.card {i // b i = c} := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv b).symm

theorem card_same_block :
    Fintype.card {p : ι × ι // b p.1 = b p.2} =
      ∑ c, Fintype.card {i // b i = c} * Fintype.card {i // b i = c} := by
  simp only [← Fintype.card_prod]
  rw [← Fintype.card_sigma]
  refine Fintype.card_congr
    { toFun := fun p => ⟨b p.1.2, ⟨p.1.1, p.2⟩, ⟨p.1.2, rfl⟩⟩
      invFun := fun x => ⟨(x.2.1.1, x.2.2.1), x.2.1.2.trans x.2.2.2.symm⟩
      left_inv := fun _ => rfl
      right_inv := ?_ }
  rintro ⟨c, ⟨i, hi⟩, ⟨j, hj⟩⟩
  subst hj
  rfl

theorem card_swap_block :
    Fintype.card {p : ι × ι // b p.2 < b p.1} = Fintype.card {p : ι × ι // b p.1 < b p.2} :=
  Fintype.card_congr
    { toFun := fun p => ⟨p.1.swap, p.2⟩
      invFun := fun p => ⟨p.1.swap, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_pairs :
    Fintype.card ι * Fintype.card ι = Fintype.card {p : ι × ι // b p.1 < b p.2} +
      Fintype.card {p : ι × ι // b p.2 < b p.1} + Fintype.card {p : ι × ι // b p.1 = b p.2} := by
  rw [← Fintype.card_prod]
  simp only [Fintype.card_subtype, Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Fintype.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun p _ => ?_
  rcases lt_trichotomy (b p.1) (b p.2) with h | h | h
  · simp [h, h.ne, not_lt_of_gt h]
  · simp [h]
  · simp [h, h.ne', not_lt_of_gt h]

theorem choose_blocks :
    (Fintype.card ι).choose 2 = Fintype.card {p : ι × ι // b p.1 < b p.2} +
      ∑ c, (Fintype.card {i // b i = c}).choose 2 := by
  have h1 := card_pairs b
  rw [card_swap_block, card_same_block] at h1
  have h2 := two_choose_add (Fintype.card ι)
  have h3 : ∑ c, Fintype.card {i // b i = c} * Fintype.card {i // b i = c} =
      2 * ∑ c, (Fintype.card {i // b i = c}).choose 2 + Fintype.card ι := by
    rw [card_eq_sum_blocks b, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => (two_choose_add _).symm
  omega

end Parab

theorem cardParab : ReciprocityTheory.Ty.Fin.St.CardParab := by
  intro K _ _ _ ι _ _
  exact ⟨card_GL_int K ι, fun s b => ⟨card_parab K b, choose_blocks b⟩⟩

end GlobalTheory.CompanionTheory.FinGL
end
end

open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_parabolic_subgroup : ReciprocityTheory.Ty.Fin.St.CardParab := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FinGL.cardParab
end

section
section
open ReciprocityTheory.Ty.Fin

namespace GlobalTheory.CompanionTheory.TyFin

theorem prod_Icc_one_eq (f : ℕ → ℤ) (d : ℕ) (h : 1 ≤ d) :
    ∏ i ∈ Finset.Icc 1 d, f i = (∏ i ∈ Finset.Ico 1 d, f i) * f d := by
  have e : Finset.Icc 1 d = Finset.Ico 1 (d + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [e, Finset.prod_Ico_succ_top h]

theorem sqfreeDimAll : ReciprocityTheory.Ty.Fin.St.SqfreeDimAll := by
  intro K _ _ _ n s b lam hb hd
  have hq1 : (1 : ℤ) < (Fintype.card K : ℤ) := by
    have := Fintype.one_lt_card (α := K)
    exact_mod_cast this
  have hne : ∀ i : ℕ, 1 ≤ i → (Fintype.card K : ℤ) ^ i - 1 ≠ 0 := by
    intro i hi h
    have : (1 : ℤ) < (Fintype.card K : ℤ) ^ i := one_lt_pow₀ hq1 (by omega)
    linarith
  have hdim := GlobalTheory.T.harish_chandra_dimension K (Fin n) s b lam
  obtain ⟨hGL, hP⟩ := GlobalTheory.T.card_parabolic_subgroup K (Fin n)
  obtain ⟨hPc, hch⟩ := hP s b
  rw [Fintype.card_fin] at hGL hch
  have hblk : ∀ c, (Nat.card (GL {i // b i = c} K) : ℤ) =
      (Fintype.card K : ℤ) ^ (Fintype.card {i // b i = c}).choose 2 *
        ((∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}), ((Fintype.card K : ℤ) ^ i - 1)) *
          ((Fintype.card K : ℤ) ^ Fintype.card {i // b i = c} - 1)) := by
    intro c
    have hpos : 1 ≤ Fintype.card {i // b i = c} := by
      obtain ⟨i, hi⟩ := hb c
      exact Fintype.card_pos_iff.2 ⟨⟨i, hi⟩⟩
    rw [(GlobalTheory.T.card_parabolic_subgroup K {i // b i = c}).1,
      prod_Icc_one_eq (fun i => (Fintype.card K : ℤ) ^ i - 1) _ hpos]
  have hZ : (Module.finrank ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace K b lam) : ℤ) *
      (Nat.card (Formalism.IrreducibleCountingLemmas.TYPES.parab K b) : ℤ) =
      (Nat.card (GL (Fin n) K) : ℤ) * ∏ c, (Module.finrank ℂ (lam c) : ℤ) := by
    exact_mod_cast hdim
  have hPz : (Nat.card (Formalism.IrreducibleCountingLemmas.TYPES.parab K b) : ℤ) =
      (Fintype.card K : ℤ) ^ Fintype.card {p : Fin n × Fin n // b p.1 < b p.2} *
        ((Fintype.card K : ℤ) ^ (∑ c, (Fintype.card {i // b i = c}).choose 2) *
          ((∏ c, ∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}), ((Fintype.card K : ℤ) ^ i - 1)) *
            ∏ c, ((Fintype.card K : ℤ) ^ Fintype.card {i // b i = c} - 1))) := by
    rw [hPc]
    push_cast
    rw [Finset.prod_congr rfl (fun c _ => hblk c), Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hPz, hGL, hch, Finset.prod_congr rfl (fun c _ => hd c), pow_add] at hZ
  have hA : (∏ c, ∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}),
      ((Fintype.card K : ℤ) ^ i - 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun c _ => Finset.prod_ne_zero_iff.2 fun i hi =>
      hne i (Finset.mem_Ico.1 hi).1
  have hq0 : (Fintype.card K : ℤ) ≠ 0 := by linarith
  have hc : (Fintype.card K : ℤ) ^ Fintype.card {p : Fin n × Fin n // b p.1 < b p.2} *
      (Fintype.card K : ℤ) ^ (∑ c, (Fintype.card {i // b i = c}).choose 2) *
      (∏ c, ∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}), ((Fintype.card K : ℤ) ^ i - 1)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq0) (pow_ne_zero _ hq0)) hA
  apply mul_left_cancel₀ hc
  linear_combination hZ

end GlobalTheory.CompanionTheory.TyFin
end

open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squarefree_dimension_formula : ReciprocityTheory.Ty.Fin.St.SqfreeDimAll := by
  atlas_forward_decl GlobalTheory.CompanionTheory.TyFin.sqfreeDimAll
end
