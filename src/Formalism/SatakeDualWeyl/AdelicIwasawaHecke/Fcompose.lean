import Formalism.SatakeDualWeyl.StatementF
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActMem
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeConvolutionMemHolds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa

section
open Formalism.UG

noncomputable section

namespace Formalism.UG.P

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem fSatake_nontriv {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) :
    (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial := by
  obtain ⟨-, -, -, hv, -⟩ := hU
  refine ⟨ϖ, ?_, ?_⟩
  · rw [hv]; exact WithZero.coe_ne_zero
  · rw [hv]
    intro h1
    have := WithZero.coe_injective (h1.trans WithZero.coe_one.symm)
    exact absurd (Multiplicative.ofAdd.injective (this.trans ofAdd_zero.symm)) (by norm_num)

theorem isCommensurated_integral_unitary_of_unramified {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (n : ℕ) :
    IsCommensurated (KU σ n) := by
  obtain ⟨-, -, -, hvϖ, -, hq2, hq⟩ := hU
  set A := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring with hA
  haveI : IsCyclic (WithZero (Multiplicative ℤ))ˣ :=
    isCyclic_of_surjective (WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ)).symm.toMonoidHom
      (MulEquiv.surjective _)
  have h0 : Valued.v ϖ ≠ 0 := by rw [hvϖ]; exact WithZero.coe_ne_zero
  haveI : Nontrivial ↥(MonoidWithZeroHom.ofClass
      (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))).valueGroup := by
    refine ⟨⟨1, ⟨Units.mk0 (Valued.v ϖ) h0, MonoidWithZeroHom.mem_valueGroup _ ⟨ϖ, rfl⟩⟩, ?_⟩⟩
    intro h
    have h1 := congrArg (fun u : ↥(MonoidWithZeroHom.ofClass
      (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))).valueGroup =>
        ((u : (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ))) h
    simp only [OneMemClass.coe_one, Units.val_one, Units.val_mk0, hvϖ] at h1
    have h2 := WithZero.coe_injective (h1.symm.trans WithZero.coe_one.symm)
    exact absurd (Multiplicative.ofAdd.injective (h2.trans ofAdd_zero.symm)) (by norm_num)
  haveI hD : IsDiscreteValuationRing ↥A.toSubring := Valuation.valuationSubring_isDiscreteValuationRing _
  have hRes : Finite (IsLocalRing.ResidueField ↥A.toSubring) := by
    apply Nat.finite_of_card_ne_zero
    rw [show Nat.card (IsLocalRing.ResidueField ↥A.toSubring) = q ^ 2 from hq]
    exact pow_ne_zero 2 (by omega)
  intro g
  obtain ⟨c, hc0, hg1, hg2⟩ := Formalism.UG.P.glint_exists_denom A (g : GL (Fin n) L)
  haveI : Finite (↥A.toSubring ⧸ Ideal.span {c * c}) :=
    glint_finite_quotient_of_dvr hRes _ (by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact mul_ne_zero hc0 hc0)
  have hO : intL L = A.toSubring := rfl
  unfold KU
  rw [hO]
  have hK : intPts A.toSubring.subtype (GU σ n) = GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range := rfl
  rw [hK]
  have hmap : ((GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range).subgroupOf (GU σ n)).map (MulAut.conj g).toMonoidHom =
      ((GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range).map (MulAut.conj (g : GL (Fin n) L)).toMonoidHom).subgroupOf (GU σ n) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, by simp⟩
    · rintro ⟨y, hy, hyx⟩
      exact ⟨⟨y, hy.1⟩, hy, Subtype.ext (by simpa using hyx)⟩
  rw [hmap, Subgroup.relIndex_subgroupOf inf_le_left]
  have hPB := glint_princ_relIndex_ne_zero (n := Fin n) A.toSubring (Ideal.span {c * c})
  have h1 : (princ (n := Fin n) A.toSubring.subtype (Ideal.span {c * c}) ⊓ GU σ n).relIndex
      (GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range) ≠ 0 := by
    rw [inf_comm (GU σ n) (bc (n := Fin n) A.toSubring.subtype).range]
    exact Subgroup.relIndex_inter_ne_zero hPB (GU σ n)
  have hle : princ (n := Fin n) A.toSubring.subtype (Ideal.span {c * c}) ⊓ GU σ n ≤
      (GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range).map (MulAut.conj (g : GL (Fin n) L)).toMonoidHom := by
    rintro h ⟨hP, hHh⟩
    obtain ⟨b, hb, hbh⟩ := glint_princ_le_map_conj A.toSubring (g : GL (Fin n) L) c hg1 hg2 hP
    refine ⟨b, ⟨?_, hb⟩, hbh⟩
    have hbe : b = (g : GL (Fin n) L)⁻¹ * h * g := by
      rw [← hbh]
      simp [MulAut.conj_apply, mul_assoc]
    rw [hbe]
    exact (GU σ n).mul_mem ((GU σ n).mul_mem ((GU σ n).inv_mem g.2) hHh) g.2
  exact fun hz => h1 (Subgroup.relIndex_eq_zero_of_le_left hle hz)

theorem fSatake_v_eq {x : L} (hx : x ≠ 0) :
    Valued.v x = ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ordL
  rw [dif_neg h, neg_neg, ofAdd_toAdd, WithZero.coe_unzero]

private lemma ordL_eq_of_valuation_eq {x : L} (hx : x ≠ 0) {k : ℤ}
    (h : Valued.v x = ((Multiplicative.ofAdd (-k) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ordL x = k := by
  rw [fSatake_v_eq hx] at h
  have h2 := WithZero.coe_injective h
  have h3 := Multiplicative.ofAdd.injective h2
  linarith

theorem fSatake_ord_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : ordL (x * y) = ordL x + ordL y := by
  apply ordL_eq_of_valuation_eq (mul_ne_zero hx hy)
  rw [map_mul, fSatake_v_eq hx, fSatake_v_eq hy, ← WithZero.coe_mul, ← ofAdd_add, neg_add]

theorem fSatake_ord_one : ordL (1 : L) = 0 := by
  apply ordL_eq_of_valuation_eq one_ne_zero
  simp


theorem fSatake_ord_of_v {x y : L} (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  unfold ordL
  simp only [h]

theorem fSatake_ord_zpow {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (k : ℤ) : ordL (ϖ ^ k) = k := by
  have h0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  apply ordL_eq_of_valuation_eq (zpow_ne_zero k h0)
  rw [map_zpow₀, hϖ, ← WithZero.coe_zpow, ← ofAdd_zsmul]
  congr 2
  simp

theorem fSatake_ord_nonneg {x : L} (hx : x ≠ 0) (hO : x ∈ intL L) : 0 ≤ ordL x := by
  have h1 : Valued.v x ≤ 1 := hO
  rw [fSatake_v_eq hx, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero,
    Multiplicative.ofAdd_le] at h1
  linarith


end Formalism.UG.P
end
end

section
open Formalism.UG

noncomputable section

namespace Formalism.UG.P

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem fSatake_borel_iff (b : GU σ n) :
    IsBorelU b ↔ (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := Iff.rfl

theorem fSatake_borel_mul {b b' : GU σ n} (hb : IsBorelU b) (hb' : IsBorelU b') :
    IsBorelU (b * b') := by
  rw [fSatake_borel_iff] at hb hb' ⊢
  simpa only [Subgroup.coe_mul, Units.val_mul] using hb.mul hb'

theorem fSatake_borel_inv {b : GU σ n} (hb : IsBorelU b) : IsBorelU b⁻¹ := by
  rw [fSatake_borel_iff] at hb ⊢
  haveI : Invertible (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := Units.invertible _
  have := Matrix.blockTriangular_inv_of_blockTriangular hb
  simpa [Matrix.coe_units_inv] using this

theorem fSatake_diag_mul {M N : Matrix (Fin n) (Fin n) L} (hM : M.BlockTriangular id)
    (hN : N.BlockTriangular id) (i : Fin n) : (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hM h, zero_mul]
    · rw [hN h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem fSatake_borel_diag_mul {b b' : GU σ n} (hb : IsBorelU b) (hb' : IsBorelU b') (i : Fin n) :
    (((b * b' : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      (((b' : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
  have := fSatake_diag_mul ((fSatake_borel_iff b).1 hb) ((fSatake_borel_iff b').1 hb') i
  simpa only [Subgroup.coe_mul, Units.val_mul] using this

theorem fSatake_borel_diag_inv {b : GU σ n} (hb : IsBorelU b) (i : Fin n) :
    (((b⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
  rw [← fSatake_borel_diag_mul (fSatake_borel_inv hb) hb i]
  simp

theorem fSatake_rev_iff (k l : Fin n) : (k : ℕ) + l + 1 = n ↔ k = l.rev := by
  have := k.isLt
  have := l.isLt
  rw [Fin.ext_iff, Fin.val_rev]
  omega

theorem fSatake_cTJ (M : Matrix (Fin n) (Fin n) L) (i l : Fin n) :
    (cT σ M * antiJ L n) i l = σ (M l.rev i) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single l.rev]
  · rw [show antiJ L n l.rev l = 1 from if_pos ((fSatake_rev_iff l.rev l).2 rfl), mul_one]
    rfl
  · intro j _ hj
    rw [show antiJ L n j l = 0 from if_neg (fun h => hj ((fSatake_rev_iff j l).1 h)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem fSatake_unit_diag_mat {M : Matrix (Fin n) (Fin n) L} (hb : ∀ i j : Fin n, j < i → M i j = 0)
    (hU : cT σ M * antiJ L n * M = antiJ L n) (i : Fin n) : σ (M i i) * M i.rev i.rev = 1 := by
  have h := congrFun (congrFun hU i) i.rev
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev] at h
  · rw [fSatake_cTJ, Fin.rev_rev,
      show antiJ L n i i.rev = 1 from if_pos ((fSatake_rev_iff i i.rev).2 (Fin.rev_rev i).symm)] at h
    exact h
  · intro l _ hl
    rw [fSatake_cTJ]
    rcases lt_or_gt_of_ne hl with h1 | h1
    · have h2 : i < l.rev := by
        simp only [Fin.lt_iff_val_lt_val, Fin.val_rev] at h1 ⊢
        omega
      rw [hb _ _ h2, map_zero, zero_mul]
    · rw [hb l i.rev h1, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem fSatake_unit_diag {b : GU σ n} (hb : IsBorelU b) (i : Fin n) :
    σ ((((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) *
      (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i.rev i.rev = 1 :=
  fSatake_unit_diag_mat hb b.2 i

theorem fSatake_diag_exists (e : Fin n → L) (he : ∀ i, σ (e i) * e i.rev = 1) :
    ∃ d : GU σ n, (((d : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal e ∧
      (((d⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        Matrix.diagonal (fun i => (e i)⁻¹) := by
  have hne : ∀ i, e i ≠ 0 := fun i h => by
    have := he i.rev
    rw [Fin.rev_rev, h, mul_zero] at this
    exact zero_ne_one this
  let g : GL (Fin n) L := ⟨Matrix.diagonal e, Matrix.diagonal (fun i => (e i)⁻¹),
    by simp [Matrix.diagonal_mul_diagonal, mul_inv_cancel₀ (hne _)],
    by simp [Matrix.diagonal_mul_diagonal, inv_mul_cancel₀ (hne _)]⟩
  have hc : cT σ (Matrix.diagonal e) = Matrix.diagonal (fun i => σ (e i)) := by
    ext a c
    by_cases h : a = c
    · subst h
      simp [cT]
    · simp [cT, Matrix.diagonal_apply, h, Ne.symm h]
  have hg : g ∈ GU σ n := by
    show cT σ (Matrix.diagonal e) * antiJ L n * Matrix.diagonal e = antiJ L n
    ext i l
    rw [hc, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [antiJ]
    split_ifs with h
    · have hl : l = i.rev := (fSatake_rev_iff l i).1 (by omega)
      subst hl
      simp [he i]
    · simp
  exact ⟨⟨g, hg⟩, rfl, rfl⟩

end Formalism.UG.P
end
end

section
open Formalism.UG

noncomputable section

namespace Formalism.UG.P

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

local notation "⟪" b "⟫" => (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)

theorem fSatake_borel_of_diag {d : GU σ n} {e : Fin n → L} (hd : ⟪d⟫ = Matrix.diagonal e) :
    IsBorelU d := by
  intro i j hij
  change ⟪d⟫ i j = 0
  rw [hd, Matrix.diagonal_apply_ne _ (ne_of_lt hij).symm]

theorem fSatake_borel_one : IsBorelU (1 : GU σ n) := by
  exact fSatake_borel_of_diag (e := fun _ => 1) (by rw [Matrix.diagonal_one]; simp)

theorem fSatake_ne_zero_of_borel {b : GU σ n} (hb : IsBorelU b) (i : Fin n) : ⟪b⟫ i i ≠ 0 := by
  intro h
  have hdet : (⟪b⟫).det = ∏ i, ⟪b⟫ i i :=
    Matrix.det_of_upperTriangular (fun i j hij => hb i j hij)
  have hu : IsUnit (⟪b⟫).det := (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  exact hu.ne_zero (by rw [hdet]; exact Finset.prod_eq_zero (Finset.mem_univ i) h)

theorem fSatake_tMat_apply_lt (ϖ : L) {m : ℕ} (a : Fin m → ℤ) (j : Fin m) (hj : (j : ℕ) < n) :
    tMat ϖ n m a ⟨j, hj⟩ ⟨j, hj⟩ = ϖ ^ (a j) := by
  simp [tMat, j.isLt]

theorem fSatake_borel_tMat {ϖ : L} {m : ℕ} {a : Fin m → ℤ} {t : GU σ n} (ht : ⟪t⟫ = tMat ϖ n m a) :
    IsBorelU t := by
  rw [tMat] at ht
  exact fSatake_borel_of_diag ht

theorem fSatake_tMat_exists {ϖ : L} {q m : ℕ} (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n)
    (a : Fin m → ℤ) : ∃ t : GU σ n, ⟪t⟫ = tMat ϖ n m a := by
  have hϖ : Valued.v ϖ = ↑(Multiplicative.ofAdd (-1 : ℤ)) := by
    obtain ⟨-, -, -, h, -⟩ := hU
    exact h
  have hσ : σ ϖ = ϖ := by
    obtain ⟨-, -, h, -⟩ := hU
    exact h
  have hϖ0 : ϖ ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have key : ∀ i j : Fin n, (i : ℕ) + j + 1 = n → tMat ϖ n m a i i * tMat ϖ n m a j j = 1 := by
    intro i j hij
    simp only [tMat, Matrix.diagonal_apply_eq]
    split_ifs <;> first
      | omega
      | (simp; done)
      | (rw [← zpow_add₀ hϖ0]; convert zpow_zero ϖ using 2; rw [add_neg_eq_zero]; congr 1;
          simp only [Fin.mk.injEq]; omega)
      | (rw [← zpow_add₀ hϖ0]; convert zpow_zero ϖ using 2; rw [neg_add_eq_zero]; congr 1;
          simp only [Fin.mk.injEq]; omega)
  have hne : ∀ i, tMat ϖ n m a i i ≠ 0 := fun i h => by
    have hi := i.isLt
    have h2 := key i ⟨n - 1 - i, by omega⟩ (by show (i : ℕ) + (n - 1 - (i : ℕ)) + 1 = n; omega)
    rw [h, zero_mul] at h2
    exact zero_ne_one h2
  have hσd : ∀ i, σ (tMat ϖ n m a i i) = tMat ϖ n m a i i := by
    intro i
    simp only [tMat, Matrix.diagonal_apply_eq]
    split_ifs <;> simp [map_zpow₀, hσ]
  have hdiag : tMat ϖ n m a = Matrix.diagonal (fun i => tMat ϖ n m a i i) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · rw [Matrix.diagonal_apply_ne _ h, tMat, Matrix.diagonal_apply_ne _ h]
  have hinv1 : tMat ϖ n m a * Matrix.diagonal (fun i => (tMat ϖ n m a i i)⁻¹) = 1 := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      exact mul_inv_cancel₀ (hne i)
    · rw [if_neg h, tMat, Matrix.diagonal_apply_ne _ h, zero_mul]
  have hinv2 : Matrix.diagonal (fun i => (tMat ϖ n m a i i)⁻¹) * tMat ϖ n m a = 1 := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      exact inv_mul_cancel₀ (hne i)
    · rw [if_neg h, tMat, Matrix.diagonal_apply_ne _ h, mul_zero]
  refine ⟨⟨⟨tMat ϖ n m a, Matrix.diagonal (fun i => (tMat ϖ n m a i i)⁻¹), hinv1, hinv2⟩, ?_⟩, rfl⟩
  show cT σ (tMat ϖ n m a) * antiJ L n * tMat ϖ n m a = antiJ L n
  rw [hdiag, cT, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, hσd]
  rw [antiJ]
  split_ifs with h
  · rw [mul_one]
    exact key i j h
  · simp

theorem fSatake_diag_mem_K {d : GU σ n} {e : Fin n → L} (hd : ⟪d⟫ = Matrix.diagonal e)
    (hd' : ⟪d⁻¹⟫ = Matrix.diagonal (fun i => (e i)⁻¹)) (hv : ∀ i, Valued.v (e i) = 1) :
    d ∈ KU σ n := by
  have hne : ∀ i, e i ≠ 0 := fun i h => by
    have h1 := hv i
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  have hint : ∀ i, e i ∈ intL L := fun i => by
    rw [intL]
    exact (Valuation.mem_integer_iff _ _).2 (hv i).le
  have hint' : ∀ i, (e i)⁻¹ ∈ intL L := fun i => by
    rw [intL]
    exact (Valuation.mem_integer_iff _ _).2 (by rw [map_inv₀, hv i, inv_one])
  let D : Matrix (Fin n) (Fin n) (intL L) := Matrix.diagonal fun i => ⟨e i, hint i⟩
  let D' : Matrix (Fin n) (Fin n) (intL L) := Matrix.diagonal fun i => ⟨(e i)⁻¹, hint' i⟩
  have h1 : D * D' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact Subtype.ext (by simp [hne i])
  have h2 : D' * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact Subtype.ext (by simp [hne i])
  rw [KU, Subgroup.mem_subgroupOf, intPts, Subgroup.mem_inf]
  refine ⟨d.2, ⟨⟨D, D', h1, h2⟩, ?_⟩⟩
  rw [bc]
  ext i j
  change ((intL L).subtype.mapMatrix D) i j = ⟪d⟫ i j
  rw [hd]
  by_cases hij : i = j
  · subst hij
    simp [D]
  · simp [D, Matrix.diagonal_apply_ne _ hij]

theorem fSatake_K_int {k : GU σ n} (hk : k ∈ KU σ n) (i j : Fin n) : ⟪k⟫ i j ∈ intL L := by
  rw [KU, Subgroup.mem_subgroupOf, intPts, Subgroup.mem_inf] at hk
  obtain ⟨g, hg⟩ := hk.2
  rw [← hg, bc]
  exact (g.val i j).2

private lemma isBorelU_mul {b c : GU σ n} (hb : IsBorelU b) (hc : IsBorelU c) :
    IsBorelU (b * c) := by
  have hB : Matrix.BlockTriangular ⟪b⟫ id := fun i j h => hb i j h
  have hC : Matrix.BlockTriangular ⟪c⟫ id := fun i j h => hc i j h
  intro i j hij
  show (⟪b⟫ * ⟪c⟫) i j = 0
  exact (hB.mul hC) hij

private lemma isBorelU_inv {b : GU σ n} (hb : IsBorelU b) : IsBorelU b⁻¹ := by
  have hB : Matrix.BlockTriangular ⟪b⟫ id := fun i j h => hb i j h
  letI : Invertible ⟪b⟫ := Units.invertible _
  have hinv : ⟪b⁻¹⟫ = (⟪b⟫)⁻¹ := by simp [Matrix.coe_units_inv]
  intro i j hij
  change ⟪b⁻¹⟫ i j = 0
  rw [hinv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hB hij

private lemma ordL_zpow_uniformizer {ϖ : L} (hϖ : Valued.v ϖ = ↑(Multiplicative.ofAdd (-1 : ℤ))) (a : ℤ) :
    ordL (ϖ ^ a) = a := by
  have hv : Valued.v (ϖ ^ a) = ((Multiplicative.ofAdd (-a) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [map_zpow₀, hϖ, ← WithZero.coe_zpow]
    congr 1
    rw [← ofAdd_zsmul]
    simp
  have hne : Valued.v (ϖ ^ a) ≠ 0 := by
    rw [hv]
    exact WithZero.coe_ne_zero
  rw [ordL, dif_neg hne]
  have h2 : WithZero.unzero hne = Multiplicative.ofAdd (-a) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, hv]
  rw [h2, toAdd_ofAdd, neg_neg]

private lemma isBorelU_sigma_diag_mul_opposite_diag {b : GU σ n} (hb : IsBorelU b) (i j : Fin n)
    (hij : (i : ℕ) + j + 1 = n) : σ (⟪b⟫ i i) * ⟪b⟫ j j = 1 := by
  have hB : ∀ p q : Fin n, q < p → ⟪b⟫ p q = 0 := fun p q h => hb p q h
  have hG : cT σ ⟪b⟫ * antiJ L n * ⟪b⟫ = antiJ L n := b.2
  have hG' := congrFun (congrFun hG i) j
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, antiJ] at hG'
  rw [if_pos hij, Finset.sum_eq_single j] at hG'
  · rw [Finset.sum_eq_single i, if_pos hij, mul_one] at hG'
    · exact hG'
    · intro p _ hp
      rw [if_neg (fun h => hp (Fin.ext (by omega))), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro q _ hq
    rcases lt_or_gt_of_ne hq with hlt | hgt
    · have hlt' := Fin.lt_iff_val_lt_val.mp hlt
      rw [Finset.sum_eq_zero, zero_mul]
      intro p _
      by_cases hp : (p : ℕ) + q + 1 = n
      · rw [hB p i (Fin.lt_iff_val_lt_val.mpr (by omega)), map_zero, zero_mul]
      · rw [if_neg hp, mul_zero]
    · rw [hB q j hgt, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma isBorelU_mul_diag {A B : GU σ n} (hA : IsBorelU A) (hB : IsBorelU B) (i : Fin n) :
    ⟪A * B⟫ i i = ⟪A⟫ i i * ⟪B⟫ i i := by
  show (⟪A⟫ * ⟪B⟫) i i = _
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hA i l h, zero_mul]
    · rw [hB l i h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma tMat_diag_mul_opposite_diag {ϖ : L} (hϖ0 : ϖ ≠ 0) {m : ℕ} (hm : 2 * m ≤ n) (a : Fin m → ℤ)
    (i j : Fin n) (hij : (i : ℕ) + j + 1 = n) : tMat ϖ n m a i i * tMat ϖ n m a j j = 1 := by
  simp only [tMat, Matrix.diagonal_apply_eq]
  split_ifs <;> first
    | omega
    | (simp; done)
    | (rw [← zpow_add₀ hϖ0]; convert zpow_zero ϖ using 2; rw [add_neg_eq_zero]; congr 1;
        simp only [Fin.mk.injEq]; omega)
    | (rw [← zpow_add₀ hϖ0]; convert zpow_zero ϖ using 2; rw [neg_add_eq_zero]; congr 1;
        simp only [Fin.mk.injEq]; omega)

private lemma sigma_tMat_diag {ϖ : L} (hσ : σ ϖ = ϖ) {m : ℕ} (a : Fin m → ℤ) (i : Fin n) :
    σ (tMat ϖ n m a i i) = tMat ϖ n m a i i := by
  simp only [tMat, Matrix.diagonal_apply_eq]
  split_ifs <;> simp [map_zpow₀, hσ]

private lemma valuation_eq_ofAdd_neg_ordL {x : L} (hx : x ≠ 0) :
    Valued.v x = ↑(Multiplicative.ofAdd (-ordL x)) := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  rw [ordL, dif_neg hv, neg_neg, ofAdd_toAdd, WithZero.coe_unzero]

private lemma valuation_zpow_uniformizer {ϖ : L} (hϖ : Valued.v ϖ = ↑(Multiplicative.ofAdd (-1 : ℤ))) (a : ℤ) :
    Valued.v (ϖ ^ a) = ((Multiplicative.ofAdd (-a) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rw [map_zpow₀, hϖ, ← WithZero.coe_zpow]
  congr 1
  rw [← ofAdd_zsmul]
  simp

private lemma withZero_eq_one_of_mul_self_eq_one {x : WithZero (Multiplicative ℤ)} (h : x * x = 1) : x = 1 := by
  have hx : x ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  obtain ⟨y, rfl⟩ := WithZero.ne_zero_iff_exists.mp hx
  rw [← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_inj] at h
  rw [← WithZero.coe_one, WithZero.coe_inj]
  have h3 := congrArg Multiplicative.toAdd h
  rw [toAdd_mul, toAdd_one] at h3
  have h2 : Multiplicative.toAdd y = 0 := by omega
  rw [← ofAdd_toAdd y, h2, ofAdd_zero]

theorem fSatake_cell_exists {ϖ : L} {q m : ℕ} (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n)
    (hm' : n ≤ 2 * m + 1) {b k : GU σ n} (hb : IsBorelU b) (hk : k ∈ KU σ n) :
    ∃ a : Fin m → ℤ, ∃ u : GU σ n, IsUnipU u ∧ ∃ k' ∈ KU σ n,
      ⟪b * k⟫ = tMat ϖ n m a * ⟪u⟫ * ⟪k'⟫ := by
  have hϖ : Valued.v ϖ = ↑(Multiplicative.ofAdd (-1 : ℤ)) := by
    obtain ⟨-, -, -, h, -⟩ := hU
    exact h
  have hσ : σ ϖ = ϖ := by
    obtain ⟨-, -, h, -⟩ := hU
    exact h
  have hσv : ∀ x, Valued.v (σ x) = Valued.v x := by
    obtain ⟨-, h, -⟩ := hU
    exact h
  have hϖ0 : ϖ ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have hbne : ∀ i, ⟪b⟫ i i ≠ 0 := fSatake_ne_zero_of_borel hb
  obtain ⟨a, ha⟩ : ∃ a : Fin m → ℤ, ∀ i : Fin m, ∀ hi : (i : ℕ) < n,
      a i = ordL (⟪b⟫ ⟨i, hi⟩ ⟨i, hi⟩) :=
    ⟨fun i => ordL (⟪b⟫ ⟨i, lt_of_lt_of_le i.isLt (by omega)⟩ ⟨i, lt_of_lt_of_le i.isLt (by omega)⟩),
      fun i hi => rfl⟩
  obtain ⟨t, ht⟩ := fSatake_tMat_exists hU hm a
  have htB : IsBorelU t := fSatake_borel_tMat ht
  have hT0 : ∀ i : Fin n, tMat ϖ n m a i i ≠ 0 := fun i h => by
    have hi := i.isLt
    have h2 := tMat_diag_mul_opposite_diag hϖ0 hm a i ⟨n - 1 - i, by omega⟩
      (by show (i : ℕ) + (n - 1 - (i : ℕ)) + 1 = n; omega)
    rw [h, zero_mul] at h2
    exact zero_ne_one h2
  obtain ⟨e, he⟩ : ∃ e : Fin n → L, ∀ i, e i = ⟪b⟫ i i * (tMat ϖ n m a i i)⁻¹ :=
    ⟨fun i => ⟪b⟫ i i * (tMat ϖ n m a i i)⁻¹, fun i => rfl⟩
  have he0 : ∀ i, e i ≠ 0 := fun i => by
    rw [he]
    exact mul_ne_zero (hbne i) (inv_ne_zero (hT0 i))
  have hrel : ∀ i j : Fin n, (i : ℕ) + j + 1 = n → σ (e i) * e j = 1 := by
    intro i j hij
    have h1 := isBorelU_sigma_diag_mul_opposite_diag hb i j hij
    have h2 := tMat_diag_mul_opposite_diag hϖ0 hm a i j hij
    rw [he, he, map_mul, map_inv₀, sigma_tMat_diag hσ a i]
    calc σ (⟪b⟫ i i) * (tMat ϖ n m a i i)⁻¹ * (⟪b⟫ j j * (tMat ϖ n m a j j)⁻¹)
        = (σ (⟪b⟫ i i) * ⟪b⟫ j j) * (tMat ϖ n m a i i * tMat ϖ n m a j j)⁻¹ := by ring
      _ = 1 := by rw [h1, h2, inv_one, mul_one]
  have hlow : ∀ i : Fin n, (i : ℕ) < m → Valued.v (e i) = 1 := by
    intro i hi
    have hT : tMat ϖ n m a i i = ϖ ^ (ordL (⟪b⟫ i i)) := by
      have h1 := fSatake_tMat_apply_lt ϖ a ⟨i, hi⟩ i.isLt
      rw [ha ⟨i, hi⟩ i.isLt] at h1
      exact h1
    rw [he, map_mul, map_inv₀, hT, valuation_zpow_uniformizer hϖ, valuation_eq_ofAdd_neg_ordL (hbne i)]
    exact mul_inv_cancel₀ WithZero.coe_ne_zero
  have hve : ∀ i, Valued.v (e i) = 1 := by
    intro i
    by_cases hi : (i : ℕ) < m
    · exact hlow i hi
    · have hin := i.isLt
      obtain ⟨j, hjv⟩ : ∃ j : Fin n, (j : ℕ) = n - 1 - i := ⟨⟨n - 1 - i, by omega⟩, rfl⟩
      have hij : (i : ℕ) + j + 1 = n := by omega
      have h1 := congrArg Valued.v (hrel i j hij)
      rw [map_mul, hσv, map_one] at h1
      by_cases hj : (j : ℕ) < m
      · rw [hlow j hj, mul_one] at h1
        exact h1
      · have hji : j = i := Fin.ext (by omega)
        rw [hji] at h1
        exact withZero_eq_one_of_mul_self_eq_one h1
  have hd1 : Matrix.diagonal e * Matrix.diagonal (fun i => (e i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (he0 i)
  have hd2 : Matrix.diagonal (fun i => (e i)⁻¹) * Matrix.diagonal e = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (he0 i)
  have hmemD : (⟨Matrix.diagonal e, Matrix.diagonal (fun i => (e i)⁻¹), hd1, hd2⟩ : GL (Fin n) L) ∈ GU σ n := by
    show cT σ (Matrix.diagonal e) * antiJ L n * Matrix.diagonal e = antiJ L n
    rw [cT, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [antiJ]
    split_ifs with h
    · rw [mul_one]
      exact hrel i j h
    · simp
  let D0 : GU σ n := ⟨⟨Matrix.diagonal e, Matrix.diagonal (fun i => (e i)⁻¹), hd1, hd2⟩, hmemD⟩
  have hD0 : ⟪D0⟫ = Matrix.diagonal e := rfl
  have hD0i : ⟪D0⁻¹⟫ = Matrix.diagonal (fun i => (e i)⁻¹) := rfl
  have hD0K : D0 ∈ KU σ n := fSatake_diag_mem_K hD0 hD0i hve
  have hD0B : IsBorelU D0 := fSatake_borel_of_diag hD0
  have htinv : ∀ i, ⟪t⁻¹⟫ i i = (tMat ϖ n m a i i)⁻¹ := fun i => by
    have h1 := isBorelU_mul_diag (isBorelU_inv htB) htB i
    rw [inv_mul_cancel, ht] at h1
    have h0 : ⟪(1 : GU σ n)⟫ i i = 1 := by simp
    rw [h0] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  have huB : IsBorelU (t⁻¹ * b * D0⁻¹) :=
    isBorelU_mul (isBorelU_mul (isBorelU_inv htB) hb) (isBorelU_inv hD0B)
  have hudiag : ∀ i, ⟪t⁻¹ * b * D0⁻¹⟫ i i = 1 := fun i => by
    rw [isBorelU_mul_diag (isBorelU_mul (isBorelU_inv htB) hb) (isBorelU_inv hD0B),
      isBorelU_mul_diag (isBorelU_inv htB) hb, htinv, hD0i, Matrix.diagonal_apply_eq, he]
    field_simp [hbne i, hT0 i]
  have huU : IsUnipU (t⁻¹ * b * D0⁻¹) := by
    unfold IsUnipU
    exact ⟨huB, hudiag⟩
  refine ⟨a, t⁻¹ * b * D0⁻¹, huU, D0 * k, (KU σ n).mul_mem hD0K hk, ?_⟩
  have hgrp : b * k = t * (t⁻¹ * b * D0⁻¹) * (D0 * k) := by group
  rw [hgrp]
  show ⟪t⟫ * ⟪t⁻¹ * b * D0⁻¹⟫ * ⟪D0 * k⟫ = _
  rw [ht]


theorem fSatake_cell_unique {ϖ : L} {q m : ℕ} (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n)
    {a a' : Fin m → ℤ} {u u' k k' : GU σ n} (hu : IsUnipU u) (hu' : IsUnipU u')
    (hk : k ∈ KU σ n) (hk' : k' ∈ KU σ n)
    (h : tMat ϖ n m a * ⟪u⟫ * ⟪k⟫ = tMat ϖ n m a' * ⟪u'⟫ * ⟪k'⟫) : a = a' := by
  have hϖ0 : ϖ ≠ 0 := by
    intro h; have := hU.2.2.2.1; rw [h, Valuation.map_zero] at this; exact absurd this WithZero.zero_ne_coe
  obtain ⟨t, ht⟩ := fSatake_tMat_exists hU hm a
  obtain ⟨t', ht'⟩ := fSatake_tMat_exists hU hm a'
  have htb := fSatake_borel_tMat ht
  have htb' := fSatake_borel_tMat ht'
  have hx : t * u * k = t' * u' * k' := by
    apply Subtype.ext; apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, ht, ht']
    exact h
  have hwk : (t' * u')⁻¹ * (t * u) = k' * k⁻¹ := by
    calc (t' * u')⁻¹ * (t * u) = (t' * u')⁻¹ * (t * u * k) * k⁻¹ := by group
      _ = (t' * u')⁻¹ * (t' * u' * k') * k⁻¹ := by rw [hx]
      _ = k' * k⁻¹ := by group
  have hwK : (t' * u')⁻¹ * (t * u) ∈ KU σ n := by rw [hwk]; exact mul_mem hk' (inv_mem hk)
  have hb1 := fSatake_borel_mul htb hu.1
  have hb2 := fSatake_borel_mul htb' hu'.1
  have hwb : IsBorelU ((t' * u')⁻¹ * (t * u)) := fSatake_borel_mul (fSatake_borel_inv hb2) hb1
  have htu : t * u = (t' * u') * ((t' * u')⁻¹ * (t * u)) := by group
  funext j
  have hj : (j : ℕ) < n := by omega
  have hdiag : ⟪t * u⟫ ⟨j, hj⟩ ⟨j, hj⟩ = ⟪(t' * u') * ((t' * u')⁻¹ * (t * u))⟫ ⟨j, hj⟩ ⟨j, hj⟩ :=
    congrArg (fun z : GU σ n => ⟪z⟫ ⟨j, hj⟩ ⟨j, hj⟩) htu
  rw [fSatake_borel_diag_mul hb2 hwb, fSatake_borel_diag_mul htb hu.1,
    fSatake_borel_diag_mul htb' hu'.1, hu.2, hu'.2, ht, ht', mul_one, mul_one,
    fSatake_tMat_apply_lt ϖ a j hj, fSatake_tMat_apply_lt ϖ a' j hj] at hdiag
  set w := (t' * u')⁻¹ * (t * u)
  have hw0 : ⟪w⟫ ⟨j, hj⟩ ⟨j, hj⟩ ≠ 0 := fSatake_ne_zero_of_borel hwb _
  have hwr0 := fSatake_ne_zero_of_borel hwb (⟨j, hj⟩ : Fin n).rev
  have hpair := congrArg ordL (fSatake_unit_diag hwb ⟨j, hj⟩)
  rw [fSatake_ord_mul ((map_ne_zero σ).2 hw0) hwr0, fSatake_ord_of_v (hU.2.1 _),
    fSatake_ord_one] at hpair
  have hn1 := fSatake_ord_nonneg hw0 (fSatake_K_int hwK _ _)
  have hn2 := fSatake_ord_nonneg hwr0 (fSatake_K_int hwK _ _)
  have h3 := congrArg ordL hdiag
  rw [fSatake_ord_mul (zpow_ne_zero _ hϖ0) hw0, fSatake_ord_zpow hU.2.2.2.1,
    fSatake_ord_zpow hU.2.2.2.1] at h3
  omega

theorem fSatake_phi_cell {ϖ : L} {q m : ℕ} (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n)
    {α : Fin m → ℂ} {φ : GU σ n → ℂ} (hφ : IsSphericalU q α φ) {x u k : GU σ n}
    {a : Fin m → ℤ} (hu : IsUnipU u) (hk : k ∈ KU σ n)
    (hx : ⟪x⟫ = tMat ϖ n m a * ⟪u⟫ * ⟪k⟫) :
    φ x = (∏ i : Fin m, α i ^ (a i) * (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) *
      φ 1 := by
  obtain ⟨huB, hu1⟩ := hu
  have hϖ : Valued.v ϖ = ↑(Multiplicative.ofAdd (-1 : ℤ)) := by
    obtain ⟨-, -, -, h, -⟩ := hU
    exact h
  obtain ⟨t, ht⟩ := fSatake_tMat_exists hU hm a
  have htB : IsBorelU t := fSatake_borel_tMat ht
  have hxe : x = t * u * k := by
    apply Subtype.ext
    apply Units.ext
    show ⟪x⟫ = ⟪t⟫ * ⟪u⟫ * ⟪k⟫
    rw [hx, ht]
  have h1 := hφ (t * u) 1 k (isBorelU_mul htB huB) hk
  rw [mul_one] at h1
  rw [hxe, h1]
  congr 1
  rw [chiDeltaU]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hi : (i : ℕ) < n := lt_of_lt_of_le i.isLt (by omega)
  have hd : ⟪t * u⟫ ⟨i, hi⟩ ⟨i, hi⟩ = ϖ ^ (a i) := by
    show (⟪t⟫ * ⟪u⟫) ⟨i, hi⟩ ⟨i, hi⟩ = _
    rw [ht, tMat, Matrix.diagonal_mul, hu1, mul_one]
    simp [i.isLt]
  rw [dif_pos hi, hd, ordL_zpow_uniformizer hϖ]

theorem fSatake_vanish (hSph : SphericalExistsU) [CompleteSpace L] {ϖ : L} {q m : ℕ}
    (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n) (hm' : n ≤ 2 * m + 1) {α : Fin m → ℂ}
    (hα : ∀ i, α i ≠ 0) {φ : GU σ n → ℂ} (hφ : IsSphericalU q α φ) (x : GU σ n)
    (hx : ¬ ∃ b k : GU σ n, IsBorelU b ∧ k ∈ KU σ n ∧ x = b * k) : φ x = 0 := by
  classical
  obtain ⟨φ0, -, -, huniq⟩ := hSph L ϖ σ q n m hU hm hm' α hα
  have hP : ∀ b g k : GU σ n, IsBorelU b → k ∈ KU σ n →
      ((∃ b' k' : GU σ n, IsBorelU b' ∧ k' ∈ KU σ n ∧ b * g * k = b' * k') ↔
        (∃ b' k' : GU σ n, IsBorelU b' ∧ k' ∈ KU σ n ∧ g = b' * k')) := by
    intro b g k hb hk
    constructor
    · rintro ⟨b', k', hb', hk', he⟩
      refine ⟨b⁻¹ * b', k' * k⁻¹, isBorelU_mul (isBorelU_inv hb) hb',
        (KU σ n).mul_mem hk' ((KU σ n).inv_mem hk), ?_⟩
      calc g = b⁻¹ * (b * g * k) * k⁻¹ := by group
        _ = b⁻¹ * b' * (k' * k⁻¹) := by rw [he]; group
    · rintro ⟨b', k', hb', hk', he⟩
      refine ⟨b * b', k' * k, isBorelU_mul hb hb', (KU σ n).mul_mem hk' hk, ?_⟩
      rw [he]
      group
  let ψ : GU σ n → ℂ := fun g =>
    if (∃ b' k' : GU σ n, IsBorelU b' ∧ k' ∈ KU σ n ∧ g = b' * k') then φ g else 0
  have hψ : IsSphericalU q α ψ := by
    intro b g k hb hk
    by_cases hg : ∃ b' k' : GU σ n, IsBorelU b' ∧ k' ∈ KU σ n ∧ g = b' * k'
    · have h1 := (hP b g k hb hk).2 hg
      simp only [ψ, if_pos h1, if_pos hg]
      exact hφ b g k hb hk
    · have h1 : ¬ ∃ b' k' : GU σ n, IsBorelU b' ∧ k' ∈ KU σ n ∧ b * g * k = b' * k' :=
        fun h => hg ((hP b g k hb hk).1 h)
      simp only [ψ, if_neg h1, if_neg hg, mul_zero]
  have hψ1 : ψ 1 = φ 1 := by
    simp only [ψ]
    exact if_pos ⟨1, 1, fSatake_borel_one, (KU σ n).one_mem, by simp⟩
  have hψx : ψ x = 0 := by
    simp only [ψ]
    exact if_neg hx
  have e1 : ψ x = ψ 1 * φ0 x := congrFun (huniq ψ hψ) x
  have e2 : φ x = φ 1 * φ0 x := congrFun (huniq φ hφ) x
  rw [e2, ← hψ1, ← e1, hψx]

end Formalism.UG.P
end
end

section
open Formalism.UG

noncomputable section

namespace Formalism.UG.P

theorem finsum_mul_eq_sum_over_classes {X Y : Type} (S : Finset X) (g φv : X → ℂ) (c : Y → ℂ) (φ1 : ℂ)
    (P : Y → X → Prop) {_ : ∀ y x, Decidable (P y x)}
    (hS : ∀ x, g x ≠ 0 → x ∈ S) (huniq : ∀ x y y', P y x → P y' x → y = y')
    (hφ : ∀ x y, P y x → φv x = c y * φ1) (hnone : ∀ x, (∀ y, ¬ P y x) → φv x = 0) :
    ∑ᶠ x, g x * φv x = (∑ᶠ y, c y * ∑ᶠ x, if P y x then g x else 0) * φ1 := by
  classical
  have hsl : Function.support (fun x => g x * φv x) ⊆ (S : Set X) :=
    fun x hx => hS x (left_ne_zero_of_mul hx)
  have hin : ∀ y, (∑ᶠ x, if P y x then g x else 0) = ∑ x ∈ S, if P y x then g x else 0 := by
    intro y
    apply finsum_eq_sum_of_support_subset
    intro x hx
    by_cases hP : P y x
    · exact hS x (by simpa [hP] using hx)
    · exact absurd (by simp [hP]) hx
  have hTfin : (⋃ x ∈ (S : Set X), {y | P y x}).Finite :=
    S.finite_toSet.biUnion fun x _ => Set.Subsingleton.finite fun y hy y' hy' => huniq x y y' hy hy'
  have hout : (∑ᶠ y, c y * ∑ x ∈ S, if P y x then g x else 0) =
      ∑ y ∈ hTfin.toFinset, c y * ∑ x ∈ S, if P y x then g x else 0 := by
    apply finsum_eq_sum_of_support_subset
    intro y hy
    rw [Set.Finite.coe_toFinset]
    have hne : (∑ x ∈ S, if P y x then g x else 0) ≠ 0 := right_ne_zero_of_mul hy
    obtain ⟨x, hxS, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    refine Set.mem_biUnion (Finset.mem_coe.mpr hxS) ?_
    by_contra hP
    exact hx (if_neg hP)
  rw [finsum_eq_sum_of_support_subset _ hsl]
  simp only [hin]
  rw [hout, Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hxS => ?_
  by_cases hex : ∃ y, P y x
  · obtain ⟨y0, hy0⟩ := hex
    have hy0T : y0 ∈ hTfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact Set.mem_biUnion (Finset.mem_coe.mpr hxS) hy0
    rw [Finset.sum_eq_single y0, if_pos hy0, hφ x y0 hy0]
    · ring
    · intro y _ hy
      rw [if_neg (fun h => hy (huniq x y y0 h hy0))]
      ring
    · intro h
      exact absurd hy0T h
  · push_neg at hex
    rw [hnone x hex, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro y _
    rw [if_neg (hex y)]
    ring

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem fSatake_chiDelta_one {q m : ℕ} (α : Fin m → ℂ) :
    chiDeltaU (σ := σ) (n := n) q α 1 = 1 := by
  unfold chiDeltaU
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs with h
  · simp [fSatake_ord_one]
  · rfl

theorem fSatake_key (hSph : SphericalExistsU) [CompleteSpace L] {ϖ : L} {q m : ℕ}
    (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n) (hm' : n ≤ 2 * m + 1) {α : Fin m → ℂ}
    (hα : ∀ i, α i ≠ 0) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) {φ : GU σ n → ℂ}
    (hφ : IsSphericalU q α φ) :
    ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out * φ x.out = SatU ϖ q h α * φ 1 := by
  classical
  have hfin := finite_supp (KU σ n) (isCommensurated_integral_unitary_of_unramified hU n) h hh
  unfold SatU
  exact finsum_mul_eq_sum_over_classes (S := hfin.toFinset) (g := fun x => h x.out) (φv := fun x => φ x.out)
    (c := fun a : Fin m → ℤ =>
      ∏ i : Fin m, α i ^ (a i) * (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ))))
    (φ1 := φ 1)
    (P := fun a x => ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n,
      (((x.out : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n m a * (((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (((k : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))
    (fun x hx => hfin.mem_toFinset.mpr hx)
    (fun x a a' ⟨u, hu, k, hk, e⟩ ⟨u', hu', k', hk', e'⟩ =>
      fSatake_cell_unique hU hm hu hu' hk hk' (e.symm.trans e'))
    (fun x a ⟨u, hu, k, hk, e⟩ => fSatake_phi_cell hU hm hφ hu hk e)
    (fun x hx => fSatake_vanish hSph hU hm hm' hα hφ x.out (by
      rintro ⟨b, k, hb, hk, e⟩
      obtain ⟨a, u, hu, k', hk', e'⟩ := fSatake_cell_exists hU hm hm' hb hk
      exact hx a ⟨u, hu, k', hk', e ▸ e'⟩))

theorem fSatake_hAct_sph {q m : ℕ} {α : Fin m → ℂ} {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n))
    {φ : GU σ n → ℂ} (hφ : IsSphericalU q α φ) : IsSphericalU q α (hAct (KU σ n) h φ) := by
  intro b g k hb hk
  have hb1 : IsBorelU (1 : GU σ n) := fun i j hij => by
    simp [Matrix.one_apply_ne (ne_of_lt hij).symm]
  have hr : ∀ (y κ : GU σ n), κ ∈ KU σ n → φ (y * κ) = φ y := fun y κ hκ => by
    have := hφ 1 y κ hb1 hκ
    simpa [fSatake_chiDelta_one] using this
  have hl : ∀ y : GU σ n, φ (b * y) = chiDeltaU q α b * φ y := fun y => by
    have := hφ b y 1 hb (KU σ n).one_mem
    simpa using this
  obtain ⟨hbi, -⟩ := hh
  unfold hAct
  calc ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out • φ (b * g * k * x.out)
      = ∑ᶠ x : GU σ n ⧸ KU σ n, chiDeltaU q α b * (h x.out • φ (g * (k * x.out))) := by
        refine finsum_congr fun x => ?_
        rw [show b * g * k * x.out = b * (g * (k * x.out)) by group, hl, smul_eq_mul, smul_eq_mul]
        ring
    _ = chiDeltaU q α b * ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out • φ (g * (k * x.out)) :=
        (mul_finsum _ _).symm
    _ = chiDeltaU q α b * ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out • φ (g * x.out) := by
        congr 1
        symm
        rw [← finsum_comp_equiv (MulAction.toPerm k : (GU σ n ⧸ KU σ n) ≃ (GU σ n ⧸ KU σ n))]
        refine finsum_congr fun x => ?_
        obtain ⟨κ, hκ⟩ := out_smul (KU σ n) k x
        simp only [MulAction.toPerm_apply]
        rw [hκ]
        have e1 : h (k * x.out * κ) = h x.out := hbi ⟨k, hk⟩ κ x.out
        rw [e1, show g * (k * x.out * κ) = g * (k * x.out) * κ by group, hr _ _ κ.2]

theorem satake_transform_inert_prime (hSphericalExistsU : Formalism.UG.SphericalExistsU) : Formalism.UG.SatakeInert := by
  intro L _ _ _ ϖ σ q n m hU hm hm' α hα h hh φ hφ
  obtain ⟨φ0, -, -, huniq⟩ := hSphericalExistsU L ϖ σ q n m hU hm hm' α hα
  have h1 := huniq _ (fSatake_hAct_sph hh hφ)
  have h2 := huniq _ hφ
  have hv : hAct (KU σ n) h φ 1 = SatU ϖ q h α * φ 1 := by
    unfold hAct
    simp only [one_mul, smul_eq_mul]
    exact fSatake_key hSphericalExistsU hU hm hm' hα hh hφ
  rw [h1, hv]
  conv_rhs => rw [h2]
  funext g
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem satake_transform_multiplicative (hSphericalExistsU : Formalism.UG.SphericalExistsU) : Formalism.UG.SatMul := by
  intro L _ _ _ ϖ σ q n m hU hm hm' α hα h₁ hh₁ h₂ hh₂
  obtain ⟨φ0, hφ0, hφ01, -⟩ := hSphericalExistsU L ϖ σ q n m hU hm hm' α hα
  have hSI := satake_transform_inert_prime hSphericalExistsU L ϖ σ q n m hU hm hm' α hα
  have hh₁' := hh₁
  have hh₂' := hh₂
  obtain ⟨hb₁, hs₁⟩ := hh₁'
  obtain ⟨hb₂, hs₂⟩ := hh₂'
  have hconv : conv (KU σ n) h₁ h₂ ∈ Hecke ℂ (KU σ n) := by
    show _ ∧ _
    exact ⟨conv_biInv _ _ _ hb₁ hb₂, conv_finDosetSupp (isCommensurated_integral_unitary_of_unramified hU n) _ _ hs₁ hs₂⟩
  have hb1 : IsBorelU (1 : GU σ n) := fun i j hij => by
    simp [Matrix.one_apply_ne (ne_of_lt hij).symm]
  have hamf : φ0 ∈ AMF ℂ (⊥ : Subgroup (GU σ n)) (KU σ n)
      (1 : Representation ℂ (⊥ : Subgroup (GU σ n)) ℂ) := by
    intro γ g κ
    have hγ : (γ : GU σ n) = 1 := Subgroup.mem_bot.mp γ.2
    rw [hγ, one_mul]
    have := hφ0 1 g κ hb1 κ.2
    simpa [fSatake_chiDelta_one] using this
  have hmul := hecke_act_mul (GU σ n) ⊥ (KU σ n) ℂ ℂ 1 (isCommensurated_integral_unitary_of_unramified hU n) h₁ hh₁ h₂ hh₂ φ0 hamf
  have hs2 : IsSphericalU q α (SatU ϖ q h₂ α • φ0) := fun b g k hb hk => by
    simp only [Pi.smul_apply, smul_eq_mul, hφ0 b g k hb hk]
    ring
  rw [hSI _ hconv _ hφ0, hSI _ hh₂ _ hφ0, hSI _ hh₁ _ hs2] at hmul
  have := congrFun hmul 1
  simp only [Pi.smul_apply, smul_eq_mul, hφ01, mul_one] at this
  rw [this]

end Formalism.UG.P
end
end

section
namespace Formalism.UG.P

theorem satake_inert : Formalism.UG.SatakeInert := satake_transform_inert_prime exists_spherical_function_unitary

theorem satake_mul : Formalism.UG.SatMul := satake_transform_multiplicative exists_spherical_function_unitary

end Formalism.UG.P
end
