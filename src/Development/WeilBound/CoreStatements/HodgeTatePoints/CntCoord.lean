import Development.WeilBound.CoreStatements.HodgeTatePoints.RaCpaf
import ReciprocityTheory.DualLattices.BlockOneMulMulBlockOne
import ReciprocityTheory.DualLattices.SumValCoord
import ReciprocityTheory.DualLattices.ProdDvdOfIso
import Mathlib
import ReciprocityTheory.DualLattices.PrimeHopfOrderOfAddEquiv
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.WeilBound.CoreStatements.HodgeTatePoints.FormMemLin

section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Ra

section lattice

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem exists_smith_basis (hv : v.Integers R) {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : Submodule R (ι → R)) (hL : L.FG) :
    ∃ (Λ : Matrix ι ι R) (ε : ι → R), IsUnit Λ.det ∧
      L = Submodule.span R (Set.range fun j => ε j • Λ j) := by
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hL
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let A : Matrix (Fin (Fintype.card ι)) (Fin m) R := Matrix.of fun i k => g k (e.symm i)
  obtain ⟨P, Q, a, hP, hQ, hD⟩ := ReciprocityTheory.PGsh.Up.Smith.smith_mat hv _ m A
  have hPv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hP
  have hQv : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ hQ
  have hAQ : A * Q = P⁻¹ * (P * A * Q) := by
    simp only [← Matrix.mul_assoc, hPv, Matrix.one_mul]
  have hA : A = P⁻¹ * (P * A * Q) * Q⁻¹ := by
    rw [← hAQ, Matrix.mul_assoc, hQv, Matrix.mul_one]
  let Λ : Matrix ι ι R := Matrix.of fun j i => P⁻¹ (e i) (e j)
  let ε : ι → R := fun j => if (e j : ℕ) < m then a (e j) else 0
  have hΛ : Λ = ((P⁻¹).submatrix e e)ᵀ := by
    ext j i; rfl
  have hdet : IsUnit Λ.det := by
    rw [hΛ, Matrix.det_transpose, Matrix.det_submatrix_equiv_self]
    exact (Matrix.isUnit_nonsing_inv_det_iff).2 hP
  refine ⟨Λ, ε, hdet, le_antisymm ?_ ?_⟩
  · rw [← hg, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    have hgl : g l = ∑ k : Fin m, ∑ j : Fin (Fintype.card ι),
        (Q⁻¹ k l * (P * A * Q) j k) • Λ (e.symm j) := by
      ext i
      have h1 : A (e i) l = (P⁻¹ * (P * A * Q) * Q⁻¹) (e i) l := by rw [← hA]
      have h2 : A (e i) l = g l i := by simp [A]
      rw [← h2, h1, Matrix.mul_apply]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply (M := P⁻¹)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Λ, Matrix.of_apply, Equiv.apply_symm_apply]
      ring
    rw [SetLike.mem_coe, hgl]
    refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun j _ => ?_
    rw [hD j k]
    by_cases hkj : (k : ℕ) = (j : ℕ)
    · have hj : ((e (e.symm j)) : ℕ) < m := by
        rw [Equiv.apply_symm_apply, ← hkj]; exact k.2
      have hε : ε (e.symm j) = a j := by
        simp only [ε, if_pos hj, Equiv.apply_symm_apply]
      rw [if_pos hkj, mul_smul, ← hε]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e.symm j, rfl⟩)
    · rw [if_neg hkj, mul_zero, zero_smul]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show ε j • Λ j ∈ L
    by_cases hj : (e j : ℕ) < m
    · have hsum : ε j • Λ j = ∑ l : Fin m, Q l ⟨e j, hj⟩ • g l := by
        ext i
        have h1 : (A * Q) (e i) ⟨e j, hj⟩ = (P⁻¹ * (P * A * Q)) (e i) ⟨e j, hj⟩ := by rw [← hAQ]
        have h2 : (A * Q) (e i) ⟨e j, hj⟩ = ∑ l, Q l ⟨e j, hj⟩ * g l i := by
          rw [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun l _ => ?_
          simp [A, mul_comm]
        have h3 : (P⁻¹ * (P * A * Q)) (e i) ⟨e j, hj⟩ = a (e j) * P⁻¹ (e i) (e j) := by
          rw [Matrix.mul_apply, Finset.sum_eq_single (e j)]
          · rw [hD]; simp [mul_comm]
          · intro b _ hb
            rw [hD, if_neg, mul_zero]
            intro h
            exact hb (Fin.ext h.symm)
          · intro h; exact absurd (Finset.mem_univ _) h
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [← h2, h1, h3]
        simp only [ε, if_pos hj, Λ, Matrix.of_apply]
      rw [hsum, ← hg]
      exact Submodule.sum_mem _ fun l _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    · have : ε j = 0 := if_neg hj
      rw [this, zero_smul]
      exact Submodule.zero_mem _

noncomputable def rowEquiv {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R) (h : IsUnit Λ.det) :
    (ι → R) ≃ₗ[R] (ι → R) :=
  LinearEquiv.ofLinear (Matrix.vecMulLinear Λ) (Matrix.vecMulLinear Λ⁻¹)
    (LinearMap.ext fun x => by
      simp [Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ h])
    (LinearMap.ext fun x => by
      simp [Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ h])

theorem rowEquiv_apply {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R)
    (h : IsUnit Λ.det) (x : ι → R) : rowEquiv Λ h x = ∑ j, x j • Λ j := by
  show x ᵥ* Λ = _
  rw [Matrix.vecMul_eq_sum]

theorem map_rowEquiv {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R)
    (h : IsUnit Λ.det) (ε : ι → R) :
    (Submodule.pi Set.univ fun j => (Ideal.span {ε j} : Submodule R R)).map
        (rowEquiv Λ h : (ι → R) →ₗ[R] (ι → R)) =
      Submodule.span R (Set.range fun j => ε j • Λ j) := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.mem_comap]
    show rowEquiv Λ h x ∈ _
    rw [rowEquiv_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (hx j (Set.mem_univ j))
    rw [← hr, mul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j (ε j), ?_, ?_⟩
    · intro k _
      by_cases hk : k = j
      · subst hk
        simpa using Ideal.mem_span_singleton_self (ε k)
      · simp [Pi.single_eq_of_ne hk]
    · show rowEquiv Λ h _ = _
      rw [rowEquiv_apply, Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · intro hj; exact absurd (Finset.mem_univ _) hj

theorem dvd_of_smul_row_mem {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R)
    (h : IsUnit Λ.det) (ε : ι → R) (c : R) (j : ι)
    (hc : c • Λ j ∈ Submodule.span R (Set.range fun j => ε j • Λ j)) : ε j ∣ c := by
  rw [← map_rowEquiv Λ h ε] at hc
  obtain ⟨x, hx, hxe⟩ := hc
  have hx' : x = Pi.single j c := by
    apply (rowEquiv Λ h).injective
    have : rowEquiv Λ h x = c • Λ j := hxe
    rw [this, rowEquiv_apply, Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro hj; exact absurd (Finset.mem_univ _) hj
  have := hx j (Set.mem_univ j)
  rw [hx', Pi.single_eq_same] at this
  exact Ideal.mem_span_singleton.1 this

theorem hasLen_quot_rows {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R)
    (h : IsUnit Λ.det) (ε : ι → R) {M : Type} [AddCommGroup M] [Module R M]
    (E : M ≃ₗ[R] ((ι → R) ⧸ Submodule.span R (Set.range fun j => ε j • Λ j))) :
    HasLen v R M (∏ j, v (algebraMap R C (ε j))) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let T : Submodule R (ι → R) := Submodule.pi Set.univ fun j => (Ideal.span {ε j} : Submodule R R)
  have E1 : ((ι → R) ⧸ T) ≃ₗ[R] ((ι → R) ⧸ Submodule.span R (Set.range fun j => ε j • Λ j)) :=
    Submodule.Quotient.equiv T _ (rowEquiv Λ h) (map_rowEquiv Λ h ε)
  have E2 : ((ι → R) ⧸ T) ≃ₗ[R] ((j : ι) → R ⧸ Ideal.span {ε j}) :=
    Submodule.quotientPi fun j => (Ideal.span {ε j} : Submodule R R)
  have E3 := LinearEquiv.piCongrLeft R (fun j : ι => R ⧸ Ideal.span {ε j}) e.symm
  refine ⟨Fintype.card ι, fun i => ε (e.symm i), ⟨((E.trans E1.symm).trans E2).trans E3.symm⟩, ?_⟩
  exact Equiv.prod_comp e.symm fun j => v (algebraMap R C (ε j))

end lattice

theorem smith_of (hfg : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), (afLat p AA.carrier).FG)
    (hquot : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), Nonempty (AFQuot p AA.carrier ≃ₗ[R] ((ι → R) ⧸ afLat p AA.carrier))) :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∃ (Λ : Matrix ι ι R) (ε : ι → R), IsUnit Λ.det ∧ afLat p AA.carrier = Submodule.span R (Set.range fun j => ε j • Λ j) ∧ (∀ j, v (p : C) ≤ v (algebraMap R C (ε j)) ^ (p - 1)) ∧ HasLen v R (AFQuot p AA.carrier) (∏ j, v (algebraMap R C (ε j))) := by
  intro p _ C _ _ _ v R _ _ hv hp ι _ _ AA
  have hp1 : p - 1 ≠ 0 := by
    have := (Fact.out : p.Prime).two_le
    omega
  obtain ⟨-, -, cp, hcp, -, -⟩ := cpaf p C v R hv hp (ι → ZMod p) AA 0
  have hcoord : ∀ i, (Pi.single i cp : ι → R) ∈ afLat p AA.carrier := by
    intro i
    obtain ⟨g, hg, c, hc, -, h⟩ :=
      cpaf p C v R hv hp (ι → ZMod p) AA (Pi.evalAddMonoidHom _ i)
    have hvc : v (algebraMap R C cp) = v (algebraMap R C c) :=
      (pow_left_inj₀ zero_le zero_le hp1).1 (hcp.trans hc.symm)
    obtain ⟨u, hu⟩ : c ∣ cp := hv.dvd_of_le hvc.le
    have hmem : (Pi.single i c : ι → R) ∈ afLat p AA.carrier := by
      refine ⟨g, (Submodule.mem_inf.1 hg).1, fun x => ?_⟩
      have hs : ∑ k, (Pi.single i c : ι → R) k * ((x k).val : R) = c * ((x i).val : R) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb; simp [Pi.single_eq_of_ne hb]
        · intro hi; exact absurd (Finset.mem_univ _) hi
      rw [hs, map_mul, map_natCast]
      exact (h x).1
    have : (Pi.single i cp : ι → R) = u • (Pi.single i c : ι → R) := by
      ext k
      by_cases hk : k = i
      · subst hk; simp [hu, mul_comm]
      · simp [Pi.single_eq_of_ne hk]
    rw [this]
    exact Submodule.smul_mem _ _ hmem
  have hscale : ∀ l : ι → R, cp • l ∈ afLat p AA.carrier := by
    intro l
    have : cp • l = ∑ i, l i • (Pi.single i cp : ι → R) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hcoord i)
  obtain ⟨Λ, ε, hdet, hL⟩ := exists_smith_basis hv _ (hfg p C v R hv hp ι AA)
  refine ⟨Λ, ε, hdet, hL, fun j => ?_, ?_⟩
  · have hd : ε j ∣ cp := dvd_of_smul_row_mem Λ hdet ε cp j (hL ▸ hscale (Λ j))
    obtain ⟨t, ht⟩ := hd
    have hle : v (algebraMap R C cp) ≤ v (algebraMap R C (ε j)) := by
      rw [ht, map_mul, map_mul]
      exact mul_le_of_le_one_right' (hv.map_le_one t)
    rw [← hcp]
    exact pow_le_pow_left₀ zero_le hle _
  · obtain ⟨E⟩ := hquot p C v R hv hp ι AA
    exact hasLen_quot_rows Λ hdet ε (E.trans (Submodule.quotEquivOfEq _ _ hL))

end PositivityTheory.HtPt.Ra
end

section
noncomputable section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Ra

section Count

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

lemma monomialCount_col_mem_span {X : Type} [Fintype X] (B' : Matrix X X C) (V : Matrix X X R)
    (j : X) :
    (fun x => (B' * V.map (algebraMap R C)) x j) ∈
      Submodule.span R (Set.range fun α x => B' x α) := by
  have h : (fun x => (B' * V.map (algebraMap R C)) x j) = ∑ α, V α j • (fun x => B' x α) := by
    ext x
    simp [Matrix.mul_apply, Finset.sum_apply, Algebra.smul_def, mul_comm]
  rw [h]
  exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

lemma monomialCount_exists_factor {X : Type} [Fintype X] (B B' : Matrix X X C)
    (h : ∀ α, (fun x => B' x α) ∈ Submodule.span R (Set.range fun j x => B x j)) :
    ∃ W : Matrix X X R, B' = B * W.map (algebraMap R C) := by
  choose c hc using fun α => (Submodule.mem_span_range_iff_exists_fun R).1 (h α)
  refine ⟨fun i α => c α i, ?_⟩
  ext x α
  have := congrFun (hc α) x
  rw [Finset.sum_apply] at this
  simp only [Pi.smul_apply, Algebra.smul_def] at this
  rw [← this, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma monomialCount_prod_pow_mem {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (A : HopfOrder (C := C) R N) {ι : Type} [Fintype ι] (f : ι → N → C)
    (hf : ∀ j, f j ∈ A.carrier) (n : ι → ℕ) : (fun y => ∏ j, f j y ^ n j) ∈ A.carrier := by
  have hpow : ∀ j k, f j ^ k ∈ A.carrier := by
    intro j k
    induction k with
    | zero => simpa using A.one_mem
    | succ k ih => rw [pow_succ]; exact A.mul_mem _ _ ih (hf j)
  have : (fun y => ∏ j, f j y ^ n j) = ∏ j, f j ^ n j := by
    ext y; simp [Finset.prod_apply]
  rw [this]
  exact Finset.prod_induction _ (· ∈ A.carrier) (fun a b ha hb => A.mul_mem a b ha hb)
    A.one_mem (fun j _ => hpow j (n j))

end Count

lemma monomialCount_exponent (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : ι → NNReal) :
    (∏ j, a j) ^ (Fintype.card (ι → ZMod p) * (p - 1)) =
      (∏ j, a j ^ (p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2))) ^ 2 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hpos : 0 < Fintype.card ι := Fintype.card_pos
  have h2 : p * (p - 1) / 2 * 2 = p * (p - 1) :=
    Nat.div_mul_cancel (Nat.even_mul_pred_self p).two_dvd
  have h3 : p ^ (Fintype.card ι - 1) * p = p ^ Fintype.card ι := by
    rw [← pow_succ, Nat.sub_add_cancel hpos]
  have hcard : Fintype.card (ι → ZMod p) = p ^ Fintype.card ι := by
    simp [ZMod.card]
  rw [Finset.prod_pow, ← pow_mul, hcard]
  congr 1
  calc p ^ Fintype.card ι * (p - 1) = p ^ (Fintype.card ι - 1) * p * (p - 1) := by rw [h3]
    _ = p ^ (Fintype.card ι - 1) * (p * (p - 1)) := by ring
    _ = p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2 * 2) := by rw [h2]
    _ = p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2) * 2 := by ring

theorem cnt_coord_of (hsmith : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∃ (Λ : Matrix ι ι R) (ε : ι → R), IsUnit Λ.det ∧ afLat p AA.carrier = Submodule.span R (Set.range fun j => ε j • Λ j) ∧ (∀ j, v (p : C) ≤ v (algebraMap R C (ε j)) ^ (p - 1)) ∧ HasLen v R (AFQuot p AA.carrier) (∏ j, v (algebraMap R C (ε j)))) :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = cN ^ 2 → ∃ x : ι → (ι → ZMod p) → C, (∀ j, x j ∈ afFun p AA.carrier) ∧ AA.carrier = Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) => ∏ j, x j y ^ (α j).val)) := by
  intro p _ C _ _ _ v R _ _ hv hp1 ι _ _ AA cA cN hA hN
  obtain ⟨Λ, ε, hΛ, hspan, hε, hlen⟩ := hsmith p C v R hv hp1 ι AA
  have hcA : cA = ∏ j, v (algebraMap R C (ε j)) := hasLen_unique hv hA hlen
  have hl := fun j => lifts p C v R hv hp1 ι AA (Λ j) (ε j)
    (by rw [hspan]; exact Submodule.subset_span ⟨j, rfl⟩) (hε j)
  choose u hu_mem hu_int hu_cong using hl

  let B' : Matrix (ι → ZMod p) (ι → ZMod p) C := Matrix.of fun (x α : ι → ZMod p) =>
    ∏ j, (algebraMap R C (ε j) * u j x) ^ (α j).val
  have hB'v : v B'.det = ∏ j, v (algebraMap R C (ε j)) ^
      (p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2)) :=
    (u5 p C v R hv hp1 ι Λ u hΛ hu_int hu_cong).2 fun j => algebraMap R C (ε j)
  have hsq : cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = v B'.det ^ 2 := by
    rw [hcA, hB'v]
    exact monomialCount_exponent p _

  have hp0 : v (p : C) ≠ 0 :=
    (Valuation.ne_zero_iff v).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hε0 : ∀ j, v (algebraMap R C (ε j)) ≠ 0 := by
    intro j h0
    have hpp : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
    have := hε j
    rw [h0, zero_pow hpp] at this
    exact hp0 (le_antisymm this zero_le)
  have hB'0 : v B'.det ≠ 0 := by
    rw [hB'v]
    exact Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (hε0 j)

  have hmem : ∀ α : ι → ZMod p, (fun x => B' x α) ∈ AA.carrier := by
    intro α
    exact monomialCount_prod_pow_mem AA (fun j y => algebraMap R C (ε j) * u j y)
      (fun j => (Submodule.mem_inf.1 (hu_mem j)).1) (fun j => (α j).val)
  obtain ⟨B, hAA, hBc⟩ := hN
  obtain ⟨W, hW⟩ := monomialCount_exists_factor (R := R) B B' (fun α => hAA ▸ hmem α)
  have hdet : v B'.det = cN * v (algebraMap R C W.det) := by
    rw [hW, Matrix.det_mul, map_mul, RingHom.map_det, hBc]; rfl
  have hw1 : v (algebraMap R C W.det) ≤ 1 := hv.map_le_one W.det
  have hle : v B'.det ≤ cN := by
    rw [hdet]; exact mul_le_of_le_one_right zero_le hw1
  refine ⟨by rw [hsq]; exact pow_le_pow_left₀ zero_le hle 2, fun heq => ?_⟩
  have hBeq : v B'.det = cN := by
    rw [hsq] at heq
    exact (pow_left_inj₀ zero_le zero_le two_ne_zero).1 heq
  have hcN0 : cN ≠ 0 := hBeq ▸ hB'0
  have hw : v (algebraMap R C W.det) = 1 := by
    have h : cN * v (algebraMap R C W.det) = cN * 1 := by rw [← hdet, hBeq, mul_one]
    exact mul_left_cancel₀ hcN0 h
  have hWu : IsUnit W.det :=
    hv.isUnit_of_one (isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hw) hw
  have hBeq' : B' * (W⁻¹).map (algebraMap R C) = B := by
    rw [hW, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hWu,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  refine ⟨fun j y => algebraMap R C (ε j) * u j y, hu_mem, ?_⟩
  have hspan' : Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) =>
      ∏ j, (algebraMap R C (ε j) * u j y) ^ (α j).val) =
      Submodule.span R (Set.range fun α x => B' x α) := rfl
  rw [hspan']
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rw [hAA]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    have := monomialCount_col_mem_span (R := R) B' (W⁻¹) j
    rwa [hBeq'] at this
  · rintro _ ⟨α, rfl⟩
    exact hmem α

end PositivityTheory.HtPt.Ra
end
end

section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

section

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X Y : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]
  [AddCommGroup Y] [Fintype Y] [DecidableEq Y]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
lemma comp_mem_addFun (p : ℕ) (e : X ≃+ Y) {f : Y → C} (hf : f ∈ addFun R p Y) :
    (fun x => f (e x)) ∈ addFun R p X := by
  have h : ∀ a b : Y, f (a + b) - f a - f b ∈ pInt R p := hf
  show ∀ a b : X, f (e (a + b)) - f (e a) - f (e b) ∈ pInt R p
  intro a b
  rw [map_add]
  exact h (e a) (e b)

private theorem map_pbE_eq_of_addEquiv (e : X ≃+ Y) (SX : Submodule R (X → C)) (SY : Submodule R (Y → C))
    (h1 : ∀ f ∈ SY, (fun x => f (e x)) ∈ SX) (h2 : ∀ g ∈ SX, (fun y => g (e.symm y)) ∈ SY) :
    SY.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = SX := by
  ext g
  rw [Submodule.mem_map_equiv]
  constructor
  · intro h
    have h3 := h1 _ h
    convert h3 using 1
    funext x
    rw [pbE_symm_apply]
    simp
  · intro h
    convert h2 g h using 1
    funext y
    exact pbE_symm_apply e g y

lemma map_addFun (p : ℕ) (e : X ≃+ Y) :
    (addFun R p Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = addFun R p X := by
  exact map_pbE_eq_of_addEquiv e _ _ (fun f hf => comp_mem_addFun p e hf) (fun g hg => comp_mem_addFun p e.symm hg)

lemma map_intFun (e : X ≃+ Y) :
    (intFun R Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = intFun R X := by
  refine map_pbE_eq_of_addEquiv e _ _ ?_ ?_
  · intro f hf
    have h : ∀ y : Y, ∃ r : R, algebraMap R C r = f y := hf
    show ∀ x : X, ∃ r : R, algebraMap R C r = f (e x)
    exact fun x => h (e x)
  · intro g hg
    have h : ∀ x : X, ∃ r : R, algebraMap R C r = g x := hg
    show ∀ y : Y, ∃ r : R, algebraMap R C r = g (e.symm y)
    exact fun y => h (e.symm y)

lemma map_pFun (p : ℕ) (e : X ≃+ Y) :
    (pFun R p Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = pFun R p X := by
  refine map_pbE_eq_of_addEquiv e _ _ ?_ ?_
  · intro f hf
    simp only [pFun, Submodule.mem_pi, Set.mem_univ, true_implies] at hf ⊢
    exact fun x => hf (e x)
  · intro g hg
    simp only [pFun, Submodule.mem_pi, Set.mem_univ, true_implies] at hg ⊢
    exact fun y => hg (e.symm y)

lemma map_afFun (p : ℕ) (e : X ≃+ Y) (M : Submodule R (Y → C)) :
    (afFun p M).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) =
      afFun p (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) := by
  show Submodule.map _ (M ⊓ addFun R p Y) = _ ⊓ addFun R p X
  rw [Submodule.map_inf, map_addFun]
  exact (pbE (C := C) (R := R) e).injective

lemma map_linFun (p : ℕ) (e : X ≃+ Y) :
    (linFun R p Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = linFun R p X := by
  show Submodule.map _ (intFun R Y ⊓ addFun R p Y) = intFun R X ⊓ addFun R p X
  rw [Submodule.map_inf, map_intFun, map_addFun]
  exact (pbE (C := C) (R := R) e).injective

private theorem nonempty_quotient_linearEquiv_map {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (φ : V ≃ₗ[R] W) (L A : Submodule R V) :
    Nonempty ((↥L ⧸ Submodule.comap L.subtype A) ≃ₗ[R]
      (↥(L.map (φ : V →ₗ[R] W)) ⧸ Submodule.comap (L.map (φ : V →ₗ[R] W)).subtype (A.map (φ : V →ₗ[R] W)))) := by
  refine ⟨Submodule.Quotient.equiv _ _ (φ.submoduleMap L) ?_⟩
  ext ⟨w, hw⟩
  constructor
  · rintro ⟨⟨v, hv⟩, hvA, hvw⟩
    have hw' : φ v = w := congrArg Subtype.val hvw
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hvA ⊢
    exact ⟨v, hvA, hw'⟩
  · intro h
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at h
    obtain ⟨v, hvA, rfl⟩ := h
    obtain ⟨v', hv'L, hv'⟩ := hw
    have hvv : v' = v := φ.injective hv'
    subst hvv
    exact ⟨⟨v', hv'L⟩, hvA, rfl⟩

lemma afQuot_equiv (p : ℕ) (e : X ≃+ Y) (M : Submodule R (Y → C)) :
    Nonempty (AFQuot p M ≃ₗ[R]
      AFQuot p (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)))) := by
  obtain ⟨f⟩ := nonempty_quotient_linearEquiv_map (pbE (C := C) (R := R) e) (linFun R p Y) (afFun p M ⊔ pFun R p Y)
  rw [map_linFun, Submodule.map_sup, map_afFun, map_pFun] at f
  exact ⟨f⟩

end

lemma exists_coord (p : ℕ) [Fact p.Prime] (N : Type) [AddCommGroup N] [Finite N]
    [Module (ZMod p) N] : ∃ n : ℕ, Nonempty ((Fin n → ZMod p) ≃+ N) :=
  have : Module.Finite (ZMod p) N := Module.Finite.of_finite
  ⟨_, ⟨(Module.finBasis (ZMod p) N).equivFun.symm.toAddEquiv⟩⟩

private theorem genAF_bot_of_span_monomials {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
    {N : Type} [AddCommGroup N] (p : ℕ) {ι : Type} [Fintype ι] (M : Submodule R (N → C))
    (y : ι → N → C) (hy : ∀ j, y j ∈ afFun p M) (S : Set (N → C))
    (hS : M = Submodule.span R S) (hgen : ∀ s ∈ S, ∃ α : ι → ℕ, s = ∏ j, y j ^ α j) :
    GenAF p M ⊥ := by
  have hinv : invFun M (⊥ : AddSubgroup N) = M := by
    ext g
    constructor
    · intro h
      exact (show g ∈ M ∧ ∀ x k : N, k ∈ (⊥ : AddSubgroup N) → g (x + k) = g x from h).1
    · intro h
      show g ∈ M ∧ ∀ x k : N, k ∈ (⊥ : AddSubgroup N) → g (x + k) = g x
      refine ⟨h, ?_⟩
      intro x k hk
      rw [AddSubgroup.mem_bot] at hk
      subst hk
      simp
  show invFun M ⊥ ≤ Subalgebra.toSubmodule (Algebra.adjoin R (afFun p (invFun M ⊥) : Set (N → C)))
  rw [hinv]
  have hsp : Submodule.span R S ≤ Subalgebra.toSubmodule (Algebra.adjoin R (afFun p M : Set (N → C))) := by
    rw [Submodule.span_le]
    intro s hs
    obtain ⟨α, rfl⟩ := hgen s hs
    exact (Subalgebra.mem_toSubmodule _).mpr
      (Subalgebra.prod_mem _ (fun j _ => Subalgebra.pow_mem _ (Algebra.subset_adjoin (hy j)) _))
  intro g hg
  rw [hS] at hg
  exact hsp hg

theorem cnt_of (hcoord : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = cN ^ 2 → ∃ x : ι → (ι → ZMod p) → C, (∀ j, x j ∈ afFun p AA.carrier) ∧ AA.carrier = Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) => ∏ j, x j y ^ (α j).val))) :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card N * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card N * (p - 1)) = cN ^ 2 → GenAF p AA.carrier ⊥) := by
  intro p _ C _ _ _ v R _ _ hvR hp N _ _ _ hN AA cA cN hA hC
  letI : Module (ZMod p) N := AddCommGroup.zmodModule hN
  obtain ⟨n, ⟨e⟩⟩ := exists_coord p N
  have hcard : Fintype.card (Fin n → ZMod p) = Fintype.card N := Fintype.card_congr e.toEquiv
  obtain ⟨f⟩ := afQuot_equiv (C := C) (R := R) p e AA.carrier
  have hA' : HasLen v R (AFQuot p (hopfPull e AA).carrier) cA := by
    obtain ⟨m, c, ⟨g⟩, hc⟩ := hA
    exact ⟨m, c, ⟨f.symm.trans g⟩, hc⟩
  have hC' : HasColen R v (hopfPull e AA).carrier cN := hasColen_map v e _ _ hC
  obtain ⟨hle, heq⟩ := hcoord p C v R hvR hp (Fin n) (hopfPull e AA) cA cN hA' hC'
  rw [hcard] at hle heq
  refine ⟨hle, fun hE => ?_⟩
  obtain ⟨x, hxj, hspan⟩ := heq hE
  refine genAF_bot_of_span_monomials p AA.carrier (fun j z => x j (e.symm z)) ?_
    ((⇑(pbE (C := C) (R := R) e.symm)) '' Set.range
      (fun (α : Fin n → ZMod p) (y : Fin n → ZMod p) => ∏ j, x j y ^ (α j).val)) ?_ ?_
  · intro j
    have hx' : x j ∈ (afFun p AA.carrier).map
        (pbE (C := C) (R := R) e : (N → C) →ₗ[R] ((Fin n → ZMod p) → C)) := by
      rw [map_afFun]
      exact hxj j
    have h2 := (Submodule.mem_map_equiv _).mp hx'
    convert h2 using 1
    funext z
    rw [pbE_symm_apply]
  · have h1 := Submodule.map_span (pbE (C := C) (R := R) e.symm : ((Fin n → ZMod p) → C) →ₗ[R] (N → C))
      (Set.range fun (α : Fin n → ZMod p) (y : Fin n → ZMod p) => ∏ j, x j y ^ (α j).val)
    rw [← hspan] at h1
    rw [← map_pbE_symm e AA.carrier]
    exact h1
  · rintro s ⟨_, ⟨α, rfl⟩, rfl⟩
    refine ⟨fun j => (α j).val, ?_⟩
    funext z
    rw [Finset.prod_apply]
    rfl

end PositivityTheory.HtPt.Ra
end
end

section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

theorem smith : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∃ (Λ : Matrix ι ι R) (ε : ι → R), IsUnit Λ.det ∧ afLat p AA.carrier = Submodule.span R (Set.range fun j => ε j • Λ j) ∧ (∀ j, v (p : C) ≤ v (algebraMap R C (ε j)) ^ (p - 1)) ∧ HasLen v R (AFQuot p AA.carrier) (∏ j, v (algebraMap R C (ε j))) :=
  smith_of PositivityTheory.HtPt.Rh.aflat_fg PositivityTheory.HtPt.Rh.afquot

theorem cnt_coord : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = cN ^ 2 → ∃ x : ι → (ι → ZMod p) → C, (∀ j, x j ∈ afFun p AA.carrier) ∧ AA.carrier = Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) => ∏ j, x j y ^ (α j).val)) :=
  cnt_coord_of smith

theorem cnt : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card N * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card N * (p - 1)) = cN ^ 2 → GenAF p AA.carrier ⊥) :=
  cnt_of cnt_coord

end PositivityTheory.HtPt.Ra
end
end
