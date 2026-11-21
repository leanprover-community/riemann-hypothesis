import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemma
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicEqBlockUpper
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLeviProjection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleDeterminantTwist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIntersectionConjugate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellLeviTensorDecomposition
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGL

section
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.Twist

theorem exists_nat_labelling_blk : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N), ∃ β : Fin N → ℕ, ∀ x y, β x < β y ↔ blk e x < blk e y := by
  intro α _ _ N m _ _ e
  let o := (Fintype.orderIsoFinOfCardEq α rfl).symm
  refine ⟨fun x => (o (blk e x)).val, fun x y => ?_⟩
  exact Fin.lt_def.symm.trans (OrderIso.lt_iff_lt o)

end GlobalTheory.CompanionTheory.Twist
end

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_strict_block_order : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N), ∃ β : Fin N → ℕ, ∀ x y, β x < β y ↔ blk e x < blk e y := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Twist.exists_nat_labelling_blk
end

section
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.LeviIso

theorem leviEquiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∃ φ : Levi k m ≃* levi k N β, (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) ∧ Continuous φ ∧ Continuous φ.symm := by
  intro k _ _ _ _ α _ _ N m _ _ e β hβ
  have hz : ∀ x : GL (Fin N) k, x ∈ levi k N β → ∀ i j : Fin N, blk e i ≠ blk e j →
      (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
    intro x hx i j hij
    simp only [levi, Subgroup.mem_inf, GroundTheory.Automorphic.Iwasawa.mem_blockUpper] at hx
    rcases lt_or_gt_of_ne hij with h | h
    · exact hx.2 (OrderDual.toDual_lt_toDual.mpr ((hβ i j).2 h))
    · exact hx.1 ((hβ j i).2 h)
  have hzE : ∀ (g : Levi k m) (i j : Fin N), blk e i ≠ blk e j →
      ((leviEmb k e g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = 0 := by
    intro g i j hij
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    have hab : a ≠ b := by simpa [blk] using hij
    exact leviEmb_apply_ne k e g hab i' j'
  have hent : ∀ (g : Levi k m) (a : α) (i j : m a),
      ((leviEmb k e g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) =
        ((g a : GL (m a) k) : Matrix (m a) (m a) k) i j := by
    intro g a i j
    exact leviEmb_apply_same k e g a i j
  have hmem : ∀ g : Levi k m, leviEmb k e g ∈ levi k N β := by
    intro g
    simp only [levi, Subgroup.mem_inf, GroundTheory.Automorphic.Iwasawa.mem_blockUpper]
    constructor
    · intro i j h
      exact hzE g i j ((hβ j i).1 h).ne'
    · intro i j h
      exact hzE g i j ((hβ i j).1 (OrderDual.toDual_lt_toDual.1 h)).ne
  have hkey : ∀ x : GL (Fin N) k, x ∈ levi k N β →
      Matrix.blockDiagonal' (Matrix.blockDiag' ((x : Matrix (Fin N) (Fin N) k).submatrix e e)) =
        (x : Matrix (Fin N) (Fin N) k).submatrix e e := by
    intro x hx
    ext ⟨a, i⟩ ⟨b, j⟩
    by_cases hab : a = b
    · subst hab
      rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiag'_apply]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hab, Matrix.submatrix_apply,
        hz x hx _ _ (by simpa [blk] using hab)]
  have hmul : ∀ x y : GL (Fin N) k, x ∈ levi k N β → y ∈ levi k N β → ∀ a : α,
      Matrix.blockDiag' ((x : Matrix (Fin N) (Fin N) k).submatrix e e) a *
          Matrix.blockDiag' ((y : Matrix (Fin N) (Fin N) k).submatrix e e) a =
        Matrix.blockDiag' (((x * y : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix e e) a := by
    intro x y hx hy a
    rw [Units.val_mul, ← Matrix.submatrix_mul_equiv (x : Matrix (Fin N) (Fin N) k)
      (y : Matrix (Fin N) (Fin N) k) e e e, ← hkey x hx, ← hkey y hy]
    simp only [← Matrix.blockDiagonal'_mul, Matrix.blockDiag'_blockDiagonal']
  have hcont : ∀ f : Levi k m → Levi k m,
      (∀ a, Continuous fun g => ((f g a : GL (m a) k) : Matrix (m a) (m a) k)) →
        Continuous fun g => ((leviEmb k e (f g) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := by
    intro f hf
    refine continuous_matrix fun i j => ?_
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    by_cases hab : a = b
    · subst hab
      simp only [hent]
      exact (hf a).matrix_elem i' j'
    · have h0 : ∀ g, ((leviEmb k e (f g) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
          (e ⟨a, i'⟩) (e ⟨b, j'⟩) = 0 := fun g => hzE _ _ _ (by simpa [blk] using hab)
      simp only [h0]
      exact continuous_const
  have hLE : Continuous (leviEmb k e) := continuous_leviEmb k e
  let ψ : levi k N β → Levi k m := fun x => (fun a =>
      ⟨Matrix.blockDiag' (((x : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix e e) a,
        Matrix.blockDiag' ((((x : GL (Fin N) k)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix e e) a,
        by rw [hmul _ _ x.2 (inv_mem x.2), mul_inv_cancel, Units.val_one,
          Matrix.submatrix_one_equiv, Matrix.blockDiag'_one]; rfl,
        by rw [hmul _ _ (inv_mem x.2) x.2, inv_mul_cancel, Units.val_one,
          Matrix.submatrix_one_equiv, Matrix.blockDiag'_one]; rfl⟩ : ∀ a, GL (m a) k)
  refine ⟨{
      toFun := fun g => ⟨leviEmb k e g, hmem g⟩
      invFun := ψ
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }, fun g => rfl, ?_, ?_⟩
  · intro g
    refine funext fun a => ?_
    apply Units.ext
    ext i j
    simp only [ψ, Matrix.blockDiag'_apply, Matrix.submatrix_apply]
    exact hent g a i j
  · intro x
    apply Subtype.ext
    apply Units.ext
    ext i j
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    by_cases hab : a = b
    · subst hab
      dsimp only
      rw [hent]
      simp only [ψ, Matrix.blockDiag'_apply, Matrix.submatrix_apply]
    · have h' : blk e (e ⟨a, i'⟩) ≠ blk e (e ⟨b, j'⟩) := by simpa [blk] using hab
      dsimp only
      rw [hzE _ _ _ h', hz _ x.2 _ _ h']
  · intro g h
    apply Subtype.ext
    exact map_mul (leviEmb k e) g h
  · exact hLE.subtype_mk hmem
  · change Continuous ψ
    refine continuous_pi fun a => ?_
    rw [Units.continuous_iff]
    constructor
    · refine continuous_matrix fun i j => ?_
      simp only [Function.comp_apply, ψ, Matrix.blockDiag'_apply, Matrix.submatrix_apply]
      exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _
    · refine continuous_matrix fun i j => ?_
      simp only [ψ, Units.inv_mk, Matrix.blockDiag'_apply, Matrix.submatrix_apply]
      exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_elem _ _

end GlobalTheory.CompanionTheory.LeviIso
end

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_block_homeomorph : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∃ φ : Levi k m ≃* levi k N β, (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) ∧ Continuous φ ∧ Continuous φ.symm := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LeviIso.leviEquiv
end

section
section
set_option maxSynthPendingDepth 1

open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.DeltaLevi

open GroundTheory.Automorphic.Measures

theorem prod_pairs_le {α G : Type} [Fintype α] [LinearOrder α] [CommGroup G] (n : α → ℕ) (x : α → G) :
    ∏ c : α × α, (if c.1 ≤ c.2 then x c.1 ^ (n c.2 : ℤ) * (x c.2)⁻¹ ^ (n c.1 : ℤ) else 1) =
      ∏ a, x a ^ ((∑ b with a < b, (n b : ℤ)) - ∑ b with b < a, (n b : ℤ)) := by
  have hz : ∀ (y : G) (f : α → ℤ), ∏ b, y ^ f b = y ^ ∑ b, f b := by
    intro y f
    induction (Finset.univ : Finset α) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
  have h1 : ∀ c : α × α, (if c.1 ≤ c.2 then x c.1 ^ (n c.2 : ℤ) * (x c.2)⁻¹ ^ (n c.1 : ℤ) else 1) =
      x c.1 ^ (if c.1 ≤ c.2 then (n c.2 : ℤ) else 0) *
        x c.2 ^ (-(if c.1 ≤ c.2 then (n c.1 : ℤ) else 0)) := by
    intro c
    split_ifs <;> simp
  simp only [h1]
  rw [Finset.prod_mul_distrib, Fintype.prod_prod_type, Fintype.prod_prod_type,
    Finset.prod_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun a b => x b ^ (-(if a ≤ b then (n a : ℤ) else 0))), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  dsimp only
  rw [hz, hz, ← zpow_add, Finset.sum_neg_distrib, Finset.sum_filter, Finset.sum_filter,
    ← sub_eq_add_neg, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h | h | h
  · simp [h, h.le, h.not_ge, h.not_gt]
  · simp [h]
  · simp [h, h.le, h.not_ge, h.not_gt]

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)]
  [∀ i, DecidableEq (m i)]

theorem leviEmb_eq_zero (e : (Σ i, m i) ≃ Fin N) (g : Levi k m) {i j : Fin N}
    (h : blk e i ≠ blk e j) : (leviEmb k e g : Matrix (Fin N) (Fin N) k) i j = 0 := by
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  exact leviEmb_apply_ne k e g (by simpa using h) i j

theorem det_adLie_pairs (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ)
    (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y) (p : blockUpper k N β) (g : Levi k m)
    (hp : (p : GL (Fin N) k) = leviEmb k e g) :
    (LinearEquiv.det (adLie k N β p) : k) =
      ∏ c : α × α, if c.1 ≤ c.2 then
        ((g c.1 : GL (m c.1) k) : Matrix (m c.1) (m c.1) k).det ^ Fintype.card (m c.2) *
          ((((g c.2)⁻¹ : GL (m c.2) k)) : Matrix (m c.2) (m c.2) k).det ^ Fintype.card (m c.1)
      else 1 := by
  classical
  set P : Matrix (Fin N) (Fin N) k := ((p : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) with hPdef
  set Q : Matrix (Fin N) (Fin N) k :=
    (((p : GL (Fin N) k)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) with hQdef
  have hP : P = (leviEmb k e g : Matrix (Fin N) (Fin N) k) := by rw [hPdef, hp]
  have hQ : Q = (leviEmb k e g⁻¹ : Matrix (Fin N) (Fin N) k) := by rw [hQdef, hp, map_inv]
  let A : (ParabolicIndex N β → k) →ₗ[k] (ParabolicIndex N β → k) :=
    (((parabolicCoord k N β).symm.trans ((adLie k N β p).trans (parabolicCoord k N β))) :
      (ParabolicIndex N β → k) →ₗ[k] (ParabolicIndex N β → k))
  have hdet : (LinearEquiv.det (adLie k N β p) : k) = LinearMap.det A := by
    rw [← LinearEquiv.det_conj (adLie k N β p) (parabolicCoord k N β), LinearEquiv.coe_det]
    rfl
  have hM : ∀ s t, LinearMap.toMatrix' A s t = P s.1.1 t.1.1 * Q t.1.2 s.1.2 := by
    intro s t
    rw [LinearMap.toMatrix'_apply]
    show ((adLie k N β p ((parabolicCoord k N β).symm (Pi.single t 1)) : lieParabolic k N β) :
      Matrix (Fin N) (Fin N) k) s.1.1 s.1.2 = _
    rw [coe_adLie, coe_parabolicCoord_symm_single, mul_single_mul_apply]
  let κ : ParabolicIndex N β → α ×ₗ α := fun s => toLex (blk e s.1.1, blk e s.1.2)
  have hzero : ∀ s t, κ s ≠ κ t → LinearMap.toMatrix' A s t = 0 := by
    intro s t hst
    rw [hM]
    by_cases h1 : blk e s.1.1 = blk e t.1.1
    · have h2 : blk e t.1.2 ≠ blk e s.1.2 := by
        intro h2
        exact hst (by simp only [κ, h1, h2])
      rw [hQ, leviEmb_eq_zero e _ h2, mul_zero]
    · rw [hP, leviEmb_eq_zero e _ h1, zero_mul]
  have hBT : (LinearMap.toMatrix' A).BlockTriangular κ := fun s t hts => hzero s t hts.ne'
  have hblock : ∀ a b : α, ((LinearMap.toMatrix' A).toSquareBlock κ (toLex (a, b))).det =
      if a ≤ b then
        ((g a : GL (m a) k) : Matrix (m a) (m a) k).det ^ Fintype.card (m b) *
          ((((g b)⁻¹ : GL (m b) k)) : Matrix (m b) (m b) k).det ^ Fintype.card (m a)
      else 1 := by
    intro a b
    by_cases hab : a ≤ b
    · rw [if_pos hab]
      have hmem : ∀ (i : m a) (j : m b), ¬ β (e ⟨b, j⟩) < β (e ⟨a, i⟩) := by
        intro i j
        rw [hβ]
        simpa using hab
      let f : m a × m b → {t : ParabolicIndex N β // κ t = toLex (a, b)} := fun x =>
        ⟨⟨(e ⟨a, x.1⟩, e ⟨b, x.2⟩), hmem x.1 x.2⟩, by simp [κ]⟩
      have hf : Function.Bijective f := by
        constructor
        · rintro ⟨i, j⟩ ⟨i', j'⟩ h
          have h1 := congrArg (fun t => t.1.1.1) h
          have h2 := congrArg (fun t => t.1.1.2) h
          simp only [f] at h1 h2
          have h1' := e.injective h1
          have h2' := e.injective h2
          simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h1' h2'
          rw [h1', h2']
        · rintro ⟨⟨⟨i, j⟩, hij⟩, hκ⟩
          obtain ⟨⟨a', i⟩, rfl⟩ := e.surjective i
          obtain ⟨⟨b', j⟩, rfl⟩ := e.surjective j
          have h3 : a' = a ∧ b' = b := by simpa [κ] using hκ
          obtain ⟨rfl, rfl⟩ := h3
          exact ⟨(i, j), rfl⟩
      rw [← Matrix.det_submatrix_equiv_self (Equiv.ofBijective f hf)]
      have hk : ((LinearMap.toMatrix' A).toSquareBlock κ (toLex (a, b))).submatrix
          (Equiv.ofBijective f hf) (Equiv.ofBijective f hf) =
          Matrix.kroneckerMap (· * ·) ((g a : GL (m a) k) : Matrix (m a) (m a) k)
            ((((g b)⁻¹ : GL (m b) k)) : Matrix (m b) (m b) k).transpose := by
        ext ⟨i, j⟩ ⟨i', j'⟩
        show LinearMap.toMatrix' A (f (i, j)).1 (f (i', j')).1 = _
        rw [hM, hP, hQ]
        show (leviEmb k e g : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, i'⟩) *
          (leviEmb k e g⁻¹ : Matrix (Fin N) (Fin N) k) (e ⟨b, j'⟩) (e ⟨b, j⟩) = _
        rw [leviEmb_apply_same, leviEmb_apply_same]
        rfl
      rw [hk, Matrix.det_kronecker, Matrix.det_transpose]
    · rw [if_neg hab]
      have : IsEmpty {t : ParabolicIndex N β // κ t = toLex (a, b)} := by
        refine ⟨fun t => hab ?_⟩
        have h3 : blk e t.1.1.1 = a ∧ blk e t.1.1.2 = b := by simpa [κ] using t.2
        have h4 := t.1.2
        rw [hβ, h3.1, h3.2] at h4
        exact not_lt.1 h4
      exact Matrix.det_isEmpty
  rw [hdet, ← LinearMap.det_toMatrix', hBT.det]
  rw [Finset.prod_subset (Finset.subset_univ _) (fun c _ hc => by
    have : IsEmpty {t : ParabolicIndex N β // κ t = c} :=
      ⟨fun t => hc (Finset.mem_image.2 ⟨t.1, Finset.mem_univ _, t.2⟩)⟩
    exact Matrix.det_isEmpty)]
  rw [← Equiv.prod_comp toLex]
  exact Finset.prod_congr rfl fun c _ => hblock c.1 c.2

theorem det_adLie_levi (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ)
    (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y) (p : blockUpper k N β) (g : Levi k m)
    (hp : (p : GL (Fin N) k) = leviEmb k e g) :
    LinearEquiv.det (adLie k N β p) = ∏ a, Matrix.GeneralLinearGroup.det (g a) ^ modExp m a := by
  have h := prod_pairs_le (fun a => Fintype.card (m a))
    (fun a => Matrix.GeneralLinearGroup.det (g a))
  have hd : ∀ b, ((((g b)⁻¹ : GL (m b) k)) : Matrix (m b) (m b) k).det =
      (((Matrix.GeneralLinearGroup.det (g b))⁻¹ : kˣ) : k) := fun b => by
    rw [← map_inv]
    rfl
  have hd' : ∀ a, ((g a : GL (m a) k) : Matrix (m a) (m a) k).det =
      ((Matrix.GeneralLinearGroup.det (g a) : kˣ) : k) := fun a => rfl
  refine Units.ext ?_
  rw [det_adLie_pairs e β hβ p g hp]
  change _ = ((∏ a, Matrix.GeneralLinearGroup.det (g a) ^
    ((∑ b with a < b, (Fintype.card (m b) : ℤ)) - ∑ b with b < a, (Fintype.card (m b) : ℤ)) : kˣ) : k)
  rw [← h, Units.coe_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  split_ifs with hc
  · simp only [hd, hd', zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
  · rfl

theorem deltaHalf_eq_sqrtModular : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ),
    (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β),
    (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) →
    ∀ g : Levi k m, ((deltaHalf k m g : ℂˣ) : ℂ) = sqrtModular k N β (leviIncl (φ g)) := by
  intro k _ _ _ _ α _ _ N m _ _ e β hβ φ hφ g
  have hp : ((leviIncl (φ g) : blockUpper k N β) : GL (Fin N) k) = leviEmb k e g := hφ g
  have h := modularCharacter_blockUpper (leviIncl (φ g))
  have hs : sqrtModular k N β (leviIncl (φ g)) = ((NNReal.sqrt (MeasureTheory.distribHaarChar k
      (LinearEquiv.det (adLie k N β (leviIncl (φ g))))) : ℝ) : ℂ) := by
    rw [← h]
    rfl
  have hm : modulus k m g = ((MeasureTheory.distribHaarChar k
      (LinearEquiv.det (adLie k N β (leviIncl (φ g)))) : NNReal) : ℝ) := by
    unfold GlobalTheory.SmGL.modulus
    rw [det_adLie_levi e β hβ _ g hp, map_prod, NNReal.coe_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_zpow, NNReal.coe_zpow]
    rfl
  rw [hs, val_deltaHalf, hm, Real.coe_sqrt]

end

end GlobalTheory.CompanionTheory.DeltaLevi
end

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_character_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ g : Levi k m, ((deltaHalf k m g : ℂˣ) : ℂ) = sqrtModular k N β (leviIncl (φ g)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.DeltaLevi.deltaHalf_eq_sqrtModular
end

section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.ParIndBridge

theorem parInd_equiv_parabolicInd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), Nonempty ((parInd e ρ).Equiv (parabolicInd k N β (ρ.comp φ.symm.toMonoidHom))) := by
  intro k _ _ _ _ α _ _ N m _ _ e β hβ φ hφ W _ _ ρ
  have hP : parab k e = blockUpper k N β := GlobalTheory.T.parabolic_eq_block_upper k e β hβ
  have h12 : ∀ {p : GL (Fin N) k}, p ∈ parab k e → p ∈ blockUpper k N β := fun h => hP ▸ h
  have h21 : ∀ {p : GL (Fin N) k}, p ∈ blockUpper k N β → p ∈ parab k e := fun h => hP ▸ h
  have hchar : ∀ (p : GL (Fin N) k) (h1 : p ∈ parab k e) (h2 : p ∈ blockUpper k N β) (w : W),
      (deltaHalf k m (leviProj k e ⟨p, h1⟩) : ℂ) • ρ (leviProj k e ⟨p, h1⟩) w =
        sqrtModular k N β ⟨p, h2⟩ •
          ρ (φ.symm (GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨p, h2⟩)) w := by
    intro p h1 h2 w
    have hL := GlobalTheory.T.parabolic_levi_projection k e β hβ φ hφ p h1 h2
    rw [← hL, MulEquiv.symm_apply_apply, GlobalTheory.T.modulus_character_levi k e β hβ φ hφ, hL,
      GroundTheory.Automorphic.Parabolic.sqrtModular_leviProj]
  let σ := ρ.comp φ.symm.toMonoidHom
  let E : IndSp e ρ ≃ₗ[ℂ] GroundTheory.Automorphic.Parabolic.parabolicIndSpace k N β σ :=
    { toFun := fun f => ⟨f.1.1, fun p g => by
          have h := parInd_law e ρ f ⟨p.1, h21 p.2⟩ g
          refine h.trans ?_
          exact hchar p.1 (h21 p.2) p.2 _,
        GroundTheory.Automorphic.stabilizerOf (GlobalTheory.PRep.ind (parab k e)
          ((twist ρ (deltaHalf k m)).comp (leviProj k e))) f.1, f.2, fun x hx g => by
          have h := GroundTheory.Automorphic.mem_stabilizerOf.1 hx
          exact congrFun (congrArg Subtype.val h) g⟩
      invFun := fun f => ⟨⟨f.1, fun p g => by
          have h := f.2.1 ⟨p.1, h12 p.2⟩ g
          refine h.trans ?_
          exact (hchar p.1 p.2 (h12 p.2) _).symm⟩, by
          obtain ⟨-, K, hK, hf⟩ := f.2
          refine mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds (one_mem K)) fun x hx => ?_)
          exact Subtype.ext (funext fun g => hf x hx g)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨Representation.Equiv.mk E fun g => LinearMap.ext fun f => Subtype.ext (funext fun x => rfl)⟩

end GlobalTheory.CompanionTheory.ParIndBridge
end

section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicInd_equiv_levi_transport : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), Nonempty ((parInd e ρ).Equiv (parabolicInd k N β (ρ.comp φ.symm.toMonoidHom))) := by
  first | exact @GlobalTheory.CompanionTheory.ParIndBridge.parInd_equiv_parabolicInd | exact GlobalTheory.CompanionTheory.ParIndBridge.parInd_equiv_parabolicInd | (intros; apply GlobalTheory.CompanionTheory.ParIndBridge.parInd_equiv_parabolicInd <;> assumption)
end

section
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.JacquetEquiv

theorem nonempty_jacquetRep_equiv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (γ : Fin n → ℕ) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (π : Representation ℂ (GL (Fin n) F) V) (π' : Representation ℂ (GL (Fin n) F) V'), π.Equiv π' → Nonempty ((jacquetRep F n γ π).Equiv (jacquetRep F n γ π')) := by
  intro F _ _ _ _ n γ V V' _ _ _ _ π π' φ
  let e : V ≃ₗ[ℂ] V' := φ.toLinearEquiv
  have he : ∀ g, (e : V →ₗ[ℂ] V') ∘ₗ π g = π' g ∘ₗ (e : V →ₗ[ℂ] V') := by
    intro g
    rw [Representation.Equiv.toLinearEquiv_toLinearMap]
    exact φ.toIntertwiningMap.isIntertwining' g
  have he' := LinearEquiv.isIntertwining_symm_isIntertwining he
  let f : Representation.IntertwiningMap (MonoidHom.comp π (unipotentRadical F n γ).subtype) (MonoidHom.comp π' (unipotentRadical F n γ).subtype) :=
    ⟨(e : V →ₗ[ℂ] V'), fun x => he x⟩
  let g : Representation.IntertwiningMap (MonoidHom.comp π' (unipotentRadical F n γ).subtype) (MonoidHom.comp π (unipotentRadical F n γ).subtype) :=
    ⟨(e.symm : V' →ₗ[ℂ] V), fun x => he' x⟩
  let M := Representation.Coinvariants.map _ _ f
  let M' := Representation.Coinvariants.map _ _ g
  have hMM' : M ∘ₗ M' = LinearMap.id := by
    apply Representation.Coinvariants.hom_ext
    ext v
    simp only [LinearMap.comp_apply, LinearMap.id_apply, M, M', Representation.Coinvariants.map_mk]
    congr 1
    exact e.apply_symm_apply v
  have hM'M : M' ∘ₗ M = LinearMap.id := by
    apply Representation.Coinvariants.hom_ext
    ext v
    simp only [LinearMap.comp_apply, LinearMap.id_apply, M, M', Representation.Coinvariants.map_mk]
    congr 1
    exact e.symm_apply_apply v
  let E := LinearEquiv.ofLinearMap (re₁₂ := RingHomInvPair.ids) (re₂₁ := RingHomInvPair.ids) M M' hMM' hM'M
  refine ⟨Representation.Equiv.mk E ?_⟩
  intro m
  apply Representation.Coinvariants.hom_ext
  ext u
  have hc : f ((π (m : GL (Fin n) F)) u) = (π' (m : GL (Fin n) F)) (f u) := LinearMap.congr_fun (he m) u
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, E, LinearEquiv.coe_ofLinearMap, jacquetRep,
    GroundTheory.Automorphic.Parabolic.twist_apply, map_smul, GroundTheory.Automorphic.Parabolic.jacquetAction,
    MonoidHom.coe_mk, OneHom.coe_mk, GroundTheory.Automorphic.coinvariantsTranslate_mk, M,
    Representation.Coinvariants.map_mk]
  rw [hc]

end GlobalTheory.CompanionTheory.JacquetEquiv
end

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_module_equiv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (γ : Fin n → ℕ) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (π : Representation ℂ (GL (Fin n) F) V) (π' : Representation ℂ (GL (Fin n) F) V'), π.Equiv π' → Nonempty ((jacquetRep F n γ π).Equiv (jacquetRep F n γ π')) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.JacquetEquiv.nonempty_jacquetRep_equiv
end

section
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.FiltTransfer

theorem subQuot_of_filtration : ∀ {G H : Type} [Group G] [Group H] (ψ : H →* G) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (ρ : Representation ℂ H V) (ρ' : Representation ℂ G V'), ρ.Equiv (ρ'.comp ψ) → ∀ (K : ℕ) (X : Fin K → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (τ : ∀ j, Representation ℂ G (X j)) (Vf : ℕ → Submodule ℂ V'), Vf 0 = ⊥ → Vf K = ⊤ → Monotone Vf → ∀ (hV : ∀ i (g : G), Vf i ≤ (Vf i).comap (ρ' g)), (∀ j : Fin K, ∃ Ψ : Representation.IntertwiningMap (ρ'.subrepresentation (Vf (j + 1)) (hV (j + 1))) (τ j), Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ (x : V') ∈ Vf j) → ∃ S : Fin (K + 1) → Subrepresentation ρ, Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last K) = ⊤ ∧ ∀ t : Fin K, Nonempty ((GlobalTheory.SmGL.subQuot (S t.succ) (S t.castSucc)).Equiv ((τ t).comp ψ)) := by
  intro G H _ _ ψ V V' _ _ _ _ ρ ρ' e K X _ _ τ Vf h0 hK hm hV hΨ
  have he : ∀ (h : H) (v : V), e (ρ h v) = ρ' (ψ h) (e v) := fun h v =>
    e.toIntertwiningMap.isIntertwining _ _ h v
  let S : ℕ → Subrepresentation ρ := fun i =>
    ⟨(Vf i).comap e.toLinearMap, fun h v hv => by
      have hv' : e v ∈ Vf i := hv
      show e (ρ h v) ∈ Vf i
      rw [he]
      exact hV i (ψ h) hv'⟩
  have memS : ∀ (i : ℕ) (v : V), v ∈ (S i).toSubmodule ↔ e v ∈ Vf i := fun _ _ => Iff.rfl
  refine ⟨fun t => S t, ?_, ?_, ?_, ?_⟩
  · intro a b hab v hv
    exact hm (Fin.le_def.1 hab) hv
  · apply Subrepresentation.toSubmodule_injective
    ext v
    show e v ∈ Vf 0 ↔ v = 0
    rw [h0]
    simp
  · apply Subrepresentation.toSubmodule_injective
    ext v
    show e v ∈ Vf K ↔ True
    rw [hK]
    simp
  · intro t
    obtain ⟨Ψ, hs, hk⟩ := hΨ t
    let f : (S (t + 1)).toSubmodule →ₗ[ℂ] X t :=
      Ψ.toLinearMap ∘ₗ
        (e.toLinearMap.restrict (p := (S (t + 1)).toSubmodule) (q := Vf (t + 1)) fun _ hv => hv)
    have hf : ∀ x, f x = Ψ ⟨e x, x.2⟩ := fun _ => rfl
    have hsurj : Function.Surjective f := by
      intro y
      obtain ⟨w, rfl⟩ := hs y
      refine ⟨⟨e.symm w, ?_⟩, ?_⟩
      · show e (e.symm w) ∈ Vf (t + 1)
        simp
      · rw [hf]
        congr 1
        apply Subtype.ext
        simp
    have hker : (S t).toSubmodule.comap (S (t + 1)).toSubmodule.subtype = LinearMap.ker f := by
      ext x
      rw [LinearMap.mem_ker, hf, hk]
      rfl
    let E := (Submodule.quotEquivOfEq _ _ hker).trans (f.quotKerEquivOfSurjective hsurj)
    refine ⟨Representation.Equiv.mk E ?_⟩
    intro g
    have hE : ∀ x, E (Submodule.Quotient.mk x) = f x := fun x => rfl
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hstep : f ⟨ρ g x, (S (t + 1)).apply_mem_toSubmodule g x.2⟩ =
        τ t (ψ g) (f x) := by
      rw [hf, hf, ← Ψ.isIntertwining _ _ (ψ g)]
      congr 1
      exact Subtype.ext (he g x)
    exact hstep

end GlobalTheory.CompanionTheory.FiltTransfer
end

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_transport_equiv : ∀ {G H : Type} [Group G] [Group H] (ψ : H →* G) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (ρ : Representation ℂ H V) (ρ' : Representation ℂ G V'), ρ.Equiv (ρ'.comp ψ) → ∀ (K : ℕ) (X : Fin K → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (τ : ∀ j, Representation ℂ G (X j)) (Vf : ℕ → Submodule ℂ V'), Vf 0 = ⊥ → Vf K = ⊤ → Monotone Vf → ∀ (hV : ∀ i (g : G), Vf i ≤ (Vf i).comap (ρ' g)), (∀ j : Fin K, ∃ Ψ : Representation.IntertwiningMap (ρ'.subrepresentation (Vf (j + 1)) (hV (j + 1))) (τ j), Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ (x : V') ∈ Vf j) → ∃ S : Fin (K + 1) → Subrepresentation ρ, Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last K) = ⊤ ∧ ∀ t : Fin K, Nonempty ((GlobalTheory.SmGL.subQuot (S t.succ) (S t.castSucc)).Equiv ((τ t).comp ψ)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FiltTransfer.subQuot_of_filtration
end

section
section
set_option maxSynthPendingDepth 1

open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

noncomputable section

namespace GlobalTheory.CompanionTheory.GeomLemmaUniform

section Filtration

open GroundTheory.Automorphic GroundTheory.Automorphic.Parabolic Matrix GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.GLnLocal ValuativeRel Topology Set DoubleCoset Filter

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ}

theorem filtration_of_cellEnumeration {k : ℕ} (w : Fin k → Equiv.Perm (Fin n))
    (hcov : ∀ g : Matrix.GeneralLinearGroup (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j))
        (blockUpper F n β : Set (Matrix.GeneralLinearGroup (Fin n) F)) (blockUpper F n γ))
    (hanti : Antitone fun j => cellHeight β γ (permGL F (w j)))
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
    (hσ : IsSmooth σ) :
    ∃ V : ℕ → Submodule ℂ (JacquetModule F n γ (parabolicInd F n β σ)),
      V 0 = ⊥ ∧ V k = ⊤ ∧ Monotone V ∧
      ∃ hV : ∀ i (m : levi F n γ), V i ≤ (V i).comap (jacquetRep F n γ (parabolicInd F n β σ) m),
        ∀ j : Fin k, ∃ Ψ : Representation.IntertwiningMap
            ((jacquetRep F n γ (parabolicInd F n β σ)).subrepresentation (V (j + 1)) (hV (j + 1)))
            (twist ((invSqrtModular F n γ).comp leviIncl)
              (indRep (cellLeviSub F β γ (w j)) (cellInducing β γ (w j) σ))),
          Function.Surjective Ψ ∧
            ∀ x, Ψ x = 0 ↔ (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ V j := by
  set C : Fin k → Set (Matrix.GeneralLinearGroup (Fin n) F) := fun l =>
    doubleCoset (permGL F (w l)) (blockUpper F n β : Set (Matrix.GeneralLinearGroup (Fin n) F))
      (blockUpper F n γ)
  have hdisj : Pairwise fun i j => Disjoint (C i) (C j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro g hgi hgj
    obtain ⟨l, -, hl⟩ := hcov g
    exact hij ((hl i hgi).trans (hl j hgj).symm)
  have hcov' : ∀ g, ∃ l, g ∈ C l := fun g => (hcov g).exists
  have hcl := closure_doubleCoset_subset_of_antitone hcov hanti
  refine ⟨fun i => jacquetFiltration γ (σ := σ) (cellUnion C i), ?_, ?_, ?_, ?_⟩
  · show jacquetFiltration γ (cellUnion C 0) = ⊥
    rw [cellUnion_zero, jacquetFiltration_empty]
  · show jacquetFiltration γ (cellUnion C k) = ⊤
    rw [cellUnion_of_cover hcov', jacquetFiltration_univ]
  · exact fun i i' h => jacquetFiltration_mono γ (cellUnion_mono h)
  refine ⟨fun i m => jacquetFiltration_le_comap γ (cellUnion_mul_mem w i).1 m, fun j => ?_⟩
  have hYo : IsOpen (cellUnion C ((j : ℕ) + 1)) := isOpen_cellUnion hdisj hcov' hcl _
  have hCY : closure (C j) ∩ cellUnion C ((j : ℕ) + 1) = C j :=
    closure_inter_cellUnion_succ hdisj hcl j
  have hYQ := (cellUnion_mul_mem (F := F) (β := β) (γ := γ) w ((j : ℕ) + 1)).1
  have hYP := (cellUnion_mul_mem (F := F) (β := β) (γ := γ) w ((j : ℕ) + 1)).2
  have hdiff : cellUnion C ((j : ℕ) + 1) \ C j = cellUnion C j := by
    rw [cellUnion_succ j, union_sdiff_right, (disjoint_cellUnion hdisj j).symm.sdiff_eq_left]
  refine ⟨⟨gradedJacquetMap γ (w j) σ hYo hCY hYQ, fun m => ?_⟩, ?_, fun x => ?_⟩
  · refine LinearMap.ext fun x => ?_
    exact gradedJacquetMap_jacquetRep σ hYo hCY hYQ m x
  · exact gradedJacquetMap_surjective σ hYo hCY hYQ (cellJacquetMap_surjective hYo hCY hYP hYQ hσ)
  · have := gradedJacquetMap_eq_zero_iff σ hYo hCY hYQ
      (fun f hf h0 => exists_sub_mem_ker_of_cellJacquet_eq_zero σ hσ hYo hCY hYQ hf h0) x
    rw [hdiff] at this
    exact this

theorem normalized_piece {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (levi F n β) W) (w : Equiv.Perm (Fin n))
    {A : Type} [AddCommGroup A] [Module ℂ A] {ρ : Representation ℂ (levi F n γ) A}
    (Ψ₀ : Representation.IntertwiningMap ρ
      (twist ((invSqrtModular F n γ).comp leviIncl)
        (indRep (cellLeviSub F β γ w) (cellInducing β γ w σ))))
    (hsurj : Function.Surjective Ψ₀) :
    ∃ Ψ : Representation.IntertwiningMap ρ (indRep (cellLeviSub F β γ w) (normInducing σ γ w)),
      Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ Ψ₀ x = 0 := by
  refine ⟨(indCongrHom σ w).comp ((indTwistHom σ w).comp Ψ₀), ?_, fun x => ?_⟩
  · exact (indCongrHom_surjective σ w).comp ((indTwistHom_surjective σ w).comp hsurj)
  · constructor
    · intro h
      apply indTwistHom_injective σ w
      apply indCongrHom_injective σ w
      rw [map_zero, map_zero]
      exact h
    · intro h
      show (indCongrHom σ w) ((indTwistHom σ w) (Ψ₀ x)) = 0
      rw [h, map_zero, map_zero]

end Filtration

theorem geometricLemma_uniform : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (β γ : Fin n → ℕ), ∃ (K : ℕ) (w : Fin K → Equiv.Perm (Fin n)), (∀ g : GL (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j)) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W), GroundTheory.Automorphic.IsSmooth σ → ∃ V : ℕ → Submodule ℂ (JacquetModule F n γ (parabolicInd F n β σ)), V 0 = ⊥ ∧ V K = ⊤ ∧ Monotone V ∧ ∃ hV : ∀ i (m : levi F n γ), V i ≤ (V i).comap (jacquetRep F n γ (parabolicInd F n β σ) m), ∀ j : Fin K, ∃ Ψ : Representation.IntertwiningMap ((jacquetRep F n γ (parabolicInd F n β σ)).subrepresentation (V (j + 1)) (hV (j + 1))) (indRep (cellLeviSub F β γ (w j)) (normInducing σ γ (w j))), Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ V j := by
  intro F _ _ _ _ n β γ
  obtain ⟨k, w, hcov, hanti⟩ := GroundTheory.Automorphic.Parabolic.exists_cellEnumeration (F := F) β γ
  refine ⟨k, w, hcov, fun W _ _ σ hσ => ?_⟩
  obtain ⟨V, h0, hk, hmono, hV, hΨ⟩ := filtration_of_cellEnumeration (γ := γ) w hcov hanti σ hσ
  refine ⟨V, h0, hk, hmono, hV, fun j => ?_⟩
  obtain ⟨Ψ₀, hsurj, hker⟩ := hΨ j
  obtain ⟨Ψ, hΨs, hΨk⟩ := normalized_piece σ (w j) Ψ₀ hsurj
  exact ⟨Ψ, hΨs, fun x => (hΨk x).trans (hker x)⟩

end GlobalTheory.CompanionTheory.GeomLemmaUniform
end
end

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bernstein_zelevinsky_geometric_lemma : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (β γ : Fin n → ℕ), ∃ (K : ℕ) (w : Fin K → Equiv.Perm (Fin n)), (∀ g : GL (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j)) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W), GroundTheory.Automorphic.IsSmooth σ → ∃ V : ℕ → Submodule ℂ (JacquetModule F n γ (parabolicInd F n β σ)), V 0 = ⊥ ∧ V K = ⊤ ∧ Monotone V ∧ ∃ hV : ∀ i (m : levi F n γ), V i ≤ (V i).comap (jacquetRep F n γ (parabolicInd F n β σ) m), ∀ j : Fin K, ∃ Ψ : Representation.IntertwiningMap ((jacquetRep F n γ (parabolicInd F n β σ)).subrepresentation (V (j + 1)) (hV (j + 1))) (indRep (cellLeviSub F β γ (w j)) (normInducing σ γ (w j))), Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ V j := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GeomLemmaUniform.geometricLemma_uniform
end

section
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.CellSizes

theorem card_blk_fiber {α : Type} {N : ℕ} {m : α → Type} [DecidableEq α] [∀ i, Fintype (m i)]
    (e : (Σ i, m i) ≃ Fin N) (i : α) :
    (Finset.univ.filter fun x : Fin N => blk e x = i).card = Fintype.card (m i) := by
  have h : (Finset.univ.filter fun x : Fin N => blk e x = i) =
      (Finset.univ : Finset (m i)).map
        ⟨fun y => e ⟨i, y⟩, fun a b hab => by simpa using e.injective hab⟩ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro rfl
      exact ⟨(e.symm x).2, e.apply_symm_apply x⟩
    · rintro ⟨y, rfl⟩
      exact blk_apply e i y
  rw [h, Finset.card_map, Finset.card_univ]

theorem sizes_sum : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (w : Equiv.Perm (Fin N)), (∀ i, ∑ j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = Fintype.card (m i)) ∧ ∀ j, ∑ i, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = Fintype.card (m' j) := by
  intro α _ _ N m _ _ β' _ _ m' _ _ e e' w
  constructor
  · intro i
    have h := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun x : Fin N => blk e x = i)
      (t := (Finset.univ : Finset β')) (f := fun x => blk e' (w.symm x))
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    simp only [Finset.filter_filter] at h
    rw [← h]
    exact card_blk_fiber e i
  · intro j
    have h := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun x : Fin N => blk e' (w.symm x) = j)
      (t := (Finset.univ : Finset α)) (f := fun x => blk e x)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    simp only [Finset.filter_filter] at h
    have h2 : (Finset.univ.filter fun x : Fin N => blk e' (w.symm x) = j).card =
        (Finset.univ.filter fun y : Fin N => blk e' y = j).card :=
      Finset.card_equiv w.symm (by simp)
    simp only [and_comm (a := blk e _ = _)]
    rw [← h, h2]
    exact card_blk_fiber e' j

end GlobalTheory.CompanionTheory.CellSizes
end

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.permutation_block_counts : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (w : Equiv.Perm (Fin N)), (∀ i, ∑ j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = Fintype.card (m i)) ∧ ∀ j, ∑ i, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = Fintype.card (m' j) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CellSizes.sizes_sum
end

section
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.GeoCell

open GroundTheory.Automorphic.Parabolic

theorem eq_iff_of_lt_iff {C A B : Type} [LinearOrder A] [LinearOrder B] (f : C → A) (g : C → B)
    (h : ∀ x y, f x < f y ↔ g x < g y) (x y : C) : f x = f y ↔ g x = g y := by
  constructor
  · intro hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have := (h _ _).2 h1
      rw [hxy] at this
      exact lt_irrefl _ this
    · have := (h _ _).2 h1
      rw [hxy] at this
      exact lt_irrefl _ this
  · intro hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have := (h _ _).1 h1
      rw [hxy] at this
      exact lt_irrefl _ this
    · have := (h _ _).1 h1
      rw [hxy] at this
      exact lt_irrefl _ this

theorem card_cell_of_card_corner {n : ℕ} {β γ : Fin n → ℕ} {w w' : Equiv.Perm (Fin n)}
    (h : ∀ a b, (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w j)).card =
      (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w' j)).card) (a b : ℕ) :
    (Finset.univ.filter fun j => γ j = b ∧ β (w j) = a).card =
      (Finset.univ.filter fun j => γ j = b ∧ β (w' j) = a).card := by
  classical
  have h1 : ∀ a b, (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (w j)).card =
      (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (w' j)).card := by
    intro a b
    cases b with
    | zero => simpa using h a 0
    | succ b =>
      have key : ∀ u : Equiv.Perm (Fin n),
          (Finset.univ.filter fun j => γ j ≤ b + 1 ∧ a ≤ β (u j)).card =
            (Finset.univ.filter fun j => γ j = b + 1 ∧ a ≤ β (u j)).card +
              (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (u j)).card := by
        intro u
        rw [← Finset.card_union_of_disjoint]
        · congr 1
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
          omega
        · rw [Finset.disjoint_filter]
          intro j _ h1 h2
          omega
      have := h a (b + 1)
      rw [key w, key w', h a b] at this
      omega
  have key : ∀ u : Equiv.Perm (Fin n),
      (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (u j)).card =
        (Finset.univ.filter fun j => γ j = b ∧ β (u j) = a).card +
          (Finset.univ.filter fun j => γ j = b ∧ a + 1 ≤ β (u j)).card := by
    intro u
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    · rw [Finset.disjoint_filter]
      intro j _ h1 h2
      omega
  have := h1 a b
  rw [key w, key w', h1 (a + 1) b] at this
  omega

theorem permGL_mem_doubleCoset_iff_card : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ), (∀ x y, γ x < γ y ↔ blk e' x < blk e' y) → ∀ (w w' : Equiv.Perm (Fin N)), permGL k w' ∈ doubleCoset (permGL k w) (blockUpper k N β : Set (GL (Fin N) k)) (blockUpper k N γ) ↔ ∀ i j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w'.symm x) = j).card) := by
  intro k _ _ _ _ α _ _ N m _ _ β' _ _ m' _ _ e β hβ e' γ hγ w w'
  classical
  have hβe := eq_iff_of_lt_iff β (blk e) hβ
  have hγe := eq_iff_of_lt_iff γ (blk e') hγ
  have reidx : ∀ (u : Equiv.Perm (Fin N)) (i : α) (j : β'),
      (Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (u.symm x) = j).card =
        (Finset.univ.filter fun y : Fin N => blk e (u y) = i ∧ blk e' y = j).card := by
    intro u i j
    apply Finset.card_equiv u.symm
    intro x
    simp
  constructor
  · intro hmem i j
    have hc : ∀ a b, (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w j)).card =
        (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w' j)).card := by
      intro a b
      rw [← cellRank_permGL (F := k), ← cellRank_permGL (F := k)]
      exact (cellRank_of_mem_doubleCoset hmem a b).symm
    rw [reidx, reidx]
    by_cases hi : ∃ x0, blk e x0 = i
    · by_cases hj : ∃ y0, blk e' y0 = j
      · obtain ⟨x0, rfl⟩ := hi
        obtain ⟨y0, rfl⟩ := hj
        have conv : ∀ u : Equiv.Perm (Fin N),
            (Finset.univ.filter fun y : Fin N => blk e (u y) = blk e x0 ∧ blk e' y = blk e' y0) =
              Finset.univ.filter fun y => γ y = γ y0 ∧ β (u y) = β x0 := by
          intro u
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hβe, hγe]
          tauto
        rw [conv, conv]
        exact card_cell_of_card_corner hc _ _
      · have hz : ∀ u : Equiv.Perm (Fin N),
            (Finset.univ.filter fun y : Fin N => blk e (u y) = i ∧ blk e' y = j) = ∅ := by
          intro u
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          exact fun h => hj ⟨y, h.2⟩
        rw [hz, hz]
    · have hz : ∀ u : Equiv.Perm (Fin N),
          (Finset.univ.filter fun y : Fin N => blk e (u y) = i ∧ blk e' y = j) = ∅ := by
        intro u
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        exact fun h => hi ⟨u y, h.1⟩
      rw [hz, hz]
  · intro h
    have hcard : ∀ c : α × β', Fintype.card {y : Fin N // (blk e (w y), blk e' y) = c} =
        Fintype.card {y : Fin N // (blk e (w' y), blk e' y) = c} := by
      intro c
      rw [Fintype.card_subtype, Fintype.card_subtype]
      have conv : ∀ u : Equiv.Perm (Fin N),
          (Finset.univ.filter fun y : Fin N => (blk e (u y), blk e' y) = c) =
            Finset.univ.filter fun y => blk e (u y) = c.1 ∧ blk e' y = c.2 := by
        intro u
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
      rw [conv, conv, ← reidx, ← reidx]
      exact h c.1 c.2
    let v : Fin N ≃ Fin N := Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcard c)
    have hv : ∀ j, (blk e (w' (v j)), blk e' (v j)) = (blk e (w j), blk e' j) := fun j =>
      Equiv.ofFiberEquiv_map (fun c => Fintype.equivOfCardEq (hcard c)) j
    have hvβ : ∀ j, β (w' (v j)) = β (w j) := fun j => (hβe _ _).2 (Prod.ext_iff.1 (hv j)).1
    have hvγ : ∀ j, γ (v j) = γ j := fun j => (hγe _ _).2 (Prod.ext_iff.1 (hv j)).2
    let u : Equiv.Perm (Fin N) := w' * v * w⁻¹
    have hu : ∀ x, β (u x) = β x := by
      intro x
      simp only [u, Equiv.Perm.mul_apply]
      rw [hvβ]
      simp
    have hv' : ∀ x, γ ((v⁻¹ : Equiv.Perm (Fin N)) x) = γ x := by
      intro x
      have := hvγ ((v⁻¹ : Equiv.Perm (Fin N)) x)
      have h' : v ((v⁻¹ : Equiv.Perm (Fin N)) x) = x := Equiv.apply_symm_apply v x
      rw [h'] at this
      exact this.symm
    refine DoubleCoset.mem_doubleCoset.2 ⟨permGL k u, permGL_mem_blockUpper hu, permGL k v⁻¹,
      permGL_mem_blockUpper hv', ?_⟩
    rw [← map_mul, ← map_mul]
    congr 1
    simp only [u]
    group

end GlobalTheory.CompanionTheory.GeoCell
end

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_coset_block_matrix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ), (∀ x y, γ x < γ y ↔ blk e' x < blk e' y) → ∀ (w w' : Equiv.Perm (Fin N)), permGL k w' ∈ doubleCoset (permGL k w) (blockUpper k N β : Set (GL (Fin N) k)) (blockUpper k N γ) ↔ ∀ i j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w'.symm x) = j).card) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GeoCell.permGL_mem_doubleCoset_iff_card
end

section
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.SizeCells

theorem exists_perm_cell_sizes : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (b : SizeMatrix m m'), ∃ w : Equiv.Perm (Fin N), ∀ i j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = b.1 i j := by
  intro α _ _ N m _ _ β' _ _ m' _ _ e e' b
  obtain ⟨f⟩ := b.nonempty_rows
  obtain ⟨g⟩ := b.nonempty_cols
  let A : (Σ i, Σ j, Fin (b.1 i j)) ≃ Fin N := (Equiv.sigmaCongrRight f).trans e
  let B : (Σ j, Σ i, Fin (b.1 i j)) ≃ Fin N := (Equiv.sigmaCongrRight g).trans e'
  let S : (Σ i, Σ j, Fin (b.1 i j)) ≃ (Σ j, Σ i, Fin (b.1 i j)) :=
    { toFun := fun p => ⟨p.2.1, p.1, p.2.2⟩
      invFun := fun p => ⟨p.2.1, p.1, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let w : Equiv.Perm (Fin N) := (B.symm.trans S.symm).trans A
  have hA : ∀ p, blk e (A p) = p.1 := by
    intro p
    simp [A, blk]
  have hB : ∀ p, blk e' (B p) = p.1 := by
    intro p
    simp [B, blk]
  have hw : ∀ p, w.symm (A p) = B (S p) := by
    intro p
    simp [w]
  refine ⟨w, fun i j => ?_⟩
  have himg : (Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j) =
      Finset.univ.image (fun t : Fin (b.1 i j) => A ⟨i, j, t⟩) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨⟨i', j', t⟩, rfl⟩ := A.surjective x
      rw [hA] at h1
      rw [hw, hB] at h2
      dsimp only [S, Equiv.coe_fn_mk] at h1 h2
      subst h1
      subst h2
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      refine ⟨hA _, ?_⟩
      rw [hw, hB]
      rfl
  rw [himg, Finset.card_image_of_injective _ (fun s t h => by simpa using A.injective h)]
  simp

end GlobalTheory.CompanionTheory.SizeCells
end

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perm_block_matrix : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (b : SizeMatrix m m'), ∃ w : Equiv.Perm (Fin N), ∀ i j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = b.1 i j := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SizeCells.exists_perm_cell_sizes
end

section
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.SmoothBridge

theorem isSmooth_comp {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (ψ : H →* G) (hψ : Continuous ψ) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (hρ : GlobalTheory.PRep.IsSmooth ρ) : GroundTheory.Automorphic.IsSmooth (ρ.comp ψ) := by
  intro v
  have h := (hρ v).preimage hψ
  exact h

end GlobalTheory.CompanionTheory.SmoothBridge
end

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmooth_comp_continuous : ∀ {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (ψ : H →* G), Continuous ψ → ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W), GlobalTheory.PRep.IsSmooth ρ → GroundTheory.Automorphic.IsSmooth (ρ.comp ψ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SmoothBridge.isSmooth_comp
end

section
section
set_option maxSynthPendingDepth 1

noncomputable section

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.CompanionTheory.SmGLBridge

namespace GlobalTheory.CompanionTheory.ParIndReindex

section Generic

variable {G G' V V' W : Type} [Group G] [Group G']
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]

theorem twKer_map (r : G ≃* G') (L : V ≃ₗ[ℂ] V') {π : Representation ℂ G V}
    {π' : Representation ℂ G' V'} (hL : ∀ g v, L (π g v) = π' (r g) (L v))
    {N : Subgroup G} {N' : Subgroup G'} (hN : ∀ g, g ∈ N ↔ r g ∈ N') :
    (twKer π N 1).map (L : V →ₗ[ℂ] V') = twKer π' N' 1 := by
  delta GlobalTheory.PRep.twKer
  rw [Submodule.map_span]
  congr 1
  ext w
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨n, v, rfl⟩, rfl⟩
    exact ⟨⟨r n, (hN n).1 n.2⟩, L v, by simp [hL]⟩
  · rintro ⟨n', v', rfl⟩
    refine ⟨_, ⟨⟨r.symm n', (hN _).2 (by simpa using n'.2)⟩, L.symm v', rfl⟩, ?_⟩
    simp [hL]

def jacquetEquiv (r : G ≃* G') (L : V ≃ₗ[ℂ] V') {π : Representation ℂ G V}
    {π' : Representation ℂ G' V'} (hL : ∀ g v, L (π g v) = π' (r g) (L v))
    {N : Subgroup G} {N' : Subgroup G'} (hN : ∀ g, g ∈ N ↔ r g ∈ N') :
    Jacquet π N ≃ₗ[ℂ] Jacquet π' N' :=
  Submodule.Quotient.equiv _ _ L (twKer_map r L hL hN)

def pullFun (r : G ≃* G') {H : Subgroup G} {H' : Subgroup G'}
    (hH : ∀ h : H, r h ∈ H') {σ : Representation ℂ H W} {σ' : Representation ℂ H' W}
    (hσ : ∀ h : H, σ' ⟨r h, hH h⟩ = σ h) (f : indSpace H' σ') : indSpace H σ :=
  ⟨fun x => f.1 (r x), fun h g => by
    show f.1 (r (h * g)) = σ h (f.1 (r g))
    rw [map_mul, ← hσ h]
    exact f.2 ⟨r h, hH h⟩ (r g)⟩

theorem ind_pullFun (r : G ≃* G') {H : Subgroup G} {H' : Subgroup G'}
    (hH : ∀ h : H, r h ∈ H') {σ : Representation ℂ H W} {σ' : Representation ℂ H' W}
    (hσ : ∀ h : H, σ' ⟨r h, hH h⟩ = σ h) (f : indSpace H' σ') (g : G) :
    ind H σ g (pullFun r hH hσ f) = pullFun r hH hσ (ind H' σ' (r g) f) := by
  apply Subtype.ext
  funext x
  show f.1 (r (x * g)) = f.1 (r x * r g)
  rw [map_mul]

theorem pullFun_eq_iff (r : G ≃* G') {H : Subgroup G} {H' : Subgroup G'}
    (hH : ∀ h : H, r h ∈ H') {σ : Representation ℂ H W} {σ' : Representation ℂ H' W}
    (hσ : ∀ h : H, σ' ⟨r h, hH h⟩ = σ h) (f f' : indSpace H' σ') :
    pullFun r hH hσ f = pullFun r hH hσ f' ↔ f = f' := by
  constructor
  · intro h
    apply Subtype.ext
    funext y
    have h1 : f.1 (r (r.symm y)) = f'.1 (r (r.symm y)) :=
      congrArg (fun p : indSpace H σ => p.1 (r.symm y)) h
    simpa using h1
  · rintro rfl
    rfl

variable [TopologicalSpace G] [TopologicalSpace G'] [IsTopologicalGroup G] [IsTopologicalGroup G']

def pull (r : G ≃* G') (hr : Continuous r) {H : Subgroup G} {H' : Subgroup G'}
    (hH : ∀ h : H, r h ∈ H') {σ : Representation ℂ H W} {σ' : Representation ℂ H' W}
    (hσ : ∀ h : H, σ' ⟨r h, hH h⟩ = σ h) :
    smoothPart (ind H' σ') →ₗ[ℂ] smoothPart (ind H σ) where
  toFun f := ⟨pullFun r hH hσ f.1, by
    have hset : {g : G | ind H σ g (pullFun r hH hσ f.1) = pullFun r hH hσ f.1} =
        r ⁻¹' {g' : G' | ind H' σ' g' f.1 = f.1} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_preimage, ind_pullFun, pullFun_eq_iff]
    show IsOpen {g : G | ind H σ g (pullFun r hH hσ f.1) = pullFun r hH hσ f.1}
    rw [hset]
    exact IsOpen.preimage hr f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def indEquiv (r : G ≃* G') (hr : Continuous r) (hs : Continuous r.symm) {H : Subgroup G}
    {H' : Subgroup G'} (hH : ∀ g, g ∈ H ↔ r g ∈ H') {σ : Representation ℂ H W}
    {σ' : Representation ℂ H' W} (hσ : ∀ h : H, σ' ⟨r h, (hH h).1 h.2⟩ = σ h) :
    smoothPart (ind H σ) ≃ₗ[ℂ] smoothPart (ind H' σ') :=
  LinearEquiv.ofLinear
    (pull r.symm hs (fun h' => (hH _).2 (by simp)) (fun h' => by
      rw [← hσ ⟨r.symm h', (hH _).2 (by simp)⟩]
      congr 1
      exact Subtype.ext (by simp)))
    (pull r hr (fun h => (hH h).1 h.2) hσ)
    (LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
      show f.1.1 (r (r.symm x)) = _
      simp)))
    (LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
      show f.1.1 (r.symm (r x)) = _
      simp)))

end Generic

section Reindex

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {N : ℕ}

theorem glReindex_apply (ι : n ≃ Fin N) (g : GL n k) (i j : n) :
    ((glReindex ι g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (ι i) (ι j) =
      (g : Matrix n n k) i j := by
  show (Matrix.reindexAlgEquiv k k ι (g : Matrix n n k)) (ι i) (ι j) = (g : Matrix n n k) i j
  simp [Matrix.coe_reindexAlgEquiv]

theorem mem_parab_reindex (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (g : GL n k) :
    g ∈ parab k e ↔ glReindex ι g ∈ parab k (e.trans ι) := by
  show (g : Matrix n n k).BlockTriangular (blk e) ↔
    ((glReindex ι g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).BlockTriangular (blk (e.trans ι))
  constructor
  · intro h i j hij
    have h2 := @h (ι.symm i) (ι.symm j) (by simpa [blk] using hij)
    have e1 := glReindex_apply ι g (ι.symm i) (ι.symm j)
    simp only [Equiv.apply_symm_apply] at e1
    rw [e1]
    exact h2
  · intro h i j hij
    have h2 := @h (ι i) (ι j) (by simpa [blk] using hij)
    rw [glReindex_apply] at h2
    exact h2

private theorem leviProj_glReindex (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (g : GL n k)
    (h : g ∈ parab k e) (h' : glReindex ι g ∈ parab k (e.trans ι)) :
    leviProj k (e.trans ι) ⟨glReindex ι g, h'⟩ = leviProj k e ⟨g, h⟩ := by
  funext a
  apply Units.ext
  ext i j
  show ((glReindex ι g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (ι (e ⟨a, i⟩)) (ι (e ⟨a, j⟩)) =
    (g : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩)
  exact glReindex_apply ι g _ _

theorem mem_unipRad_reindex (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (g : GL n k) :
    g ∈ unipRad k e ↔ glReindex ι g ∈ unipRad k (e.trans ι) := by
  show g ∈ Subgroup.map (parab k e).subtype (leviProj k e).ker ↔
    glReindex ι g ∈ Subgroup.map (parab k (e.trans ι)).subtype (leviProj k (e.trans ι)).ker
  simp only [Subgroup.mem_map, MonoidHom.mem_ker]
  constructor
  · rintro ⟨⟨p, hp'⟩, hp, rfl⟩
    refine ⟨⟨glReindex ι p, (mem_parab_reindex e ι p).1 hp'⟩, ?_, rfl⟩
    rw [leviProj_glReindex e ι p hp']
    exact hp
  · rintro ⟨⟨p, hp'⟩, hp, hpg⟩
    simp only [Subgroup.coe_subtype] at hpg
    subst hpg
    have hg : g ∈ parab k e := (mem_parab_reindex e ι g).2 hp'
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    rw [leviProj_glReindex e ι g hg hp'] at hp
    exact hp

theorem leviProj_reindex (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (p : parab k e) :
    leviProj k (e.trans ι) ⟨glReindex ι p, (mem_parab_reindex (k := k) e ι p.1).1 p.2⟩ = leviProj k e p := by
  exact leviProj_glReindex e ι p.1 p.2 _

theorem leviEmb_reindex (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (g : Levi k m) :
    glReindex ι (leviEmb k e g) = leviEmb k (e.trans ι) g := by
  apply Units.ext
  ext i j
  have h1 := glReindex_apply (k := k) ι (leviEmb k e g) (ι.symm i) (ι.symm j)
  simp only [Equiv.apply_symm_apply] at h1
  rw [h1]
  rfl

theorem continuous_glReindex_symm (ι : n ≃ Fin N) :
    Continuous (glReindex (k := k) ι).symm := by
  have h1 : ⇑(glReindex (k := k) ι).symm = ⇑(glReindex (k := k) ι.symm) :=
    funext (glReindex_symm ι)
  rw [h1]
  exact continuous_glReindex ι.symm

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def parIndEquiv (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (ρ : Representation ℂ (Levi k m) W) :
    IndSp e ρ ≃ₗ[ℂ] IndSp (e.trans ι) ρ :=
  indEquiv (glReindex ι) (continuous_glReindex ι) (continuous_glReindex_symm ι)
    (mem_parab_reindex e ι) (fun h => by
      show (twist ρ (deltaHalf k m)) (leviProj k (e.trans ι) _) = (twist ρ (deltaHalf k m)) (leviProj k e h)
      rw [leviProj_reindex])

theorem parIndEquiv_apply (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (ρ : Representation ℂ (Levi k m) W)
    (g : GL n k) (f : IndSp e ρ) :
    parIndEquiv e ι ρ (parInd e ρ g f) = parInd (e.trans ι) ρ (glReindex ι g) (parIndEquiv e ι ρ f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext y
  show f.1.1 ((glReindex ι).symm y * g) = f.1.1 ((glReindex ι).symm (y * glReindex ι g))
  rw [map_mul, MulEquiv.symm_apply_apply]

end Reindex

theorem jac_parInd_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' n : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] [Fintype n] [DecidableEq n] {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ n) (e' : (Σ j, m' j) ≃ n) {N : ℕ} (ι : n ≃ Fin N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), Nonempty ((jac e' (parInd e ρ)).Equiv (jac (e'.trans ι) (parInd (e.trans ι) ρ))) := by
  intro k _ _ _ _ α β' n _ _ _ _ _ _ m _ _ m' _ _ e e' N ι W _ _ ρ
  refine ⟨Representation.Equiv.mk
    (jacquetEquiv (glReindex (k := k) ι) (parIndEquiv e ι ρ) (parIndEquiv_apply e ι ρ)
      (mem_unipRad_reindex e' ι)) (fun l => ?_)⟩
  apply LinearMap.ext
  intro y
  obtain ⟨v, rfl⟩ := Quot.exists_rep y
  have h1 := parIndEquiv_apply e ι ρ (leviEmb k e' l) v
  rw [leviEmb_reindex] at h1
  have h2 : parIndEquiv e ι ρ ((((deltaHalf k m')⁻¹ l : ℂˣ) : ℂ) • parInd e ρ (leviEmb k e' l) v) =
      (((deltaHalf k m')⁻¹ l : ℂˣ) : ℂ) •
        parInd (e.trans ι) ρ (leviEmb k (e'.trans ι) l) (parIndEquiv e ι ρ v) := by
    rw [LinearEquiv.map_smul, h1]
  exact congrArg (Quot.mk _) h2

end GlobalTheory.CompanionTheory.ParIndReindex
end
end

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induction_reindex_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' n : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] [Fintype n] [DecidableEq n] {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ n) (e' : (Σ j, m' j) ≃ n) {N : ℕ} (ι : n ≃ Fin N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), Nonempty ((jac e' (parInd e ρ)).Equiv (jac (e'.trans ι) (parInd (e.trans ι) ρ))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ParIndReindex.jac_parInd_reindex
end

section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.GeoAssembly

def equivComp {G H V V' : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (e : ρ.Equiv ρ') (ψ : H →* G) : Representation.Equiv (ρ.comp ψ) (ρ'.comp ψ) :=
  Representation.Equiv.mk' ⟨e.toLinearEquiv.toLinearMap, fun h => by
      ext x; exact LinearMap.congr_fun (e.isIntertwining' (ψ h)) x⟩ e.invFun
    e.left_inv e.right_inv

set_option maxHeartbeats 1000000 in

theorem jacquetOfInducedFiltration : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetOfInducedFiltration k := by
  intro k _ _ _ _ α β n _ _ _ _ _ _ m _ _ m' _ _ e e'
  let N := Fintype.card n
  let ι : n ≃ Fin N := Fintype.equivFin n
  let E := e.trans ι
  let E' := e'.trans ι
  obtain ⟨βF, hβ⟩ := GlobalTheory.T.exists_strict_block_order m E
  obtain ⟨γF, hγ⟩ := GlobalTheory.T.exists_strict_block_order m' E'
  obtain ⟨φ, hφ, -, hφsc⟩ := GlobalTheory.T.levi_block_homeomorph k E βF hβ
  obtain ⟨φ', hφ', -, -⟩ := GlobalTheory.T.levi_block_homeomorph k E' γF hγ
  obtain ⟨K, w, hcov, hfilt⟩ := GlobalTheory.T.bernstein_zelevinsky_geometric_lemma k N βF γF
  let sz : Equiv.Perm (Fin N) → α → β → ℕ := fun v i j =>
    (Finset.univ.filter fun x : Fin N => blk E x = i ∧ blk E' (v.symm x) = j).card
  let toSM : Fin K → SizeMatrix m m' := fun t => ⟨sz (w t), GlobalTheory.T.permutation_block_counts E E' (w t)⟩
  have hsz : ∀ v v' : Equiv.Perm (Fin N), permGL k v' ∈ doubleCoset (permGL k v)
      (blockUpper k N βF : Set (GL (Fin N) k)) (blockUpper k N γF) ↔ sz v = sz v' := by
    intro v v'
    rw [GlobalTheory.T.double_coset_block_matrix k E βF hβ E' γF hγ v v']
    exact ⟨fun h => funext fun i => funext fun j => h i j, fun h i j => congrFun (congrFun h i) j⟩
  have hself : ∀ v : Equiv.Perm (Fin N), permGL k v ∈ doubleCoset (permGL k v)
      (blockUpper k N βF : Set (GL (Fin N) k)) (blockUpper k N γF) := fun v =>
    (hsz v v).2 rfl
  have inj : Function.Injective toSM := by
    intro t t' h
    have h1 : sz (w t) = sz (w t') := congrArg Subtype.val h
    obtain ⟨j, -, huniq⟩ := hcov (permGL k (w t'))
    exact (huniq t ((hsz _ _).2 h1)).trans (huniq t' (hself _)).symm
  have surj : Function.Surjective toSM := by
    intro B
    obtain ⟨v, hv⟩ := GlobalTheory.T.exists_perm_block_matrix E E' B
    obtain ⟨t, ht, -⟩ := hcov (permGL k v)
    refine ⟨t, Subtype.ext ?_⟩
    show sz (w t) = B.1
    rw [(hsz _ _).1 ht]
    exact funext fun i => funext fun j => hv i j
  refine ⟨K, Equiv.ofBijective toSM ⟨inj, surj⟩, ?_⟩
  intro W _ _ ρ hρ
  let σ := ρ.comp φ.symm.toMonoidHom
  have hσ : GroundTheory.Automorphic.IsSmooth σ := GlobalTheory.T.isSmooth_comp_continuous φ.symm.toMonoidHom hφsc ρ hρ
  have hF := hfilt W σ hσ
  obtain ⟨V, hF⟩ := hF
  obtain ⟨hV0, hF⟩ := hF
  obtain ⟨hVK, hF⟩ := hF
  obtain ⟨hVmono, hV, hΨ⟩ := hF
  have e1' := GlobalTheory.T.induction_reindex_equiv k e e' ι ρ
  obtain ⟨e1⟩ := e1'
  have e2' := GlobalTheory.T.jac_equiv_jacquetRep_comp_levi_equiv k E' γF hγ φ' hφ' (V := IndSp E ρ) (parInd E ρ)
  obtain ⟨e2⟩ := e2'
  have e3' := GlobalTheory.T.parabolicInd_equiv_levi_transport k E βF hβ φ hφ ρ
  obtain ⟨e3⟩ := e3'
  have e4' := GlobalTheory.T.jacquet_module_equiv k N γF (V := IndSp E ρ) (parInd E ρ) _ e3
  obtain ⟨e4⟩ := e4'
  have e12 := e1.trans e2
  have e45 := equivComp e4 φ'.toMonoidHom
  have e5 := e12.trans e45
  have hT := GlobalTheory.T.filtration_transport_equiv φ'.toMonoidHom _ _ e5 K _
    (fun j => indRep (cellLeviSub k βF γF (w j)) (normInducing σ γF (w j))) V hV0 hVK hVmono hV hΨ
  obtain ⟨S, hT⟩ := hT
  obtain ⟨hS1, hS2, hS3, hS4⟩ := hT
  refine ⟨S, hS1, hS2, hS3, fun t f g => ?_⟩
  have q1' := hS4 t
  obtain ⟨q1⟩ := q1'
  have c' := GlobalTheory.T.levi_intersection_conjugate k E βF hβ φ hφ E' γF hγ φ' hφ' ρ (w t)
  obtain ⟨f0, g0, c'⟩ := c'
  obtain ⟨q2⟩ := c'
  have q3' := GlobalTheory.T.cell_levi_tensor_decomposition (fun i j => by rw [Fintype.card_fin, Fintype.card_fin]; rfl) f0 g0 f g ρ
  obtain ⟨q3⟩ := q3'
  exact ⟨q1.trans (q2.trans q3)⟩

end GlobalTheory.CompanionTheory.GeoAssembly
end
