import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMapSurjectiveFiniteField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjOfIsConjGlFieldExtensionInclusionStatement

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.NormFibre

theorem card_conj_mul_card_commute {G : Type} [Group G] (g : G) :
    Nat.card {g' : G // IsConj g g'} * Nat.card {x : G // Commute x g} = Nat.card G := by
  have e1 : {g' : G // IsConj g g'} ≃ MulAction.orbit (ConjAct G) g :=
    Equiv.subtypeEquivRight (fun g' => by rw [ConjAct.mem_orbit_conjAct, isConj_comm])
  have e2 : {x : G // Commute x g} ≃ MulAction.stabilizer (ConjAct G) g :=
    { toFun := fun x => ⟨ConjAct.toConjAct x.1, by
          rw [MulAction.mem_stabilizer_iff, ConjAct.toConjAct_smul, x.2.eq, mul_inv_cancel_right]⟩
      invFun := fun y => ⟨ConjAct.ofConjAct y.1, by
          have h := y.2
          rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def, mul_inv_eq_iff_eq_mul] at h
          exact h⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [Nat.card_congr e1, Nat.card_congr e2, ← Nat.card_prod,
    Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct G) g),
    Nat.card_congr (ConjAct.toConjAct (G := G)).toEquiv.symm]

section Fields

variable {F F' : Type} [Field F] [Field F'] [Algebra F F']

theorem galAct_incl (n : ℕ) (t : F' ≃ₐ[F] F') (γ : GL (Fin n) F) :
    galAct F F' n t (incl F F' n γ) = incl F F' n γ := by
  ext i j
  simp [galAct_apply, gal, incl]

theorem galAct_coe (n : ℕ) (t : F' ≃ₐ[F] F') (x : GL (Fin n) F') :
    ((galAct F F' n t x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
      (x : Matrix (Fin n) (Fin n) F').map t := by
  ext i j
  simp [galAct_apply, gal]

end Fields

section Count

variable {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']

def nrmFibreEquivOf (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) {n : ℕ}
    {c g' : GL (Fin n) F'} (y : GL (Fin n) F') (hy : y * c * y⁻¹ = g') :
    {δ : GL (Fin n) F' // nrm s δ = g'} ≃ {δ : GL (Fin n) F' // nrm s δ = c} :=
  have htw := (GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n).2.2.1
  { toFun := fun δ => ⟨y⁻¹ * δ.1 * galAct F F' n s y, by
        rw [htw, δ.2, ← hy]; group⟩
    invFun := fun ε => ⟨y * ε.1 * galAct F F' n s y⁻¹, by
        have := htw ε.1 y⁻¹
        rw [inv_inv] at this
        rw [this, ε.2, hy]⟩
    left_inv := fun δ => by
      apply Subtype.ext
      simp only [map_inv]
      group
    right_inv := fun ε => by
      apply Subtype.ext
      simp only [map_inv]
      group }

def nrmFibreEquiv (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) {n : ℕ}
    {c g' : GL (Fin n) F'} (h : IsConj c g') :
    {δ : GL (Fin n) F' // nrm s δ = g'} ≃ {δ : GL (Fin n) F' // nrm s δ = c} :=
  nrmFibreEquivOf s hs _ (isConj_iff.1 h).choose_spec

theorem card_isConj_nrm (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) {n : ℕ}
    (c : GL (Fin n) F') :
    Nat.card {δ : GL (Fin n) F' // IsConj c (nrm s δ)} =
      Nat.card {g' : GL (Fin n) F' // IsConj c g'} * Nat.card {δ : GL (Fin n) F' // nrm s δ = c} := by
  have e : {δ : GL (Fin n) F' // IsConj c (nrm s δ)} ≃
      Σ g' : {g' : GL (Fin n) F' // IsConj c g'}, {δ : GL (Fin n) F' // nrm s δ = g'.1} :=
    { toFun := fun δ => ⟨⟨nrm s δ.1, δ.2⟩, ⟨δ.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, by rw [p.2.2]; exact p.1.2⟩
      left_inv := fun δ => rfl
      right_inv := fun p => by
        rcases p with ⟨⟨g', hg⟩, ⟨δ, hδ⟩⟩
        dsimp only at hδ
        subst hδ
        rfl }
  rw [← Nat.card_prod]
  exact Nat.card_congr (e.trans ((Equiv.sigmaCongrRight fun g' => nrmFibreEquiv s hs g'.2).trans
    (Equiv.sigmaEquivProd _ _)))

end Count

section Centraliser

variable {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']

theorem card_nrm_eq_mul_card_commute (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s)
    (n : ℕ) (γ : GL (Fin n) F) :
    Nat.card {δ : GL (Fin n) F' // nrm s δ = incl F F' n γ} * Nat.card {x : GL (Fin n) F // Commute x γ} =
      Nat.card {x : GL (Fin n) F' // Commute x (incl F F' n γ)} := by
  obtain ⟨-, hinj, -, hcomm, hmul⟩ := GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n
  obtain ⟨δ₀, hδ₀B, hδ₀⟩ := GlobalTheory.T.norm_map_surjective_finite_field F F' s hs n γ
  have hcfix : ∀ t : F' ≃ₐ[F] F', galAct F F' n t (incl F F' n γ) = incl F F' n γ := fun t => galAct_incl n t γ
  set c := incl F F' n γ with hc
  set B := Subalgebra.centralizer F' {(c : Matrix (Fin n) (Fin n) F')} with hB
  have memB : ∀ x : GL (Fin n) F', (x : Matrix (Fin n) (Fin n) F') ∈ B ↔ Commute x c := by
    intro x
    rw [hB, Subalgebra.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    rw [Commute, SemiconjBy, Units.ext_iff, Units.val_mul, Units.val_mul]
    exact eq_comm
  have hcs : (c : Matrix (Fin n) (Fin n) F').map s = c := by rw [← galAct_coe, hcfix]
  have hstab : ∀ x ∈ B, x.map s ∈ B := by
    intro x hx
    rw [hB, Subalgebra.mem_centralizer_iff] at hx ⊢
    simp only [Set.mem_singleton_iff, forall_eq] at hx ⊢
    have e1 : ((c : Matrix (Fin n) (Fin n) F') * x).map s = ((c : Matrix (Fin n) (Fin n) F').map s) * x.map s :=
      Matrix.map_mul (f := (s : F' →+* F'))
    have e2 : (x * (c : Matrix (Fin n) (Fin n) F')).map s = x.map s * ((c : Matrix (Fin n) (Fin n) F').map s) :=
      Matrix.map_mul (f := (s : F' →+* F'))
    rw [hcs] at e1 e2
    rw [← e1, ← e2, hx]
  have h90 := GlobalTheory.T.card_twistedNorm_one_mul_card_fixed_units F F' s hs n B hstab
  have hδ₀comm : ∀ e : GL (Fin n) F', Commute e c → Commute δ₀ e := by
    intro e he
    have hle : Algebra.adjoin F' {(c : Matrix (Fin n) (Fin n) F')} ≤
        Subalgebra.centralizer F' {(e : Matrix (Fin n) (Fin n) F')} := by
      apply Algebra.adjoin_le
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz, SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg, ← Units.val_mul, ← Units.val_mul, he.eq]
    have h1 := hle hδ₀B
    rw [Subalgebra.mem_centralizer_iff] at h1
    have h2 := h1 _ rfl
    exact Units.ext (by rw [Units.val_mul, Units.val_mul]; exact h2.symm)
  have hδ₀c : Commute δ₀ c := hδ₀comm c (Commute.refl c)
  have key : ∀ ε : GL (Fin n) F', Commute ε c → nrm s (δ₀ * ε) = c * nrm s ε := by
    intro ε hε
    rw [hmul δ₀ ε ?_, hδ₀]
    intro t u
    have h3 : Commute δ₀ (galAct F F' n (t⁻¹ * u) ε) := by
      apply hδ₀comm
      have := hε.map (galAct F F' n (t⁻¹ * u))
      rwa [hcfix] at this
    have h4 := h3.map (galAct F F' n t)
    have e : galAct F F' n t (galAct F F' n (t⁻¹ * u) ε) = galAct F F' n u ε := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]
    rwa [e] at h4
  have hYcomm : ∀ δ : GL (Fin n) F', nrm s δ = c → Commute δ c := by
    intro δ h
    have := hcomm δ
    rw [h, hcfix] at this
    exact this
  have eY : {δ : GL (Fin n) F' // nrm s δ = c} ≃
      {ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1} :=
    { toFun := fun δ => ⟨δ₀⁻¹ * δ.1, (memB _).2 (hδ₀c.inv_left.mul_left (hYcomm _ δ.2)), by
          have := key (δ₀⁻¹ * δ.1) (hδ₀c.inv_left.mul_left (hYcomm _ δ.2))
          rw [mul_inv_cancel_left, δ.2] at this
          simpa using this.symm⟩
      invFun := fun ε => ⟨δ₀ * ε.1, by rw [key _ ((memB _).1 ε.2.1), ε.2.2, mul_one]⟩
      left_inv := fun δ => Subtype.ext (mul_inv_cancel_left _ _)
      right_inv := fun ε => Subtype.ext (inv_mul_cancel_left _ _) }
  have eC' : {x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B} ≃ {x : GL (Fin n) F' // Commute x c} :=
    Equiv.subtypeEquivRight memB
  have eC : {x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B} ≃
      {x : GL (Fin n) F // Commute x γ} :=
    Equiv.subtypeEquivRight fun x => by
      rw [memB]
      exact ⟨fun h => hinj (by simpa only [map_mul] using h.eq), fun h => h.map _⟩
  rw [Nat.card_congr eY, ← Nat.card_congr eC, ← Nat.card_congr eC']
  exact h90

end Centraliser

theorem card_isNorm_mul_card : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (γ : GL (Fin n) F),
    Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ} * Nat.card (GL (Fin n) F) =
      Nat.card {γ' : GL (Fin n) F // IsConj γ γ'} * Nat.card (GL (Fin n) F') := by
  intro F F' _ _ _ _ s hs n γ
  have hX : Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ} =
      Nat.card {g' : GL (Fin n) F' // IsConj (incl F F' n γ) g'} *
        Nat.card {δ : GL (Fin n) F' // nrm s δ = incl F F' n γ} :=
    card_isConj_nrm s hs (incl F F' n γ)
  have hY := card_nrm_eq_mul_card_commute s hs n γ
  have h1 := card_conj_mul_card_commute (incl F F' n γ)
  have h2 := card_conj_mul_card_commute γ
  rw [hX, ← h2, ← h1, ← hY]
  ring

end GlobalTheory.Shin.NormFibre
end
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_isGaloisTwistedNormGL_mul_card_GL : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (γ : GL (Fin n) F), Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ} * Nat.card (GL (Fin n) F) = Nat.card {γ' : GL (Fin n) F // IsConj γ γ'} * Nat.card (GL (Fin n) F') := by
  first | (exact @GlobalTheory.Shin.NormFibre.card_isNorm_mul_card) | (exact GlobalTheory.Shin.NormFibre.card_isNorm_mul_card) | (intros; apply GlobalTheory.Shin.NormFibre.card_isNorm_mul_card  <;> assumption)
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem exists_isNorm : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (δ : GL (Fin n) F'), ∃ γ : GL (Fin n) F, IsNorm s δ γ := by
  intro F F' _ _ _ _ s hs n δ₀
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI : Finite (GL (Fin n) F) := inferInstance
  haveI : Finite (GL (Fin n) F') := inferInstance
  letI := Fintype.ofFinite (GL (Fin n) F)
  letI := Fintype.ofFinite (GL (Fin n) F')
  have hfib := GlobalTheory.T.card_isGaloisTwistedNormGL_mul_card_GL F F' s hs n
  have hnd := GlobalTheory.T.isConj_of_isConj_glFieldExtensionInclusion F F' n
  let cl : GL (Fin n) F → ℕ := fun γ => Nat.card {γ' : GL (Fin n) F // IsConj γ γ'}
  have hcl_pos : ∀ γ, 0 < cl γ := fun γ => Nat.card_pos_iff.2 ⟨⟨⟨γ, IsConj.refl γ⟩⟩, inferInstance⟩
  have hcl_eq : ∀ γ, (cl γ : ℚ) = ((Finset.univ.filter fun γ' => IsConj γ γ').card : ℚ) := by
    intro γ
    simp only [cl, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcard : ∀ γ, Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ}
      = (Finset.univ.filter fun δ => IsNorm s δ γ).card := by
    intro γ
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let f : GL (Fin n) F' → GL (Fin n) F → ℚ := fun δ γ => if IsNorm s δ γ then ((cl γ : ℚ))⁻¹ else 0
  have h1 : ∀ δ, ∑ γ, f δ γ = if ∃ γ, IsNorm s δ γ then 1 else 0 := by
    intro δ
    by_cases h : ∃ γ, IsNorm s δ γ
    · obtain ⟨γ₀, h₀⟩ := h
      rw [if_pos ⟨γ₀, h₀⟩]
      have hiff : ∀ γ, IsNorm s δ γ ↔ IsConj γ₀ γ := by
        intro γ
        constructor
        · intro hγ
          exact hnd γ₀ γ (h₀.trans hγ.symm)
        · intro hγ
          exact (isConj_iff.2 (by
            obtain ⟨c, hc⟩ := isConj_iff.1 hγ
            exact ⟨incl F F' n c, by rw [← hc]; simp [map_mul, map_inv]⟩)).symm.trans h₀
      have hcl' : ∀ γ, IsConj γ₀ γ → cl γ = cl γ₀ := by
        intro γ hγ
        exact Nat.card_congr (Equiv.subtypeEquivRight fun γ' => ⟨fun h => hγ.trans h, fun h => hγ.symm.trans h⟩)
      have : ∀ γ, f δ γ = if IsConj γ₀ γ then ((cl γ₀ : ℚ))⁻¹ else 0 := by
        intro γ
        simp only [f, hiff γ]
        split_ifs with hh
        · rw [hcl' γ hh]
        · rfl
      simp only [this]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, ← hcl_eq]
      exact mul_inv_cancel₀ (by exact_mod_cast (hcl_pos γ₀).ne')
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro γ _
      simp only [f]
      rw [if_neg (fun hh => h ⟨γ, hh⟩)]
  have h2 : ∀ γ, ∑ δ, f δ γ = (Nat.card (GL (Fin n) F') : ℚ) / Nat.card (GL (Fin n) F) := by
    intro γ
    simp only [f]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, ← hcard]
    have hG : (0 : ℚ) < Nat.card (GL (Fin n) F) := by exact_mod_cast Nat.card_pos
    have hc : (0 : ℚ) < cl γ := by exact_mod_cast hcl_pos γ
    have hq : (Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ} : ℚ) * Nat.card (GL (Fin n) F)
        = cl γ * Nat.card (GL (Fin n) F') := by exact_mod_cast hfib γ
    field_simp
    linarith [hq]
  have hsum : ∑ δ : GL (Fin n) F', (if ∃ γ, IsNorm s δ γ then (1 : ℚ) else 0) = ∑ δ : GL (Fin n) F', (1 : ℚ) := by
    simp only [← h1]
    rw [Finset.sum_comm]
    simp only [h2]
    rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ, Finset.card_univ,
      ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    have hG : (0 : ℚ) < Nat.card (GL (Fin n) F) := by exact_mod_cast Nat.card_pos
    field_simp
  have hle : ∀ δ ∈ (Finset.univ : Finset (GL (Fin n) F')),
      (if ∃ γ, IsNorm s δ γ then (1 : ℚ) else 0) ≤ 1 := by
    intro δ _
    split_ifs <;> norm_num
  have := (Finset.sum_eq_sum_iff_of_le hle).1 hsum δ₀ (Finset.mem_univ _)
  by_contra hno
  rw [if_neg hno] at this
  norm_num at this

end GlobalTheory.Shin
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.every_element_is_norm : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (δ : GL (Fin n) F'), ∃ γ : GL (Fin n) F, IsNorm s δ γ := by
  first | (exact @GlobalTheory.Shin.exists_isNorm) | (exact GlobalTheory.Shin.exists_isNorm) | (intros; apply GlobalTheory.Shin.exists_isNorm  <;> assumption)
end
