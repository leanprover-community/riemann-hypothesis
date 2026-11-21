import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousInvolutiveLocalTransposeInverse

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.MassTor

section Closed

variable {G : Type} [Group G] [TopologicalSpace G]

theorem isCompact_closure_zpowers_iff {T : Subgroup G} (hT : IsClosed (T : Set G)) (t : T) :
    IsCompact (closure (Subgroup.zpowers (t : G) : Set G)) ↔ IsCompact (closure (Subgroup.zpowers t : Set T)) := by
  have hE : Topology.IsClosedEmbedding (Subtype.val : T → G) := hT.isClosedEmbedding_subtypeVal
  have h1 : (Subgroup.zpowers (t : G) : Set G) = Subtype.val '' (Subgroup.zpowers t : Set T) := by
    have := MonoidHom.map_zpowers T.subtype t
    rw [← Subgroup.coe_subtype, ← Subgroup.coe_map, this]
  rw [h1, hE.closure_image_eq, ← hE.isEmbedding.isCompact_iff]

theorem cptPart_eq_map {T : Subgroup G} (hT : IsClosed (T : Set G)) :
    cptPart T = (Subgroup.closure {t : T | IsCompact (closure (Subgroup.zpowers t : Set T))}).map T.subtype := by
  rw [MonoidHom.map_closure]
  unfold cptPart
  congr 1
  ext g
  constructor
  · rintro ⟨hg, hc⟩
    exact ⟨⟨g, hg⟩, (isCompact_closure_zpowers_iff hT ⟨g, hg⟩).1 hc, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t.2, (isCompact_closure_zpowers_iff hT t).2 ht⟩

theorem cptPart_le (T : Subgroup G) : cptPart T ≤ T :=
  (Subgroup.closure_le _).2 fun _ hg => hg.1

theorem mem_cptPart_iff {T : Subgroup G} (hT : IsClosed (T : Set G)) (t : T) :
    (t : G) ∈ cptPart T ↔ t ∈ Subgroup.closure {s : T | IsCompact (closure (Subgroup.zpowers s : Set T))} := by
  rw [cptPart_eq_map hT, Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, h⟩
    rwa [show s = t from Subtype.ext h] at hs
  · intro h
    exact ⟨t, h, rfl⟩

end Closed

theorem mem_closure_cpt_iff {A B : Type} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B] (e : A ≃ₜ* B)
    (a : A) :
    a ∈ Subgroup.closure {s : A | IsCompact (closure (Subgroup.zpowers s : Set A))} ↔
      e a ∈ Subgroup.closure {s : B | IsCompact (closure (Subgroup.zpowers s : Set B))} := by
  have key : ∀ s : A, IsCompact (closure (Subgroup.zpowers s : Set A)) ↔
      IsCompact (closure (Subgroup.zpowers (e s) : Set B)) := by
    intro s
    have h1 : (Subgroup.zpowers (e s) : Set B) = e '' (Subgroup.zpowers s : Set A) := by
      have := MonoidHom.map_zpowers e.toMulEquiv.toMonoidHom s
      have h := congrArg (fun H : Subgroup B => (H : Set B)) this
      rw [Subgroup.coe_map] at h
      exact h.symm
    rw [h1]
    have h2 := e.toHomeomorph.image_closure (Subgroup.zpowers s : Set A)
    have h3 := e.toHomeomorph.isCompact_image (s := closure (Subgroup.zpowers s : Set A))
    rw [show (⇑e.toHomeomorph : A → B) = ⇑e from rfl] at h2 h3
    rw [← h2, h3]
  have himg : e.toMulEquiv.toMonoidHom '' {s : A | IsCompact (closure (Subgroup.zpowers s : Set A))} =
      {s : B | IsCompact (closure (Subgroup.zpowers s : Set B))} := by
    ext b
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (key s).1 hs
    · intro hb
      refine ⟨e.symm b, (key _).2 ?_, ?_⟩
      · simpa using hb
      · exact e.apply_symm_apply b
  have hmap := MonoidHom.map_closure e.toMulEquiv.toMonoidHom
    {s : A | IsCompact (closure (Subgroup.zpowers s : Set A))}
  rw [himg] at hmap
  rw [← hmap, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨a, h, rfl⟩
  · rintro ⟨x, hx, h⟩
    have : x = a := e.injective h
    rwa [← this]

theorem card_doubleCoset_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) (H K : Subgroup A) (H' K' : Subgroup B)
    (hH : ∀ a, a ∈ H ↔ e a ∈ H') (hK : ∀ a, a ∈ K ↔ e a ∈ K') :
    Nat.card (DoubleCoset.Quotient (H : Set A) (K : Set A)) =
      Nat.card (DoubleCoset.Quotient (H' : Set B) (K' : Set B)) := by
  apply Nat.card_congr
  refine Quotient.congr e.toEquiv fun x y => ?_
  rw [DoubleCoset.rel_iff, DoubleCoset.rel_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨e a, (hH a).1 ha, e b, (hK b).1 hb, by simp [map_mul]⟩
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨e.symm a, (hH _).2 (by simpa using ha), e.symm b, (hK _).2 (by simpa using hb), ?_⟩
    apply e.injective
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv] at h
    simp [map_mul, h]

theorem isClosed_twCent {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (θ : G →* G)
    (hθ : Continuous θ) (δ : G) : IsClosed (twCent θ δ : Set G) :=
  isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul hθ)

theorem mass_eq_of_equiv (G G' : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] (θ : G →* G) (θ' : G' →* G') (Γ : Subgroup G) (Γ' : Subgroup G')
    (δ : G) (δ' : G') (hT : IsClosed (twCent θ δ : Set G)) (hT' : IsClosed (twCent θ' δ' : Set G'))
    (e : twCent θ δ ≃ₜ* twCent θ' δ')
    (hΓ : ∀ t : twCent θ δ, (t : G) ∈ Γ ↔ ((e t : twCent θ' δ') : G') ∈ Γ') :
    mass θ Γ δ = mass θ' Γ' δ' := by
  have hC : ∀ t : twCent θ δ, (t : G) ∈ cptPart (twCent θ δ) ↔ ((e t : twCent θ' δ') : G') ∈ cptPart (twCent θ' δ') :=
    fun t => by rw [mem_cptPart_iff hT, mem_cptPart_iff hT', mem_closure_cpt_iff e]
  have hmem : ∀ t : twCent θ δ, (t : G) ∈ Γ ⊓ cptPart (twCent θ δ) ↔
      ((e t : twCent θ' δ') : G') ∈ Γ' ⊓ cptPart (twCent θ' δ') := fun t => by
    simp only [Subgroup.mem_inf]
    rw [hΓ t, hC t]
  let f : (Γ ⊓ cptPart (twCent θ δ) : Subgroup G) ≃ (Γ' ⊓ cptPart (twCent θ' δ') : Subgroup G') :=
    { toFun := fun g => ⟨(e ⟨g, cptPart_le _ g.2.2⟩ : G'), (hmem _).1 g.2⟩
      invFun := fun g' => ⟨(e.symm ⟨g', cptPart_le _ g'.2.2⟩ : G),
        (hmem (e.symm ⟨g', cptPart_le _ g'.2.2⟩)).2 (by rw [e.apply_symm_apply]; exact g'.2)⟩
      left_inv := fun g => by ext; simp
      right_inv := fun g' => by ext; simp }
  unfold mass
  rw [card_doubleCoset_congr e.toMulEquiv _ _ (Γ'.subgroupOf (twCent θ' δ')) ((cptPart (twCent θ' δ')).subgroupOf _)
    (fun a => by simp only [Subgroup.mem_subgroupOf]; exact hΓ a)
    (fun a => by simp only [Subgroup.mem_subgroupOf]; exact hC a), Nat.card_congr f]

end GlobalTheory.MassTor
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedCentralizerMass_eq_of_topEquiv : ∀ (G G' : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] (θ : G →* G) (θ' : G' →* G') (Γ : Subgroup G) (Γ' : Subgroup G') (δ : G) (δ' : G'), IsClosed (twCent θ δ : Set G) → IsClosed (twCent θ' δ' : Set G') → ∀ (e : twCent θ δ ≃ₜ* twCent θ' δ'), (∀ t : twCent θ δ, (t : G) ∈ Γ ↔ ((e t : twCent θ' δ') : G') ∈ Γ') → mass θ Γ δ = mass θ' Γ' δ' := by
  first | exact @GlobalTheory.MassTor.mass_eq_of_equiv | exact GlobalTheory.MassTor.mass_eq_of_equiv | (intros; apply GlobalTheory.MassTor.mass_eq_of_equiv <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.MassNorm

open GlobalTheory.ClassParam (krylov)

section Core

variable {R : Type} [CommRing R] {m : ℕ}

theorem aeval_of_commute_cyclic {M N : Matrix (Fin m) (Fin m) R} (v : Fin m → R) (hv : IsUnit (krylov M v).det)
    (h : Commute N M) : ∃ p : R[X], N = aeval M p := by
  let a := (krylov M v)⁻¹ *ᵥ (N *ᵥ v)
  let p : R[X] := ∑ j : Fin m, monomial (j : ℕ) (a j)
  have hp : aeval M p *ᵥ v = N *ᵥ v := by
    have : krylov M v *ᵥ a = N *ᵥ v := by rw [mulVec_mulVec, mul_nonsing_inv _ hv, one_mulVec]
    rw [← this]
    ext i
    simp [p, krylov, map_sum, aeval_monomial, Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.mulVec.eq_def (Matrix.of _), dotProduct, mul_comm]
  have hc : Commute (aeval M p) M := by
    have := congrArg (aeval M) (mul_comm p X)
    rwa [map_mul, map_mul, aeval_X] at this
  refine ⟨p, ((isUnit_iff_isUnit_det _).2 hv).mul_right_cancel ?_⟩
  rw [GlobalTheory.Orb.mul_krylov_of_commute h, GlobalTheory.Orb.mul_krylov_of_commute hc, hp]

def psi (c : R →+* R) (D : GL (Fin m) R) (x : Matrix (Fin m) (Fin m) R) : Matrix (Fin m) (Fin m) R :=
  D.val * GlobalTheory.Tw.Phi m R * (c.mapMatrix x)ᵀ * (GlobalTheory.Tw.Phi m R)ᵀ * (D⁻¹).val

theorem PhiT_mul_Phi : (GlobalTheory.Tw.Phi m R)ᵀ * GlobalTheory.Tw.Phi m R = 1 := mul_eq_one_comm.1 (Phi_mul_transpose m R)

theorem psi_mul (c : R →+* R) (D : GL (Fin m) R) (x y : Matrix (Fin m) (Fin m) R) :
    psi c D (x * y) = psi c D y * psi c D x := by
  have h1 : (D⁻¹).val * D.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [psi, map_mul, Matrix.transpose_mul]
  calc _ = D.val * GlobalTheory.Tw.Phi m R * (c.mapMatrix y)ᵀ * ((GlobalTheory.Tw.Phi m R)ᵀ * ((D⁻¹).val * D.val) * GlobalTheory.Tw.Phi m R) *
        (c.mapMatrix x)ᵀ * (GlobalTheory.Tw.Phi m R)ᵀ * (D⁻¹).val := by
        rw [h1, Matrix.mul_one, PhiT_mul_Phi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem psi_add (c : R →+* R) (D : GL (Fin m) R) (x y : Matrix (Fin m) (Fin m) R) :
    psi c D (x + y) = psi c D x + psi c D y := by
  simp only [psi, map_add, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem psi_smul (c : R →+* R) (D : GL (Fin m) R) (r : R) (x : Matrix (Fin m) (Fin m) R) :
    psi c D (r • x) = c r • psi c D x := by
  have : c.mapMatrix (r • x) = c r • c.mapMatrix x := by ext i j; simp
  simp only [psi, this, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem psi_one (c : R →+* R) (D : GL (Fin m) R) : psi c D 1 = 1 := by
  simp only [psi, map_one, Matrix.transpose_one, Matrix.mul_one]
  rw [Matrix.mul_assoc D.val, Phi_mul_transpose, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem psi_pow (c : R →+* R) (D : GL (Fin m) R) (x : Matrix (Fin m) (Fin m) R) (k : ℕ) :
    psi c D (x ^ k) = psi c D x ^ k := by
  induction k with
  | zero => simp [psi_one]
  | succ k ih => rw [pow_succ, psi_mul, ih, pow_succ']

theorem psi_aeval (c : R →+* R) (D : GL (Fin m) R) (x : Matrix (Fin m) (Fin m) R) (p : R[X]) :
    psi c D (aeval x p) = aeval (psi c D x) (p.map c) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, psi_add, hp, hq, Polynomial.map_add, map_add]
  | monomial k r =>
    rw [aeval_monomial, Polynomial.map_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul, psi_smul, psi_pow, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem psi_units (c : R →+* R) (D h : GL (Fin m) R) :
    psi c D h.val = (D * thetaGL m c h⁻¹ * D⁻¹).val := by
  rw [Units.val_mul, Units.val_mul, GlobalTheory.LocTwist.thetaGL_val, inv_inv]
  simp only [psi, Matrix.mul_assoc]

theorem twCent_le (c : R →+* R) (hc : ∀ x, c (c x) = x) (D₁ D₂ : GL (Fin m) R)
    (hN : D₁ * thetaGL m c D₁ = D₂ * thetaGL m c D₂) (v : Fin m → R)
    (hv : IsUnit (krylov (D₁ * thetaGL m c D₁).val v).det) :
    twCent (thetaGL m c) D₁ ≤ twCent (thetaGL m c) D₂ := by
  have hθ : ∀ g, thetaGL m c (thetaGL m c g) = g := GlobalTheory.LocTwist.thetaGL_thetaGL m c hc
  have hpsiN : ∀ D : GL (Fin m) R, psi c D (D * thetaGL m c D).val = ((D * thetaGL m c D)⁻¹).val := by
    intro D
    rw [psi_units]
    congr 1
    simp only [_root_.mul_inv_rev, map_mul, map_inv, hθ]
    group
  have hmem : ∀ (D g : GL (Fin m) R), g ∈ twCent (thetaGL m c) D ↔ psi c D g.val = (g⁻¹).val := by
    intro D g
    rw [psi_units]
    constructor
    · intro h
      have h' : g⁻¹ * D = D * thetaGL m c g⁻¹ := (twCent (thetaGL m c) D).inv_mem h
      congr 1
      rw [← h']; group
    · intro h
      have h' : D * thetaGL m c g⁻¹ * D⁻¹ = g⁻¹ := Units.ext h
      have : g⁻¹ ∈ twCent (thetaGL m c) D := by
        change g⁻¹ * D = D * thetaGL m c g⁻¹
        calc g⁻¹ * D = (D * thetaGL m c g⁻¹ * D⁻¹) * D := by rw [h']
          _ = _ := by group
      simpa using (twCent (thetaGL m c) D).inv_mem this
  intro g hg
  have hcomm : g * (D₁ * thetaGL m c D₁) = (D₁ * thetaGL m c D₁) * g := by
    have h1 : g * D₁ = D₁ * thetaGL m c g := hg
    have h2 : thetaGL m c g = D₁⁻¹ * g * D₁ := by rw [mul_assoc, h1]; group
    have h3 := congrArg (thetaGL m c) h2
    rw [hθ, map_mul, map_mul, map_inv, h2] at h3
    calc g * (D₁ * thetaGL m c D₁)
        = (D₁ * thetaGL m c D₁) * ((thetaGL m c D₁)⁻¹ * (D₁⁻¹ * g * D₁) * thetaGL m c D₁) := by group
      _ = _ := by rw [← h3]
  obtain ⟨p, hp⟩ := aeval_of_commute_cyclic v hv (N := g.val) (by
    change g.val * (D₁ * thetaGL m c D₁).val = (D₁ * thetaGL m c D₁).val * g.val
    rw [← Units.val_mul, ← Units.val_mul, hcomm])
  have e1 := psi_aeval c D₁ (D₁ * thetaGL m c D₁).val p
  rw [hpsiN] at e1
  have e2 := psi_aeval c D₂ (D₂ * thetaGL m c D₂).val p
  rw [hpsiN, ← hN] at e2
  rw [hmem] at hg ⊢
  rw [← hg, hp, e1, e2]

end Core

section Global

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem thF_ratF (m : ℕ) (g : GL (Fin m) E) : thF E m (ratF E m g) = ratF E m (thE E m g) :=
  (GlobalTheory.ThetaPull.map_thetaGL (algebraMap E (Af E)) _ _
    (fun x => (conjFin_algebraMap (IsCMField.complexConj E).toRingEquiv x).symm) g).symm

theorem isClosed_twCent_thF (m : ℕ) (δ : GL (Fin m) (Af E)) : IsClosed (twCent (thF E m) δ : Set (GL (Fin m) (Af E))) := by
  have e : (twCent (thF E m) δ : Set (GL (Fin m) (Af E))) = {g | (g * δ).val = (δ * thF E m g).val} := by
    ext g; exact Units.ext_iff
  rw [e]
  haveI : T2Space (Af E) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  exact isClosed_eq (Units.continuous_val.comp (continuous_id.mul continuous_const))
    (Units.continuous_val.comp (continuous_const.mul (GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _))))

theorem mass_eq_of_charpoly (m : ℕ) (δ₁ δ₂ : GL (Fin m) E)
    (h : (δ₂ * thE E m δ₂).val.charpoly = (δ₁ * thE E m δ₁).val.charpoly)
    (hs : (δ₁ * thE E m δ₁).val.charpoly.Separable) :
    mass (thF E m) (ratF E m).range (ratF E m δ₂) = mass (thF E m) (ratF E m).range (ratF E m δ₁) := by
  have hθE : ∀ g, thE E m (thE E m g) = g :=
    GlobalTheory.ThetaPull.thetaGL_thetaGL _ (fun x => IsCMField.complexConj_apply_apply E x)
  obtain ⟨x, hx⟩ := GlobalTheory.Orb.IsRegSS.exists_conj (A := E) (M := (δ₁ * thE E m δ₁).val) hs h
  have hx' : (δ₂ * thE E m δ₂) * x = x * (δ₁ * thE E m δ₁) := Units.ext hx
  have hu : (x⁻¹ * δ₂ * thE E m x) * thE E m (x⁻¹ * δ₂ * thE E m x) = δ₁ * thE E m δ₁ := by
    simp only [map_mul, map_inv, hθE]
    calc _ = x⁻¹ * ((δ₂ * thE E m δ₂) * x) := by group
      _ = _ := by rw [hx']; group
  have hc : ∀ y, conjFin (IsCMField.complexConj E).toRingEquiv (conjFin (IsCMField.complexConj E).toRingEquiv y) = y :=
    fun y => GlobalTheory.ThetaPull.cFin_cFin y
  have hN : ratF E m δ₁ * thF E m (ratF E m δ₁) =
      ratF E m (x⁻¹ * δ₂ * thE E m x) * thF E m (ratF E m (x⁻¹ * δ₂ * thE E m x)) := by
    rw [thF_ratF, thF_ratF, ← map_mul, ← map_mul, hu]
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field _ hs
  have hv' : IsUnit (GlobalTheory.ClassParam.krylov (ratF E m δ₁ * thF E m (ratF E m δ₁)).val (algebraMap E (Af E) ∘ v)).det := by
    have h1 := (IsUnit.mk0 _ hv).map (algebraMap E (Af E))
    rw [RingHom.map_det, RingHom.mapMatrix_apply, GlobalTheory.ClassParam.krylov_map] at h1
    rw [thF_ratF, ← map_mul]
    exact h1
  have heq : twCent (thF E m) (ratF E m δ₁) = twCent (thF E m) (ratF E m (x⁻¹ * δ₂ * thE E m x)) :=
    le_antisymm (twCent_le _ hc _ _ hN _ hv') (twCent_le _ hc _ _ hN.symm _ (hN ▸ hv'))
  set y := ratF E m x with hy
  have hconj : ratF E m (x⁻¹ * δ₂ * thE E m x) = y⁻¹ * ratF E m δ₂ * thF E m y := by
    rw [hy, thF_ratF, map_mul, map_mul, map_inv]
  have hT : twCent (thF E m) (ratF E m δ₁) = (twCent (thF E m) (ratF E m δ₂)).map (MulAut.conj y⁻¹).toMonoidHom := by
    rw [heq, hconj, GlobalTheory.TwOrbConj.twCent_conj]
  have hf : ∀ t : twCent (thF E m) (ratF E m δ₂), y⁻¹ * (t : GL (Fin m) (Af E)) * y ∈ twCent (thF E m) (ratF E m δ₁) := by
    intro t
    rw [hT]
    exact ⟨t, t.2, by simp [MulAut.conj_apply]⟩
  have hg : ∀ s : twCent (thF E m) (ratF E m δ₁), y * (s : GL (Fin m) (Af E)) * y⁻¹ ∈ twCent (thF E m) (ratF E m δ₂) := by
    intro s
    have hs' : (s : GL (Fin m) (Af E)) ∈ (twCent (thF E m) (ratF E m δ₂)).map (MulAut.conj y⁻¹).toMonoidHom :=
      hT ▸ s.2
    obtain ⟨t, ht, he⟩ := hs'
    have : (s : GL (Fin m) (Af E)) = y⁻¹ * t * y := by rw [← he]; simp [MulAut.conj_apply]
    rw [this]; simpa [mul_assoc] using ht
  let e : twCent (thF E m) (ratF E m δ₂) ≃ₜ* twCent (thF E m) (ratF E m δ₁) :=
    { toFun := fun t => ⟨y⁻¹ * t * y, hf t⟩
      invFun := fun s => ⟨y * s * y⁻¹, hg s⟩
      left_inv := fun t => Subtype.ext (by simp [mul_assoc])
      right_inv := fun s => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := Continuous.subtype_mk
        ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
      continuous_invFun := Continuous.subtype_mk
        ((continuous_const.mul continuous_subtype_val).mul continuous_const) _ }
  have hyΓ : y ∈ (ratF E m).range := ⟨x, rfl⟩
  refine GlobalTheory.T.twistedCentralizerMass_eq_of_topEquiv _ _ (thF E m) (thF E m) _ _ (ratF E m δ₂) (ratF E m δ₁) (isClosed_twCent_thF E m _)
    (isClosed_twCent_thF E m _) e fun t => ?_
  change (t : GL (Fin m) (Af E)) ∈ (ratF E m).range ↔ y⁻¹ * (t : GL (Fin m) (Af E)) * y ∈ (ratF E m).range
  rw [Subgroup.mul_mem_cancel_right _ hyΓ, Subgroup.mul_mem_cancel_left _ ((ratF E m).range.inv_mem hyΓ)]

end Global

end GlobalTheory.MassNorm

theorem GlobalTheory.BCT.mass_eq_kap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (δ : GL (Fin n) E), (δ * thE E n δ).val.charpoly ∈ Ell E n → mass (thF E n) (ratF E n).range (ratF E n δ) = kap (δ * thE E n δ).val.charpoly * 2 ^ nfac (δ * thE E n δ).val.charpoly := by
  intro E _ _ _ _ n δ hP
  have hd : (δ * thE E n δ).val.charpoly.natDegree = n := hP.2.1
  have hs : (δ * thE E n δ).val.charpoly.Separable := hP.2.2.1
  generalize hPdef : (δ * thE E n δ).val.charpoly = P at hd hs ⊢
  have hcast : ∀ (k : ℕ) (_ : k = n), (∃ δ' : GL (Fin k) E, (δ' * thE E k δ').val.charpoly = P) ∧
      ∀ δ' : GL (Fin k) E, (δ' * thE E k δ').val.charpoly = P →
        mass (thF E k) (ratF E k).range (ratF E k δ') = mass (thF E n) (ratF E n).range (ratF E n δ) := by
    intro k hk
    subst hk
    exact ⟨⟨δ, hPdef⟩, fun δ' h' => GlobalTheory.MassNorm.mass_eq_of_charpoly E k δ δ' (h'.trans hPdef.symm) (hPdef ▸ hs)⟩
  obtain ⟨hex, hm⟩ := hcast _ hd
  unfold GlobalTheory.BCT.kap GlobalTheory.BCT.nfac
  rw [dif_pos hex, hm _ hex.choose_spec, div_mul_cancel₀ _ (pow_ne_zero _ two_ne_zero)]
end
end
