import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapNormCoeff
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharpolyBaseChangeIntegrallyClosed

section
section
noncomputable section

namespace GlobalTheory.NormalDescent

open CategoryTheory Polynomial TensorProduct

theorem charK_map_of_isPushout {A B A' B' K K' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Field K] [Field K'] [Algebra A K] [Algebra A' K'] (φ : A →+* B) (α : A →+* A') (β : B →+* B')
    (φ' : A' →+* B')
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ'))
    (hφ : φ.Finite) (hφ' : φ'.Finite) (ι : K →+* K')
    (hι : ∀ a : A, ι (algebraMap A K a) = algebraMap A' K' (α a)) (b : B) :
    charK φ' hφ' K' (β b) = (charK φ hφ K b).map ι := by
  algebraize [φ, α, β, φ', φ'.comp α]
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm
  have P : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.1 H
  have hb : IsBaseChange A' (IsScalarTower.toAlgHom A B B').toLinearMap := P.symm.out
  haveI : Module.Finite A B := hφ
  haveI : Module.Finite A' B' := hφ'
  letI : Algebra K K' := ι.toAlgebra
  letI : Algebra A K' := (ι.comp (algebraMap A K)).toAlgebra
  haveI : IsScalarTower A K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A A' K' := IsScalarTower.of_algebraMap_eq fun a => hι a
  let e : K' ⊗[K] (K ⊗[A] B) ≃ₗ[K'] K' ⊗[A'] B' :=
    AlgebraTensorModule.cancelBaseChange A K K' K' B ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange A A' K' K' B).symm ≪≫ₗ
      AlgebraTensorModule.congr (LinearEquiv.refl K' K') hb.equiv
  unfold charK
  change (Algebra.lmul K' (K' ⊗[A'] B') (1 ⊗ₜ β b)).charpoly =
    (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).charpoly.map (algebraMap K K')
  rw [← LinearMap.charpoly_baseChange, ← e.charpoly_conj]
  congr 1
  refine LinearMap.ext fun y => ?_
  obtain ⟨t, rfl⟩ := e.surjective y
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul c' u =>
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [tmul_add, map_add, hs, ht]
    | tmul c x =>
      simp [e, IsBaseChange.equiv_tmul]
      rfl

end GlobalTheory.NormalDescent
end
end

open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpolyMulBaseChangeFinite_map_of_isPushout : ∀ {A B A' B' K K' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Field K] [Field K']
    [Algebra A K] [Algebra A' K'] (φ : A →+* B) (α : A →+* A') (β : B →+* B') (φ' : A' →+* B'),
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ') →
    ∀ (hφ : φ.Finite) (hφ' : φ'.Finite) (ι : K →+* K'), (∀ a : A, ι (algebraMap A K a) = algebraMap A' K' (α a)) →
    ∀ b : B, charK φ' hφ' K' (β b) = (charK φ hφ K b).map ι := by
  atlas_forward_decl GlobalTheory.NormalDescent.charK_map_of_isPushout
end

section
section
open CategoryTheory Polynomial GlobalTheory.NormalDescent

namespace GlobalTheory.NormalDescent

theorem reverse_map_of_injective {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (Q : R[X]) : (Q.map f).reverse = Q.reverse.map f := by
  rw [reverse, reverse, natDegree_map_eq_of_injective hf, reflect_map]

theorem normCoeff_map_of_isPushout {A B A' B' : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [CommRing A']
    [IsDomain A'] [IsIntegrallyClosed A'] [CommRing B'] (φ : A →+* B) (α : A →+* A') (β : B →+* B') (φ' : A' →+* B')
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ'))
    (hα : Function.Injective α) (hφ : φ.Finite) (hφ' : φ'.Finite) (b : B) (k : ℕ) :
    α (normCoeff φ hφ b k) = normCoeff φ' hφ' (β b) k := by
  have hbc := @GlobalTheory.T.charpolyMulBaseChangeFinite_map_of_isPushout
  have hint := @GlobalTheory.T.exists_charpoly_baseChange_integrallyClosed
  let ι : FractionRing A →+* FractionRing A' := IsLocalization.map (FractionRing A') α
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective α hα)
  have hι : ∀ a : A, ι (algebraMap A (FractionRing A) a) = algebraMap A' (FractionRing A') (α a) :=
    fun a => IsLocalization.map_eq _ _
  have hc := hbc φ α β φ' H hφ hφ' ι hι b
  have spec : ∀ {R S : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] (ψ : R →+* S)
      (hψ : ψ.Finite) (s : S), algebraMap R (FractionRing R) (normCoeff ψ hψ s k) =
        (charK ψ hψ (FractionRing R) s).reverse.coeff k := by
    intro R S _ _ _ _ ψ hψ s
    obtain ⟨P, hP⟩ := hint (K := FractionRing R) ψ hψ s
    refine algebraMap_normCoeff ψ hψ s k ⟨P.reverse.coeff k, ?_⟩
    rw [← hP, reverse_map_of_injective _ (IsFractionRing.injective R (FractionRing R)), coeff_map]
  apply IsFractionRing.injective A' (FractionRing A')
  rw [← hι, spec, spec, hc, reverse_map_of_injective ι ι.injective, coeff_map]

end GlobalTheory.NormalDescent
end

open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reversedCharpolyCoeff_map_of_isPushout : ∀ {A B A' B' : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [CommRing A']
    [IsDomain A'] [IsIntegrallyClosed A'] [CommRing B'] (φ : A →+* B) (α : A →+* A') (β : B →+* B') (φ' : A' →+* B'),
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ') →
    Function.Injective α → ∀ (hφ : φ.Finite) (hφ' : φ'.Finite) (b : B) (k : ℕ),
    α (normCoeff φ hφ b k) = normCoeff φ' hφ' (β b) k := by
  atlas_forward_decl GlobalTheory.NormalDescent.normCoeff_map_of_isPushout
end

section
section
noncomputable section

open CategoryTheory Polynomial TensorProduct

namespace GlobalTheory.NormalDescent

theorem charpoly_reverse_coeff_smul {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) (c : K) (k : ℕ) :
    (c • f).charpoly.reverse.coeff k = c ^ k * f.charpoly.reverse.coeff k := by
  classical
  let e := Module.finBasis K V
  rw [← LinearMap.charpoly_toMatrix _ e, ← LinearMap.charpoly_toMatrix _ e, Matrix.reverse_charpoly,
    Matrix.reverse_charpoly, map_smul, mul_comm, ← comp_C_mul_X_coeff]
  generalize LinearMap.toMatrix e e f = M
  congr 1
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← coe_compRingHom_apply, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j <;> simp [hij] <;> ring

theorem exists_charK_coeff {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Finite) (b : B) (n : ℕ) :
    ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b).coeff n := by
  classical
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  let K := FractionRing A
  let Ω := AlgebraicClosure K
  let ι := algebraMap K Ω
  let V := K ⊗[A] B
  haveI : Module.Free K V := Module.Free.of_divisionRing _ _
  let e := Module.finBasis K V
  let Mx := Algebra.leftMulMatrix e ((1 : K) ⊗ₜ[A] b)
  have hg : charK φ hφ K b = Mx.charpoly := by
    show (Algebra.lmul K V ((1 : K) ⊗ₜ[A] b)).charpoly = _
    show _ = (Algebra.leftMulMatrix e _).charpoly
    rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
  have hb : IsIntegral A b := Algebra.IsIntegral.isIntegral b
  have h1 : IsIntegral A ((1 : K) ⊗ₜ[A] b) :=
    hb.map (Algebra.TensorProduct.includeRight : B →ₐ[A] K ⊗[A] B)
  have h2 : IsIntegral A Mx := h1.map ((Algebra.leftMulMatrix e).restrictScalars A)
  have h3 : IsIntegral A (Mx.map ι) := h2.map (AlgHom.mapMatrix (IsScalarTower.toAlgHom A K Ω))
  obtain ⟨p, hpm, hp⟩ := h3
  have hroot : ∀ μ ∈ (Mx.charpoly.map ι).roots, IsIntegral A μ := by
    intro μ hμ
    have hs : μ ∈ spectrum Ω (Mx.map ι) := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map]
      exact isRoot_of_mem_roots hμ
    have h4 := spectrum.subset_polynomial_aeval (Mx.map ι) (p.map (algebraMap A Ω)) ⟨μ, hs, rfl⟩
    have h5 : aeval (Mx.map ι) (p.map (algebraMap A Ω)) = 0 := by
      rw [aeval_map_algebraMap, aeval_def]; exact hp
    rw [h5] at h4
    refine ⟨p, hpm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap Ω]
    by_contra hne
    exact (spectrum.mem_iff.1 h4) (by
      simpa using (IsUnit.mk0 _ hne).map (algebraMap Ω (Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) Ω)))
  have hl : Mx.charpoly.map ι ∈ Polynomial.lifts (integralClosure A Ω).val.toRingHom :=
    (IsAlgClosed.splits _).mem_lift_of_roots_mem_range ((Matrix.charpoly_monic _).map _) _
      fun μ hμ => ⟨⟨μ, hroot μ hμ⟩, rfl⟩
  rw [lifts_iff_coeff_lifts] at hl
  obtain ⟨s, hs⟩ := hl n
  have hc : IsIntegral A (Mx.charpoly.coeff n) := by
    refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K Ω) ι.injective).1 ?_
    show IsIntegral A (ι _)
    rw [← coeff_map, ← hs]
    exact s.2
  rw [hg]
  exact IsIntegrallyClosed.isIntegral_iff.1 hc

theorem normCoeff_mul : ∀ {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Finite) (u : A) (b : B) (k : ℕ), normCoeff φ hφ (φ u * b) k = u ^ k * normCoeff φ hφ b k := by
  intro A B _ _ _ _ φ hφ u b k
  have hrev : ∀ b' : B, ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b').reverse.coeff k :=
    fun b' => by rw [coeff_reverse]; exact exists_charK_coeff φ hφ b' _
  have key : (charK φ hφ (FractionRing A) (φ u * b)).reverse.coeff k
      = (algebraMap A (FractionRing A) u) ^ k * (charK φ hφ (FractionRing A) b).reverse.coeff k := by
    letI := φ.toAlgebra
    haveI : Module.Finite A B := hφ
    haveI : Module.Free (FractionRing A) (FractionRing A ⊗[A] B) := Module.Free.of_divisionRing _ _
    have e1 : (1 : FractionRing A) ⊗ₜ[A] (φ u * b)
        = algebraMap A (FractionRing A) u • ((1 : FractionRing A) ⊗ₜ[A] b) := by
      rw [algebraMap_smul, ← tmul_smul, Algebra.smul_def]; rfl
    show (Algebra.lmul _ _ ((1 : FractionRing A) ⊗ₜ[A] (φ u * b))).charpoly.reverse.coeff k = _
    rw [e1, map_smul]
    exact charpoly_reverse_coeff_smul _ _ _
  apply IsFractionRing.injective A (FractionRing A)
  rw [map_mul, map_pow, algebraMap_normCoeff _ _ _ _ (hrev _), algebraMap_normCoeff _ _ _ _ (hrev _), key]

end GlobalTheory.NormalDescent
end
end

open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reversedCharpolyCoeffInDomain_mul : ∀ {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Finite) (u : A) (b : B) (k : ℕ), normCoeff φ hφ (φ u * b) k = u ^ k * normCoeff φ hφ b k := by
  atlas_forward_decl GlobalTheory.NormalDescent.normCoeff_mul
end

section
section
open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.NormalDescent

noncomputable section

namespace GlobalTheory.NormalDescent

open TopologicalSpace Opposite GlobalTheory.LBGerm GlobalTheory.FiniteAmple

theorem injective_res_of_isAffineOpen {X : Scheme.{0}} {V W : X.Opens} (hV : IsAffineOpen V) [IsDomain Γ(X, V)]
    (h : W ≤ V) {x : X} (hx : x ∈ W) : Function.Injective (X.presheaf.map (homOfLE h).op).hom := by
  have hxV : x ∈ V := h hx
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxV⟩ : V)
  have hloc := hV.isLocalization_stalk ⟨x, hxV⟩
  have hinj : Function.Injective (X.presheaf.germ V x hxV).hom :=
    IsLocalization.injective (M := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl) (S := X.presheaf.stalk x)
      (Ideal.primeCompl_le_nonZeroDivisors _)
  intro a b e
  apply hinj
  rw [← X.presheaf.germ_res (homOfLE h) x hx]
  simp only [CommRingCat.comp_apply, e]

theorem exists_sec_normCoeff_local : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] {M : LB X}, M.IsLB → ∀ t : (M.pull f).Sec, ∃ u : ∀ k, (lbPow M k).Sec, ∀ x : X,
      ∃ (V : X.Opens) (hV : IsAffineOpen V) (_ : IsDomain Γ(X, V)) (_ : IsIntegrallyClosed Γ(X, V))
        (τ : Γ(Y, f ⁻¹ᵁ V)), x ∈ V ∧ (∀ y : Y, f y ∈ V → (y ∈ nonzeroLocus t ↔ y ∈ Y.basicOpen τ)) ∧
        ∀ (k : ℕ) (z : X), z ∈ V →
          (z ∈ nonzeroLocus (u k) ↔ z ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k)) := by
  intro X Y f _ _ _ M hM t
  let α : Type := {p : X.Opens × M.ι // IsAffineOpen p.1 ∧ p.1 ≤ M.U p.2 ∧ IsIrreducible (p.1 : Set X)}
  have nd : ∀ a : α, IsDomain Γ(X, a.1.1) ∧ IsIntegrallyClosed Γ(X, a.1.1) := fun a =>
    GlobalTheory.IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible a.2.2.2
  have cov : ∀ x : X, ∃ a : α, x ∈ a.1.1 := fun x => by
    obtain ⟨i, hi⟩ := exists_chart hM x
    have hC := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents
      (irreducibleComponent_mem_irreducibleComponents x)
    obtain ⟨V, hV, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := M.U i ⊓ ⟨_, hC⟩) (x := x)
      ⟨hi, mem_irreducibleComponent⟩
    have hle : V ≤ M.U i ⊓ ⟨_, hC⟩ := hle
    exact ⟨⟨(V, i), hV, hle.trans inf_le_left, ⟨⟨x, hx⟩,
      (isIrreducible_irreducibleComponent (x := x)).2.open_subset V.isOpen fun q hq => (hle hq).2⟩⟩, hx⟩
  have le : ∀ a : α, f ⁻¹ᵁ a.1.1 ≤ (M.pull f).U fun _ => a.1.2 := fun a y hy => mem_pull.2 (a.2.2.1 hy)
  let τ : ∀ a : α, Γ(Y, f ⁻¹ᵁ a.1.1) := fun a => resG Y (le a) (t.f fun _ => a.1.2)
  let c : ∀ (k : ℕ) (a : α), Γ(X, a.1.1) := fun k a =>
    haveI := (nd a).1
    normCoeff (f.app a.1.1).hom (f.finite_app _ a.2.1) (τ a) k
  have key : ∀ k (x : X) (a b : α), x ∈ a.1.1 → x ∈ b.1.1 → gs (𝟙 X) x _ (c k a) =
      (gm (𝟙 X) x (M.U a.1.2 ⊓ M.U b.1.2) (M.g a.1.2 b.1.2)).val ^ k * gs (𝟙 X) x _ (c k b) := by
    intro k x a b ha hb
    obtain ⟨W, hW, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := a.1.1 ⊓ b.1.1) (x := x) ⟨ha, hb⟩
    have hle : W ≤ a.1.1 ⊓ b.1.1 := hle
    have la : W ≤ a.1.1 := hle.trans inf_le_left
    have lb : W ≤ b.1.1 := hle.trans inf_le_right
    have lg : W ≤ M.U a.1.2 ⊓ M.U b.1.2 := le_inf (la.trans a.2.2.1) (lb.trans b.2.2.1)
    have hWi : IsIrreducible (W : Set X) := ⟨⟨x, hx⟩, a.2.2.2.2.open_subset W.isOpen la⟩
    obtain ⟨_, _⟩ := GlobalTheory.IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible hWi
    obtain ⟨_, _⟩ := nd a
    obtain ⟨_, _⟩ := nd b
    have ea := GlobalTheory.T.reversedCharpolyCoeff_map_of_isPushout _ _ _ _ (isPushout_app f a.2.1 hW la) (injective_res_of_isAffineOpen a.2.1 la hx)
      (f.finite_app _ a.2.1) (f.finite_app _ hW) (τ a) k
    have eb := GlobalTheory.T.reversedCharpolyCoeff_map_of_isPushout _ _ _ _ (isPushout_app f b.2.1 hW lb) (injective_res_of_isAffineOpen b.2.1 lb hx)
      (f.finite_app _ b.2.1) (f.finite_app _ hW) (τ b) k
    have eτ : resG Y (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ a.1.1 from fun _ hy => la hy) (τ a) =
        (f.app W).hom (resG X lg (M.g a.1.2 b.1.2).val) *
          resG Y (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ b.1.1 from fun _ hy => lb hy) (τ b) := fn_ext fun y hy => by
      have hy' : (𝟙 Y ≫ f) y ∈ W := hy
      rw [gs_mul (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y (le a) (la hy),
        gs_res (𝟙 Y) y (le b) (lb hy), gs_pull (𝟙 Y) f y W hy, gs_res (𝟙 Y ≫ f) y _ hy',
        gs_unit (𝟙 Y ≫ f) y _ (lg hy'),
        ← gm_pull_g M f (𝟙 Y) y (fun _ => a.1.2) (fun _ => b.1.2) (le a (la hy)) (le b (lb hy))]
      exact gs_compat t (𝟙 Y) y (le a (la hy)) (le b (lb hy))
    have e : resG X la (c k a) = resG X lg (M.g a.1.2 b.1.2).val ^ k * resG X lb (c k b) :=
      ea.trans ((congrArg (fun z => normCoeff (f.app W).hom (f.finite_app _ hW) z k) eτ).trans
        ((GlobalTheory.T.reversedCharpolyCoeffInDomain_mul _ _ _ _ k).trans (congrArg (_ * ·) eb.symm)))
    have e' := congrArg (gs (𝟙 X) x W) e
    rwa [gs_mul _ x _ hx, gs_pow _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx,
      gs_unit _ x _ (lg hx)] at e'
  choose u hu using fun k => exists_sec_of_refinement (isLB_lbPow hM k) (fun a : α => a.1.1)
    (fun a _ => a.1.2) (fun a x hx => mem_powChart.2 (a.2.2.1 hx)) cov (c k) fun x a b ha hb => by
      rw [gm_lbPow_g k (𝟙 X) x _ _ (mem_powChart.2 (a.2.2.1 ha)) (mem_powChart.2 (b.2.2.1 hb)),
        Units.val_pow_eq_pow_val]
      exact key k x a b ha hb
  refine ⟨u, fun x => ?_⟩
  obtain ⟨a, ha⟩ := cov x
  refine ⟨a.1.1, a.2.1, (nd a).1, (nd a).2, τ a, ha, fun y hy => ?_, fun k z hz => ?_⟩
  · have hy : y ∈ f ⁻¹ᵁ a.1.1 := hy
    rw [mem_nonzeroLocus_iff_isUnit t (le a hy), ← gs_res (𝟙 Y) y (le a) hy]
    exact isUnit_gs_iff (𝟙 Y) y _ hy _
  · have hJ : z ∈ (lbPow M k).U fun _ => a.1.2 := mem_powChart.2 (a.2.2.1 hz)
    rw [mem_nonzeroLocus_iff_isUnit (u k) hJ, hu k z _ a hJ hz, Units.isUnit_units_mul]
    exact isUnit_gs_iff (𝟙 X) z _ hz _

end GlobalTheory.NormalDescent
end
end

open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sec_normCoeff_local' : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    {M : LB X}, M.IsLB → ∀ t : (M.pull f).Sec, ∃ u : ∀ k, (lbPow M k).Sec, ∀ x : X,
      ∃ (V : X.Opens) (hV : IsAffineOpen V) (_ : IsDomain Γ(X, V)) (_ : IsIntegrallyClosed Γ(X, V))
        (τ : Γ(Y, f ⁻¹ᵁ V)), x ∈ V ∧ (∀ y : Y, f y ∈ V → (y ∈ nonzeroLocus t ↔ y ∈ Y.basicOpen τ)) ∧
        ∀ (k : ℕ) (z : X), z ∈ V →
          (z ∈ nonzeroLocus (u k) ↔ z ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k)) := by
  atlas_forward_decl GlobalTheory.NormalDescent.exists_sec_normCoeff_local
end

section
section
open CategoryTheory Polynomial GlobalTheory.NormalDescent

namespace GlobalTheory.NormalDescent

theorem exists_normCoeff_not_mem {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Finite) (b : B) (hQ₀ : ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap φ = ⊥)
    (p : Ideal A) (hp : p.IsPrime) (hb : ∀ Q : Ideal B, Q.IsPrime → Q.comap φ = p → b ∉ Q) :
    ∃ k, 1 ≤ k ∧ normCoeff φ hφ b k ∉ p := by
  classical
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  set K := FractionRing A
  obtain ⟨P, hP⟩ := GlobalTheory.T.exists_charpoly_baseChange_integrallyClosed (K := K) φ hφ b
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hdeg : (charK φ hφ K b).natDegree = P.natDegree := by
    rw [← hP]; exact natDegree_map_eq_of_injective hinj P
  have hmon : P.Monic := by
    have h1 := charK_monic φ hφ K b
    rw [← hP] at h1
    apply hinj
    rw [Monic, leadingCoeff_map_of_injective hinj] at h1
    simpa using h1
  by_contra hcon
  push_neg at hcon

  have hcoeff : ∀ j < P.natDegree, P.coeff j ∈ p := by
    intro j hj
    have hk : 1 ≤ P.natDegree - j := by omega
    have hrev : (charK φ hφ K b).reverse.coeff (P.natDegree - j) = algebraMap A K (P.coeff j) := by
      rw [coeff_reverse, hdeg, revAt_le (by omega), show P.natDegree - (P.natDegree - j) = j by omega,
        ← hP, coeff_map]
    have hex : ∃ a : A, algebraMap A K a = (charK φ hφ K b).reverse.coeff (P.natDegree - j) :=
      ⟨P.coeff j, hrev.symm⟩
    have := algebraMap_normCoeff φ hφ b _ hex
    rw [hrev] at this
    have := hinj this
    rw [← this]
    exact hcon _ hk

  set M := TensorProduct A K B
  have hCH : Polynomial.aeval ((1 : K) ⊗ₜ[A] b : M) (charK φ hφ K b) = 0 := by
    have h := LinearMap.aeval_self_charpoly (Algebra.lmul K M ((1 : K) ⊗ₜ[A] b))
    have h2 : Algebra.lmul K M (Polynomial.aeval ((1 : K) ⊗ₜ[A] b : M) (charK φ hφ K b)) = 0 := by
      rw [← Polynomial.aeval_algHom_apply]; exact h
    have h3 := LinearMap.congr_fun h2 1
    simpa using h3
  have hker : Algebra.TensorProduct.includeRight (R := A) (A := K) (B := B) (Polynomial.aeval b P) = 0 := by
    rw [← Polynomial.aeval_algHom_apply, Algebra.TensorProduct.includeRight_apply,
      ← Polynomial.aeval_map_algebraMap K, hP]
    exact hCH

  let I : Ideal B := RingHom.ker (Algebra.TensorProduct.includeRight (R := A) (A := K) (B := B))
  have hI : I.comap (algebraMap A B) ≤ p := by
    intro a ha
    obtain ⟨Q₀, hQ₀p, hQ₀c⟩ := hQ₀
    have ha' : (1 : K) ⊗ₜ[A] (algebraMap A B a) = 0 := ha
    have := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors A)
      (TensorProduct.mk A K B 1)).1 ha'
    obtain ⟨⟨s, hs⟩, hs0⟩ := this
    have hs0' : φ (s * a) = 0 := by
      rw [map_mul]; simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hs0
    have hmem : s * a ∈ Q₀.comap φ := by simp [Ideal.mem_comap, hs0']
    rw [hQ₀c, Ideal.mem_bot] at hmem
    have hs' : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have : a = 0 := by
      rcases mul_eq_zero.1 hmem with h | h
      · exact absurd h hs'
      · exact h
    rw [this]; exact p.zero_mem
  haveI : Algebra.IsIntegral A B := inferInstance
  obtain ⟨Q, hQI, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B) p I hI
  have hPQ : Polynomial.aeval b P ∈ Q := hQI (by simpa [I, RingHom.mem_ker] using hker)
  have hbd : b ^ P.natDegree ∈ Q := by
    have hsum := hmon.as_sum
    rw [hsum, map_add, map_pow, aeval_X, map_sum] at hPQ
    refine (Q.add_mem_iff_left ?_).1 hPQ
    refine Q.sum_mem fun j hj => ?_
    rw [map_mul, aeval_C, aeval_X_pow]
    refine Q.mul_mem_right _ ?_
    have : P.coeff j ∈ Q.comap (algebraMap A B) := by
      rw [hQc]; exact hcoeff j (Finset.mem_range.1 hj)
    exact this
  exact hb Q hQp hQc (hQp.mem_of_pow_mem _ hbd)

end GlobalTheory.NormalDescent
end

open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reversedCharpolyCoeff_not_mem_prime : ∀ {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Finite) (b : B), (∃ Q : Ideal B, Q.IsPrime ∧ Q.comap φ = ⊥) → ∀ p : Ideal A, p.IsPrime →
    (∀ Q : Ideal B, Q.IsPrime → Q.comap φ = p → b ∉ Q) → ∃ k, 1 ≤ k ∧ normCoeff φ hφ b k ∉ p := by
  atlas_forward_decl GlobalTheory.NormalDescent.exists_normCoeff_not_mem
end

section
section
open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.NormalDescent

namespace GlobalTheory.NormalDescent

theorem mem_basicOpen_normCoeff_of_fibre {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Surjective f]
    {V : X.Opens} (hV : IsAffineOpen V) [IsDomain Γ(X, V)] [IsIntegrallyClosed Γ(X, V)]
    (τ : Γ(Y, f ⁻¹ᵁ V)) (x : X) (hx : x ∈ V) (h : ∀ y : Y, f y = x → y ∈ Y.basicOpen τ) :
    ∃ k, 1 ≤ k ∧ x ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k) := by
  have hV' := hV.preimage f
  have sq := hV.SpecMap_appLE_fromSpec f hV' le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at sq
  have pt : ∀ q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V),
      hV.fromSpec (PrimeSpectrum.comap (f.app V).hom q) = f (hV'.fromSpec q) := fun q => congr($(sq) q)
  obtain ⟨p, rfl⟩ : x ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  have e₁ : ∀ c : Γ(X, V), hV.fromSpec p ∈ X.basicOpen c ↔ c ∉ p.asIdeal := fun c => by
    rw [← Scheme.Hom.mem_preimage, hV.fromSpec_preimage_basicOpen]; rfl
  have e₂ : ∀ q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V), hV'.fromSpec q ∈ Y.basicOpen τ ↔ τ ∉ q.asIdeal :=
    fun q : Spec Γ(Y, f ⁻¹ᵁ V) => by rw [← Scheme.Hom.mem_preimage, hV'.fromSpec_preimage_basicOpen]; rfl
  have inj := hV.fromSpec.isOpenEmbedding.injective
  have h0 : ∃ Q : Ideal Γ(Y, f ⁻¹ᵁ V), Q.IsPrime ∧ Q.comap (f.app V).hom = ⊥ := by
    let P0 : PrimeSpectrum Γ(X, V) := ⟨⊥, Ideal.isPrime_bot⟩
    obtain ⟨y, hy⟩ := f.surjective (hV.fromSpec P0)
    have hyV : f y ∈ V := by
      have hr : hV.fromSpec P0 ∈ Set.range hV.fromSpec := ⟨P0, rfl⟩
      rw [hV.range_fromSpec] at hr
      rw [hy]; exact hr
    obtain ⟨q, rfl⟩ : y ∈ Set.range hV'.fromSpec := by rw [hV'.range_fromSpec]; exact hyV
    exact ⟨q.asIdeal, q.isPrime, congrArg PrimeSpectrum.asIdeal (inj ((pt q).trans hy))⟩
  obtain ⟨k, hk, hc⟩ := GlobalTheory.T.exists_reversedCharpolyCoeff_not_mem_prime (f.app V).hom (f.finite_app V hV) τ h0 p.asIdeal p.isPrime
    (fun Q hQ hQp => by
      let q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V) := ⟨Q, hQ⟩
      have e : PrimeSpectrum.comap (f.app V).hom q = p := PrimeSpectrum.ext hQp
      exact (e₂ q).1 (h _ ((pt q).symm.trans (congrArg hV.fromSpec e))))
  exact ⟨k, hk, (e₁ _).2 hc⟩

end GlobalTheory.NormalDescent
end

open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_basicOpen_normCoeff_of_fibre : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Surjective f] {V : X.Opens} (hV : IsAffineOpen V)
    [IsDomain Γ(X, V)] [IsIntegrallyClosed Γ(X, V)] (τ : Γ(Y, f ⁻¹ᵁ V)) (x : X), x ∈ V →
    (∀ y : Y, f y = x → y ∈ Y.basicOpen τ) →
    ∃ k, 1 ≤ k ∧ x ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k) := by
  atlas_forward_decl GlobalTheory.NormalDescent.mem_basicOpen_normCoeff_of_fibre
end

section
section
noncomputable section

namespace GlobalTheory.NormalDescent

open Polynomial TensorProduct

section Algebra

variable {A B : Type} [CommRing A] [CommRing B]

theorem exists_mul_pow_mem_map (φ : A →+* B) (p : Ideal A) [p.IsPrime] (b : B)
    (h : ∀ Q : Ideal B, Q.IsPrime → Q.comap φ = p → b ∈ Q) :
    ∃ s ∉ p, ∃ n : ℕ, φ s * b ^ n ∈ p.map φ := by
  by_contra hne
  push Not at hne
  let T : Submonoid B := p.primeCompl.map φ ⊔ Submonoid.powers b
  have hdisj : Disjoint ((p.map φ : Ideal B) : Set B) (T : Set B) := by
    rw [Set.disjoint_left]
    intro x hxJ hxT
    obtain ⟨y, hy, z, hz, rfl⟩ := Submonoid.mem_sup.mp hxT
    obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hy
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hz
    exact hne s (Ideal.mem_primeCompl_iff.mp hs) n hxJ
  obtain ⟨Q, hQ, hJQ, hQT⟩ := Ideal.exists_le_prime_disjoint (S := T) (disjoint := hdisj)
  have hcomap : Q.comap φ = p := by
    apply le_antisymm
    · intro a ha
      by_contra hap
      exact Set.disjoint_left.mp hQT (Ideal.mem_comap.mp ha)
        (Submonoid.mem_sup_left (Submonoid.mem_map_of_mem φ (Ideal.mem_primeCompl_iff.mpr hap)))
    · exact Ideal.map_le_iff_le_comap.mp hJQ
  exact Set.disjoint_left.mp hQT (h Q hQ hcomap) (Submonoid.mem_sup_right (Submonoid.mem_powers b))

theorem exists_monic_coeff_mem (φ : A →+* B) (hφ : φ.Finite) (p : Ideal A) (u : B) (hu : u ∈ p.map φ) :
    ∃ g : A[X], g.Monic ∧ (∀ i < g.natDegree, g.coeff i ∈ p) ∧ eval₂ φ u g = 0 := by
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  have hrange : LinearMap.range (Algebra.lmul A B u) ≤ p • (⊤ : Submodule A B) := by
    rintro _ ⟨y, rfl⟩
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    exact Ideal.mul_mem_right _ _ hu
  obtain ⟨g, hgm, -, hgc, hg0⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
      (f := Algebra.lmul A B u) (I := p) (hI := hrange)
  refine ⟨g, hgm, fun i hi => Ideal.pow_le_self (Nat.sub_ne_zero_of_lt hi) (hgc i), ?_⟩
  have e2 := Polynomial.aeval_algHom_apply (Algebra.lmul A B) u g
  rw [hg0] at e2
  have e3 := congrArg (fun F : Module.End A B => F 1) e2
  have e4 : aeval u g = 0 := by simpa using e3.symm
  rw [aeval_def] at e4
  exact e4

theorem mem_of_aeval_eq_zero {R : Type} [CommRing R] [Algebra A R] (P : Ideal R) [hP : P.IsPrime] (g : A[X])
    (hg : g.Monic) (hc : ∀ i < g.natDegree, algebraMap A R (g.coeff i) ∈ P) (w : R) (hw : aeval w g = 0) :
    w ∈ P := by
  have key := hw
  rw [aeval_eq_sum_range, Finset.sum_range_succ, hg.coeff_natDegree, one_smul] at key
  have hsum : (∑ i ∈ Finset.range g.natDegree, g.coeff i • w ^ i) ∈ P := by
    refine P.sum_mem fun i hi => ?_
    rw [Algebra.smul_def]
    exact P.mul_mem_right _ (hc i (Finset.mem_range.mp hi))
  have hpow : w ^ g.natDegree ∈ P := by
    have e : w ^ g.natDegree = -(∑ i ∈ Finset.range g.natDegree, g.coeff i • w ^ i) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact key
    rw [e]
    exact P.neg_mem hsum
  exact hP.mem_of_pow_mem _ hpow

theorem coeff_prod_X_sub_C_mem {R : Type} [CommRing R] (P : Ideal R) [P.IsPrime] (s : Multiset R)
    (hs : ∀ a ∈ s, a ∈ P) (i : ℕ) (hi : i < Multiset.card s) :
    ((s.map fun a => X - C a).prod).coeff i ∈ P := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map, Polynomial.map_multiset_prod,
    Multiset.map_map]
  have hX : ∀ a ∈ s, ((Polynomial.map (Ideal.Quotient.mk P)) ∘ fun a => X - C a) a = X := by
    intro a ha
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr (hs a ha)]
  rw [Multiset.map_congr rfl hX, Multiset.map_const', Multiset.prod_replicate, coeff_X_pow,
    if_neg hi.ne]

end Algebra

section Spectral

variable {A B : Type} [CommRing A] [CommRing B]

theorem aeval_eq_zero_of_isRoot (φ : A →+* B) (hφ : φ.Finite) (K Ω : Type) [Field K] [Algebra A K] [Field Ω]
    [Algebra A Ω] [Algebra K Ω] [IsScalarTower A K Ω] (b : B) (h : A[X]) (hh : eval₂ φ b h = 0) (μ : Ω)
    (hμ : ((charK φ hφ K b).map (algebraMap K Ω)).IsRoot μ) :
    aeval μ h = 0 := by
  let := φ.toAlgebra
  have : Module.Finite A B := hφ
  have hb : aeval b h = 0 := by
    rw [aeval_def]
    exact hh
  have h1 : aeval ((1 : K) ⊗ₜ[A] b) h = 0 := by
    have e := Polynomial.aeval_algHom_apply
      (Algebra.TensorProduct.includeRight : B →ₐ[A] K ⊗[A] B) b h
    rw [hb, map_zero] at e
    exact e
  have hK : aeval (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)) (h.map (algebraMap A K)) = 0 := by
    rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_map_algebraMap, h1, map_zero]
  have hΩ : aeval ((Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).baseChange Ω)
      ((h.map (algebraMap A K)).map (algebraMap K Ω)) = 0 := by
    have e := Polynomial.aeval_algHom_apply (Module.End.baseChangeHom K Ω (K ⊗[A] B))
      (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)) (h.map (algebraMap A K))
    rw [hK, map_zero, ← Polynomial.aeval_map_algebraMap Ω] at e
    exact e
  have hroot : ((Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).baseChange Ω).charpoly.IsRoot μ := by
    rw [LinearMap.charpoly_baseChange]
    exact hμ
  obtain ⟨v, hv⟩ :=
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).mpr hroot).exists_hasEigenvector
  have e := Module.End.aeval_apply_of_hasEigenvector
    (p := (h.map (algebraMap A K)).map (algebraMap K Ω)) hv
  rw [hΩ, LinearMap.zero_apply, eq_comm, smul_eq_zero] at e
  rcases e with e | e
  · rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.eval_map_algebraMap] at e
  · exact absurd e hv.2

end Spectral

section Main

variable {A B : Type} [CommRing A] [IsDomain A] [CommRing B]

theorem mem_of_forall_mem_prime (φ : A →+* B) (hφ : φ.Finite) (b : B) (p : Ideal A) [p.IsPrime]
    (h : ∀ Q : Ideal B, Q.IsPrime → Q.comap φ = p → b ∈ Q) (k : ℕ) (hk : 1 ≤ k) (a : A)
    (ha : algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b).reverse.coeff k) : a ∈ p := by
  classical
  set K := FractionRing A with hKdef
  set χ := charK φ hφ K b with hχdef
  have hχm : χ.Monic := charK_monic φ hφ K b
  by_cases hkN : χ.natDegree < k
  · have h0 : algebraMap A K a = 0 := by
      rw [ha, coeff_reverse, revAt_eq_self_of_lt hkN]
      exact coeff_eq_zero_of_natDegree_lt hkN
    have ha0 : a = 0 := IsFractionRing.injective A K (h0.trans (map_zero _).symm)
    rw [ha0]
    exact p.zero_mem
  push Not at hkN
  obtain ⟨s, hs, n, hsn⟩ := exists_mul_pow_mem_map φ p b h
  obtain ⟨g, hgm, hgc, hg0⟩ := exists_monic_coeff_mem φ hφ p _ hsn
  have hbint : ∃ m : A[X], m.Monic ∧ eval₂ φ b m = 0 := by
    letI := φ.toAlgebra
    haveI : Module.Finite A B := hφ
    exact Algebra.IsIntegral.isIntegral (R := A) b
  obtain ⟨m, hmm, hm0⟩ := hbint
  have hinj : Function.Injective (algebraMap A (AlgebraicClosure K)) := by
    rw [IsScalarTower.algebraMap_eq A K (AlgebraicClosure K), RingHom.coe_comp]
    exact (algebraMap K (AlgebraicClosure K)).injective.comp (IsFractionRing.injective A K)
  obtain ⟨P, -, hP, hPp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (S := integralClosure A (AlgebraicClosure K)) p ⊥ (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      have hx0 : x = 0 := hinj (by
        rw [IsScalarTower.algebraMap_apply A (integralClosure A (AlgebraicClosure K))
          (AlgebraicClosure K), hx, map_zero, map_zero])
      rw [hx0]
      exact p.zero_mem)
  have hint : ∀ μ ∈ (χ.map (algebraMap K (AlgebraicClosure K))).roots,
      μ ∈ integralClosure A (AlgebraicClosure K) := by
    intro μ hμ
    have e := aeval_eq_zero_of_isRoot φ hφ K (AlgebraicClosure K) b m hm0 μ (mem_roots'.mp hμ).2
    exact (mem_integralClosure_iff A (AlgebraicClosure K)).mpr ⟨m, hmm, by rwa [aeval_def] at e⟩
  have hmemP : ∀ c : integralClosure A (AlgebraicClosure K),
      (χ.map (algebraMap K (AlgebraicClosure K))).IsRoot (c : AlgebraicClosure K) → c ∈ P := by
    intro c hc
    have e1 : eval₂ φ b (g.comp (C s * X ^ n)) = 0 := by
      rw [eval₂_comp]
      simpa using hg0
    have e2 := aeval_eq_zero_of_isRoot φ hφ K (AlgebraicClosure K) b _ e1 (c : AlgebraicClosure K) hc
    rw [aeval_comp] at e2
    simp only [map_mul, aeval_C, map_pow, aeval_X] at e2
    have e3 : aeval (algebraMap A (integralClosure A (AlgebraicClosure K)) s * c ^ n) g = 0 := by
      apply Subtype.val_injective
      rw [Polynomial.aeval_subalgebra_coe]
      simpa using e2
    have hw := mem_of_aeval_eq_zero P g hgm
      (fun i hi => by rw [← Ideal.mem_comap, hPp]; exact hgc i hi) _ e3
    rcases hP.mem_or_mem hw with h1 | h1
    · have h2 : s ∈ P.comap (algebraMap A (integralClosure A (AlgebraicClosure K))) := h1
      rw [hPp] at h2
      exact (hs h2).elim
    · exact hP.mem_of_pow_mem n h1
  obtain ⟨t, ht⟩ : ∃ t : Multiset (integralClosure A (AlgebraicClosure K)),
      t.map Subtype.val = (χ.map (algebraMap K (AlgebraicClosure K))).roots :=
    ⟨(χ.map (algebraMap K (AlgebraicClosure K))).roots.attach.map fun x => ⟨x.1, hint x.1 x.2⟩,
      by simp [Multiset.map_map]⟩
  have hsplit : (χ.map (algebraMap K (AlgebraicClosure K))).Splits := IsAlgClosed.splits _
  have hprod : χ.map (algebraMap K (AlgebraicClosure K)) =
      ((t.map fun c => X - C c).prod).map (algebraMap (integralClosure A (AlgebraicClosure K))
        (AlgebraicClosure K)) := by
    conv_lhs => rw [hsplit.eq_prod_roots_of_monic (hχm.map _), ← ht]
    rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro c _
    simp
  have hcard : Multiset.card t = χ.natDegree := by
    rw [← Multiset.card_map Subtype.val t, ht, ← hsplit.natDegree_eq_card_roots, natDegree_map]
  have hi : χ.natDegree - k < Multiset.card t := by omega
  have hc := coeff_prod_X_sub_C_mem P t (fun c hct => hmemP c (by
      have hmem : (c : AlgebraicClosure K) ∈ (χ.map (algebraMap K (AlgebraicClosure K))).roots := by
        rw [← ht]
        exact Multiset.mem_map_of_mem _ hct
      exact (mem_roots'.mp hmem).2)) _ hi
  have hval : algebraMap A (AlgebraicClosure K) a =
      algebraMap (integralClosure A (AlgebraicClosure K)) (AlgebraicClosure K)
        ((t.map fun c => X - C c).prod.coeff (χ.natDegree - k)) := by
    rw [IsScalarTower.algebraMap_apply A K (AlgebraicClosure K), ha, coeff_reverse, revAt_le hkN,
      ← Polynomial.coeff_map, hprod, Polynomial.coeff_map]
  have hAR : algebraMap A (integralClosure A (AlgebraicClosure K)) a =
      (t.map fun c => X - C c).prod.coeff (χ.natDegree - k) := by
    apply Subtype.val_injective
    change algebraMap (integralClosure A (AlgebraicClosure K)) (AlgebraicClosure K)
      (algebraMap A (integralClosure A (AlgebraicClosure K)) a) = _
    rw [← IsScalarTower.algebraMap_apply, hval]
    rfl
  have hmemA : a ∈ P.comap (algebraMap A (integralClosure A (AlgebraicClosure K))) := by
    rw [Ideal.mem_comap, hAR]
    exact hc
  rwa [hPp] at hmemA

end Main

section Main

variable {A B : Type} [CommRing A] [IsDomain A] [CommRing B]

theorem exists_prime_comap_eq_notMem (φ : A →+* B) (hφ : φ.Finite) (b : B) (p : Ideal A) [p.IsPrime] (k : ℕ)
    (hk : 1 ≤ k) (h : normCoeff φ hφ b k ∉ p) : ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap φ = p ∧ b ∉ Q := by
  by_contra hne
  push Not at hne
  apply h
  by_cases hex : ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b).reverse.coeff k
  · exact mem_of_forall_mem_prime φ hφ b p hne k hk _ (algebraMap_normCoeff φ hφ b k hex)
  · rw [normCoeff, dif_neg hex]
    exact p.zero_mem

end Main

section Geometry

open AlgebraicGeometry CategoryTheory

theorem exists_mem_basicOpen_of_mem_basicOpen_normCoeff : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f]
    {V : X.Opens} (hV : IsAffineOpen V) [IsDomain Γ(X, V)] [IsIntegrallyClosed Γ(X, V)] (τ : Γ(Y, f ⁻¹ᵁ V))
    (x : X) (k : ℕ), x ∈ V → 1 ≤ k →
    x ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k) → ∃ y ∈ Y.basicOpen τ, f y = x := by
  intro X Y f _ V hV _ _ τ x k hxV hk hx
  have hU : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  set px := hV.primeIdealOf ⟨x, hxV⟩ with hpx
  have hfx : hV.fromSpec px = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hnot : normCoeff (f.app V).hom (f.finite_app V hV) τ k ∉ px.asIdeal := by
    have h1 : hV.fromSpec px ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k) := by
      rw [hfx]
      exact hx
    have h2 : px ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k) := h1
    rw [hV.fromSpec_preimage_basicOpen] at h2
    exact (PrimeSpectrum.mem_basicOpen _ _).mp h2
  obtain ⟨Q, hQ, hQp, hτQ⟩ :=
    exists_prime_comap_eq_notMem (f.app V).hom (f.finite_app V hV) τ px.asIdeal k hk hnot
  let q : Spec Γ(Y, f ⁻¹ᵁ V) := (⟨Q, hQ⟩ : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V))
  refine ⟨hU.fromSpec q, ?_, ?_⟩
  · have h3 : q ∈ PrimeSpectrum.basicOpen τ := (PrimeSpectrum.mem_basicOpen _ _).mpr hτQ
    rw [← hU.fromSpec_preimage_basicOpen] at h3
    exact h3
  · have e := IsAffineOpen.SpecMap_appLE_fromSpec f hV hU le_rfl
    have e2 : f (hU.fromSpec q) = hV.fromSpec (Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl) q) := by
      rw [← Scheme.Hom.comp_apply, ← e, Scheme.Hom.comp_apply]
    rw [e2, Scheme.Hom.appLE_eq_app, Spec.map_apply]
    have hq : PrimeSpectrum.comap (f.app V).hom q = px := PrimeSpectrum.ext hQp
    rw [hq, hfx]

end Geometry

end GlobalTheory.NormalDescent
end
end

open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_basicOpen_of_mem_basicOpen_normCoeff' : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] {V : X.Opens} (hV : IsAffineOpen V)
    [IsDomain Γ(X, V)] [IsIntegrallyClosed Γ(X, V)] (τ : Γ(Y, f ⁻¹ᵁ V)) (x : X) (k : ℕ), x ∈ V → 1 ≤ k →
    x ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k) → ∃ y ∈ Y.basicOpen τ, f y = x := by
  atlas_forward_decl GlobalTheory.NormalDescent.exists_mem_basicOpen_of_mem_basicOpen_normCoeff
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.NormalDescent

theorem exists_sec_image {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Surjective f] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] {M : LB X} (hM : M.IsLB) (t : (M.pull f).Sec) : ∃ u : ∀ k, (lbPow M k).Sec,
      (∀ x : X, (∀ y : Y, f y = x → y ∈ nonzeroLocus t) → ∃ k, 1 ≤ k ∧ x ∈ nonzeroLocus (u k)) ∧
      ∀ (x : X) (k : ℕ), 1 ≤ k → x ∈ nonzeroLocus (u k) → ∃ y ∈ nonzeroLocus t, f y = x := by
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_sec_normCoeff_local' f hM t
  refine ⟨u, fun x hx => ?_, fun x k hk hx => ?_⟩
  · obtain ⟨V, hV, _, _, τ, hxV, ht, hc⟩ := hu x
    obtain ⟨k, hk, h⟩ := GlobalTheory.T.exists_mem_basicOpen_normCoeff_of_fibre f hV τ x hxV fun y hy => (ht y (hy ▸ hxV)).1 (hx y hy)
    exact ⟨k, hk, (hc k x hxV).2 h⟩
  · obtain ⟨V, hV, _, _, τ, hxV, ht, hc⟩ := hu x
    obtain ⟨y, hy, rfl⟩ := GlobalTheory.T.exists_mem_basicOpen_of_mem_basicOpen_normCoeff' f hV τ x k hxV hk ((hc k x hxV).1 hx)
    exact ⟨y, (ht y hxV).2 hy, rfl⟩

theorem isAmpleLB_of_pull : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X), AlgebraicGeometry.IsNoetherian X →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsFinite f → Function.Surjective f →
    ∀ L : ReciprocityTheory.ChartRestriction.G.Semi.LB X, L.IsLB → GlobalTheory.IsAmpleLB (L.pull f) → GlobalTheory.IsAmpleLB L := by
  intro X X' f _ hN _ hs L hL h
  have := GlobalTheory.IsNormalScheme.of_pred hN
  have : Surjective f := ⟨hs⟩
  refine GlobalTheory.isAmpleLB_of_forall_le hL fun x U hx => ?_
  have hfin : (f ⁻¹' {x}).Finite := f.finite_preimage_singleton x
  obtain ⟨n, hn, s, hS, hle, -⟩ := h.exists_affine_finite_subset hfin (U := f ⁻¹ᵁ U)
    (fun y (hy : f y = x) => show f y ∈ U from hy ▸ hx)
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull (isLB_lbPow hL n) f) (isLB_lbPow h.isLB n)
    (lbIso_lbPow_pull hL f n).symm s
  obtain ⟨u, hu₁, hu₂⟩ := exists_sec_image f (isLB_lbPow hL n) t
  obtain ⟨k, hk, hxk⟩ := hu₁ x fun y hy => ht.ge (hS hy)
  have e := nonzeroLocus_secOfPowPow (u k)
  refine ⟨n * k, Nat.mul_pos hn hk, secOfPowPow (u k), e.ge hxk, fun z hz => ?_⟩
  obtain ⟨w, hw, rfl⟩ := hu₂ z k hk (e.le hz)
  exact hle (ht.le hw)

end GlobalTheory.NormalDescent
end
end
