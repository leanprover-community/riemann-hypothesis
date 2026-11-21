import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmRepresentationEigenDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodNormIntegral
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsDiffSumSmulOfIsLieComb
import BuildAid.ForwardExisting

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

namespace GlobalTheory.EigDescentFrac

theorem span_image_span {K L P V : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup P]
    [Module K P] [AddCommGroup V] [Module K V] [Module L V] [IsScalarTower K L V]
    (g : P →ₗ[K] V) (S : Set P) :
    Submodule.span L (g '' (Submodule.span K S : Set P)) = Submodule.span L (g '' S) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨x, hx, rfl⟩
  have : Submodule.span K S ≤ ((Submodule.span L (g '' S)).restrictScalars K).comap g :=
    Submodule.span_le.2 fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩
  exact this hx

theorem span_image_iSup {K L P V : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup P]
    [Module K P] [AddCommGroup V] [Module K V] [Module L V] [IsScalarTower K L V]
    (g : P →ₗ[K] V) {κ : Sort*} (W : κ → Submodule K P) :
    Submodule.span L (g '' ((⨆ i, W i : Submodule K P) : Set P)) =
      ⨆ i, Submodule.span L (g '' (W i : Set P)) := by
  refine le_antisymm (Submodule.span_le.2 ?_)
    (iSup_le fun i => Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.2 (le_iSup W i))))
  rintro _ ⟨x, hx, rfl⟩
  have : (⨆ i, W i) ≤ ((⨆ i, Submodule.span L (g '' (W i : Set P))).restrictScalars K).comap g :=
    iSup_le fun i y hy =>
      (le_iSup (fun i => Submodule.span L (g '' (W i : Set P))) i) (Submodule.subset_span ⟨y, hy, rfl⟩)
  exact this hx

theorem baseChange_eq_iSup_eigK : ∀ {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)} {R : Type} [CommRing R] [IsDomain R]
    {L : Type} [Field L] [Algebra R L] (j : FractionRing R →+* L)
    (hj : ∀ x : R, j (algebraMap R (FractionRing R) x) = algebraMap R L x) {n : ℕ} {V : Type*} [AddCommGroup V]
    [Module L V] (β : (Fin n → R) →ₛₗ[algebraMap R L] V)
    (hβ : LinearIndependent L (fun k ↦ β (Pi.single k 1)) ∧ Submodule.span L (Set.range fun k ↦ β (Pi.single k 1)) = ⊤)
    (ρ : orderC c →+* Module.End R (Fin n → R)) (T : orderC c → Module.End L V)
    (hT : ∀ a x, β (ρ a x) = T a (β x)) (N : Submodule R (Fin n → R)) {I : Type} [Fintype I]
    (σ : I → E →+* FractionRing R)
    (h : Submodule.span L (β '' (N : Set (Fin n → R))) = ⨆ i, ⨅ a : orderC c, Module.End.eigenspace (T a) (j (σ i a))),
   N.baseChange (FractionRing R) = ⨆ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ (σ i) := by
  intro E _ _ c R _ _ L _ _ j hj n V _ _ β hβ ρ T hT N I _ σ h
  classical
  letI : Algebra (FractionRing R) L := j.toAlgebra
  letI : Module (FractionRing R) V := Module.compHom V j
  haveI : IsScalarTower (FractionRing R) L V := ⟨fun k l v => by
    show (j k * l) • v = j k • l • v
    rw [mul_smul]⟩
  have hsmul : ∀ (k : FractionRing R) (v : V), k • v = j k • v := fun _ _ => rfl
  let bK : Module.Basis (Fin n) (FractionRing R) (FractionRing R ⊗[R] (Fin n → R)) :=
    Algebra.TensorProduct.basis (FractionRing R) (Pi.basisFun R (Fin n))
  have hbK : ∀ k, bK k = (1 : FractionRing R) ⊗ₜ[R] (Pi.single k (1 : R) : Fin n → R) := fun k => by
    simp [bK, Algebra.TensorProduct.basis_apply, Pi.basisFun_apply]
  let bL : Module.Basis (Fin n) L V := Module.Basis.mk hβ.1 hβ.2.ge
  have hbL : ∀ k, bL k = β (Pi.single k 1) := fun k => Module.Basis.mk_apply _ _ _
  let g : (FractionRing R ⊗[R] (Fin n → R)) →ₗ[FractionRing R] V :=
    bK.constr (FractionRing R) fun k => β (Pi.single k 1)
  have hgb : ∀ k, g (bK k) = β (Pi.single k 1) := fun k => bK.constr_basis _ _ _
  have hg1 : ∀ m : Fin n → R, g (1 ⊗ₜ m) = β m := by
    intro m
    have hm : m = ∑ k, m k • (Pi.single k (1 : R) : Fin n → R) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    rw [hm, TensorProduct.tmul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.tmul_smul, ← algebraMap_smul (FractionRing R) (m k), map_smul, ← hbK, hgb,
      β.map_smulₛₗ, hsmul, hj]
  let e : L ⊗[FractionRing R] (FractionRing R ⊗[R] (Fin n → R)) ≃ₗ[L] V :=
    (Algebra.TensorProduct.basis L bK).equiv bL (Equiv.refl _)
  have hbc : IsBaseChange L g := by
    refine IsBaseChange.of_equiv e fun m => ?_
    have h' : (e.toLinearMap.restrictScalars (FractionRing R) ∘ₗ
        TensorProduct.mk (FractionRing R) L _ 1) = g := by
      refine bK.ext fun k => ?_
      have := (Algebra.TensorProduct.basis L bK).equiv_apply k bL (Equiv.refl _)
      rw [Algebra.TensorProduct.basis_apply] at this
      simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
        LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
      rw [this, Equiv.refl_apply, hbL, hgb]
    exact congrArg (fun φ => φ m) h'
  have hF : ∀ (a : orderC c) (v : FractionRing R ⊗[R] (Fin n → R)),
      T a (g v) = g ((ρ a).baseChange (FractionRing R) v) := by
    intro a v
    have h' : (T a).restrictScalars (FractionRing R) ∘ₗ g =
        g ∘ₗ (ρ a).baseChange (FractionRing R) := by
      refine bK.ext fun k => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars]
      rw [hgb, hbK, LinearMap.baseChange_tmul, hg1, hT]
    exact congrArg (fun φ => φ v) h'
  have heig : ∀ (a : orderC c) (t : FractionRing R),
      Submodule.span L (g '' (Module.End.eigenspace ((ρ a).baseChange (FractionRing R)) t :
        Set (FractionRing R ⊗[R] (Fin n → R)))) = Module.End.eigenspace (T a) (j t) := by
    intro a t
    rw [Module.End.eigenspace_def, Module.End.eigenspace_def]
    refine GlobalTheory.GaloisDescent.span_image_ker hbc hbc _ _ fun v => ?_
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hF]
    rfl
  apply GlobalTheory.GaloisDescent.span_image_injective hbc
  simp only
  rw [Submodule.baseChange_eq_span, span_image_span, Submodule.map_coe, Set.image_image]
  simp only [TensorProduct.mk_apply, hg1]
  rw [h, span_image_iSup]
  refine iSup_congr fun i => ?_
  rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK, GlobalTheory.GaloisDescent.span_image_iInf hbc]
  exact iInf_congr fun a => (heig a _).symm

end GlobalTheory.EigDescentFrac
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_basis_fraction_field_independent : ∀ {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)} {R : Type} [CommRing R] [IsDomain R]
    {L : Type} [Field L] [Algebra R L] (j : FractionRing R →+* L)
    (hj : ∀ x : R, j (algebraMap R (FractionRing R) x) = algebraMap R L x) {n : ℕ} {V : Type*} [AddCommGroup V]
    [Module L V] (β : (Fin n → R) →ₛₗ[algebraMap R L] V)
    (hβ : LinearIndependent L (fun k ↦ β (Pi.single k 1)) ∧ Submodule.span L (Set.range fun k ↦ β (Pi.single k 1)) = ⊤)
    (ρ : orderC c →+* Module.End R (Fin n → R)) (T : orderC c → Module.End L V)
    (hT : ∀ a x, β (ρ a x) = T a (β x)) (N : Submodule R (Fin n → R)) {I : Type} [Fintype I]
    (σ : I → E →+* FractionRing R)
    (h : Submodule.span L (β '' (N : Set (Fin n → R))) = ⨆ i, ⨅ a : orderC c, Module.End.eigenspace (T a) (j (σ i a))),
   N.baseChange (FractionRing R) = ⨆ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ (σ i) := by
  atlas_forward_decl GlobalTheory.EigDescentFrac.baseChange_eq_iSup_eigK
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

namespace GlobalTheory

theorem dualBasis_baseChange : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] {M' : Type*} [AddCommGroup M'] [Module R' M']
    (f : M →ₛₗ[algebraMap R R'] M') (hf : Function.Bijective (liftSemi f)) {n : ℕ}
    (b : Module.Dual R M ≃ₗ[R] (Fin n → R)) (x : Fin n → Module.Dual R' M')
    (hx : ∀ k c, x k (f c) = algebraMap R R' (b.symm (Pi.single k 1) c)),
   LinearIndependent R' x ∧ Submodule.span R' (Set.range x) = ⊤ := by
  intro R R' _ _ _ M _ _ _ _ M' _ _ f hf n b x hx
  classical
  let B : Module.Basis (Fin n) R (Module.Dual R M) := Module.Basis.ofEquivFun b
  have hB : ∀ k, B k = b.symm (Pi.single k 1) := fun k => by simp [B]
  let C : Module.Basis (Fin n) R M := B.dualBasis.map (Module.evalEquiv R M).symm
  have hC : ∀ k l, B k (C l) = if k = l then 1 else 0 := fun k l => by
    have e : B k (C l) = Module.evalEquiv R M (C l) (B k) := rfl
    rw [e]
    simp only [C, Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Module.Basis.dualBasis_apply_self]
  let D : Module.Basis (Fin n) R' M' :=
    (Algebra.TensorProduct.basis R' C).map (LinearEquiv.ofBijective (liftSemi f) hf)
  have hD : ∀ k, D k = f (C k) := fun k => by
    simp [D, Algebra.TensorProduct.basis_apply]
  have hxD : ∀ k, x k = D.dualBasis k := fun k => by
    refine D.ext fun l => ?_
    rw [hD, hx, ← hB, hC, ← hD, D.dualBasis_apply_self]
    by_cases h : k = l
    · subst h; simp
    · simp [h, Ne.symm h]
  have : x = ⇑D.dualBasis := funext hxD
  rw [this]
  exact ⟨D.dualBasis.linearIndependent, D.dualBasis.span_eq⟩

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinear_dual_basis_base_change : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] {M' : Type*} [AddCommGroup M'] [Module R' M']
    (f : M →ₛₗ[algebraMap R R'] M') (hf : Function.Bijective (liftSemi f)) {n : ℕ}
    (b : Module.Dual R M ≃ₗ[R] (Fin n → R)) (x : Fin n → Module.Dual R' M')
    (hx : ∀ k c, x k (f c) = algebraMap R R' (b.symm (Pi.single k 1) c)),
   LinearIndependent R' x ∧ Submodule.span R' (Set.range x) = ⊤ := by
  atlas_forward_decl GlobalTheory.dualBasis_baseChange
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

namespace GlobalTheory

theorem annihilator_baseChange : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Projective R M] {M' : Type*} [AddCommGroup M'] [Module R' M']
    (f : M →ₛₗ[algebraMap R R'] M') (hf : Function.Bijective (liftSemi f)) (F : Submodule R M)
    (hF : ∃ N : Submodule R M, IsCompl F N) (F' : Submodule R' M') (hF' : F' = Submodule.span R' (f '' (F : Set M)))
    (g : Module.Dual R M →ₛₗ[algebraMap R R'] Module.Dual R' M') (hg : ∀ h c, g h (f c) = algebraMap R R' (h c)),
   Submodule.span R' (g '' (F.dualAnnihilator : Set (Module.Dual R M))) = F'.dualAnnihilator := by
  intro R R' _ _ _ M _ _ _ _ M' _ _ f hf F hF F' hF' g hg
  subst hF'
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨h, hh, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
    intro w hw
    refine Submodule.span_induction (p := fun w _ => g h w = 0) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨c, hc, rfl⟩
      rw [hg, (Submodule.mem_dualAnnihilator h).1 hh c hc, map_zero]
    · simp
    · intro x y _ _ hx hy; simp [hx, hy]
    · intro a x _ hx; simp [hx]
  · intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    obtain ⟨N, hN⟩ := hF
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
    let q : M →ₗ[R] M := LinearMap.id - F.subtype ∘ₗ Submodule.linearProjOfIsCompl F N hN
    have hqF : ∀ c ∈ F, q c = 0 := by
      intro c hc
      have e : F.linearProjOfIsCompl N hN c = ⟨c, hc⟩ := Submodule.linearProjOfIsCompl_apply_left hN ⟨c, hc⟩
      simp [q, e]
    have hqd : ∀ m, m - q m ∈ F := by intro m; simp [q]
    let k : Fin n → Module.Dual R M := fun i => LinearMap.proj i ∘ₗ s ∘ₗ q
    have hk : ∀ i, k i ∈ F.dualAnnihilator := by
      intro i; rw [Submodule.mem_dualAnnihilator]; intro c hc; simp [k, hqF c hc]
    have hexp : ∀ m : M, m = ∑ i, s m i • π (Pi.single i 1) := by
      intro m
      have e1 : m = π (s m) := by rw [← LinearMap.comp_apply, hs, LinearMap.id_apply]
      conv_lhs => rw [e1, pi_eq_sum_univ (s m)]
      simp only [map_sum, map_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      ext j
      simp [Pi.single_apply, eq_comm]
    have key : φ = ∑ i, φ (f (π (Pi.single i 1))) • g (k i) := by
      apply LinearMap.ext; intro w
      obtain ⟨z, rfl⟩ := hf.2 w
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x c =>
        rw [liftSemi_tmul, map_smul, map_smul]
        congr 1
        have h1 : φ (f c) = φ (f (q c)) := by
          have := hφ _ (Submodule.subset_span ⟨_, hqd c, rfl⟩)
          rw [map_sub, map_sub, sub_eq_zero] at this; exact this
        rw [h1, hexp (q c)]
        simp [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, hg, k, Algebra.smul_def, mul_comm]
    rw [key]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k i, hk i, rfl⟩)

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinear_filtration_base_change : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Projective R M] {M' : Type*} [AddCommGroup M'] [Module R' M']
    (f : M →ₛₗ[algebraMap R R'] M') (hf : Function.Bijective (liftSemi f)) (F : Submodule R M)
    (hF : ∃ N : Submodule R M, IsCompl F N) (F' : Submodule R' M') (hF' : F' = Submodule.span R' (f '' (F : Set M)))
    (g : Module.Dual R M →ₛₗ[algebraMap R R'] Module.Dual R' M') (hg : ∀ h c, g h (f c) = algebraMap R R' (h c)),
   Submodule.span R' (g '' (F.dualAnnihilator : Set (Module.Dual R M))) = F'.dualAnnihilator := by
  atlas_forward_decl GlobalTheory.annihilator_baseChange
end

section
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HodgeUnif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem isDiff_mul (hA : IsAbelianScheme A) (u : HolUnif A L g) {w w' : Fin g → ℂ} {v v' : epsR ℂ ⟶ A}
    (hv : IsTangent v) (hv' : IsTangent v') (h : u.IsDiff w v) (h' : u.IsDiff w' v') :
    u.IsDiff (w + w') (v * v') := by
  have := GlobalTheory.isDiff_sum_smul_of_isLieComb A hA L g 2 u ![v, v'] ![w, w'] ![1, 1] (v * v')
    (fun i => by fin_cases i <;> assumption) (fun i => by fin_cases i <;> assumption)
    ⟨![v, v'], fun i => by
      fin_cases i <;> (rw [← GlobalTheory.GrpTangent.epsScale_left]; simp [GlobalTheory.GrpTangent.epsScale_one]),
      by simp [List.ofFn_succ]⟩
  simpa [Fin.sum_univ_two] using this

theorem isDiff_smul (hA : IsAbelianScheme A) (u : HolUnif A L g) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A}
    (hv : IsTangent v) (h : u.IsDiff w v) (r : ℂ) :
    u.IsDiff (r • w) (GlobalTheory.GrpTangent.epsScale r ≫ v) := by
  have := GlobalTheory.isDiff_sum_smul_of_isLieComb A hA L g 1 u ![v] ![w] ![r] (GlobalTheory.GrpTangent.epsScale r ≫ v)
    (fun i => by fin_cases i; assumption) (fun i => by fin_cases i; assumption)
    ⟨![GlobalTheory.GrpTangent.epsScale r ≫ v], fun i => by
      fin_cases i; simp [Over.comp_left, GlobalTheory.GrpTangent.epsScale_left], by simp⟩
  simpa using this

theorem exists_isLieImage_isDiff (hA : IsAbelianScheme A) (u : HolUnif A L g) (P : u.Λ →+ HdR A)
    (hP : ∀ x : u.Λ, ∃ v, IsLieImage (P x) v ∧ u.IsDiff x v) (c : u.Λ →₀ ℂ) :
    ∃ v, IsLieImage (c.sum fun x r ↦ r • P x) v ∧ u.IsDiff (c.sum fun x r ↦ r • (x : Fin g → ℂ)) v := by
  induction c using Finsupp.induction with
  | zero =>
    refine ⟨1, by simpa using isLieImage_one_iff.2 (zero_mem (Fil A)), ?_⟩
    simpa [Hom.one_def] using GlobalTheory.ArchMetricCompare.isDiff_zero u
  | single_add a b f _ _ ih =>
    obtain ⟨v, hv, hd⟩ := ih
    obtain ⟨v₀, hv₀, hd₀⟩ := hP a
    refine ⟨(GlobalTheory.GrpTangent.epsScale b ≫ v₀) * v, ?_, ?_⟩
    · rw [Finsupp.sum_add_index' (h := fun x r ↦ r • P x) (fun _ ↦ zero_smul ℂ _)
        (fun _ _ _ ↦ add_smul _ _ _), Finsupp.sum_single_index (h := fun x r ↦ r • P x) (zero_smul ℂ _)]
      exact (hv₀.smul b).add hv
    · rw [Finsupp.sum_add_index' (h := fun (x : u.Λ) (r : ℂ) ↦ r • (x : Fin g → ℂ)) (fun _ ↦ zero_smul ℂ _)
        (fun _ _ _ ↦ add_smul _ _ _),
        Finsupp.sum_single_index (h := fun (x : u.Λ) (r : ℂ) ↦ r • (x : Fin g → ℂ)) (zero_smul ℂ _)]
      exact isDiff_mul hA u (hv₀.smul b).1 hv.1 (isDiff_smul hA u hv₀.1 hd₀ b) hd

theorem sum_smul_mem_fil_iff :
    ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g : ℕ) (u : HolUnif A L g)
    (P : u.Λ →+ HdR A), LieExact A → (∀ x : u.Λ, ∃ v, IsLieImage (P x) v ∧ u.IsDiff x v) →
    ∀ c : u.Λ →₀ ℂ, (c.sum fun x r ↦ r • P x) ∈ Fil A ↔ (c.sum fun x r ↦ r • (x : Fin g → ℂ)) = 0 := by
  intro A _ hA L g u P hE hP c
  obtain ⟨v, hv, hd⟩ := exists_isLieImage_isDiff hA u P hP c
  rw [← isLieImage_one_iff, GlobalTheory.ArchMetricCompare.isDiff_ne_iff u hv.1 hd, ← Hom.one_def]
  exact ⟨fun h ↦ (hE.1 _).unique hv h, fun e ↦ e ▸ hv⟩

end GlobalTheory.HodgeUnif
end
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_combination_in_hodge_filtration : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g : ℕ) (u : HolUnif A L g)
    (P : u.Λ →+ HdR A), LieExact A → (∀ x : u.Λ, ∃ v, IsLieImage (P x) v ∧ u.IsDiff x v) →
    ∀ c : u.Λ →₀ ℂ, (c.sum fun x r ↦ r • P x) ∈ Fil A ↔ (c.sum fun x r ↦ r • (x : Fin g → ℂ)) = 0 := by
  atlas_forward_decl GlobalTheory.HodgeUnif.sum_smul_mem_fil_iff
end

section
section
namespace GlobalTheory

theorem spanning_map_factors_through_quotient :
    ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (P : Λ →+ W)
    (F : Submodule ℂ W), Submodule.span ℂ (Set.range P) = ⊤ → Module.finrank ℂ W = 2 * g →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ c : Λ →₀ ℂ, (c.sum fun x r ↦ r • P x) ∈ F ↔ (c.sum fun x r ↦ r • (x : Fin g → ℂ)) = 0) →
    ∃ Q : W →ₗ[ℂ] (Fin g → ℂ), LinearMap.ker Q = F ∧ (∀ x, Q (P x) = x) ∧ Module.finrank ℂ F = g := by
  intro W _ _ g Λ P F hspan hdim hR hF
  set Ψ : (Λ →₀ ℂ) →ₗ[ℂ] W := Finsupp.linearCombination ℂ (fun x => P x) with hΨ
  set Ψ' : (Λ →₀ ℂ) →ₗ[ℂ] (Fin g → ℂ) := Finsupp.linearCombination ℂ (fun x => (x : Fin g → ℂ)) with hΨ'
  have hF' : ∀ c, Ψ c ∈ F ↔ Ψ' c = 0 := by
    intro c
    simpa [hΨ, hΨ', Finsupp.linearCombination_apply] using hF c
  have hsurj : Function.Surjective Ψ := by
    rw [← LinearMap.range_eq_top, hΨ, Finsupp.range_linearCombination]
    exact hspan
  have hker : LinearMap.ker Ψ ≤ LinearMap.ker Ψ' := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    exact (hF' c).1 (by rw [hc]; exact F.zero_mem)
  let Q : W →ₗ[ℂ] (Fin g → ℂ) :=
    ((LinearMap.ker Ψ).liftQ Ψ' hker).comp (Ψ.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hQ : ∀ c, Q (Ψ c) = Ψ' c := by
    intro c
    have : (Ψ.quotKerEquivOfSurjective hsurj).symm (Ψ c) = (LinearMap.ker Ψ).mkQ c := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [Q, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  have hQP : ∀ x, Q (P x) = x := by
    intro x
    have := hQ (Finsupp.single x 1)
    simpa [hΨ, hΨ'] using this
  have hkerQ : LinearMap.ker Q = F := by
    ext w
    obtain ⟨c, rfl⟩ := hsurj w
    rw [LinearMap.mem_ker, hQ, hF']
  refine ⟨Q, hkerQ, hQP, ?_⟩
  have hrange : LinearMap.range Q = ⊤ := by
    have h1 : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) ≤ (LinearMap.range Q).restrictScalars ℝ := by
      rw [Submodule.span_le]
      intro x hx
      exact ⟨P ⟨x, hx⟩, hQP ⟨x, hx⟩⟩
    rw [hR] at h1
    rw [eq_top_iff]
    intro y _
    exact h1 (Submodule.mem_top : y ∈ (⊤ : Submodule ℝ (Fin g → ℂ)))
  rcases Nat.eq_zero_or_pos g with hg | hg
  · subst hg
    have hP0 : ∀ x, P x = 0 := by
      intro x
      have : x = 0 := Subsingleton.elim _ _
      rw [this, map_zero]
    have hbot : (⊤ : Submodule ℂ W) = ⊥ := by
      rw [← hspan, eq_bot_iff, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      simp [hP0 x]
    haveI : Subsingleton W := by
      rw [← Submodule.subsingleton_iff ℂ]
      exact subsingleton_of_bot_eq_top hbot.symm
    exact Module.finrank_zero_of_subsingleton
  · haveI : FiniteDimensional ℂ W := Module.finite_of_finrank_pos (by omega)
    have := LinearMap.finrank_range_add_finrank_ker Q
    rw [hrange, finrank_top, Module.finrank_fin_fun, hkerQ, hdim] at this
    omega

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_projection_from_lattice : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (P : Λ →+ W)
    (F : Submodule ℂ W), Submodule.span ℂ (Set.range P) = ⊤ → Module.finrank ℂ W = 2 * g →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ c : Λ →₀ ℂ, (c.sum fun x r ↦ r • P x) ∈ F ↔ (c.sum fun x r ↦ r • (x : Fin g → ℂ)) = 0) →
    ∃ Q : W →ₗ[ℂ] (Fin g → ℂ), LinearMap.ker Q = F ∧ (∀ x, Q (P x) = x) ∧ Module.finrank ℂ F = g := by
  atlas_forward_decl GlobalTheory.spanning_map_factors_through_quotient
end

section
section
namespace GlobalTheory

theorem eigenvector_mem_ker_of_ne_coord_char :
    ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (P : Λ →+ W),
    Submodule.span ℂ (Set.range P) = ⊤ → ∀ (Q : W →ₗ[ℂ] (Fin g → ℂ)), (∀ x, Q (P x) = x) →
    ∀ (O : Type) (T : O → Module.End ℂ W) (χ : O → Fin g → ℂ),
    (∀ a (x : Λ), (fun j ↦ χ a j * (x : Fin g → ℂ) j) ∈ Λ) →
    (∀ a (x y : Λ), (y : Fin g → ℂ) = (fun j ↦ χ a j * (x : Fin g → ℂ) j) → T a (P x) = P y) →
    ∀ ψ : O → ℂ, (∀ j, ∃ a, χ a j ≠ ψ a) →
    (⨅ a, Module.End.eigenspace (T a) (ψ a) : Submodule ℂ W) ≤ LinearMap.ker Q := by
  intro W _ _ g Λ P hspan Q hQ O T χ hΛ hT ψ hψ w hw

  let D : O → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun a =>
    { toFun := fun v j => χ a j * v j
      map_add' := by intro u v; funext j; simp [mul_add]
      map_smul' := by intro c v; funext j; simp; ring }
  have hcomm : ∀ a, Q ∘ₗ T a = D a ∘ₗ Q := by
    intro a
    refine LinearMap.ext_on_range hspan ?_
    intro x
    have h1 : T a (P x) = P ⟨_, hΛ a x⟩ := hT a x ⟨_, hΛ a x⟩ rfl
    simp only [LinearMap.comp_apply, h1, hQ]
    rfl
  rw [LinearMap.mem_ker]
  have hw' : ∀ a, T a w = ψ a • w := by
    intro a
    have := (Submodule.mem_iInf _).1 hw a
    exact Module.End.mem_eigenspace_iff.1 this
  funext j
  obtain ⟨a, ha⟩ := hψ j
  have h2 := congrArg (fun f => f w) (hcomm a)
  simp only [LinearMap.comp_apply, hw', map_smul] at h2
  have h3 := congrFun h2 j
  change ψ a * Q w j = χ a j * Q w j at h3
  have h4 : (χ a j - ψ a) * Q w j = 0 := by rw [sub_mul, ← h3]; ring
  rcases mul_eq_zero.1 h4 with h | h
  · exact absurd (sub_eq_zero.1 h) ha
  · simpa using h

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_projection_eigenvalue_compat : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (P : Λ →+ W),
    Submodule.span ℂ (Set.range P) = ⊤ → ∀ (Q : W →ₗ[ℂ] (Fin g → ℂ)), (∀ x, Q (P x) = x) →
    ∀ (O : Type) (T : O → Module.End ℂ W) (χ : O → Fin g → ℂ),
    (∀ a (x : Λ), (fun j ↦ χ a j * (x : Fin g → ℂ) j) ∈ Λ) →
    (∀ a (x y : Λ), (y : Fin g → ℂ) = (fun j ↦ χ a j * (x : Fin g → ℂ) j) → T a (P x) = P y) →
    ∀ ψ : O → ℂ, (∀ j, ∃ a, χ a j ≠ ψ a) →
    (⨅ a, Module.End.eigenspace (T a) (ψ a) : Submodule ℂ W) ≤ LinearMap.ker Q := by
  atlas_forward_decl GlobalTheory.eigenvector_mem_ker_of_ne_coord_char
end

section
section
namespace GlobalTheory

theorem finrank_iSup_iInf_eigenspace_ge_card : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (O : Type) (T : O → Module.End ℂ W),
    (∀ a b, Commute (T a) (T b)) → ∀ (I : Type) [Fintype I] (ψ : I → O → ℂ), Function.Injective ψ →
    (∀ i, 1 ≤ Module.finrank ℂ (⨅ a, Module.End.eigenspace (T a) (ψ i a) : Submodule ℂ W)) →
    Fintype.card I ≤ Module.finrank ℂ (⨆ i, ⨅ a, Module.End.eigenspace (T a) (ψ i a) : Submodule ℂ W) := by
  intro W _ _ _ O T hc I _ ψ hψ hpos
  set V : I → Submodule ℂ W := fun i => ⨅ a, Module.End.eigenspace (T a) (ψ i a) with hVdef
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)
  have hV : iSupIndep V := by
    refine (hind.comp hψ).mono ?_
    intro i
    exact iInf_mono fun a => Module.End.eigenspace_le_maxGenEigenspace
  have hne : ∀ i, ∃ v ∈ V i, v ≠ 0 := by
    intro i
    have : V i ≠ ⊥ := by
      intro h
      have h2 := hpos i
      change 1 ≤ Module.finrank ℂ (V i) at h2
      rw [h, finrank_bot] at h2
      omega
    exact Submodule.exists_mem_ne_zero_of_ne_bot this
  choose v hvV hv0 using hne
  set S : Submodule ℂ W := ⨆ i, V i
  have hvS : ∀ i, v i ∈ S := fun i => Submodule.mem_iSup_of_mem i (hvV i)
  have hli : LinearIndependent ℂ v := iSupIndep.linearIndependent V hV hvV hv0
  let w : I → S := fun i => ⟨v i, hvS i⟩
  have hw : LinearIndependent ℂ w := by
    apply LinearIndependent.of_comp S.subtype
    exact hli
  exact hw.fintype_card_le_finrank

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_le_finrank_sup_eigenspaces : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (O : Type) (T : O → Module.End ℂ W),
    (∀ a b, Commute (T a) (T b)) → ∀ (I : Type) [Fintype I] (ψ : I → O → ℂ), Function.Injective ψ →
    (∀ i, 1 ≤ Module.finrank ℂ (⨅ a, Module.End.eigenspace (T a) (ψ i a) : Submodule ℂ W)) →
    Fintype.card I ≤ Module.finrank ℂ (⨆ i, ⨅ a, Module.End.eigenspace (T a) (ψ i a) : Submodule ℂ W) := by
  atlas_forward_decl GlobalTheory.finrank_iSup_iInf_eigenspace_ge_card
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FilCx

theorem fil_eq_iSup_eigenspace_bar : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (c : Ideal (OF E)), c ≠ ⊥ → ∀ (𝔠 : FracId (FR E)) (L : Set E) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X)
      (α : orderC c → (X.A ⟶ X.A)) [∀ a, IsMonHom (α a)],
      (∀ (a : orderC c) w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α a) →
      Fil X.A = ⨆ i, ⨅ a : orderC c,
        Module.End.eigenspace (push (dp0 ℂ) (𝟙 _) (α a)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) a) := by
  intro hPC hADR E _ _ _ I _ φ hφ c hc 𝔠 L X U α _ hα
  obtain ⟨ε, hpc⟩ := hPC
  set g := Module.finrank ℚ (FR E) with hg
  have hLB : (X.diag U.c).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (X.isLB U.c) _ _
  obtain ⟨P, hspan, hdim, hlie, hend, -⟩ := hpc X.A g X.ab X.dim (X.diag U.c) hLB U.u
  clear hpc
  have hLE : LieExact X.A := (hADR.2.1 ℂ X.A g X.ab X.dim).1
  obtain ⟨Q, hQker, hQP, hFdim⟩ :=
    GlobalTheory.T.hodge_projection_from_lattice (HdR X.A) g U.u.Λ P (Fil X.A) hspan hdim U.u.full (GlobalTheory.T.lattice_combination_in_hodge_filtration X.A X.ab _ g U.u P hLE hlie)
  let M : orderC c → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun a ↦
    LinearMap.pi fun j ↦ (φ (U.e j) (a : E)) • LinearMap.proj j
  have hM : ∀ a w, M a w = fun j ↦ φ (U.e j) (a : E) * w j := fun a w ↦ by ext j; simp [M]
  have hMΛ : ∀ (a : orderC c) (x : U.u.Λ), (fun j ↦ φ (U.e j) (a : E) * (x : Fin g → ℂ) j) ∈ U.u.Λ := by
    intro a x
    rw [← U.u.ker, hα a, (U.u.ker x).2 x.2]
    simp
  have hT : ∀ (a : orderC c) (x y : U.u.Λ), (y : Fin g → ℂ) = (fun j ↦ φ (U.e j) (a : E) * (x : Fin g → ℂ) j) →
      push (dp0 ℂ) (𝟙 _) (α a) (P x) = P y := by
    intro a x y hy
    exact hend (α a) (M a) (fun w ↦ by rw [hM]; exact hα a w) x y (by rw [hy, hM])
  have hbar : ∀ σ : E →+* ℂ, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ = ComplexEmbedding.conjugate σ := fun σ ↦ by
    ext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar, ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]
  have hnreal : ∀ σ : E →+* ℂ, ¬ ComplexEmbedding.IsReal σ := fun σ h ↦
    (NumberField.InfinitePlace.isComplex_mk_iff (φ := σ)).1 (NumberField.IsTotallyComplex.isComplex _) h
  have hsep : ∀ (i : I) (j : Fin g), ∃ a : orderC c, φ (U.e j) (a : E) ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) (a : E) := by
    intro i j
    by_contra h
    push_neg at h
    have h1 := GlobalTheory.CMExtend.ringHom_ext_orderC hc _ _ h
    rw [hbar] at h1
    obtain ⟨k, -, hk⟩ := hφ (φ (U.e j))
    have e1 := hk (U.e j) (Or.inl rfl)
    have e2 := hk i (Or.inr h1)
    rw [e1, ← e2] at h1
    exact hnreal _ h1.symm
  have hinj : Function.Injective fun (i : I) (a : orderC c) ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) (a : E) := by
    intro i i' h
    have h1 := GlobalTheory.CMExtend.ringHom_ext_orderC hc _ _ (fun a ↦ congrFun h a)
    rw [hbar, hbar] at h1
    have h2 : φ i = φ i' := by
      ext x
      simpa [ComplexEmbedding.conjugate_coe_eq] using congrArg (starRingEnd ℂ) (RingHom.congr_fun h1 x)
    obtain ⟨k, -, hk⟩ := hφ (φ i)
    exact (hk i (Or.inl rfl)).trans (hk i' (Or.inl h2)).symm
  have hcomm : ∀ a b : orderC c, Commute (push (dp0 ℂ) (𝟙 _) (α a)) (push (dp0 ℂ) (𝟙 _) (α b)) := by
    intro a b
    refine LinearMap.ext_on_range hspan fun x ↦ ?_
    simp only [Module.End.mul_apply]
    rw [hT b x ⟨_, hMΛ b x⟩ rfl, hT a x ⟨_, hMΛ a x⟩ rfl, hT a _ ⟨_, hMΛ a ⟨_, hMΛ b x⟩⟩ rfl,
      hT b _ ⟨_, hMΛ b ⟨_, hMΛ a x⟩⟩ rfl]
    congr 1
    ext j
    simp only
    ring
  have hpos : 0 < g := Module.finrank_pos
  haveI : FiniteDimensional ℂ (HdR X.A) := Module.finite_of_finrank_pos (by rw [hdim]; omega)
  have hEdim : Module.finrank ℂ (HdR X.A) = Module.finrank ℚ E := by
    rw [hdim, ← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]

  let Φ : E →+* (Fin g → ℂ) := Pi.ringHom fun j ↦ φ (U.e j)
  let L' : AddSubgroup E := AddSubgroup.comap Φ.toAddMonoidHom U.u.Λ.toAddSubgroup
  let jL : L' →+ U.u.Λ :=
    { toFun := fun x ↦ ⟨Φ x, x.2⟩
      map_zero' := by ext; simp
      map_add' := fun x y ↦ by ext; simp }
  have hone : ∀ i, 1 ≤ Module.finrank ℂ (⨅ a : orderC c,
      Module.End.eigenspace (push (dp0 ℂ) (𝟙 _) (α a)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) a) : Submodule ℂ (HdR X.A)) := by
    intro i
    refine le_of_eq (GlobalTheory.T.cm_representation_eigen_decomposition E (orderC c) (GlobalTheory.CMExtend.exists_natMul_mem_orderC hc) L' ?_ (HdR X.A)
      (P.comp jL) ?_ hEdim (fun a ↦ push (dp0 ℂ) (𝟙 _) (α a)) ?_ (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i))).symm
    · intro a ha x hx
      show Φ (a * x) ∈ U.u.Λ
      have e : Φ (a * x) = fun j ↦ φ (U.e j) a * (Φ x) j := by rw [map_mul]; rfl
      rw [e]; exact hMΛ ⟨a, ha⟩ ⟨Φ x, hx⟩
    · refine eq_top_mono (Submodule.span_mono ?_) hspan
      rintro _ ⟨y, rfl⟩
      obtain ⟨x, -, hx⟩ := (U.lat y).1 y.2
      have hxy : Φ x = y := by
        rw [hx]; funext j; simp only [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord, Pi.zero_apply, zero_mul, add_zero]; rfl
      have hmem : x ∈ L' := by
        show Φ x ∈ U.u.Λ
        rw [hxy]; exact y.2
      refine ⟨⟨x, hmem⟩, ?_⟩
      show P (jL ⟨x, hmem⟩) = P y
      congr 1
      exact Subtype.ext hxy
    · intro a x y hy
      refine hT a (jL x) (jL y) ?_
      show Φ y = fun j ↦ φ (U.e j) a * (Φ x) j
      rw [hy, map_mul]; rfl
  have hle : (⨆ i, ⨅ a : orderC c,
      Module.End.eigenspace (push (dp0 ℂ) (𝟙 _) (α a)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) a)) ≤ Fil X.A := by
    refine iSup_le fun i ↦ ?_
    rw [← hQker]
    exact GlobalTheory.T.hodge_projection_eigenvalue_compat (HdR X.A) g U.u.Λ P hspan Q hQP (orderC c) (fun a ↦ push (dp0 ℂ) (𝟙 _) (α a))
      (fun a j ↦ φ (U.e j) (a : E)) hMΛ hT (fun a ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) a) (fun j ↦ hsep i j)
  have hge := GlobalTheory.T.card_le_finrank_sup_eigenspaces (HdR X.A) (orderC c) (fun a ↦ push (dp0 ℂ) (𝟙 _) (α a)) hcomm I _ hinj hone
  have hcard : Fintype.card I = g := by rw [Fintype.card_congr U.e.symm, Fintype.card_fin]
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hFdim, ← hcard]; exact hge)).symm

end GlobalTheory.FilCx
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_order_uniformization_endomorphisms : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (c : Ideal (OF E)), c ≠ ⊥ → ∀ (𝔠 : FracId (FR E)) (L : Set E) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X)
      (α : orderC c → (X.A ⟶ X.A)) [∀ a, IsMonHom (α a)],
      (∀ (a : orderC c) w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α a) →
      Fil X.A = ⨆ i, ⨅ a : orderC c,
        Module.End.eigenspace (push (dp0 ℂ) (𝟙 _) (α a)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) a) := by
  atlas_forward_decl GlobalTheory.FilCx.fil_eq_iSup_eigenspace_bar
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FilEig

theorem fil_baseChange_eq_iSup_eigK : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)),
      (Submodule.map eH.toLinearMap (Fil X₀.A)).baseChange (FractionRing R) =
        ⨆ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) := by
  intro hPC hDR hDC E _ _ _ _ I _ d φ hφ 𝔣 h𝔣 l _ Q hQ hQl y hy lam 𝔠 R _ hR X₀ X U p cm hpull hrm hα j hj φK hφK n eH
  choose α hαm hαp hαu using hα
  have hcm : ∀ a, IsMonHom (cm.act a) := cm.hom
  have hgrp : IsGrpPullback X.A X₀.A (spMap (algebraMap R ℂ)) p := hpull.grp
  obtain ⟨hbc, hF1⟩ := hDR.2.2.1 R X₀.A _ X₀.ab X₀.dim ℂ X.A p hgrp
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim hDR.1 X₀.ab X₀.dim
  obtain ⟨-, hcompl, -⟩ := hDR.2.1 R X₀.A _ X₀.ab X₀.dim
  have hcorr : ∀ (h : HdR X₀.A) c, hbc.bcMap h ((GlobalTheory.Published.AbelianDeRham.bcMor hgrp).pull c) = algebraMap R ℂ (h c) :=
    fun h c ↦ (hbc.corr_iff.2 rfl) c
  let β : (Fin n → R) →ₛₗ[algebraMap R ℂ] HdR X.A := hbc.bcMap.comp eH.symm.toLinearMap
  have hc0 : condQ 𝔣 Q ≠ ⊥ := by
    rw [condQ, Ne, Ideal.mul_eq_bot, not_or]
    refine ⟨h𝔣.1, ?_⟩
    rw [← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff]
    push_neg
    intro q _
    rw [Ideal.zero_eq_bot]
    exact q.ne_bot
  have hC := GlobalTheory.T.cm_order_uniformization_endomorphisms hPC hDR E I φ hφ.2.2.2.2.2.2.1 (condQ 𝔣 Q) hc0 𝔠 _ X U α hαu
  refine GlobalTheory.T.lattice_basis_fraction_field_independent j hj β ?_ _ (fun a ↦ push (dp0 ℂ) (𝟙 _) (α a)) ?_ _ (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) ?_
  · exact GlobalTheory.T.semilinear_dual_basis_base_change (GlobalTheory.Published.AbelianDeRham.bcMor hgrp).pull hbc eH _ (fun k c ↦ hcorr _ c)
  · intro a x
    have e := GrpMor.Corr.push (GlobalTheory.Published.AbelianDeRham.bcMor hgrp) (cm.act a) (α a)
      (hαp a).symm (hbc.corr_iff.2 rfl : (GlobalTheory.Published.AbelianDeRham.bcMor hgrp).Corr (eH.symm x) (hbc.bcMap (eH.symm x)))
    have e2 := hbc.corr_iff.1 e
    simp only [β, LinearMap.comp_apply, LinearEquiv.coe_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply]
    rw [act_apply]
    simpa [LinearEquiv.conjRingEquiv, LinearEquiv.conj_apply] using e2
  · have himg : β '' (Submodule.map eH.toLinearMap (Fil X₀.A) : Set (Fin n → R)) = hbc.bcMap '' (Fil X₀.A : Set (HdR X₀.A)) := by
      ext v
      simp [β]
    rw [himg, Fil, GlobalTheory.T.semilinear_filtration_base_change (GlobalTheory.Published.AbelianDeRham.bcMor hgrp).pull hbc _ hcompl _ hF1 hbc.bcMap hcorr]
    change Fil X.A = _
    rw [hC]
    congr 1
    ext i : 1
    congr 1
    ext a : 1
    congr 1
    show _ = j (φK i _)
    rw [← RingHom.comp_apply, hφK i]
    rfl

end GlobalTheory.FilEig
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_auxiliary_set_local_conditions : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)),
      (Submodule.map eH.toLinearMap (Fil X₀.A)).baseChange (FractionRing R) =
        ⨆ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) := by
  atlas_forward_decl GlobalTheory.FilEig.fil_baseChange_eq_iSup_eigK
end
