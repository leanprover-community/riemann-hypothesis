import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraFiniteProjectiveRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraBaseChangeIso

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DetSpan

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations

theorem ord_nonneg_of_int (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (x : R) :
    0 ≤ ord_vw R (algebraMap R (FractionRing R) x) := by
  unfold ord_vw
  by_cases hx : x = 0
  · subst hx; simp
  · have h0 : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) (algebraMap R (FractionRing R) x) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hx
    have h1 := (IsDiscreteValuationRing.maximalIdeal R).valuation_le_one (K := FractionRing R) x
    have := (WithZero.log_le_log h0 one_ne_zero).2 h1
    rw [WithZero.log_one] at this
    omega

theorem ord_le (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (n : ℕ) (D t u : R)
    (h : D ^ n = t * u) (hD : D ≠ 0) :
    ord_vw R (algebraMap R (FractionRing R) u) ≤ n * ord_vw R (algebraMap R (FractionRing R) D) := by
  unfold ord_vw
  set v := (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R)
  have inj := IsFractionRing.injective R (FractionRing R)
  have hDn : D ^ n ≠ 0 := pow_ne_zero _ hD
  have hu : u ≠ 0 := by rintro rfl; rw [mul_zero] at h; exact hDn h
  have ne : ∀ y : R, y ≠ 0 → v (algebraMap R (FractionRing R) y) ≠ 0 := fun y hy => by
    rw [Valuation.ne_zero_iff]; exact (map_ne_zero_iff _ inj).2 hy
  have e1 : v (algebraMap R (FractionRing R) D) ^ n = v (algebraMap R (FractionRing R) t) * v (algebraMap R (FractionRing R) u) := by
    rw [← map_pow, ← map_pow, h, map_mul, map_mul]
  have e2 : v (algebraMap R (FractionRing R) D) ^ n ≤ v (algebraMap R (FractionRing R) u) := by
    rw [e1]
    exact mul_le_of_le_one_left' ((IsDiscreteValuationRing.maximalIdeal R).valuation_le_one (K := FractionRing R) t)
  have e3 := (WithZero.log_le_log (pow_ne_zero _ (ne D hD)) (ne u hu)).2 e2
  rw [WithZero.log_pow, nsmul_eq_mul] at e3
  linarith

theorem wedge_eq_smul_gen_val_le : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (L : Type) [AddCommGroup L] [Module R L]
    [Module.Free R L] [Module.Finite R L] (n : ℕ), Module.finrank R L = n →
    ∀ (e : Fin n → (L →ₗ[R] R)) (D : R), D ≠ 0 → (∀ ω : L →ₗ[R] R, D • ω ∈ Submodule.span R (Set.range e)) →
    ∀ (l : ℕ), ∃ (δ₀ : L [⋀^Fin n]→ₗ[R] R) (u₀ : R), Submodule.span R {δ₀} = ⊤ ∧
      Matrix.detRowAlternating.compLinearMap (LinearMap.pi e) = u₀ • δ₀ ∧
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) u₀) ≤
        n • GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) D) := by
  intro R _ _ _ L _ _ _ _ n hn e D hD hspan l
  classical
  let b := Module.finBasisOfFinrankEq R L hn
  refine ⟨b.det, Matrix.detRowAlternating.compLinearMap (LinearMap.pi e) b, ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    intro f _
    rw [AlternatingMap.eq_smul_basis_det b f]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · exact AlternatingMap.eq_smul_basis_det b _
  · set u := Matrix.detRowAlternating.compLinearMap (LinearMap.pi e) b with hu_def
    choose t ht using fun k => (Submodule.mem_span_range_iff_exists_fun R).1 (hspan (b.coord k))
    let E : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => e i (b j)
    have hu : u = E.det := by
      rw [← Matrix.det_transpose]
      rfl
    have hm : Matrix.of t * E = D • (1 : Matrix (Fin n) (Fin n) R) := by
      ext k j
      have := congrArg (fun f : L →ₗ[R] R => f (b j)) (ht k)
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Module.Basis.coord_apply,
        Module.Basis.repr_self] at this
      simp only [Matrix.mul_apply, Matrix.of_apply, E, Matrix.smul_apply, Matrix.one_apply, this, smul_eq_mul,
        Finsupp.single_apply]
      by_cases hkj : k = j
      · subst hkj; simp
      · simp [hkj, Ne.symm hkj]
    have hkey : D ^ n = (Matrix.of t).det * u := by
      rw [hu, ← Matrix.det_mul, hm, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, _root_.mul_one]
    have hord := ord_le R n D _ u hkey hD
    have hu0 : u ≠ 0 := by
      rintro h0; rw [h0, mul_zero] at hkey; exact pow_ne_zero n hD hkey
    have inj := IsFractionRing.injective R (FractionRing R)
    have hc : (0 : ℚ) ≤ (ord_vw R ((l : ℕ) : FractionRing R) : ℚ) := by
      rw [← map_natCast (algebraMap R (FractionRing R))]
      exact_mod_cast ord_nonneg_of_int R (l : R)
    unfold val_vp
    rw [if_neg ((map_ne_zero_iff _ inj).2 hu0), if_neg ((map_ne_zero_iff _ inj).2 hD), ← WithTop.coe_nsmul,
      WithTop.coe_le_coe, nsmul_eq_mul, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hc
    exact_mod_cast hord

end GlobalTheory.DetSpan
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_top_exterior_power : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (L : Type) [AddCommGroup L] [Module R L]
    [Module.Free R L] [Module.Finite R L] (n : ℕ), Module.finrank R L = n →
    ∀ (e : Fin n → (L →ₗ[R] R)) (D : R), D ≠ 0 → (∀ ω : L →ₗ[R] R, D • ω ∈ Submodule.span R (Set.range e)) →
    ∀ (l : ℕ), ∃ (δ₀ : L [⋀^Fin n]→ₗ[R] R) (u₀ : R), Submodule.span R {δ₀} = ⊤ ∧
      Matrix.detRowAlternating.compLinearMap (LinearMap.pi e) = u₀ • δ₀ ∧
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) u₀) ≤
        n • GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) D) := by
  atlas_forward_decl GlobalTheory.DetSpan.wedge_eq_smul_gen_val_le
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Lie.free_finrank_of_isLocalRing : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (R : Type) [CommRing R] [IsLocalRing R] (X : Obj F 𝔠 (Sp R)),
    Module.Free R X.Lie ∧ Module.Finite R X.Lie ∧ Module.finrank R X.Lie = Module.finrank ℚ F := by
  intro F _ _ 𝔠 R _ _ X
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank X
  haveI := hfin
  haveI := hproj
  haveI : Module.Free R X.Lie := Module.free_of_flat_of_isLocalRing
  refine ⟨inferInstance, hfin, ?_⟩
  have h := hrk (IsLocalRing.closedPoint R)
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  exact h
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_free_rank_degree : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (R : Type) [CommRing R] [IsLocalRing R] (X : Obj F 𝔠 (Sp R)),
    Module.Free R X.Lie ∧ Module.Finite R X.Lie ∧ Module.finrank R X.Lie = Module.finrank ℚ F := by
  atlas_forward_decl GlobalTheory.Lie.free_finrank_of_isLocalRing
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieCoord

theorem exists_lieCoord_unif : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)} {φ : I → E →+* ℂ} {L : Set E}
    (R : Subring ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X) (p : X.A.left ⟶ X₀.A.left),
    X.IsPullBy X₀ (spMap R.subtype) p →
    ∃ cd : X₀.Lie →ₗ[R] (Fin (Module.finrank ℚ (FR E)) → ℂ),
      (∀ v, ∃ v' : X.Lie, Obj.LieCorr R.subtype p v v' ∧ U.u.IsDiff (cd v) v'.hom) ∧
      (∀ v (v' : X.Lie) W, Obj.LieCorr R.subtype p v v' → U.u.IsDiff W v'.hom → W = cd v) ∧
      ∀ ω : X₀.Lie →ₗ[R] R, ∃ lam : Fin (Module.finrank ℚ (FR E)) → ℂ, ∀ v, ((ω v : R) : ℂ) = ∑ j, lam j * cd v j := by
  intro E _ _ I _ 𝔠 φ L R X₀ X U p hpull
  obtain ⟨e, he⟩ := GlobalTheory.T.lie_algebra_base_change_iso (R := R) (R' := ℂ) hpull
  obtain ⟨h₁, h₂⟩ := GlobalTheory.TorusTransfer.tangent_bijective U.u X.dim
  obtain ⟨d, hdi, hd⟩ := GlobalTheory.DiagCoord.exists_diff_linear U.u X.rm h₁ h₂
  have hds : Function.Surjective d := fun w => by
    obtain ⟨v, ⟨hv, hw⟩, -⟩ := h₂ w
    exact ⟨GlobalTheory.Serre.Lie.mk X.rm v hv, (h₁ v hv).unique (hd _) hw⟩
  let D : X.Lie ≃ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) := LinearEquiv.ofBijective d ⟨hdi, hds⟩
  let cd : X₀.Lie →ₗ[R] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    ((D.toLinearMap ∘ₗ e.toLinearMap).restrictScalars R) ∘ₗ TensorProduct.mk R ℂ X₀.Lie 1
  have hcd : ∀ v, cd v = d (e (1 ⊗ₜ v)) := fun v => rfl
  refine ⟨cd, fun v => ⟨e (1 ⊗ₜ v), (he v _).2 rfl, by rw [hcd]; exact hd _⟩, fun v v' W hc hW => ?_, fun ω => ?_⟩
  · have h' : v' = e (1 ⊗ₜ v) := (he v v').1 hc
    rw [hcd, ← h']
    exact (h₁ _ v'.isTangent).unique hW (hd v')
  · let ωc : ℂ ⊗[R] X₀.Lie →ₗ[ℂ] ℂ := LinearMap.liftBaseChange ℂ ((Algebra.linearMap R ℂ) ∘ₗ ω)
    let Λ : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] ℂ := ωc ∘ₗ e.symm.toLinearMap ∘ₗ D.symm.toLinearMap
    refine ⟨fun j => Λ (Pi.single j 1), fun v => ?_⟩
    have h1 : ((ω v : R) : ℂ) = Λ (cd v) := by
      simp [Λ, ωc, cd, D]
      rfl
    rw [h1, LinearMap.pi_apply_eq_sum_univ Λ (cd v)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    ext i
    simp [Pi.single_apply, eq_comm]

end GlobalTheory.LieCoord
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_period_coordinates : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)} {φ : I → E →+* ℂ} {L : Set E}
    (R : Subring ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X) (p : X.A.left ⟶ X₀.A.left),
    X.IsPullBy X₀ (spMap R.subtype) p →
    ∃ cd : X₀.Lie →ₗ[R] (Fin (Module.finrank ℚ (FR E)) → ℂ),
      (∀ v, ∃ v' : X.Lie, Obj.LieCorr R.subtype p v v' ∧ U.u.IsDiff (cd v) v'.hom) ∧
      (∀ v (v' : X.Lie) W, Obj.LieCorr R.subtype p v v' → U.u.IsDiff W v'.hom → W = cd v) ∧
      ∀ ω : X₀.Lie →ₗ[R] R, ∃ lam : Fin (Module.finrank ℚ (FR E)) → ℂ, ∀ v, ((ω v : R) : ℂ) = ∑ j, lam j * cd v j := by
  atlas_forward_decl GlobalTheory.LieCoord.exists_lieCoord_unif
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

theorem exists_lie_end_diagonal_of_tensor : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)} {φ : I → E →+* ℂ} {L : Set E}
    (R : Subring ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X) (p : X.A.left ⟶ X₀.A.left)
    (c : Ideal (OF E)) (cm : OAct (orderC c) X₀.A),
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ cd : X₀.Lie →ₗ[R] (Fin (Module.finrank ℚ (FR E)) → ℂ),
      (∀ v, ∃ v' : X.Lie, Obj.LieCorr R.subtype p v v' ∧ U.u.IsDiff (cd v) v'.hom) →
      (∀ v (v' : X.Lie) W, Obj.LieCorr R.subtype p v v' → U.u.IsDiff W v'.hom → W = cd v) →
    ∀ t : orderC c ⊗[ℤ] R, ∃ T : X₀.Lie →ₗ[R] X₀.Lie, ∀ v j, cd (T v) j =
      Algebra.TensorProduct.productMap ((φ (U.e j)).comp (orderC c).subtype).toIntAlgHom
        (algebraMap R ℂ).toIntAlgHom t * cd v j := by
  intro E _ _ I _ 𝔠 φ L R X₀ X U p c cm hcm cd hcd1 hcd2 t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, fun v j ↦ by simp⟩
  | add s t hs ht =>
    obtain ⟨S, hS⟩ := hs
    obtain ⟨T, hT⟩ := ht
    exact ⟨S + T, fun v j ↦ by
      rw [LinearMap.add_apply, map_add, Pi.add_apply, hS, hT, map_add, add_mul]⟩
  | tmul a x =>
    have := cm.hom a
    obtain ⟨α, hα, hp, hex⟩ := hcm a
    refine ⟨x • GlobalTheory.Serre.Lie.map X₀.rm X₀.rm (cm.act a), fun v j ↦ ?_⟩
    obtain ⟨v', hc, hd⟩ := hcd1 v
    let F : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
      LinearMap.pi fun j ↦ φ (U.e j) (a : E) • LinearMap.proj j
    have hd' := GlobalTheory.HomLinear.isDiff_comp U.u U.u α F (fun w ↦ hex w) v'.isTangent hd
    have hc' : Obj.LieCorr R.subtype p (GlobalTheory.Serre.Lie.map X₀.rm X₀.rm (cm.act a) v)
        (GlobalTheory.Serre.Lie.map X.rm X.rm α v') := by
      unfold Obj.LieCorr at hc ⊢
      rw [GlobalTheory.Serre.Lie.hom_map, GlobalTheory.Serre.Lie.hom_map, Over.comp_left, Over.comp_left,
        Category.assoc, hp, ← Category.assoc, hc, Category.assoc]
    have h := congrFun (hcd2 _ _ _ hc' hd') j
    rw [LinearMap.smul_apply, map_smul, Pi.smul_apply, ← h,
      Algebra.TensorProduct.productMap_apply_tmul]
    change (x : ℂ) * (φ (U.e j) (a : E) * cd v j) = φ (U.e j) (a : E) * (x : ℂ) * cd v j
    ring

end GlobalTheory.LatModel
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_order_action_descends : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)} {φ : I → E →+* ℂ} {L : Set E}
    (R : Subring ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X) (p : X.A.left ⟶ X₀.A.left)
    (c : Ideal (OF E)) (cm : OAct (orderC c) X₀.A),
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ cd : X₀.Lie →ₗ[R] (Fin (Module.finrank ℚ (FR E)) → ℂ),
      (∀ v, ∃ v' : X.Lie, Obj.LieCorr R.subtype p v v' ∧ U.u.IsDiff (cd v) v'.hom) →
      (∀ v (v' : X.Lie) W, Obj.LieCorr R.subtype p v v' → U.u.IsDiff W v'.hom → W = cd v) →
    ∀ t : orderC c ⊗[ℤ] R, ∃ T : X₀.Lie →ₗ[R] X₀.Lie, ∀ v j, cd (T v) j =
      Algebra.TensorProduct.productMap ((φ (U.e j)).comp (orderC c).subtype).toIntAlgHom
        (algebraMap R ℂ).toIntAlgHom t * cd v j := by
  atlas_forward_decl GlobalTheory.LatModel.exists_lie_end_diagonal_of_tensor
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LatModel

theorem exists_detGen_wedge_val_le : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
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
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (D : R), D ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ClearsIdem (FractionRing R) (condQ 𝔣 Q) D →
    ∃ (δ₀ : X₀.DetGen) (u₀ : R),
      (Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun k ↦ e (U.e k)) : X₀.DetOmega) = u₀ • δ₀.1 ∧
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) u₀) ≤
        Fintype.card I • GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) D) := by
  classical
  intro _hdR E _ _ _ _ I _ d φ hφ 𝔣 _h𝔣 l _ Q _hQ _hQl y _hy lam 𝔠 R _ _hR X₀ X U p cm hpull _hcm hα j hj φK hφK e a he D hD hcl
  have hinj : Function.Injective φ := by
    intro i i' h
    obtain ⟨k, -, hk⟩ := hφ.2.2.2.2.2.2.1 (φ i)
    exact (hk i (Or.inl rfl)).trans (hk i' (Or.inl h)).symm
  have hKinj : Function.Injective φK := fun i i' h ↦ hinj (by rw [← hφK i, ← hφK i', h])
  obtain ⟨hfree, hfin, hrk⟩ := GlobalTheory.T.lie_algebra_free_rank_degree R X₀
  obtain ⟨cd, hcd1, hcd2, hlam⟩ := GlobalTheory.T.lie_algebra_period_coordinates R X₀ X U p hpull
  choose t ht using fun i ↦ hcl (φK i)
  choose T hT using fun i ↦ GlobalTheory.T.cm_order_action_descends R X₀ X U p (condQ 𝔣 Q) cm hα cd hcd1 hcd2 (t i)
  have hfac : ∀ i k, Algebra.TensorProduct.productMap ((φ (U.e k)).comp (orderC (condQ 𝔣 Q)).subtype).toIntAlgHom
      (algebraMap R ℂ).toIntAlgHom (t i) = if U.e k = i then ((D : R) : ℂ) else 0 := by
    intro i k
    have h2 : ∀ x : orderC (condQ 𝔣 Q) ⊗[ℤ] R, Algebra.TensorProduct.productMap
        ((φ (U.e k)).comp (orderC (condQ 𝔣 Q)).subtype).toIntAlgHom (algebraMap R ℂ).toIntAlgHom x =
        j (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.coordAt R (condQ 𝔣 Q) (φK (U.e k)) x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a x =>
        show φ (U.e k) (a : E) * (x : ℂ) = j (φK (U.e k) (a : E) * algebraMap R (FractionRing R) x)
        rw [map_mul, hj, ← hφK (U.e k)]
        rfl
      | add x z hx hz => rw [map_add, map_add, hx, hz, map_add]
    rw [h2, ht i (φK (U.e k))]
    by_cases h : U.e k = i
    · subst h
      simp [hj]
    · rw [if_neg (fun h' ↦ h (hKinj h')), if_neg h]
      simp
  have hspan : ∀ ω : X₀.Lie →ₗ[R] R, D • ω ∈ Submodule.span R (Set.range fun k ↦ e (U.e k)) := by
    intro ω
    obtain ⟨lm, hlm⟩ := hlam ω
    have hval : ∀ i v, (((ω ∘ₗ T i) v : R) : ℂ) =
        ∑ k, lm k * ((if U.e k = i then ((D : R) : ℂ) else 0) * cd v k) := by
      intro i v
      rw [LinearMap.comp_apply, hlm]
      simp_rw [hT i v, hfac i]
    have hg : ∀ i, ∃ s : R, ω ∘ₗ T i = s • e i := by
      intro i
      refine (he i).2.2 _ ((D : ℂ) * lm (U.e.symm i)) ?_
      intro v v' W hv hW
      rw [hcd2 v v' W hv hW, hval i v, Finset.sum_eq_single (U.e.symm i)]
      · simp only [Equiv.apply_symm_apply, if_true]
        ring
      · intro k _ hk
        rw [if_neg (fun (h : U.e k = i) ↦ hk (by rw [← h, Equiv.symm_apply_apply]))]
        simp
      · intro h
        exact absurd (Finset.mem_univ _) h
    choose s hs using hg
    have heq : D • ω = ∑ i, s i • e i := by
      ext v
      rw [LinearMap.smul_apply, LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum]
      have key : ∀ i, (((s i • e i) v : R) : ℂ) =
          ∑ k, lm k * ((if U.e k = i then ((D : R) : ℂ) else 0) * cd v k) := by
        intro i
        rw [← hs i, hval]
      simp_rw [key]
      rw [Finset.sum_comm]
      simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [smul_eq_mul, Subring.coe_mul, hlm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      ring
    rw [heq]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨U.e.symm i, by simp⟩)
  haveI := hfree
  haveI := hfin
  obtain ⟨δ₀, u₀, hδ, hu, hv⟩ := GlobalTheory.T.exists_generator_top_exterior_power R X₀.Lie _ hrk (fun k ↦ e (U.e k)) D hD hspan l
  refine ⟨⟨δ₀, hδ⟩, u₀, hu, ?_⟩
  have hc : Fintype.card I = Module.finrank ℚ (FR E) := by
    rw [← Fintype.card_congr U.e, Fintype.card_fin]
  rw [hc]
  exact hv

end GlobalTheory.LatModel
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_over_l_idele_character_value : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
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
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (D : R), D ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ClearsIdem (FractionRing R) (condQ 𝔣 Q) D →
    ∃ (δ₀ : X₀.DetGen) (u₀ : R),
      (Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun k ↦ e (U.e k)) : X₀.DetOmega) = u₀ • δ₀.1 ∧
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) u₀) ≤
        Fintype.card I • GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) D) := by
  atlas_forward_decl GlobalTheory.LatModel.exists_detGen_wedge_val_le
end
