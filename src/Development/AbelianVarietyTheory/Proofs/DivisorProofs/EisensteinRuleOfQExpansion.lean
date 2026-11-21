import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRenumber

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

def permCLE (σ : Equiv.Perm (Fin g)) : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ σ).toContinuousLinearEquiv

@[simp] theorem permCLE_apply (σ : Equiv.Perm (Fin g)) (w : Fin g → ℂ) : permCLE σ w = w ∘ σ := rfl

def pre (u : HolUnif A L g) (T : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) : HolUnif A L g where
  ex z := u.ex (T z)
  ex_add z w := by rw [map_add, u.ex_add]
  ex_onto y := by
    obtain ⟨x, rfl⟩ := u.ex_onto y
    exact ⟨T.symm x, by simp⟩
  Λ := u.Λ.comap (((T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).restrictScalars ℤ)
  ker z := by rw [u.ker]; rfl
  discrete := by
    haveI := u.discrete
    exact DiscreteTopology.of_continuous_injective
      (f := fun x : u.Λ.comap (((T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).restrictScalars ℤ)
        ↦ (⟨T x, x.2⟩ : u.Λ))
      (by fun_prop) (fun x y h ↦ Subtype.ext (T.injective (congrArg Subtype.val h)))
  full := by
    have h1 : ((u.Λ.comap (((T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).restrictScalars ℤ) :
        Submodule ℤ (Fin g → ℂ)) : Set (Fin g → ℂ)) =
        (T.symm.toLinearEquiv.restrictScalars ℝ : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) '' (u.Λ : Set (Fin g → ℂ)) := by
      ext x
      simp only [SetLike.mem_coe, Submodule.mem_comap, Set.mem_image]
      constructor
      · intro hx; exact ⟨T x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩; simpa using hy
    rw [h1, Submodule.span_image, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact (T.symm.toLinearEquiv.restrictScalars ℝ).surjective
  hol U f := ⟨(u.hol U f).1.preimage T.continuous,
    (u.hol U f).2.comp T.differentiableOn (fun _ hz ↦ hz)⟩
  fr i z := u.fr i (T z)
  fr_hol i := (u.fr_hol i).comp T.differentiableOn (fun _ hz ↦ hz)
  fr_ne i z h := u.fr_ne i (T z) h
  fr_compat i j z h := u.fr_compat i j (T z) h

theorem pre_isDiff (u : HolUnif A L g) (T : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) (w : Fin g → ℂ)
    (v : epsR ℂ ⟶ A) : (pre u T).IsDiff w v ↔ u.IsDiff (T w) v := by
  have key : ∀ (U : A.left.Opens) (f : Γ(A.left, U)),
      fderiv ℂ (fun z ↦ valAt' ((pre u T).ex z).left U f) 0 w =
        fderiv ℂ (fun z ↦ valAt' (u.ex z).left U f) 0 (T w) := by
    intro U f
    have : (fun z ↦ valAt' ((pre u T).ex z).left U f) = (fun z ↦ valAt' (u.ex z).left U f) ∘ T := rfl
    rw [this, ContinuousLinearEquiv.comp_right_fderiv, map_zero]
    rfl
  unfold HolUnif.IsDiff
  simp only [key]

end GlobalTheory.TorusRenumber

namespace GlobalTheory.TorusRenumber

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem pre_isAH (u : HolUnif A L g) (T : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ))
    (Hm Hm' : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (h : u.IsAH Hm χ) (hH : Hm'.IsHermitian)
    (hT : ∀ z l, T z ⬝ᵥ Hm.mulVec (star (T l)) = z ⬝ᵥ Hm'.mulVec (star l)) :
    (pre u T).IsAH Hm' (fun l ↦ χ ⟨T l, l.2⟩) := by
  obtain ⟨-, hpos, hχ, hfr⟩ := h
  refine ⟨hH, fun z hz ↦ ?_, fun l ↦ hχ _, fun l i z hz ↦ ?_⟩
  · rw [← hT]
    exact hpos _ (fun h0 ↦ hz (T.injective (by rw [h0, map_zero])))
  · have := hfr ⟨T l, l.2⟩ i (T z) hz
    change u.fr i (T z) = _ * _ * u.fr i (T (z + l))
    rw [this, hT, hT, map_add]

theorem perm_dot_diagonal (σ : Equiv.Perm (Fin g)) (d : Fin g → ℂ) (z l : Fin g → ℂ) :
    permCLE σ z ⬝ᵥ (Matrix.diagonal d).mulVec (star (permCLE σ l)) =
      z ⬝ᵥ (Matrix.diagonal (d ∘ σ.symm)).mulVec (star l) := by
  simp only [permCLE_apply, Matrix.mulVec_diagonal, dotProduct, Function.comp_apply, Pi.star_apply]
  exact Equiv.sum_comp σ (fun i ↦ z i * (d (σ.symm i) * star (l i))) |>.symm.trans (by simp) |>.symm

end GlobalTheory.TorusRenumber

namespace GlobalTheory.TorusRenumber

theorem isTorusPoint_perm  (F : Type) [Field F] [NumberField F] (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ))
    (π : Equiv.Perm (Fin (Module.finrank ℚ F))) (𝔞 𝔟 : FracId F) (z : (F →+* ℝ) → ℂ)
    (X : Obj F (𝔞 * 𝔟⁻¹) (Sp ℂ)) (δ : X.DetOmega)
    (h : IsTorusPoint e 𝔞 𝔟 z X δ) :
      IsTorusPoint (π.trans e) 𝔞 𝔟 z X ((((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℂ) • δ) := by
  obtain ⟨c, u, hc, hlat, hact, ⟨χ, hAH⟩, hdet⟩ := h
  set T := permCLE π.symm with hTdef
  refine ⟨c, pre u T, hc, ?_, ?_, ⟨_, pre_isAH u T _ _ χ hAH ?_ ?_⟩, ?_⟩
  · intro w
    change T w ∈ u.Λ ↔ _
    rw [hlat]
    simp only [hTdef, permCLE_apply, Equiv.trans_apply]
    constructor
    · rintro ⟨m, hm, β, hβ, hw⟩
      refine ⟨m, hm, β, hβ, funext fun i ↦ ?_⟩
      simpa using congrFun hw (π i)
    · rintro ⟨m, hm, β, hβ, rfl⟩
      exact ⟨m, hm, β, hβ, funext fun i ↦ by simp⟩
  · intro a w
    change u.ex (T _) = u.ex (T w) ≫ _
    rw [← hact a (T w)]
    congr 1
    funext j
    simp [hTdef]
  · rw [show (Matrix.diagonal fun i ↦ ((2 * (π.trans e) i (c : F) / (4 * Real.pi ^ 2 * (z ((π.trans e) i)).im) : ℝ) : ℂ)) =
      (Matrix.diagonal fun i ↦ ((2 * e i (c : F) / (4 * Real.pi ^ 2 * (z (e i)).im) : ℝ) : ℂ)).submatrix π π by
        rw [Matrix.submatrix_diagonal_equiv]; rfl]
    exact hAH.1.submatrix π
  · intro w l
    rw [hTdef, perm_dot_diagonal]
    rfl
  · intro v W' hW'
    have hW : ∀ i, u.IsDiff ((W'.submatrix id π.symm) i) (v i).hom := fun i ↦ by
      exact (pre_isDiff u T (W' i) (v i).hom).1 (hW' i)
    rw [AlternatingMap.smul_apply, hdet v _ hW, Matrix.det_permute', Equiv.Perm.sign_symm, smul_eq_mul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs <;> simp [hs]

end GlobalTheory.TorusRenumber
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_point_permutation_sign : ∀ (F : Type) [Field F] [NumberField F] (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ))
    (π : Equiv.Perm (Fin (Module.finrank ℚ F))) (𝔞 𝔟 : FracId F) (z : (F →+* ℝ) → ℂ)
    (X : Obj F (𝔞 * 𝔟⁻¹) (Sp ℂ)) (δ : X.DetOmega),
    IsTorusPoint e 𝔞 𝔟 z X δ → IsTorusPoint (π.trans e) 𝔞 𝔟 z X ((((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℂ) • δ) := by
  atlas_forward_decl GlobalTheory.TorusRenumber.isTorusPoint_perm
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet

open ReciprocityTheory.ChartRestriction.G.Chart (isTan_iff) in

theorem detGen_apply_ne_zero_of_isDiff : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left)
    (u : HolUnif X.A L (Module.finrank ℚ F)) (δ : X.DetGen) (v : Fin (Module.finrank ℚ F) → X.Lie)
    (W : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ),
    (∀ j, u.IsDiff (W j) (v j).hom) → W.det ≠ 0 → δ.1 v ≠ 0 := by
  intro F _ _ 𝔠 X L u δ v W hW hdet
  obtain ⟨h1, h2⟩ := GlobalTheory.TorusTransfer.tangent_bijective u X.dim
  have hsm : Smooth X.A.hom := by
    haveI := X.dim
    exact SmoothOfRelativeDimension.smooth (Module.finrank ℚ F) X.A.hom
  obtain ⟨v₀, hv₀, -⟩ := GlobalTheory.exists_lieBasis_of_holUnif X.A L _ u hsm h1 h2
  let b := Serre.Lie.basis X.rm hv₀
  have hsmul : ∀ (c : ℂ) (w : Fin (Module.finrank ℚ F) → ℂ) (x : X.Lie), u.IsDiff w x.hom →
      u.IsDiff (c • w) (c • x).hom := by
    intro c w x h
    have := GlobalTheory.UnifLieBasis.isDiff_smul u ((isTan_iff _).2 x.isTangent) h c
    convert this using 1
    rfl
  have hsum : ∀ a : Fin (Module.finrank ℚ F) → ℂ, u.IsDiff (∑ j, a j • W j) (∑ j, a j • v j).hom := by
    intro a
    rw [Serre.Lie.hom_sum, ← List.prod_ofFn]
    exact (GlobalTheory.UnifLieBasis.isDiff_list_prod u _ _ (fun j ↦ (isTan_iff _).2 (a j • v j).isTangent)
      (fun j ↦ hsmul _ _ _ (hW j))).2
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have h0 := hsum a
    rw [ha] at h0
    have hz : u.IsDiff 0 (0 : X.Lie).hom := by
      rw [Serre.Lie.hom_zero]
      exact GlobalTheory.UnifLieBasis.isDiff_zero u
    have heq : ∑ j, a j • W j = 0 := (h1 _ (0 : X.Lie).isTangent).unique h0 hz
    rw [← Matrix.vecMul_eq_sum] at heq
    by_contra hne
    push_neg at hne
    obtain ⟨i, hi⟩ := hne
    exact hdet (Matrix.exists_vecMul_eq_zero_iff.1 ⟨a, fun h ↦ hi (by rw [h]; rfl), heq⟩)
  haveI : Nonempty (Fin (Module.finrank ℚ F)) := Fin.pos_iff_nonempty.1 Module.finrank_pos
  let B := basisOfLinearIndependentOfCardEqFinrank hli
    (by rw [Fintype.card_fin, Module.finrank_eq_card_basis b, Fintype.card_fin])
  have hB : (B : Fin (Module.finrank ℚ F) → X.Lie) = v := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hmem : B.det ∈ Submodule.span ℂ {δ.1} := by rw [δ.2]; exact Submodule.mem_top
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hmem
  intro h0
  have h1' := B.det_self
  rw [← ht, hB, AlternatingMap.smul_apply, h0, smul_zero] at h1'
  exact zero_ne_one h1'

end GlobalTheory.LatJet
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_nonzero_differentials : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left)
    (u : HolUnif X.A L (Module.finrank ℚ F)) (δ : X.DetGen) (v : Fin (Module.finrank ℚ F) → X.Lie)
    (W : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ),
    (∀ j, u.IsDiff (W j) (v j).hom) → W.det ≠ 0 → δ.1 v ≠ 0 := by
  atlas_forward_decl GlobalTheory.LatJet.detGen_apply_ne_zero_of_isDiff
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatSumCmp

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem defCoord_sub (φ : I → E →+* ℂ) (z : I → ℂ) (x x' : E) (i : I) :
    defCoord φ z (x - x') i = defCoord φ z x i - defCoord φ z x' i := by
  simp only [defCoord, map_sub]; ring

theorem defCoord_zero (φ : I → E →+* ℂ) (z : I → ℂ) (i : I) : defCoord φ z 0 i = 0 := by
  simp [defCoord]

theorem defCoord_ne_zero (φ : I → E →+* ℂ) (z : I → ℂ) (hz : z ∈ polydisc I) (x : E) (hx : x ≠ 0) (i : I) :
    defCoord φ z x i ≠ 0 := by
  intro h
  have h0 : φ i x ≠ 0 := by simpa using hx
  have h1 : φ i x = -(z i * starRingEnd ℂ (φ i x)) := eq_neg_of_add_eq_zero_left h
  have h2 : ‖φ i x‖ = ‖z i‖ * ‖φ i x‖ := by
    conv_lhs => rw [h1]
    simp
  have h3 : 0 < ‖φ i x‖ := norm_pos_iff.2 h0
  have h4 := hz i
  nlinarith

theorem defCoord_mul (φ : I → E →+* ℂ) (z : I → ℂ) (a x : E) (i : I) (ha : starRingEnd ℂ (φ i a) = φ i a) :
    defCoord φ z (a * x) i = φ i a * defCoord φ z x i := by
  simp only [defCoord, map_mul, ha]; ring

theorem prod_cpow_ofReal {J : Type} (s : Finset J) (f : J → ℝ) (hf : ∀ i, 0 ≤ f i) (r : ℂ) :
    ∏ i ∈ s, ((f i : ℝ) : ℂ) ^ r = (((∏ i ∈ s, f i : ℝ)) : ℂ) ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun i _ => hf i)]

theorem defTerm_eq (φ : I → E →+* ℂ) (k : ℕ) (z : I → ℂ) (σ : ℂ) (x : E) :
    GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defTerm φ k z σ x =
      (∏ i, defCoord φ z x i)⁻¹ ^ k * ((‖∏ i, defCoord φ z x i‖ : ℝ) : ℂ) ^ (-2 * σ) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defTerm
  rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib, norm_prod,
    prod_cpow_ofReal _ _ (fun _ => norm_nonneg _)]

theorem lattice_unit_mul (c : Ideal (OF E)) (y : (Af E)ˣ) (u : (OF E)ˣ) (x : E) (hx : x ∈ lattice c y) :
    algebraMap (OF E) E (u : OF E) * x ∈ lattice c y := by
  unfold lattice at hx ⊢
  simp only [Set.mem_setOf_eq] at hx ⊢
  rw [map_mul, _root_.mul_assoc]
  refine Subring.mul_mem _ ?_ hx
  apply Subring.le_topologicalClosure
  refine Subring.mem_map.2 ⟨_, ?_, rfl⟩
  exact Subring.subset_closure (Or.inl ⟨(u : OF E), rfl⟩)

end GlobalTheory.LatSumCmp

namespace GlobalTheory.LatSumCmp

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (LatPair latRel eisClass eisTerm latPt latM_eq_dual eisClass_mk latPt_ne_zero)

section Pairs

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def vPt (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)) (τ : (FR E →+* ℝ) → ℂ)
    (lam : Fin (Module.finrank ℚ (FR E)) → ℂ) (p : FR E × FR E) : Fin (Module.finrank ℚ (FR E)) → ℂ :=
  fun j ↦ lam j * (2 * Real.pi * Complex.I * ((e j p.1 : ℂ) + (e j p.2 : ℂ) * τ (e j)))

def wPt (φ : I → E →+* ℂ) (z : I → ℂ) (ue : Fin (Module.finrank ℚ (FR E)) ≃ I) (x : E) :
    Fin (Module.finrank ℚ (FR E)) → ℂ :=
  fun j ↦ defCoord φ z x (ue j)

theorem vPt_apply (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)) (τ : (FR E →+* ℝ) → ℂ)
    (lam : Fin (Module.finrank ℚ (FR E)) → ℂ) (p : FR E × FR E) (j : Fin (Module.finrank ℚ (FR E))) :
    vPt e τ lam p j = lam j * latPt τ p (e j) := rfl

theorem vPt_inj (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)) (τ : (FR E →+* ℝ) → ℂ)
    (lam : Fin (Module.finrank ℚ (FR E)) → ℂ) (hτ : τ ∈ halfSpace (FR E)) (hlam : ∀ j, lam j ≠ 0)
    {p p' : FR E × FR E} (h : vPt e τ lam p = vPt e τ lam p') : p = p' := by
  have j0 : Fin (Module.finrank ℚ (FR E)) := ⟨0, Module.finrank_pos⟩
  have h1 := congrFun h j0
  simp only [vPt] at h1
  have h2 := mul_left_cancel₀ (hlam j0) h1
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  have h3 := mul_left_cancel₀ hc h2
  have him := congrArg Complex.im h3
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_mul, zero_add, add_zero] at him
  have hb : e j0 p.2 = e j0 p'.2 := mul_right_cancel₀ (hτ (e j0)).ne' him
  have hb' : p.2 = p'.2 := (e j0).injective hb
  rw [hb'] at h3
  have ha : ((e j0 p.1 : ℝ) : ℂ) = e j0 p'.1 := add_right_cancel h3
  have ha' : p.1 = p'.1 := (e j0).injective (by exact_mod_cast ha)
  exact Prod.ext ha' hb'

theorem vPt_unit (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)) (τ : (FR E →+* ℝ) → ℂ)
    (lam : Fin (Module.finrank ℚ (FR E)) → ℂ) (a : FR E) (p : FR E × FR E) :
    vPt e τ lam (a * p.1, a * p.2) = fun j ↦ (e j a : ℂ) * vPt e τ lam p j := by
  funext j
  simp only [vPt, map_mul, Complex.ofReal_mul]; ring

theorem wPt_unit (φ : I → E →+* ℂ) (z : I → ℂ) (ue : Fin (Module.finrank ℚ (FR E)) ≃ I)
    (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)) (he : ∀ j (x : FR E), (e j x : ℂ) = φ (ue j) (x : E))
    (a : FR E) (x : E) : wPt φ z ue ((a : E) * x) = fun j ↦ (e j a : ℂ) * wPt φ z ue x j := by
  funext j
  simp only [wPt]
  rw [defCoord_mul φ z (a : E) x (ue j) (by rw [← he]; exact Complex.conj_ofReal _), he]

end Pairs

end GlobalTheory.LatSumCmp

namespace GlobalTheory.LatSumCmp

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (LatPair latRel eisClass eisTerm latPt latM_eq_dual eisClass_mk latPt_ne_zero)

section Equiv

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem out_spec {L : Set E} (q : modUnits L) : ∃ u : (OF E)ˣ, ∃ x ∈ L, x ≠ 0 ∧
    q.1.out = algebraMap (OF E) E (u : OF E) * x := by
  obtain ⟨x, hx, hx0, hq⟩ := q.2
  obtain ⟨u, hu⟩ : (unitRel (E := E)).r x q.1.out :=
    Quotient.exact (show Quotient.mk unitRel x = Quotient.mk unitRel q.1.out by rw [Quotient.out_eq, hq])
  exact ⟨u, x, hx, hx0, hu⟩

theorem out_mem {L : Set E} (hLu : ∀ u : (OF E)ˣ, ∀ x ∈ L, algebraMap (OF E) E (u : OF E) * x ∈ L)
    (q : modUnits L) : q.1.out ∈ L ∧ q.1.out ≠ 0 := by
  obtain ⟨u, x, hx, hx0, hq⟩ := out_spec q
  rw [hq]
  exact ⟨hLu u x hx, mul_ne_zero ((u.isUnit.map (algebraMap (OF E) E)).ne_zero) hx0⟩

theorem exists_equiv (φ : I → E →+* ℂ) (z : I → ℂ) (hz : z ∈ polydisc I) (ue : Fin (Module.finrank ℚ (FR E)) ≃ I)
    (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)) (he : ∀ j (x : FR E), (e j x : ℂ) = φ (ue j) (x : E))
    (τ : (FR E →+* ℝ) → ℂ) (hτ : τ ∈ halfSpace (FR E)) (lam : Fin (Module.finrank ℚ (FR E)) → ℂ)
    (hlam : ∀ j, lam j ≠ 0) (𝔞 𝔟 : FracId (FR E)) (L : Set E)
    (hLu : ∀ u : (OF E)ˣ, ∀ x ∈ L, algebraMap (OF E) E (u : OF E) * x ∈ L)
    (hL : ∀ w, (∃ x ∈ L, w = wPt φ z ue x) ↔ ∃ m ∈ dualLat 𝔞, ∃ β ∈ 𝔟.elt, w = vPt e τ lam (m, β)) :
    ∃ ψ : modUnits L ≃ Quotient (latRel 𝔞 𝔟), ∀ q, ∃ p : LatPair 𝔞 𝔟, ψ q = Quotient.mk _ p ∧
      wPt φ z ue q.1.out = vPt e τ lam p.1 := by
  classical
  have j0 : Fin (Module.finrank ℚ (FR E)) := ⟨0, Module.finrank_pos⟩
  have hpair : ∀ x ∈ L, x ≠ 0 → ∃ p : LatPair 𝔞 𝔟, wPt φ z ue x = vPt e τ lam p.1 := by
    intro x hx hx0
    obtain ⟨m, hm, β, hβ, h⟩ := (hL _).1 ⟨x, hx, rfl⟩
    refine ⟨⟨(m, β), by rw [latM_eq_dual]; exact hm, hβ, ?_⟩, h⟩
    intro h0
    apply defCoord_ne_zero φ z hz x hx0 (ue j0)
    have := congrFun h j0
    rw [h0] at this
    simpa [vPt, wPt] using this
  choose pr hpr using fun q : modUnits L => hpair q.1.out (out_mem hLu q).1 (out_mem hLu q).2
  let ψ : modUnits L → Quotient (latRel 𝔞 𝔟) := fun q => Quotient.mk _ (pr q)
  have hinj : Function.Injective ψ := by
    intro q1 q2 h
    obtain ⟨ε, h1, h2⟩ := Quotient.exact h
    have key : wPt φ z ue q2.1.out = wPt φ z ue ((((ε : 𝓞 (FR E)) : FR E) : E) * q1.1.out) := by
      rw [hpr q2, show (pr q2).1 = (_ * (pr q1).1.1, _ * (pr q1).1.2) from Prod.ext h1 h2, vPt_unit,
        wPt_unit φ z ue e he, hpr q1]
    have hx : q2.1.out = (((ε : 𝓞 (FR E)) : FR E) : E) * q1.1.out := by
      by_contra hne
      apply defCoord_ne_zero φ z hz _ (sub_ne_zero.2 hne) (ue j0)
      rw [defCoord_sub]; exact sub_eq_zero.2 (congrFun key j0)
    apply Subtype.ext
    rw [← Quotient.out_eq q1.1, ← Quotient.out_eq q2.1]
    exact Quotient.sound ⟨ε, hx⟩
  have hsurj : Function.Surjective ψ := by
    intro cl
    obtain ⟨p, rfl⟩ := Quotient.exists_rep cl
    have hm : p.1.1 ∈ dualLat 𝔞 := by
      have h0 : ∀ a : FR E, a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 → a ∈ dualLat 𝔞 := fun a ha => by
        rw [latM_eq_dual] at ha; exact ha
      exact h0 _ p.2.1
    obtain ⟨x, hx, hxw⟩ := (hL (vPt e τ lam p.1)).2 ⟨p.1.1, hm, p.1.2, p.2.2.1, rfl⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      have := congrFun hxw j0
      simp only [vPt_apply, wPt, defCoord_zero] at this
      exact mul_ne_zero (hlam j0) (latPt_ne_zero hτ p.2.2.2 (e j0)) this
    let q : modUnits L := ⟨Quotient.mk _ x, x, hx, hx0, rfl⟩
    refine ⟨q, ?_⟩
    obtain ⟨u, hu⟩ : (unitRel (E := E)).r x q.1.out := Quotient.exact (Quotient.out_eq q.1).symm
    have hcoe : algebraMap (OF E) E (u : OF E) = (((u : OF E) : FR E) : E) := rfl
    have key : vPt e τ lam (pr q).1 = vPt e τ lam (((u : OF E) : FR E) * p.1.1, ((u : OF E) : FR E) * p.1.2) := by
      rw [← hpr q, vPt_unit, hu, hcoe, wPt_unit φ z ue e he, ← hxw]
    have := vPt_inj e τ lam hτ hlam key
    show Quotient.mk _ (pr q) = Quotient.mk _ p
    exact (Quotient.sound (show (latRel 𝔞 𝔟).r p (pr q) from ⟨u, congrArg Prod.fst this, congrArg Prod.snd this⟩)).symm
  exact ⟨Equiv.ofBijective ψ ⟨hinj, hsurj⟩, fun q => ⟨pr q, rfl, hpr q⟩⟩

theorem defTerm_pair (φ : I → E →+* ℂ) (z : I → ℂ) (ue : Fin (Module.finrank ℚ (FR E)) ≃ I)
    (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)) (τ : (FR E →+* ℝ) → ℂ)
    (lam : Fin (Module.finrank ℚ (FR E)) → ℂ) (x : E) (p : FR E × FR E)
    (hW : wPt φ z ue x = vPt e τ lam p) (k : ℕ) (σ : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defTerm φ k z σ x =
      ((∏ j, lam j)⁻¹ ^ k * ((‖∏ j, lam j‖ : ℝ) : ℂ) ^ (-2 * σ)) * eisTerm k σ τ p := by
  rw [defTerm_eq]
  have hP : ∏ i, defCoord φ z x i = (∏ j, lam j) * ∏ t, latPt τ p t := by
    rw [← Equiv.prod_comp ue (fun i => defCoord φ z x i), ← Equiv.prod_comp e (fun t => latPt τ p t),
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => congrFun hW j
  rw [hP]
  unfold eisTerm
  rw [_root_.mul_inv, _root_.mul_pow, norm_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  ring

end Equiv

end GlobalTheory.LatSumCmp

namespace GlobalTheory.LatSumCmp

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (LatPair latRel eisClass eisTerm latPt eisClass_mk)

theorem defSum_eq_eis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (𝔞 𝔟 : FracId (FR E))
    (φ : I → E →+* ℂ) (c : Ideal (OF E)) (y : (Af E)ˣ), IsCMType φ → c ≠ ⊥ → ∀ s : ℕ, 1 ≤ s →
    ∀ z ∈ polydisc I, ∀ (ue : Fin (Module.finrank ℚ (FR E)) ≃ I) (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ))
      (τ : (FR E →+* ℝ) → ℂ) (lam : Fin (Module.finrank ℚ (FR E)) → ℂ),
      (∀ j (x : FR E), (e j x : ℂ) = φ (ue j) (x : E)) → τ ∈ halfSpace (FR E) → (∀ j, lam j ≠ 0) →
      (∀ w : Fin (Module.finrank ℚ (FR E)) → ℂ, (∃ x ∈ lattice c y, w = fun j ↦ defCoord φ z x (ue j)) ↔
        ∃ m ∈ dualLat 𝔞, ∃ β ∈ 𝔟.elt,
          w = fun j ↦ lam j * (2 * Real.pi * Complex.I * ((e j m : ℂ) + (e j β : ℂ) * τ (e j)))) →
      ∀ G, IsEis 𝔞 𝔟 (2 * s) G → ∀ g, IsDefSum φ (2 * s) (lattice c y) g →
        g z = (cWt E (2 * s) : ℂ) * ((∏ j, lam j)⁻¹) ^ (2 * s) * G τ := by
  intro E _ _ _ I _ 𝔞 𝔟 φ c y _ _ s hs z hz ue e τ lam he hτ hlam hL G hG g hg
  classical
  obtain ⟨ψ, hψ⟩ := exists_equiv φ z hz ue e he τ hτ lam hlam 𝔞 𝔟 (lattice c y)
    (fun u x hx => lattice_unit_mul c y u x hx) hL
  set A : ℂ → ℂ := fun σ => (∏ j, lam j)⁻¹ ^ (2 * s) * ((‖∏ j, lam j‖ : ℝ) : ℂ) ^ (-2 * σ) with hA
  have hterm : ∀ (σ : ℂ) (q : modUnits (lattice c y)),
      GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defTerm φ (2 * s) z σ q.1.out = A σ * eisClass 𝔞 𝔟 (2 * s) σ τ (ψ q) := by
    intro σ q
    obtain ⟨p, hp, hW⟩ := hψ q
    rw [hp, eisClass_mk 𝔞 𝔟 (even_two_mul s), defTerm_pair φ z ue e τ lam _ _ hW]
  have hsum : ∀ σ : ℂ, ∀ S, HasSum (eisClass 𝔞 𝔟 (2 * s) σ τ) S →
      HasSum (fun q : modUnits (lattice c y) => GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defTerm φ (2 * s) z σ q.1.out) (A σ * S) := by
    intro σ S h
    simp only [hterm]
    exact ((Equiv.hasSum_iff ψ).2 h).mul_left (A σ)
  have hA0 : A 0 = (∏ j, lam j)⁻¹ ^ (2 * s) := by simp [hA]
  obtain ⟨G', hG', hgz⟩ := hg z hz
  suffices hG'eq : G' = A 0 * G τ by rw [hgz, hG'eq, hA0]; ring
  rcases eq_or_ne s 1 with rfl | hs1
  · obtain ⟨H', hH'd, hH's, rfl⟩ := hG'.2 (by norm_num)
    obtain ⟨H, hH, rfl⟩ := hG.2 (by norm_num)
    have hτ' : τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf (FR E) := hτ
    have hkey : ∀ σ : ℂ, 0 < σ.re → H' σ = A σ * H σ τ := by
      intro σ hσ
      obtain ⟨hsm, hHe⟩ := hH.1 σ hσ τ hτ'
      have h1 : HasSum (eisClass 𝔞 𝔟 2 σ τ) (H σ τ) := by rw [hHe]; exact hsm.hasSum
      exact (hH's σ hσ).unique (hsum σ _ h1)
    let U : Set ℂ := {σ | -1 / 2 < σ.re}
    have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hUc : IsPreconnected U := (convex_halfSpace_re_gt (-1 / 2)).isPreconnected
    have hf : AnalyticOnNhd ℂ H' U := hH'd.analyticOnNhd hUo
    have hn : ((‖∏ j, lam j‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 fun j _ => hlam j))
    have hAd : Differentiable ℂ A := fun σ =>
      (differentiableAt_const _).mul (((differentiableAt_const (-2 : ℂ)).mul differentiableAt_id).const_cpow (Or.inl hn))
    have hHd : DifferentiableOn ℂ (fun σ => H σ τ) U := hH.2.2 [] τ hτ'
    have hg' : AnalyticOnNhd ℂ (fun σ => A σ * H σ τ) U := (hAd.differentiableOn.mul hHd).analyticOnNhd hUo
    have hev : H' =ᶠ[nhds 1] (fun σ => A σ * H σ τ) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (0 : ℝ) < (1 : ℂ).re by simp)] with σ hσ
      exact hkey σ hσ
    exact hf.eqOn_of_preconnected_of_eventuallyEq hg' hUc (show (-1 / 2 : ℝ) < (1 : ℂ).re by norm_num) hev
      (show (-1 / 2 : ℝ) < (0 : ℂ).re by norm_num)
  · have hk : 2 * s ≠ 2 := by omega
    have h2 := hsum 0 _ (hG.1 hk τ hτ)
    have hd : ∀ x : E, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defTerm φ (2 * s) z 0 x = ∏ i, (defCoord φ z x i)⁻¹ ^ (2 * s) := by
      intro x; simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defTerm]
    simp only [hd] at h2
    exact (hG'.1 hk).unique h2

end GlobalTheory.LatSumCmp
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polydisc_cm_uniformization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (𝔞 𝔟 : FracId (FR E))
    (φ : I → E →+* ℂ) (c : Ideal (OF E)) (y : (Af E)ˣ), IsCMType φ → c ≠ ⊥ → ∀ s : ℕ, 1 ≤ s →
    ∀ z ∈ polydisc I, ∀ (ue : Fin (Module.finrank ℚ (FR E)) ≃ I) (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ))
      (τ : (FR E →+* ℝ) → ℂ) (lam : Fin (Module.finrank ℚ (FR E)) → ℂ),
      (∀ j (x : FR E), (e j x : ℂ) = φ (ue j) (x : E)) → τ ∈ halfSpace (FR E) → (∀ j, lam j ≠ 0) →
      (∀ w : Fin (Module.finrank ℚ (FR E)) → ℂ, (∃ x ∈ lattice c y, w = fun j ↦ defCoord φ z x (ue j)) ↔
        ∃ m ∈ dualLat 𝔞, ∃ β ∈ 𝔟.elt,
          w = fun j ↦ lam j * (2 * Real.pi * Complex.I * ((e j m : ℂ) + (e j β : ℂ) * τ (e j)))) →
      ∀ G, IsEis 𝔞 𝔟 (2 * s) G → ∀ g, IsDefSum φ (2 * s) (lattice c y) g →
        g z = (cWt E (2 * s) : ℂ) * ((∏ j, lam j)⁻¹) ^ (2 * s) * G τ := by
  atlas_forward_decl GlobalTheory.LatSumCmp.defSum_eq_eis
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EisRuleProof

theorem card_emb (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by
  rw [← NumberField.Embeddings.card F ℂ]
  refine Fintype.card_of_bijective (f := fun τ : F →+* ℝ ↦ (Complex.ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩
  · intro τ τ' hτ
    ext y
    have := DFunLike.congr_fun hτ y
    simpa using this
  · intro φ
    have hr : NumberField.ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
    exact ⟨hr.embedding, by ext y; simp⟩

theorem isHolForm_mul {F : Type} [Field F] [NumberField F] {𝔞 𝔟 : FracId F} {k : ℕ}
    {g : ((F →+* ℝ) → ℂ) → ℂ} (h : IsHolForm 𝔞 𝔟 k g) (K : ℂ) : IsHolForm 𝔞 𝔟 k (fun z ↦ K * g z) := by
  refine ⟨h.1.const_mul K, fun a b c d hm z hz ↦ ?_⟩
  simp only
  rw [h.2 a b c d hm z hz]; ring

theorem dF_pos (F : Type) [Field F] [NumberField F] : (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF
  exact abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F)

theorem omegaFactor_ne_zero {F : Type} [Field F] [NumberField F] (𝔞 : FracId F) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ≠ 0 := by
  have hn : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔞 ≠ 0 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm
    exact_mod_cast mt FractionalIdeal.absNorm_eq_zero_iff.1 𝔞.ne_zero
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor
  exact_mod_cast mul_ne_zero (Real.rpow_pos_of_pos (dF_pos F) _).ne' hn

theorem cK_ne_zero (F : Type) [Field F] [NumberField F] (k : ℕ) : (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) ≠ 0 := by
  have : (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK
    exact mul_pos (pow_pos (Nat.cast_pos.2 (Nat.factorial_pos _)) _) (Real.rpow_pos_of_pos (dF_pos F) _)
  exact_mod_cast this.ne'

def smulGen {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {X : Obj F 𝔠 (Sp ℂ)} (δ : X.DetGen) (c : ℂ)
    (hc : c ≠ 0) : X.DetGen :=
  ⟨c • δ.1, by rw [Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]; exact δ.2⟩

theorem sign_pow_even (x : ℤˣ) (s : ℕ) : ((x : ℤ) : ℂ) ^ (2 * s) = 1 := by
  rcases Int.units_eq_one_or x with h | h <;> simp [h, pow_mul]

theorem eisRule_of (hQ : GlobalTheory.RealMult.QExpansionOnAll) (hExp : EisExp) (hMod : EisMod) (hFour : EisFourier)
    (hTor : TorusForm) : EisRule := by
  intro E _ _ _ hf 𝔠 s hs zv hzv R₀ m hm hmz
  have key : ∀ 𝔞 𝔟 𝔠' : FracId (FR E), 𝔠' = 𝔞 * 𝔟⁻¹ → ∃ r : Rule (trivialObjectCondition 𝔠') R₀ (2 * s),
      ∀ (I : Type) [Fintype I] (φ : I → E →+* ℂ) (c : Ideal (OF E)) (y : (Af E)ˣ), IsCMType φ → c ≠ ⊥ →
        IsEisRule φ (lattice c y) m r := by
    intro 𝔞 𝔟 𝔠' h𝔠
    subst h𝔠
    have e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ) := (Fintype.equivFinOfCardEq (card_emb (FR E))).symm
    obtain ⟨G, hG, hGd, hGexp⟩ := hExp (FR E) hf 𝔞 𝔟 s hs
    have hGmod := hMod (FR E) 𝔞 𝔟 s hs G hG hGd
    obtain ⟨Z, a, hZ, hfo, ha0, hint⟩ := hFour (FR E) 𝔞 𝔟 (2 * s) (by omega) G hGexp
    have hω0 := omegaFactor_ne_zero 𝔞
    have hck0 := cK_ne_zero (FR E) (2 * s)
    set ω : ℂ := (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) with hω
    set ck : ℂ := (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK (FR E) (2 * s) : ℂ) with hck
    have hcw : (cWt E (2 * s) : ℂ) = ck := rfl
    set gF : ((FR E →+* ℝ) → ℂ) → ℂ := fun z ↦ (m * ck / ω ^ (2 * s)) * G z with hgFdef
    have hgF : IsHolForm 𝔞 𝔟 (2 * s) gF := isHolForm_mul hGmod _
    have hfoF : HasFourier 𝔞 𝔟 gF (fun ξ ↦ m * a ξ) := by
      intro z hz
      have := (hfo z hz).mul_left m
      convert this using 1 <;> first | rfl | (funext ξ; ring) | (simp only [gF]; ring)
    have hcoef : ∀ ξ, m * a ξ ∈ R₀ := by
      intro ξ
      by_cases hξ : ξ = 0
      · subst hξ
        rw [ha0]
        obtain ⟨Z', hZ', hZ'v⟩ := hzv (ClassGroup.mk (FR E) 𝔞)⁻¹
        have hne : (1 - ((2 * s : ℕ) : ℂ)) ∈ ({1}ᶜ : Set ℂ) := by
          have : ((2 * s : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * s ≠ 0)
          simpa using this
        have heq := GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.IsClassZeta.eqOn (F := FR E) ⟨hZ.1, hZ.2⟩ ⟨hZ'.1, hZ'.2⟩ hne
        rw [heq, hZ'v]
        have h5 : m * ((2 : ℂ)⁻¹ ^ Module.finrank ℚ (FR E) * ((zv (ClassGroup.mk (FR E) 𝔞)⁻¹ : ℚ) : ℂ)) =
            m * (((zv (ClassGroup.mk (FR E) 𝔞)⁻¹ / 2 ^ Module.finrank ℚ (FR E) : ℚ)) : ℂ) := by
          rw [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, div_eq_mul_inv, inv_pow]; ring
        rw [h5]; exact hmz _
      · obtain ⟨n, hn⟩ := hint ξ hξ
        rw [hn]
        exact R₀.mul_mem hm (intCast_mem R₀ n)
    obtain ⟨r, hrv, -⟩ := hQ (FR E) hf e 𝔞 𝔟 (2 * s) R₀ gF (fun ξ ↦ m * a ξ) hgF hfoF hcoef
    refine ⟨r, fun I _ φ c y hφ hc ↦ ?_⟩
    intro g hg z hz X U δ C hdet
    obtain ⟨e', τ, lam, he', hτ, hlam, hΛ, htp⟩ := hTor E I 𝔞 𝔟 φ c y hφ hc z hz X U
    have hgz := GlobalTheory.T.polydisc_cm_uniformization E I 𝔞 𝔟 φ c y hφ hc s hs z hz U.e e' τ lam he' hτ hlam
      (fun w ↦ (U.lat w).symm.trans (hΛ w)) G hG g hg
    have hlamp : ∏ j, lam j ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ ↦ hlam j
    set K : ℂ := ω / ∏ j, lam j with hK
    have hK0 : K ≠ 0 := div_ne_zero hω0 hlamp
    have hval : ∀ δ' : X.DetGen, U.IsDet δ'.1 K → r.val ℂ X trivial δ' = gF τ := by
      intro δ' hδ'
      have htp' := htp δ'.1 hδ'
      let π : Equiv.Perm (Fin (Module.finrank ℚ (FR E))) := e.trans e'.symm
      have hπ : π.trans e' = e := by ext j; simp [π]
      have hA := GlobalTheory.T.torus_point_permutation_sign (FR E) e' π 𝔞 𝔟 τ X δ'.1 htp'
      rw [hπ] at hA
      have hsg : (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℂ) ≠ 0 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
      have h1 := hrv τ hτ X trivial (smulGen δ' _ hsg) hA
      have h2 := r.homog ℂ X trivial δ' (smulGen δ' _ hsg) _ rfl
      rw [sign_pow_even, _root_.one_mul] at h2
      rw [← h2, h1]
    by_cases hdeg : ∃ (v : Fin (Module.finrank ℚ (FR E)) → X.Lie)
        (W : Matrix (Fin (Module.finrank ℚ (FR E))) (Fin (Module.finrank ℚ (FR E))) ℂ),
        (∀ j, U.u.IsDiff (W j) (v j).hom) ∧ W.det ≠ 0
    · obtain ⟨v, W, hv, hW⟩ := hdeg
      have hδv := GlobalTheory.T.determinant_nonzero_differentials (FR E) _ X _ U.u δ v W hv hW
      have hC : C ≠ 0 := by
        intro h0; apply hδv; rw [hdet v W hv, h0, zero_mul]
      have hδ' : U.IsDet (smulGen δ (K / C) (div_ne_zero hK0 hC)).1 K := by
        intro v W hv
        show ((K / C) • δ.1) v = K * W.det
        rw [AlternatingMap.smul_apply, hdet v W hv, smul_eq_mul]
        field_simp
      have h1 := hval _ hδ'
      have h2 := r.homog ℂ X trivial δ (smulGen δ (K / C) (div_ne_zero hK0 hC)) (K / C) rfl
      rw [h1] at h2
      have hCK : C ^ (2 * s) * (K / C) ^ (2 * s) = K ^ (2 * s) := by
        rw [← mul_pow]; congr 1; field_simp
      rw [← h2, ← _root_.mul_assoc, hCK, hgz, hcw, hK, hgFdef]
      simp only
      rw [div_pow, inv_pow]
      field_simp
    · push_neg at hdeg
      have hδK : U.IsDet δ.1 K := fun v W hv ↦ by rw [hdet v W hv, hdeg v W hv]; simp
      have hδ2 : U.IsDet (smulGen δ 2 two_ne_zero).1 K := by
        intro v W hv
        show ((2 : ℂ) • δ.1) v = K * W.det
        rw [AlternatingMap.smul_apply, hdet v W hv, hdeg v W hv]; simp
      have h1 := hval _ hδK
      have h2 := hval _ hδ2
      have h3 := r.homog ℂ X trivial δ (smulGen δ 2 two_ne_zero) 2 rfl
      rw [h1, h2] at h3
      have hg0 : gF τ = 0 := by
        have h4 : ((2 : ℂ) ^ (2 * s) - 1) * gF τ = 0 := by rw [sub_mul, h3]; ring
        refine (mul_eq_zero.1 h4).resolve_left ?_
        have : (1 : ℝ) < 2 ^ (2 * s) := one_lt_pow₀ (by norm_num) (by omega)
        intro h5
        have h6 : (2 : ℂ) ^ (2 * s) = 1 := sub_eq_zero.1 h5
        have h7 : ((2 : ℝ) ^ (2 * s) : ℂ) = 1 := by push_cast; exact h6
        have h8 : (2 : ℝ) ^ (2 * s) = 1 := by exact_mod_cast h7
        linarith
      have hmG : m * G τ = 0 := by
        simp only [gF] at hg0
        have := mul_eq_zero.1 hg0
        rcases this with h | h
        · rcases mul_eq_zero.1 (div_eq_zero_iff.1 h |>.resolve_right (pow_ne_zero _ hω0)) with h' | h'
          · rw [h', zero_mul]
          · exact absurd h' hck0
        · rw [h, mul_zero]
      rw [h1, hgz, hg0, mul_zero]
      linear_combination (-(cWt E (2 * s) : ℂ) * ((∏ j, lam j)⁻¹) ^ (2 * s)) * hmG

  exact key 𝔠 1 𝔠 (by simp)

end GlobalTheory.EisRuleProof
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_rule_of_q_expansion : GlobalTheory.RealMult.QExpansionOnAll → EisExp → EisMod → EisFourier → TorusForm → EisRule := by
  atlas_forward_decl GlobalTheory.EisRuleProof.eisRule_of
end
