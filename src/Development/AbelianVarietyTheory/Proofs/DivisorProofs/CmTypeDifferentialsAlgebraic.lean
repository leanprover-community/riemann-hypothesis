import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormExistsForCmObject
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeSeparatesEmbeddings
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualEq
import BuildAid.ForwardExisting

section
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagPolForm

theorem exists_of_isLB (P : GlobalTheory.Published.AbelianDeRham.Free) {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]
    {g : ℕ} (hA : IsAbelianScheme A) (gA : SmoothOfRelativeDimension g A.hom) (L : LB A.left) (hLB : L.IsLB) :
    ∃ ψ : LinearMap.BilinForm R (HdR A), IsPolForm (dp0 R) (𝟙 _) A L ψ := by
  obtain ⟨h0, -, -, -, e, he⟩ := P R A _ hA gA
  obtain ⟨z, hz, -⟩ := (isChern_existsUnique_and_iso R ⊥ (dp0 R) _ (A.hom ≫ 𝟙 _)).1 _ hLB
  obtain ⟨n, a, b, hab⟩ := PolExists.exists_sum_wedge (e.symm z)
  have hm : ∀ c : FirstDeRham (A.hom ≫ 𝟙 _), c ∈ primDR A := fun c ↦ by
    change c ∈ prim (dp0 R) (𝟙 _) A
    rw [show prim (dp0 R) (𝟙 _) A = ⊤ from h0]; trivial
  let a' : Fin n → primDR A := fun k ↦ ⟨a k, hm _⟩
  let b' : Fin n → primDR A := fun k ↦ ⟨b k, hm _⟩
  have hz' : IsChern (dp0 R) (A.hom ≫ 𝟙 _) L (∑ k, CatCoh.cup _ (a' k).1 (b' k).1) := by
    have : z = ∑ k, CatCoh.cup _ (a k) (b k) := by
      rw [← e.apply_symm_apply z, ← hab, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ he _ _
    exact this ▸ hz
  exact ⟨_, n, a', b', hz', rfl⟩

theorem diag_polForm_exists : GlobalTheory.Published.AbelianDeRham.Free → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]
    (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt), ∃ ψ : LinearMap.BilinForm R (HdR X.A), IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ := by
  intro P F _ _ 𝔠 R _ X c
  exact exists_of_isLB P X.A X.ab X.dim _ (pull_isLB (X.isLB c) _)

end GlobalTheory.DiagPolForm
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_form_exists_free_de_rham : GlobalTheory.Published.AbelianDeRham.Free → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]
    (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt), ∃ ψ : LinearMap.BilinForm R (HdR X.A), IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ := by
  atlas_forward_decl GlobalTheory.DiagPolForm.diag_polForm_exists
end

section
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbDual

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMultAdjoint

theorem polForm_adjoint_rm : GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt) (ψ : LinearMap.BilinForm R (HdR X.A)),
    IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ → ∀ (b : 𝓞 F) (x y : HdR X.A),
      ψ (act (dp0 R) (𝟙 _) X.rm b x) y = ψ x (act (dp0 R) (𝟙 _) X.rm b y) := by
  intro HR HD F _ _ 𝔠 R _ X c ψ hψ b x y
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab
  have gAB := smooth_prod X.dim X.dim
  have C := cupSquare_of_free HR.1 hAB gAB
  have := X.rm.hom
  obtain ⟨φ, hφ, h2φ⟩ := GlobalTheory.PolPairing.exists_isCorrForm_diag HR F 𝔠 R X c
  obtain ⟨φ', hφ', h2φ'⟩ := GlobalTheory.PolPairing.exists_isCorrForm_diag HR F 𝔠 R X (b • c)
  have eψ : ψ = (2 : R) • φ := IsPolForm.unique HR.1 X.ab X.dim (pull_isLB (X.isLB c) _) hψ h2φ
  obtain ⟨χ, hχ, k⟩ := hφ.pull (X.isLB c) (homMor (dp0 R) (𝟙 _) (𝟙 X.A))
    (homMor (dp0 R) (𝟙 _) (X.rm.act b)) (h := (lift (fst X.A X.A) (snd X.A X.A ≫ X.rm.act b)).left)
    (by simp only [← Over.comp_left, lift_fst, lift_snd, Category.comp_id])
    (by simp only [← Over.comp_left, lift_fst, lift_snd, Category.comp_id])
    (X.isLB (b • c)) (LBIso.symm (X.smul b c))
  obtain rfl := hχ.unique C (X.isLB (b • c)) hφ'
  have key : ∀ u v, χ u v = φ u (push (dp0 R) (𝟙 _) (X.rm.act b) v) := fun u v ↦ by
    have e := k (push (dp0 R) (𝟙 _) (𝟙 X.A) u) u (push (dp0 R) (𝟙 _) (X.rm.act b) v) v (fun _ ↦ rfl) fun _ ↦ rfl
    rwa [push_id, LinearMap.id_apply, RingHom.id_apply] at e
  change ψ (push (dp0 R) (𝟙 _) (X.rm.act b) x) y = ψ x (push (dp0 R) (𝟙 _) (X.rm.act b) y)
  have e₁ := (LinearMap.IsAlt.neg hψ.isAlt y (push (dp0 R) (𝟙 _) (X.rm.act b) x)).symm
  have e₂ := LinearMap.IsAlt.neg h2φ'.isAlt y x
  rw [e₁, eψ]
  simp only [LinearMap.smul_apply, ← key] at e₂ ⊢
  exact e₂

end GlobalTheory.RealMultAdjoint
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_form_ring_action_symmetric : GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt) (ψ : LinearMap.BilinForm R (HdR X.A)),
    IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ → ∀ (b : 𝓞 F) (x y : HdR X.A),
      ψ (act (dp0 R) (𝟙 _) X.rm b x) y = ψ x (act (dp0 R) (𝟙 _) X.rm b y) := by
  atlas_forward_decl GlobalTheory.RealMultAdjoint.polForm_adjoint_rm
end

section
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMSep

theorem exists_int_ne' : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} (φ : I → E →+* ℂ), IsCMType φ →
    ∀ i j, i ≠ j → ∃ b : 𝓞 (FR E), φ i ((b : FR E) : E) ≠ φ j ((b : FR E) : E) :=
  fun {E} _ _ _ {I} φ hφ i j hij => exists_int_ne E I φ hφ i j hij

end GlobalTheory.CMSep
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_of_isCMType_of_ne : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} (φ : I → E →+* ℂ), IsCMType φ →
    ∀ i j, i ≠ j → ∃ b : 𝓞 (FR E), φ i ((b : FR E) : E) ≠ φ j ((b : FR E) : E) := by
  atlas_forward_decl GlobalTheory.CMSep.exists_int_ne'
end

section
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMSep

theorem exists_int_sep_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ i : I, ∃ b₀ : 𝓞 (FR E), ∀ j : I, φ j ((b₀ : FR E) : E) = φ i ((b₀ : FR E) : E) → j = i := by
  intro E _ _ _ I _ φ hφ i

  let L : I → FR E →ₗ[ℚ] ℂ := fun j => ((φ j).comp (algebraMap (FR E) E)).toRatAlgHom.toLinearMap
  have hL : ∀ j (x : FR E), L j x = φ j (x : E) := fun j x => rfl
  let p : {j : I // j ≠ i} → Subspace ℚ (FR E) := fun j => LinearMap.ker (L j.1 - L i)
  have hp : ∀ j, p j ≠ ⊤ := by
    intro j htop
    obtain ⟨a, ha⟩ := exists_int_ne E I φ hφ j.1 i j.2
    have : ((a : FR E)) ∈ p j := htop ▸ Submodule.mem_top
    simp only [p, LinearMap.mem_ker, LinearMap.sub_apply, hL, sub_eq_zero] at this
    exact ha this
  have hcov : ⋃ j, (p j : Set (FR E)) ≠ Set.univ := by
    intro h
    obtain ⟨j, hj⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ h
    exact hp j hj
  obtain ⟨x, hx⟩ : ∃ x : FR E, ∀ j : {j : I // j ≠ i}, x ∉ p j := by
    by_contra hno
    push_neg at hno
    exact hcov (Set.eq_univ_of_forall fun x => by
      obtain ⟨j, hj⟩ := hno x
      exact Set.mem_iUnion.mpr ⟨j, hj⟩)
  obtain ⟨y, hy0, hyint'⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset (FR E))
  have hyint := hyint' x (Finset.mem_singleton_self x)
  refine ⟨⟨y • x, hyint⟩, fun j hj => ?_⟩
  by_contra hji
  apply hx ⟨j, hji⟩
  simp only [p, LinearMap.mem_ker, LinearMap.sub_apply, hL, sub_eq_zero]
  have e : ((y • x : FR E) : E) = (y : E) * (x : E) := by simp [zsmul_eq_mul]
  change φ j ((y • x : FR E) : E) = φ i ((y • x : FR E) : E) at hj
  rw [e, map_mul, map_mul, map_intCast, map_intCast] at hj
  exact mul_left_cancel₀ (by exact_mod_cast hy0) hj

end GlobalTheory.CMSep
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_separating_integer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ i : I, ∃ b₀ : 𝓞 (FR E), ∀ j : I, φ j ((b₀ : FR E) : E) = φ i ((b₀ : FR E) : E) → j = i := by
  atlas_forward_decl GlobalTheory.CMSep.exists_int_sep_all
end

section
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RealMultEigen

theorem diagonalizable_corank_le_two {V : Type*} {κ : Type} [AddCommGroup V] [Module ℂ V] (b : Module.Basis κ ℂ V) (S : Module.End ℂ V) (ν : κ → ℂ)
    (hS : ∀ k, S (b k) = ν k • b k) (k₁ k₂ : κ) (hν : ∀ k, ν k = 0 → k = k₁ ∨ k = k₂) :
    Module.rank ℂ (V ⧸ LinearMap.range S) ≤ 2 ∧ Disjoint (LinearMap.ker S) (LinearMap.range S) := by
  classical
  have hr : ∀ k x, b.repr (S x) k = ν k * b.repr x k := fun k x => by
    have : (b.coord k) ∘ₗ S = ν k • b.coord k := b.ext fun l => by
      by_cases h : l = k
      · subst h; simp [hS]
      · simp [hS, Finsupp.single_apply, h]
    simpa using LinearMap.congr_fun this x
  constructor
  · let q := (LinearMap.range S).mkQ
    have htop : Submodule.span ℂ (({q (b k₁), q (b k₂)} : Finset _) : Set (V ⧸ LinearMap.range S)) = ⊤ := by
      rw [eq_top_iff, ← (LinearMap.range S).range_mkQ, LinearMap.range_eq_map (Submodule.mkQ _), ← b.span_eq, Submodule.map_span,
        Submodule.span_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      by_cases h : ν k = 0
      · apply Submodule.subset_span
        rcases hν k h with rfl | rfl <;> simp [q]
      · have : (LinearMap.range S).mkQ (b k) = 0 := by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact ⟨(ν k)⁻¹ • b k, by rw [map_smul, hS, smul_smul, inv_mul_cancel₀ h, one_smul]⟩
        rw [this]
        exact Submodule.zero_mem _
    rw [← rank_top, ← htop]
    refine (rank_span_finset_le _).trans ?_
    exact_mod_cast Finset.card_le_two
  · rw [Submodule.disjoint_def]
    rintro _ hx ⟨y, rfl⟩
    rw [LinearMap.mem_ker] at hx
    apply b.repr.injective
    ext k
    have h := hr k (S y)
    rw [hx, hr] at h
    rw [hr]
    simp only [map_zero, Finsupp.zero_apply] at h ⊢
    rcases mul_eq_zero.1 h.symm with h | h
    · rw [h, zero_mul]
    · exact h

theorem exists_eigenbasis {V : Type*} [AddCommGroup V] [Module ℂ V] {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (full : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (P : Λ →+ V) (hspan : Submodule.span ℂ (Set.range P) = ⊤)
    (hdim : Module.finrank ℂ V = 2 * g) (T : Module.End ℂ V) (r : Fin g → ℝ)
    (hT : ∀ x : Λ, ∃ x' : Λ, (x' : Fin g → ℂ) = (fun j => (r j : ℂ) * (x : Fin g → ℂ) j) ∧ T (P x) = P x') :
    ∃ b : Module.Basis (Fin g × Bool) ℂ V, ∀ k, T (b k) = (r k.1 : ℂ) • b k := by
  classical
  haveI : IsZLattice ℝ Λ := ⟨full⟩
  letI : Module ℝ V := Module.compHom V (algebraMap ℝ ℂ)
  haveI : IsScalarTower ℝ ℂ V := ⟨fun a c v => by
    change (a • c) • v = (algebraMap ℝ ℂ a) • c • v
    rw [smul_smul, Algebra.smul_def]⟩
  let bZ := Module.Free.chooseBasis ℤ Λ
  let bR := bZ.ofZLatticeBasis ℝ Λ
  let Q : (Fin g → ℂ) →ₗ[ℝ] V := bR.constr ℝ fun k => P (bZ k)
  have hQ : ∀ x : Λ, Q x = P x := fun x => by
    have : (Q.toAddMonoidHom.toIntLinearMap ∘ₗ Λ.subtype) = P.toIntLinearMap := bZ.ext fun k => by
      have := bR.constr_basis ℝ (fun k => P (bZ k)) k
      simpa [bR, Q] using this
    exact LinearMap.congr_fun this x
  let M : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
    { toFun := fun w j => (r j : ℂ) * w j
      map_add' := fun w w' => by funext j; simp [mul_add]
      map_smul' := fun c w => by funext j; simp; ring }
  have hTQ : ∀ w, T (Q w) = Q (M w) := fun w => by
    have : (T.restrictScalars ℝ) ∘ₗ Q = Q ∘ₗ M := bR.ext fun k => by
      obtain ⟨x', h1, h2⟩ := hT (bZ k)
      have e : bR k = bZ k := by simp [bR]
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, e]
      rw [hQ, h2, ← hQ, h1]
      rfl
    exact LinearMap.congr_fun this w
  let v : Fin g × Bool → V := fun k => Q (Pi.single k.1 (if k.2 then Complex.I else 1))
  have hv : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [← hQ]
    generalize (x : Fin g → ℂ) = w
    have hw : w = ∑ j, ((w j).re • (Pi.single j 1 : Fin g → ℂ) + (w j).im • (Pi.single j Complex.I : Fin g → ℂ)) := by
      funext l
      simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
    rw [hw, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_add, map_smul, map_smul]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨(j, false), rfl⟩)
    · exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨(j, true), rfl⟩)
  refine ⟨basisOfTopLeSpanOfCardEqFinrank v hv (by rw [hdim]; simp [mul_comm]), fun k => ?_⟩
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]
  have : M (Pi.single k.1 (if k.2 then Complex.I else 1)) =
      r k.1 • (Pi.single k.1 (if k.2 then Complex.I else 1) : Fin g → ℂ) := by
    funext l
    by_cases h : l = k.1
    · subst h; simp [M]
    · simp [M, Pi.single_apply, h]
  simp only [v]
  rw [hTQ, this, map_smul]
  rfl

theorem rank_coker_le_two : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
      (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X), IsCMType φ →
    ∀ (i : I) (b₀ : 𝓞 (FR E)), (∀ j : I, φ j ((b₀ : FR E) : E) = φ i ((b₀ : FR E) : E) → j = i) →
      Module.rank ℂ (HdR X.A ⧸ LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b₀ - φ i ((b₀ : FR E) : E) • 1)) ≤ 2 ∧
      Disjoint (LinearMap.ker (act (dp0 ℂ) (𝟙 _) X.rm b₀ - φ i ((b₀ : FR E) : E) • 1))
        (LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b₀ - φ i ((b₀ : FR E) : E) • 1)) := by
  intro hPC _ E _ _ _ I _ φ L 𝔠 X U _ i b₀ hsep
  obtain ⟨ε, hε⟩ := hPC
  obtain ⟨P, hspan, hdim, -, hend, -⟩ :=
    hε X.A (Module.finrank ℚ (FR E)) X.ab X.dim (X.diag U.c) (LB.isLB_pull (X.isLB _) _) U.u
  have hreal : ∀ j, (((φ j ((b₀ : FR E) : E)).re : ℝ) : ℂ) = φ j ((b₀ : FR E) : E) := fun j =>
    Complex.conj_eq_iff_re.1 ((b₀ : FR E).2 (φ j))
  let M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    { toFun := fun w j => φ (U.e j) ((b₀ : FR E) : E) * w j
      map_add' := fun w w' => by funext j; simp [mul_add]
      map_smul' := fun r w => by funext j; simp; ring }
  haveI := U.u.discrete
  obtain ⟨b, hb⟩ := exists_eigenbasis U.u.Λ U.u.full P hspan hdim (act (dp0 ℂ) (𝟙 _) X.rm b₀)
    (fun j => (φ (U.e j) ((b₀ : FR E) : E)).re) (fun x => by
      have hx : M x ∈ U.u.Λ := by
        rw [← U.u.ker]
        refine (U.act b₀ x).trans ?_
        rw [(U.u.ker x).2 x.2]
        haveI := X.rm.hom b₀
        exact MonObj.one_comp _
      refine ⟨⟨M x, hx⟩, ?_, ?_⟩
      · funext j
        rw [hreal]
        rfl
      · haveI := X.rm.hom b₀
        exact hend (X.rm.act b₀) M (U.act b₀) x ⟨M x, hx⟩ rfl)
  refine diagonalizable_corank_le_two b _ (fun k => φ (U.e k.1) ((b₀ : FR E) : E) - φ i ((b₀ : FR E) : E)) (fun k => ?_)
    (U.e.symm i, false) (U.e.symm i, true) (fun k hk => ?_)
  · rw [LinearMap.sub_apply, hb, hreal, sub_smul]
    rfl
  · obtain ⟨j, c⟩ := k
    have : j = U.e.symm i := by rw [← hsep _ (sub_eq_zero.1 hk)]; simp
    subst this
    cases c <;> simp

end GlobalTheory.RealMultEigen
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_de_rham_eigenspace_corank_le_two : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
      (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X), IsCMType φ →
    ∀ (i : I) (b₀ : 𝓞 (FR E)), (∀ j : I, φ j ((b₀ : FR E) : E) = φ i ((b₀ : FR E) : E) → j = i) →
      Module.rank ℂ (HdR X.A ⧸ LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b₀ - φ i ((b₀ : FR E) : E) • 1)) ≤ 2 ∧
      Disjoint (LinearMap.ker (act (dp0 ℂ) (𝟙 _) X.rm b₀ - φ i ((b₀ : FR E) : E) • 1))
        (LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b₀ - φ i ((b₀ : FR E) : E) • 1)) := by
  atlas_forward_decl GlobalTheory.RealMultEigen.rank_coker_le_two
end

section
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DescRank

open TensorProduct

variable {K L : Type} [Field K] [Field L] [Algebra K L] {P P' : Type*} [AddCommGroup P] [Module K P]
  [AddCommGroup P'] [Module L P'] (mp : P →ₛₗ[algebraMap K L] P') (hbc : Function.Bijective (liftSemi mp))
include hbc

theorem ext_of_bc {φ₁ φ₂ : Module.Dual L P'} (h : ∀ c, φ₁ (mp c) = φ₂ (mp c)) : φ₁ = φ₂ := by
  refine LinearMap.ext fun y ↦ ?_
  obtain ⟨z, rfl⟩ := hbc.2 y
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, h c]

def extForm (v : Module.Dual K P) : Module.Dual L P' :=
  liftSemi ({ toFun := fun c ↦ algebraMap K L (v c), map_add' := by simp, map_smul' := by simp } :
      P →ₛₗ[algebraMap K L] L) ∘ₗ (LinearEquiv.ofBijective _ hbc).symm.toLinearMap

theorem extForm_apply (v : Module.Dual K P) (c : P) : extForm mp hbc v (mp c) = algebraMap K L (v c) := by
  have : mp c = LinearEquiv.ofBijective _ hbc (1 ⊗ₜ c) := (one_smul L (mp c)).symm
  rw [extForm, this, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, liftSemi_tmul, one_smul]
  rfl

theorem extForm_zero : extForm mp hbc 0 = 0 :=
  ext_of_bc mp hbc fun c ↦ by rw [extForm_apply]; simp

theorem extForm_injective : Function.Injective (extForm mp hbc) := by
  intro v w h
  refine LinearMap.ext fun c ↦ (algebraMap K L).injective ?_
  rw [← extForm_apply mp hbc, ← extForm_apply mp hbc, h]

variable (g₀ : P →ₗ[K] P) (g : P' →ₗ[L] P') (hg : ∀ c, g (mp c) = mp (g₀ c))
include hg

theorem extForm_dualMap (w : Module.Dual K P) :
    extForm mp hbc (g₀.dualMap w) = g.dualMap (extForm mp hbc w) :=
  ext_of_bc mp hbc fun c ↦ by
    rw [extForm_apply, LinearMap.dualMap_apply, LinearMap.dualMap_apply, hg, extForm_apply]

theorem disjoint_desc (h : Disjoint (LinearMap.ker g.dualMap) (LinearMap.range g.dualMap)) :
    Disjoint (LinearMap.ker g₀.dualMap) (LinearMap.range g₀.dualMap) := by
  rw [Submodule.disjoint_def] at h ⊢
  rintro v hv ⟨w, rfl⟩
  have e := h (extForm mp hbc (g₀.dualMap w))
    (by rw [LinearMap.mem_ker, ← extForm_dualMap mp hbc g₀ g hg, LinearMap.mem_ker.1 hv, extForm_zero])
    ⟨extForm mp hbc w, (extForm_dualMap mp hbc g₀ g hg w).symm⟩
  exact extForm_injective mp hbc (e.trans (extForm_zero mp hbc).symm)

end GlobalTheory.DescRank

namespace GlobalTheory.DescRank

open TensorProduct

theorem rank_quot_range_dualMap {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : V →ₗ[k] V) : Module.rank k (Module.Dual k V ⧸ LinearMap.range f.dualMap) = Module.finrank k (LinearMap.ker f) := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, (Subspace.quotAnnihilatorEquiv _).rank_eq, ← Module.finrank_eq_rank,
    Subspace.dual_finrank_eq]

variable {K L : Type} [Field K] [Field L] [Algebra K L] {P P' : Type*} [AddCommGroup P] [Module K P]
  [AddCommGroup P'] [Module L P'] (mp : P →ₛₗ[algebraMap K L] P') (hbc : Function.Bijective (liftSemi mp))
  (g₀ : P →ₗ[K] P) (g : P' →ₗ[L] P') (hg : ∀ c, g (mp c) = mp (g₀ c))
include hbc hg

theorem rank_coker_desc [FiniteDimensional K P]
    (h : Module.rank L (Module.Dual L P' ⧸ LinearMap.range g.dualMap) ≤ 2) :
    Module.rank K (Module.Dual K P ⧸ LinearMap.range g₀.dualMap) ≤ 2 := by
  haveI : FiniteDimensional L P' := Module.Finite.equiv (LinearEquiv.ofBijective _ hbc)
  rw [rank_quot_range_dualMap] at h ⊢
  let j₀ : L ⊗[K] LinearMap.ker g₀ →ₗ[L] P' := liftSemi mp ∘ₗ (LinearMap.ker g₀).subtype.baseChange L
  have hj₀ : Function.Injective j₀ := by
    refine hbc.1.comp ?_
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
  have hmem : ∀ z, j₀ z ∈ LinearMap.ker g := by
    intro z
    induction z with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | tmul x c =>
      simp only [j₀, LinearMap.comp_apply, LinearMap.baseChange_tmul, Submodule.coe_subtype, liftSemi_tmul,
        LinearMap.mem_ker, map_smul, hg, LinearMap.mem_ker.1 c.2, map_zero, smul_zero]
  let j : L ⊗[K] LinearMap.ker g₀ →ₗ[L] LinearMap.ker g := LinearMap.codRestrict _ j₀ hmem
  have hj : Function.Injective j := fun x y e ↦ hj₀ (congrArg Subtype.val e)
  have hle := LinearMap.finrank_le_finrank_of_injective hj
  rw [Module.finrank_baseChange] at hle
  have h' : Module.finrank L (LinearMap.ker g) ≤ 2 := by exact_mod_cast h
  exact_mod_cast hle.trans h'

end GlobalTheory.DescRank

namespace GlobalTheory.DescRank

theorem desc_of_baseChange : GlobalTheory.Published.AbelianDeRham →
    ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X₀ : Obj F 𝔠 (Sp Qb)) (X : Obj F 𝔠 (Sp ℂ))
      (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    ∀ (b : 𝓞 F) (β : Qb),
      Module.rank ℂ (HdR X.A ⧸ LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b - algebraMap Qb ℂ β • 1)) ≤ 2 →
      Disjoint (LinearMap.ker (act (dp0 ℂ) (𝟙 _) X.rm b - algebraMap Qb ℂ β • 1))
        (LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b - algebraMap Qb ℂ β • 1)) →
      Module.rank Qb (HdR X₀.A ⧸ LinearMap.range (act (dp0 Qb) (𝟙 _) X₀.rm b - β • 1)) ≤ 2 ∧
      Disjoint (LinearMap.ker (act (dp0 Qb) (𝟙 _) X₀.rm b - β • 1))
        (LinearMap.range (act (dp0 Qb) (𝟙 _) X₀.rm b - β • 1)) := by
  intro hD F _ _ 𝔠 X₀ X p hp b β hrank hdisj
  let m := GlobalTheory.Published.AbelianDeRham.bcMor hp.grp
  have hBC : m.IsBC := (hD.2.2.1 Qb X₀.A _ X₀.ab X₀.dim ℂ X.A p hp.grp).1
  haveI : FiniteDimensional Qb (prim (dp0 Qb) (𝟙 _) X₀.A) := (GlobalTheory.Published.AbelianDeRham.Free.prim hD.1 X₀.ab X₀.dim).1
  haveI := X₀.rm.hom
  haveI := X.rm.hom
  let g₀ := primPull (dp0 Qb) (𝟙 _) (X₀.rm.act b) - β • LinearMap.id
  let g := primPull (dp0 ℂ) (𝟙 _) (X.rm.act b) - algebraMap Qb ℂ β • LinearMap.id
  have e₀ : act (dp0 Qb) (𝟙 _) X₀.rm b - β • 1 = g₀.dualMap := by
    refine LinearMap.ext fun h ↦ LinearMap.ext fun c ↦ ?_
    simp [g₀, act_apply, push_apply, smul_eq_mul]
  have e : act (dp0 ℂ) (𝟙 _) X.rm b - algebraMap Qb ℂ β • 1 = g.dualMap := by
    refine LinearMap.ext fun h ↦ LinearMap.ext fun c ↦ ?_
    simp [g, act_apply, push_apply, smul_eq_mul]
  have hg : ∀ c, g (m.pull c) = m.pull (g₀ c) := by
    intro c
    have k := (homMor (dp0 Qb) (𝟙 _) (X₀.rm.act b)).comp m
    have e1 : primPull (dp0 ℂ) (𝟙 _) (X.rm.act b) (m.pull c) = k.pull c :=
      GrpMor.pull_pull m (homMor (dp0 ℂ) (𝟙 _) (X.rm.act b)) k (fun _ ↦ rfl) (hp.act b) c
    have e2 : m.pull (primPull (dp0 Qb) (𝟙 _) (X₀.rm.act b) c) = k.pull c :=
      GrpMor.pull_pull (homMor (dp0 Qb) (𝟙 _) (X₀.rm.act b)) m k (fun _ ↦ rfl) rfl c
    simp only [g, g₀, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smulₛₗ, e1, e2]
  rw [e₀]
  rw [e] at hrank hdisj
  exact ⟨rank_coker_desc m.pull hBC g₀ g hg hrank, disjoint_desc m.pull hBC g₀ g hg hdisj⟩

end GlobalTheory.DescRank
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_endomorphism_corank_de_rham : GlobalTheory.Published.AbelianDeRham →
    ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X₀ : Obj F 𝔠 (Sp Qb)) (X : Obj F 𝔠 (Sp ℂ))
      (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    ∀ (b : 𝓞 F) (β : Qb),
      Module.rank ℂ (HdR X.A ⧸ LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b - algebraMap Qb ℂ β • 1)) ≤ 2 →
      Disjoint (LinearMap.ker (act (dp0 ℂ) (𝟙 _) X.rm b - algebraMap Qb ℂ β • 1))
        (LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b - algebraMap Qb ℂ β • 1)) →
      Module.rank Qb (HdR X₀.A ⧸ LinearMap.range (act (dp0 Qb) (𝟙 _) X₀.rm b - β • 1)) ≤ 2 ∧
      Disjoint (LinearMap.ker (act (dp0 Qb) (𝟙 _) X₀.rm b - β • 1))
        (LinearMap.range (act (dp0 Qb) (𝟙 _) X₀.rm b - β • 1)) := by
  atlas_forward_decl GlobalTheory.DescRank.desc_of_baseChange
end

section
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenFunctional

theorem mul_comm_of_rank_coker {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (T : Module.End K V) (c : K)
    (hrk : Module.rank K (V ⧸ LinearMap.range (T - c • 1)) ≤ 2)
    (hdis : Disjoint (LinearMap.ker (T - c • 1)) (LinearMap.range (T - c • 1)))
    (y₀ : V) (hy : y₀ ≠ 0) (hTy : T y₀ = c • y₀) (f f' : Module.Dual K V) (hf0 : f y₀ = 0) (hf'0 : f' y₀ = 0)
    (hf : ∀ x, f (T x) = c * f x) (hf' : ∀ x, f' (T x) = c * f' x) (x y : V) :
    f x * f' y = f y * f' x := by
  set W := LinearMap.range (T - c • 1) with hW
  have vanish : ∀ (g : Module.Dual K V), (∀ x, g (T x) = c * g x) → ∀ w ∈ W, g w = 0 := by
    rintro g hg w ⟨v, rfl⟩
    simp [hg, smul_eq_mul]
  have hyW : y₀ ∉ W := by
    intro h
    have hk : y₀ ∈ LinearMap.ker (T - c • 1) := by simp [hTy]
    exact hy ((Submodule.disjoint_def.1 hdis) y₀ hk h)
  by_contra hD
  have hD' : f x * f' y - f y * f' x ≠ 0 := sub_ne_zero.2 hD
  have hli : LinearIndependent K ![W.mkQ y₀, W.mkQ x, W.mkQ y] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    replace hg : g 0 • y₀ + g 1 • x + g 2 • y ∈ W := by
      rw [← Submodule.Quotient.mk_eq_zero]
      simpa [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul] using hg
    have e1 := vanish f hf _ hg
    have e2 := vanish f' hf' _ hg
    simp only [map_add, map_smul, smul_eq_mul, hf0, hf'0, mul_zero, zero_add] at e1 e2
    have hb : g 1 = 0 := by
      have : g 1 * (f x * f' y - f y * f' x) = 0 := by linear_combination f' y * e1 - f y * e2
      exact (mul_eq_zero.1 this).resolve_right hD'
    have hc : g 2 = 0 := by
      have : g 2 * (f x * f' y - f y * f' x) = 0 := by linear_combination f x * e2 - f' x * e1
      exact (mul_eq_zero.1 this).resolve_right hD'
    rw [hb, hc, zero_smul, zero_smul, add_zero, add_zero] at hg
    have ha : g 0 = 0 := by
      by_contra ha
      exact hyW ((W.smul_mem_iff ha).1 hg)
    intro j; fin_cases j <;> assumption
  have := hli.cardinal_lift_le_rank
  simp only [Cardinal.mk_fintype, Fintype.card_fin, Nat.cast_ofNat, Cardinal.lift_ofNat] at this
  have h3 : (3 : Cardinal) ≤ 2 := by
    have := this.trans (Cardinal.lift_le.2 hrk)
    simpa using this
  norm_num at h3

end GlobalTheory.EigenFunctional

namespace GlobalTheory.EigenFunctional

theorem mul_comm_of_eigen : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
      (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
      (U : Unif φ L 0 X), IsCMType φ → X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    ∀ (i : I) (y₀ : HdR X₀.A), y₀ ≠ 0 →
      (∀ (b : 𝓞 (FR E)) (β : Qb), algebraMap Qb ℂ β = φ i ((b : FR E) : E) →
        act (dp0 Qb) (𝟙 _) X₀.rm b y₀ = β • y₀) →
    ∀ f f' : Module.Dual Qb (HdR X₀.A), f y₀ = 0 → f' y₀ = 0 →
      (∀ (b : 𝓞 (FR E)) (β : Qb), algebraMap Qb ℂ β = φ i ((b : FR E) : E) →
        ∀ x, f (act (dp0 Qb) (𝟙 _) X₀.rm b x) = β * f x ∧ f' (act (dp0 Qb) (𝟙 _) X₀.rm b x) = β * f' x) →
      ∀ x y, f x * f' y = f y * f' x := by
  intro hPC hDR E _ _ _ I _ φ L 𝔠 X₀ X p U hcm hp i y₀ hy0 hy f f' hf0 hf'0 hff x y
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.T.cm_type_separating_integer E I φ hcm i
  have halg : IsAlgebraic ℚ (φ i ((b₀ : FR E) : E)) := by
    have h1 : IsIntegral ℤ (φ i ((b₀ : FR E) : E)) :=
      ((b₀.2.map (algebraMap (FR E) E).toIntAlgHom).map (φ i).toIntAlgHom)
    exact (h1.tower_top (A := ℚ)).isAlgebraic
  let β₀ : Qb := ⟨φ i ((b₀ : FR E) : E), mem_algebraicClosure_iff.2 halg⟩
  have hβ : algebraMap Qb ℂ β₀ = φ i ((b₀ : FR E) : E) := rfl
  obtain ⟨hC1, hC2⟩ := GlobalTheory.T.cm_de_rham_eigenspace_corank_le_two hPC hDR E I φ L 𝔠 X U hcm i b₀ hb₀
  rw [← hβ] at hC1 hC2
  obtain ⟨hQ1, hQ2⟩ := GlobalTheory.T.algebraic_endomorphism_corank_de_rham hDR (FR E) 𝔠 X₀ X p hp b₀ β₀ hC1 hC2
  exact mul_comm_of_rank_coker _ β₀ hQ1 hQ2 y₀ hy0 (hy b₀ β₀ hβ) f f' hf0 hf'0
    (fun z ↦ (hff b₀ β₀ hβ z).1) (fun z ↦ (hff b₀ β₀ hβ z).2) x y

end GlobalTheory.EigenFunctional
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_periods_algebraic_nonzero : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
      (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
      (U : Unif φ L 0 X), IsCMType φ → X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    ∀ (i : I) (y₀ : HdR X₀.A), y₀ ≠ 0 →
      (∀ (b : 𝓞 (FR E)) (β : Qb), algebraMap Qb ℂ β = φ i ((b : FR E) : E) →
        act (dp0 Qb) (𝟙 _) X₀.rm b y₀ = β • y₀) →
    ∀ f f' : Module.Dual Qb (HdR X₀.A), f y₀ = 0 → f' y₀ = 0 →
      (∀ (b : 𝓞 (FR E)) (β : Qb), algebraMap Qb ℂ β = φ i ((b : FR E) : E) →
        ∀ x, f (act (dp0 Qb) (𝟙 _) X₀.rm b x) = β * f x ∧ f' (act (dp0 Qb) (𝟙 _) X₀.rm b x) = β * f' x) →
      ∀ x y, f x * f' y = f y * f' x := by
  atlas_forward_decl GlobalTheory.EigenFunctional.mul_comm_of_eigen
end

section
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PeriodLattice

theorem periods_unif : GlobalTheory.Published.PeriodComparison →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
    (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X),
    ∃ P : E →+ HdR X.A, Submodule.span ℂ (Set.range P) = ⊤ ∧
      ∀ (a : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) a * w' j) = U.u.ex w' ≫ α) →
        ∀ x, push (dp0 ℂ) (𝟙 _) α (P x) = P (a * x) := by
  intro hPC E _ _ _ I _ φ L 𝔠 X U
  obtain ⟨ε, hε⟩ := hPC
  obtain ⟨P₀, hspan, -, -, hend, -⟩ :=
    hε X.A (Module.finrank ℚ (FR E)) X.ab X.dim (X.diag U.c) (LB.isLB_pull (X.isLB _) _) U.u
  let em : E →ₗ[ℚ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    { toFun := fun x j => φ (U.e j) x
      map_add' := fun x x' => by funext j; simp
      map_smul' := fun q x => by funext j; simp [Rat.smul_def] }
  have hem : ∀ x j, em x j = φ (U.e j) x := fun _ _ => rfl
  have hdc : ∀ x, (fun j => GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord φ 0 x (U.e j)) = em x := fun x => by
    funext j; simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord, hem]
  let S : AddSubgroup E :=
    { carrier := {x | em x ∈ U.u.Λ}
      add_mem' := fun {a b} ha hb => by
        show em (a + b) ∈ U.u.Λ
        rw [map_add]; exact add_mem ha hb
      zero_mem' := by
        show em 0 ∈ U.u.Λ
        rw [map_zero]; exact zero_mem _
      neg_mem' := fun {a} ha => by
        show em (-a) ∈ U.u.Λ
        rw [map_neg]; exact neg_mem ha }
  have hemL : ∀ x ∈ S, em x ∈ U.u.Λ := fun x hx => hx
  let Q : S →+ HdR X.A :=
    { toFun := fun x => P₀ ⟨em x, hemL x x.2⟩
      map_zero' := by
        rw [show (⟨em ((0 : S) : E), hemL _ (0 : S).2⟩ : U.u.Λ) = 0 from
          Subtype.ext (by simp), map_zero]
      map_add' := fun x x' => by
        rw [← map_add]
        congr 1
        ext
        simp }
  have hsur : ∀ w ∈ U.u.Λ, ∃ x, em x = w := fun w hw => by
    obtain ⟨x, -, rfl⟩ := (U.lat w).1 hw
    exact ⟨x, (hdc x).symm⟩
  have hΛ : (U.u.Λ : Set (Fin (Module.finrank ℚ (FR E)) → ℂ)) = em '' (S : Set E) := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, rfl⟩ := hsur w hw
      exact ⟨x, hw, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hemL x hx
  have hdim : Module.finrank ℚ E ≤ 2 * Module.finrank ℚ (FR E) := by
    rw [← Module.finrank_mul_finrank ℚ (FR E) E, Algebra.IsQuadraticExtension.finrank_eq_two (FR E) E, mul_comm]
  have full : ∀ x : E, ∃ n : ℕ, 0 < n ∧ n • x ∈ S :=
    exists_nsmul_mem S em hdim (hΛ ▸ U.u.full)
  obtain ⟨P, hP⟩ := exists_ext S full Q
  have hP1 : ∀ x (hx : x ∈ S), P x = P₀ ⟨em x, hemL x hx⟩ := fun x hx => by
    rw [hP x 1 one_pos (by rw [one_smul]; exact hx), Nat.cast_one, inv_one, one_smul]
    show P₀ _ = P₀ _
    congr 2
    simp
  refine ⟨P, ?_, ?_⟩
  · refine top_unique (hspan ▸ Submodule.span_mono ?_)
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    obtain ⟨x, rfl⟩ := hsur w hw
    exact ⟨x, hP1 x hw⟩
  · intro a α _ hα x
    obtain ⟨n, hn, hnx⟩ := full x
    obtain ⟨m, hm, hmx⟩ := full (a * x)
    have hpos : 0 < n * m := Nat.mul_pos hn hm
    have hNx : (n * m) • x ∈ S := by
      rw [mul_comm, mul_smul]; exact S.nsmul_mem hnx _
    have hNax : (n * m) • (a * x) ∈ S := by
      rw [mul_smul]; exact S.nsmul_mem hmx _
    let M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
      { toFun := fun w j => φ (U.e j) a * w j
        map_add' := fun w w' => by funext j; simp [mul_add]
        map_smul' := fun r w => by funext j; simp; ring }
    rw [hP x _ hpos hNx, hP (a * x) _ hpos hNax, map_smul]
    congr 1
    exact hend α M (fun w => hα w) ⟨em ((n * m) • x), hemL _ hNx⟩ ⟨em ((n * m) • (a * x)), hemL _ hNax⟩
      (by funext j; simp only [hem, M, LinearMap.coe_mk, AddHom.coe_mk, map_nsmul, nsmul_eq_mul, map_mul]; ring)

end GlobalTheory.PeriodLattice
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_de_rham_period_map_equivariant : GlobalTheory.Published.PeriodComparison →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
    (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X),
    ∃ P : E →+ HdR X.A, Submodule.span ℂ (Set.range P) = ⊤ ∧
      ∀ (a : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) a * w' j) = U.u.ex w' ≫ α) →
        ∀ x, push (dp0 ℂ) (𝟙 _) α (P x) = P (a * x) := by
  atlas_forward_decl GlobalTheory.PeriodLattice.periods_unif
end

section
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrderPrimitive

theorem exists_primitive_mul_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
    (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X),
    ∃ b : E, (∀ x ∈ L, b * x ∈ L) ∧ IntermediateField.adjoin ℚ {b} = ⊤ := by
  intro E _ _ _ I _ φ L 𝔠 X U
  classical
  set g := Module.finrank ℚ (FR E) with hg
  let emb : E →ₗ[ℚ] (Fin g → ℂ) :=
    { toFun := fun x j => φ (U.e j) x
      map_add' := fun x x' => by funext j; simp
      map_smul' := fun q x => by funext j; simp [Rat.smul_def] }
  have hemb : ∀ x j, emb x j = φ (U.e j) x := fun _ _ => rfl
  have hdc : ∀ x, (fun j => GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord φ 0 x (U.e j)) = emb x := fun x => by
    funext j; simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord, hemb]
  have hdim : Module.finrank ℚ E ≤ 2 * g := by
    rw [hg, ← Module.finrank_mul_finrank ℚ (FR E) E, Algebra.IsQuadraticExtension.finrank_eq_two (FR E) E, mul_comm]
  have hgpos : 0 < g := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    omega
  have hinj : Function.Injective emb := fun x y hxy => by
    have := congrFun hxy ⟨0, hgpos⟩
    rw [hemb, hemb] at this
    exact (φ (U.e ⟨0, hgpos⟩)).injective this
  let f : E →ₗ[ℤ] (Fin g → ℂ) := emb.toAddMonoidHom.toIntLinearMap
  have hf : ∀ x, f x = emb x := fun _ => rfl
  have hfinj : Function.Injective f := hinj
  let K : Submodule ℤ E := U.u.Λ.comap f
  have hmemK : ∀ x, x ∈ K ↔ x ∈ L := fun x => by
    show emb x ∈ U.u.Λ ↔ x ∈ L
    rw [U.lat]
    constructor
    · rintro ⟨x', hx', h⟩
      rw [hdc] at h
      exact hinj h ▸ hx'
    · intro hx
      exact ⟨x, hx, (hdc x).symm⟩
  have hmap : Submodule.map f K = U.u.Λ := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hw
      obtain ⟨x, hx, rfl⟩ := (U.lat w).1 hw
      exact ⟨x, (hmemK x).2 hx, by rw [hf, hdc]⟩
  haveI : DiscreteTopology U.u.Λ := U.u.discrete
  haveI : IsZLattice ℝ U.u.Λ := ⟨U.u.full⟩
  have hΛfin : U.u.Λ.FG := Module.Finite.iff_fg.1 (ZLattice.module_finite ℝ U.u.Λ)
  have hKfg : K.FG := Submodule.fg_of_fg_map_injective f hfinj (hmap ▸ hΛfin)
  obtain ⟨T, hTfin, hTspan⟩ := Submodule.fg_def.1 hKfg
  have hsp : Submodule.span ℝ (emb '' (K.toAddSubgroup : Set E)) = ⊤ := by
    have : emb '' (K.toAddSubgroup : Set E) = (U.u.Λ : Set (Fin g → ℂ)) := by
      rw [← hmap]
      ext w
      simp [hf]
    rw [this]
    exact U.u.full
  have full : ∀ x : E, ∃ n : ℕ, 0 < n ∧ n • x ∈ K.toAddSubgroup :=
    GlobalTheory.PeriodLattice.exists_nsmul_mem K.toAddSubgroup emb hdim hsp
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element ℚ E
  choose N hNpos hNmem using fun x : E => full (β * x)
  let Tf := hTfin.toFinset
  let n : ℕ := ∏ t ∈ Tf, N t
  have hnpos : 0 < n := Finset.prod_pos fun t _ => hNpos t
  have hmul : ∀ t ∈ T, (n : E) * β * t ∈ K := by
    intro t ht
    have htT : t ∈ Tf := hTfin.mem_toFinset.2 ht
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem N htT
    have e : (n : E) * β * t = m • (N t • (β * t)) := by
      rw [smul_smul, nsmul_eq_mul, mul_comm m, ← hm, _root_.mul_assoc]
    rw [e]
    exact K.smul_of_tower_mem m (hNmem t)
  refine ⟨(n : E) * β, fun x hx => ?_, ?_⟩
  · have hxK : x ∈ K := (hmemK x).2 hx
    have hle : Submodule.span ℤ T ≤ K.comap (LinearMap.mulLeft ℤ ((n : E) * β)) := by
      refine Submodule.span_le.2 fun t ht => ?_
      exact hmul t ht
    rw [hTspan] at hle
    exact (hmemK _).1 (hle hxK)
  · have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hnpos.ne'
    refine top_unique (hβ ▸ IntermediateField.adjoin_simple_le_iff.2 ?_)
    have e : β = algebraMap ℚ E ((n : ℚ)⁻¹) * ((n : E) * β) := by
      rw [← _root_.mul_assoc, map_inv₀, map_natCast, inv_mul_cancel₀ (by exact_mod_cast hnpos.ne'), _root_.one_mul]
    have h2 := mul_mem (IntermediateField.algebraMap_mem (IntermediateField.adjoin ℚ {(n : E) * β}) ((n : ℚ)⁻¹))
      (IntermediateField.mem_adjoin_simple_self ℚ ((n : E) * β))
    rwa [← e] at h2

end GlobalTheory.OrderPrimitive
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_lattice_multiplier : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
    (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X),
    ∃ b : E, (∀ x ∈ L, b * x ∈ L) ∧ IntermediateField.adjoin ℚ {b} = ⊤ := by
  atlas_forward_decl GlobalTheory.OrderPrimitive.exists_primitive_mul_mem
end

section
section
open Polynomial

namespace GlobalTheory

theorem spanEquivariant_aeval_map_apply {E : Type} [Field E] [NumberField E] {V : Type 1} [AddCommGroup V] [Module ℂ V]
    (P : E →+ V) (b : E) (T : Module.End ℂ V) (hT : ∀ x, T (P x) = P (b * x)) (q : ℚ[X]) :
    ∀ x, aeval T (q.map (algebraMap ℚ ℂ)) (P x) = P (aeval b q * x) := by
  induction q using Polynomial.induction_on with
  | C c =>
    intro x
    simp only [Polynomial.map_C, aeval_C, Module.algebraMap_end_apply]
    have h := map_ratCast_smul P E ℂ c x
    rw [smul_eq_mul] at h
    rw [eq_ratCast (algebraMap ℚ ℂ), eq_ratCast (algebraMap ℚ E), h]
  | add p q hp hq =>
    intro x
    simp only [Polynomial.map_add, map_add, LinearMap.add_apply, hp, hq, add_mul]
  | monomial n c ih =>
    intro x
    have e1 : (C c * X ^ (n + 1) : ℚ[X]) = (C c * X ^ n) * X := by ring
    rw [e1, Polynomial.map_mul, map_mul, Module.End.mul_apply, Polynomial.map_X, aeval_X, hT, ih,
      show aeval b (C c * X ^ n * X) = aeval b (C c * X ^ n) * b by rw [map_mul, aeval_X], mul_assoc]

theorem aeval_apply_of_apply_eq_smul {V : Type 1} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) (μ : ℂ) (y : V)
    (hy : T y = μ • y) (q : ℂ[X]) : aeval T q y = q.eval μ • y := by
  induction q using Polynomial.induction_on with
  | C c => simp [Module.algebraMap_end_apply]
  | add p q hp hq => simp [hp, hq, add_smul]
  | monomial n c ih =>
    have e1 : (C c * X ^ (n + 1) : ℂ[X]) = (C c * X ^ n) * X := by ring
    rw [e1, map_mul, Module.End.mul_apply, aeval_X, hy, map_smul, ih]
    conv_rhs => rw [eval_mul, eval_X]
    rw [smul_smul, mul_comm]

theorem spanEquivariant_minpoly_eigen_transfer : ∀ (E : Type) [Field E] [NumberField E] (V : Type 1) [AddCommGroup V] [Module ℂ V] (P : E →+ V),
    Submodule.span ℂ (Set.range P) = ⊤ → ∀ (b : E) (T : Module.End ℂ V), (∀ x, T (P x) = P (b * x)) →
    IntermediateField.adjoin ℚ {b} = ⊤ →
    Polynomial.aeval T ((minpoly ℚ b).map (algebraMap ℚ ℂ)) = 0 ∧
    ∀ (σ : E →+* ℂ) (a : E) (S : Module.End ℂ V), (∀ x, S (P x) = P (a * x)) → ∀ y, T y = σ b • y → S y = σ a • y := by
  intro E _ _ V _ _ P hspan b T hT hadj
  constructor
  · apply LinearMap.ext_on_range hspan
    intro x
    rw [spanEquivariant_aeval_map_apply P b T hT, minpoly.aeval, zero_mul, map_zero, LinearMap.zero_apply]
  · intro σ a S hS y hy
    have hint : IsIntegral ℚ b := Algebra.IsIntegral.isIntegral b
    have ha : a ∈ Algebra.adjoin ℚ {b} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hadj]
      trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨r, rfl⟩ := ha
    have hSeq : S = aeval T (r.map (algebraMap ℚ ℂ)) := by
      apply LinearMap.ext_on_range hspan
      intro x
      rw [hS, spanEquivariant_aeval_map_apply P b T hT]
      rfl
    rw [hSeq, aeval_apply_of_apply_eq_smul T (σ b) y hy, eval_map_algebraMap]
    congr 1
    exact Polynomial.aeval_algHom_apply σ.toRatAlgHom b r

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_minpoly_eigenvalue_compat : ∀ (E : Type) [Field E] [NumberField E] (V : Type 1) [AddCommGroup V] [Module ℂ V] (P : E →+ V),
    Submodule.span ℂ (Set.range P) = ⊤ → ∀ (b : E) (T : Module.End ℂ V), (∀ x, T (P x) = P (b * x)) →
    IntermediateField.adjoin ℚ {b} = ⊤ →
    Polynomial.aeval T ((minpoly ℚ b).map (algebraMap ℚ ℂ)) = 0 ∧
    ∀ (σ : E →+* ℂ) (a : E) (S : Module.End ℂ V), (∀ x, S (P x) = P (a * x)) → ∀ y, T y = σ b • y → S y = σ a • y := by
  atlas_forward_decl GlobalTheory.spanEquivariant_minpoly_eigen_transfer
end

section
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieImagePoly

theorem exists_isLieImage_aeval (A : Over (Sp ℂ)) [GrpObj A] (Lb : LB A.left) (g : ℕ) (u : HolUnif A Lb g)
    (α : A ⟶ A) [IsMonHom α] (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) (hD : ∀ z, u.ex (D z) = u.ex z ≫ α)
    (h : HdR A) (v : epsR ℂ ⟶ A) (w : Fin g → ℂ) (c : ℂ) (hv : IsLieImage h v) (hw : u.IsDiff w v)
    (hc : D w = c • w) (Q : Polynomial ℂ) :
    ∃ v', IsLieImage (Polynomial.aeval (push (dp0 ℂ) (𝟙 _) α) Q h) v' ∧ u.IsDiff (Q.eval c • w) v' := by
  induction Q using Polynomial.induction_on with
  | C a =>
    refine ⟨GlobalTheory.GrpTangent.epsScale a ≫ v, ?_, ?_⟩
    · rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
      exact hv.smul a
    · rw [Polynomial.eval_C]
      exact GlobalTheory.PeriodLattice.isDiff_epsScale u hw a
  | add p q hp hq =>
    obtain ⟨v₁, h₁, d₁⟩ := hp
    obtain ⟨v₂, h₂, d₂⟩ := hq
    refine ⟨v₁ * v₂, ?_, ?_⟩
    · rw [map_add, LinearMap.add_apply]
      exact h₁.add h₂
    · rw [Polynomial.eval_add, add_smul]
      exact GlobalTheory.UnifDifferential.isDiff_mul u ((ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff _).2 h₁.1)
        ((ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff _).2 h₂.1) d₁ d₂
  | monomial n a ih =>
    obtain ⟨v₁, h₁, d₁⟩ := ih
    refine ⟨v₁ ≫ α, ?_, ?_⟩
    · have e : Polynomial.C a * Polynomial.X ^ (n + 1) = Polynomial.X * (Polynomial.C a * Polynomial.X ^ n) := by ring
      rw [e, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
      exact h₁.push α
    · have e : Polynomial.eval c (Polynomial.C a * Polynomial.X ^ (n + 1)) =
          c * Polynomial.eval c (Polynomial.C a * Polynomial.X ^ n) := by simp [pow_succ]; ring
      have k := GlobalTheory.UnifLieBasis.isDiff_comp u α D hD h₁.1 d₁
      rwa [map_smul, hc, smul_smul, mul_comm, ← e] at k

end GlobalTheory.LieImagePoly
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_image_polynomial_endomorphism : ∀ (A : Over (Sp ℂ)) [GrpObj A] (Lb : LB A.left) (g : ℕ) (u : HolUnif A Lb g) (α : A ⟶ A) [IsMonHom α]
    (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)), (∀ z, u.ex (D z) = u.ex z ≫ α) →
    ∀ (h : HdR A) (v : epsR ℂ ⟶ A) (w : Fin g → ℂ) (c : ℂ), IsLieImage h v → u.IsDiff w v → D w = c • w →
    ∀ Q : Polynomial ℂ, ∃ v', IsLieImage (Polynomial.aeval (push (dp0 ℂ) (𝟙 _) α) Q h) v' ∧ u.IsDiff (Q.eval c • w) v' := by
  atlas_forward_decl GlobalTheory.LieImagePoly.exists_isLieImage_aeval
end

section
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem DeRham.corr_aeval_push : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A']
    (b : Sp R' ⟶ Sp R) (φ : A'.left ⟶ A.left) (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ b φ) (f : A ⟶ A) (f' : A' ⟶ A')
    [IsMonHom f] [IsMonHom f'], φ ≫ f.left = f'.left ≫ φ → ∀ (x : HdR A) (x' : HdR A'), m.Corr x x' →
    ∀ Q : Polynomial R, m.Corr (Polynomial.aeval (push (dp0 R) (𝟙 _) f) Q x) (Polynomial.aeval (push (dp0 R') (𝟙 _) f') (Q.map σ) x') := by
  intro R R' _ _ σ A _ A' _ b φ m f f' _ _ e
  have hT : ∀ (x : HdR A) (x' : HdR A'), m.Corr x x' →
      m.Corr (push (dp0 R) (𝟙 _) f x) (push (dp0 R') (𝟙 _) f' x') :=
    fun x x' h ↦ GrpMor.Corr.push (m := m) m f f' e h
  intro x x' hx Q
  revert x x'
  refine Polynomial.induction_on Q ?_ ?_ ?_
  · intro a x x' hx c
    simp only [Polynomial.aeval_C, Polynomial.map_C, Module.algebraMap_end_apply,
      LinearMap.smul_apply, smul_eq_mul, hx c, map_mul]
  · intro p q hp hq x x' hx c
    simp only [Polynomial.map_add, map_add, LinearMap.add_apply, hp x x' hx c, hq x x' hx c]
  · intro n a ih x x' hx
    have h := ih _ _ (hT x x' hx)
    rw [_root_.pow_succ, ← _root_.mul_assoc, Polynomial.map_mul, Polynomial.map_X]
    simp only [map_mul, Polynomial.aeval_X, Module.End.mul_apply] at h ⊢
    exact h

end GlobalTheory
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_correspondence_polynomial : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A']
    (b : Sp R' ⟶ Sp R) (φ : A'.left ⟶ A.left) (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ b φ) (f : A ⟶ A) (f' : A' ⟶ A')
    [IsMonHom f] [IsMonHom f'], φ ≫ f.left = f'.left ≫ φ → ∀ (x : HdR A) (x' : HdR A'), m.Corr x x' →
    ∀ Q : Polynomial R, m.Corr (Polynomial.aeval (push (dp0 R) (𝟙 _) f) Q x) (Polynomial.aeval (push (dp0 R') (𝟙 _) f') (Q.map σ) x') := by
  atlas_forward_decl GlobalTheory.DeRham.corr_aeval_push
end

section
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigProj

open Polynomial

theorem eigProj_poly : ∀ (E : Type) [Field E] [NumberField E] (b : E) (σ : E →+* ℂ), ∃ (Q : Polynomial Qb) (c : ℂ),
    (Polynomial.X - Polynomial.C (σ b)) * Q.map (algebraMap Qb ℂ) = Polynomial.C c * (minpoly ℚ b).map (algebraMap ℚ ℂ) ∧
    (Q.map (algebraMap Qb ℂ)).eval (σ b) = 1 := by
  intro E _ _ b σ
  have hint : IsIntegral ℚ b := Algebra.IsIntegral.isIntegral b
  have hcomp : σ.comp (algebraMap ℚ E) = algebraMap ℚ ℂ := Subsingleton.elim _ _
  have hroot : (minpoly ℚ b).eval₂ (algebraMap ℚ ℂ) (σ b) = 0 := by
    rw [← hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
  have hmem : σ b ∈ algebraicClosure ℚ ℂ := by
    exact mem_algebraicClosure_iff.2 (hint.map (σ.toRatAlgHom)).isAlgebraic
  set β : Qb := ⟨σ b, hmem⟩ with hβ
  have hι : algebraMap Qb ℂ β = σ b := rfl
  have hcompQ : (algebraMap Qb ℂ).comp (algebraMap ℚ Qb) = algebraMap ℚ ℂ := Subsingleton.elim _ _
  have hrootQ : (minpoly ℚ b).eval₂ (algebraMap ℚ Qb) β = 0 := by
    apply (algebraMap Qb ℂ).injective
    rw [Polynomial.hom_eval₂, hcompQ, hι, hroot, map_zero]
  set fQ := (minpoly ℚ b).map (algebraMap ℚ Qb) with hfQ
  have hfQroot : fQ.IsRoot β := by
    rw [Polynomial.IsRoot, hfQ, Polynomial.eval_map]; exact hrootQ
  set g := fQ /ₘ (X - C β) with hg
  have hfac : (X - C β) * g = fQ := (Polynomial.mul_divByMonic_eq_iff_isRoot).2 hfQroot
  have hsep : (minpoly ℚ b).Separable := Algebra.IsSeparable.isSeparable ℚ b
  have hder := hsep.eval₂_derivative_ne_zero (algebraMap ℚ Qb) hrootQ
  have hgβ : g.eval β ≠ 0 := by
    intro h0
    apply hder
    have : (derivative (minpoly ℚ b)).eval₂ (algebraMap ℚ Qb) β = (derivative fQ).eval β := by
      rw [hfQ, Polynomial.derivative_map, Polynomial.eval_map]
    rw [this, ← hfac, derivative_mul]
    simp [h0]
  refine ⟨C (g.eval β)⁻¹ * g, (algebraMap Qb ℂ (g.eval β))⁻¹, ?_, ?_⟩
  · have key : (X - C β) * (C (g.eval β)⁻¹ * g) = C (g.eval β)⁻¹ * fQ := by rw [← hfac]; ring
    have := congrArg (Polynomial.map (algebraMap Qb ℂ)) key
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hι, map_inv₀] at this
    simp only [Polynomial.map_mul, Polynomial.map_C, map_inv₀]
    rw [this, hfQ, Polynomial.map_map, hcompQ]
  · rw [Polynomial.eval_map, ← hι, Polynomial.eval₂_at_apply, Polynomial.eval_mul, Polynomial.eval_C,
      inv_mul_cancel₀ hgβ, map_one]

end GlobalTheory.EigProj
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_polynomial_linear_factor_split : ∀ (E : Type) [Field E] [NumberField E] (b : E) (σ : E →+* ℂ), ∃ (Q : Polynomial Qb) (c : ℂ),
    (Polynomial.X - Polynomial.C (σ b)) * Q.map (algebraMap Qb ℂ) = Polynomial.C c * (minpoly ℚ b).map (algebraMap ℚ ℂ) ∧
    (Q.map (algebraMap Qb ℂ)).eval (σ b) = 1 := by
  atlas_forward_decl GlobalTheory.EigProj.eigProj_poly
end

section
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CMEigen

theorem exists_algebraic_eigenvectors : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
    (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
    (U : Unif φ L 0 X) (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ) (hp : X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p),
    IsCMType φ →
    (∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom ∧ a i ≠ 0) →
    (∀ b : E, (∀ x ∈ L, b * x ∈ L) → ∃ α : X.A ⟶ X.A, IsMonHom α ∧
      ∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
    (∀ (b : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
      ∃ α₀ : X₀.A ⟶ X₀.A, IsMonHom α₀ ∧ α.left ≫ p = p ≫ α₀.left) →
    ∃ (y₀ : I → HdR X₀.A) (yv : I → HdR X.A) (w : I → ℂ), ∀ i,
      y₀ i ≠ 0 ∧ (GlobalTheory.Published.AbelianDeRham.bcMor hp.grp).Corr (y₀ i) (yv i) ∧ U.IsCMVec i (yv i) (w i) ∧ w i ≠ 0 ∧
        IsAlgebraic ℚ (w i / a i) := by
  intro hPC hD _hDC E _ _ _ I _ φ L 𝔠 X₀ X p U v₀ v a hp _hφ hva hex hdesc
  obtain ⟨P, hspan, hP⟩ := GlobalTheory.T.cm_de_rham_period_map_equivariant hPC E I φ L 𝔠 X U
  obtain ⟨b, hbL, hbprim⟩ := GlobalTheory.T.exists_primitive_lattice_multiplier E I φ L 𝔠 X U
  obtain ⟨α, hαm, hα⟩ := hex b hbL
  haveI := hαm
  obtain ⟨α₀, hα₀m, hα₀⟩ := hdesc b α hα
  haveI := hα₀m
  obtain ⟨hf, heig⟩ := GlobalTheory.T.generator_minpoly_eigenvalue_compat E (HdR X.A) P hspan b (push (dp0 ℂ) (𝟙 _) α) (hP b α hα) hbprim
  have hE₀ : LieExact X₀.A := (hD.2.1 Qb X₀.A _ X₀.ab X₀.dim).1
  have hE : LieExact X.A := (hD.2.1 ℂ X.A _ X.ab X.dim).1
  obtain ⟨hBC, hF⟩ := hD.2.2.1 Qb X₀.A _ X₀.ab X₀.dim ℂ X.A p hp.grp
  let D : (Fin (Module.finrank ℚ (FR E)) → ℂ) →L[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    ContinuousLinearMap.pi fun j ↦ φ (U.e j) b • ContinuousLinearMap.proj j
  have hDz : ∀ z, D z = fun j ↦ φ (U.e j) b * z j := fun z ↦ by
    funext j; simp [D]
  have hD' : ∀ z, U.u.ex (D z) = U.u.ex z ≫ α := fun z ↦ by rw [hDz]; exact hα z
  have key : ∀ i, ∃ (y₀ : HdR X₀.A) (yv : HdR X.A), y₀ ≠ 0 ∧
      (GlobalTheory.Published.AbelianDeRham.bcMor hp.grp).Corr y₀ yv ∧ U.IsCMVec i yv (a i) := by
    intro i
    obtain ⟨hLC, hdiff, ha⟩ := hva i
    obtain ⟨Q, c, hQ, hQ1⟩ := GlobalTheory.T.minimal_polynomial_linear_factor_split E b (φ i)
    obtain ⟨h₀, hh₀⟩ := hE₀.2 (v₀ i).hom (v₀ i).isTangent
    obtain ⟨h, hh⟩ := hBC.exists h₀
    have hlie : IsLieImage h (v i).hom := IsLieImage.baseChange (hφ := hp.grp) hF hE hh hLC hh₀
    have hcorr := GlobalTheory.T.de_rham_correspondence_polynomial Qb ℂ (algebraMap Qb ℂ) X₀.A X.A _ p (GlobalTheory.Published.AbelianDeRham.bcMor hp.grp) α₀ α hα₀.symm h₀ h hh Q
    have hDw : D (Pi.single (U.e.symm i) (a i)) = φ i b • Pi.single (U.e.symm i) (a i) := by
      rw [hDz]
      funext j
      by_cases hj : j = U.e.symm i
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    obtain ⟨v', hv'1, hv'2⟩ := GlobalTheory.T.lie_image_polynomial_endomorphism X.A (X.diag U.c) _ U.u α D hD' h (v i).hom _ (φ i b) hlie hdiff hDw
      (Q.map (algebraMap Qb ℂ))
    rw [hQ1, one_smul] at hv'2
    have hTy : push (dp0 ℂ) (𝟙 _) α (Polynomial.aeval (push (dp0 ℂ) (𝟙 _) α) (Q.map (algebraMap Qb ℂ)) h) =
        φ i b • Polynomial.aeval (push (dp0 ℂ) (𝟙 _) α) (Q.map (algebraMap Qb ℂ)) h := by
      have e1 := congrArg (Polynomial.aeval (push (dp0 ℂ) (𝟙 _) α)) hQ
      rw [map_mul, map_mul, hf, mul_zero, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at e1
      have e2 := LinearMap.congr_fun e1 h
      rw [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.zero_apply, sub_eq_zero] at e2
      simpa [Algebra.algebraMap_eq_smul_one] using e2
    refine ⟨_, _, ?_, hcorr, fun a' α' _ hα' ↦ heig (φ i) a' _ (hP a' α' hα') _ hTy, v', hv'1, hv'2⟩
    intro h0
    rw [h0] at hcorr
    have hz : (GlobalTheory.Published.AbelianDeRham.bcMor hp.grp).Corr 0 0 := fun c ↦ by simp
    have hy0 := hBC.unique hcorr hz
    rw [hy0] at hv'1
    have hv1 : v' = 1 := (hE.1 0).unique hv'1 (isLieImage_one_iff.2 (zero_mem _))
    rw [hv1] at hv'2
    have := GlobalTheory.ArchMetricCompare.eq_zero_of_isDiff U.u hv'2
    exact ha (by simpa using congrFun this (U.e.symm i))
  choose y₀ yv hy using key
  exact ⟨y₀, yv, a, fun i ↦ ⟨(hy i).1, (hy i).2.1, (hy i).2.2, (hva i).2.2,
    by rw [div_self (hva i).2.2]; exact isAlgebraic_one⟩⟩

end GlobalTheory.CMEigen
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_period_transcendence_relation : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
    (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
    (U : Unif φ L 0 X) (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ) (hp : X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p),
    IsCMType φ →
    (∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom ∧ a i ≠ 0) →
    (∀ b : E, (∀ x ∈ L, b * x ∈ L) → ∃ α : X.A ⟶ X.A, IsMonHom α ∧
      ∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
    (∀ (b : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
      ∃ α₀ : X₀.A ⟶ X₀.A, IsMonHom α₀ ∧ α.left ≫ p = p ≫ α₀.left) →
    ∃ (y₀ : I → HdR X₀.A) (yv : I → HdR X.A) (w : I → ℂ), ∀ i,
      y₀ i ≠ 0 ∧ (GlobalTheory.Published.AbelianDeRham.bcMor hp.grp).Corr (y₀ i) (yv i) ∧ U.IsCMVec i (yv i) (w i) ∧ w i ≠ 0 ∧
        IsAlgebraic ℚ (w i / a i) := by
  atlas_forward_decl GlobalTheory.CMEigen.exists_algebraic_eigenvectors
end

section
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMEigen

theorem polForm_bc {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R] [CommRing R']
    (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {p : X'.A.left ⟶ X.A.left}
    (hX : X'.IsPullBy X (spMap σ) p) (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) p) (c : 𝔠.elt)
    {ψ : LinearMap.BilinForm R (HdR X.A)} (hψ : IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ) :
    ∃ ψ' : LinearMap.BilinForm R' (HdR X'.A), IsPolForm (dp0 R') (𝟙 _) X'.A (X'.diag c) ψ' ∧
      ∀ x x' y y', m.Corr x x' → m.Corr y y' → ψ' x' y' = σ (ψ x y) := by
  obtain ⟨ψ', ⟨n, a, b, hch, he⟩, h'⟩ :=
    IsPolForm.pull_comp m (X.isLB c) (π := (lift (𝟙 X.A) (𝟙 X.A)).left) (L := X.P c) hψ
  obtain ⟨φ₂, hsq, hiso⟩ := hX.pol
  have e : (lift (𝟙 X'.A) (𝟙 X'.A)).left ≫ φ₂ = p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left := by
    apply Limits.pullback.hom_ext
    · change _ ≫ (fst X.A X.A).left = _ ≫ (fst X.A X.A).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst]
      simp
    · change _ ≫ (snd X.A X.A).left = _ ≫ (snd X.A X.A).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd]
      simp
  have hI : LBIso (X'.diag c) ((X.P c).pull (p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso (hiso c) _ e.symm
  exact ⟨ψ', ⟨n, a, b, (isChern_existsUnique_and_iso _ _ _ _ _).2 _ _ (pull_isLB (X.isLB c) _)
    (pull_isLB (X'.isLB c) _) hI.symm _ hch, he⟩, h'⟩

theorem corr_inj {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} (hσ : Function.Injective σ)
    {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A'] {b : Sp R' ⟶ Sp R} {q : A'.left ⟶ A.left}
    {m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ b q} {x y : HdR A} {x' : HdR A'}
    (hx : m.Corr x x') (hy : m.Corr y x') : x = y :=
  LinearMap.ext fun c ↦ hσ ((hx c).symm.trans (hy c))

theorem corr_smul {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
    {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A'] {b : Sp R' ⟶ Sp R} {q : A'.left ⟶ A.left}
    {m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ b q} {x : HdR A} {x' : HdR A'}
    (hx : m.Corr x x') (r : R) : m.Corr (r • x) (σ r • x') := fun c ↦ by
  simp only [LinearMap.smul_apply, smul_eq_mul, hx c, map_mul]

theorem isAlg_emb {E : Type} [Field E] [NumberField E] (τ : E →+* ℂ) (x : E) : τ x ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic x).algHom τ.toRatAlgHom

set_option maxHeartbeats 1000000 in

theorem eigen_ops : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
    (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
    (U : Unif φ L 0 X) (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ), IsCMType φ →
    X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    (∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom ∧ a i ≠ 0) →
    (∀ b : E, (∀ x ∈ L, b * x ∈ L) → ∃ α : X.A ⟶ X.A, IsMonHom α ∧
      ∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
    (∀ (b : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
      ∃ α₀ : X₀.A ⟶ X₀.A, IsMonHom α₀ ∧ α.left ≫ p = p ≫ α₀.left) →
    ∃ (N : I → Module.End Qb (HdR X₀.A))
      (m : GrpMor (dp0 Qb) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap Qb ℂ) (spMap (algebraMap Qb ℂ)) p)
      (ψ : LinearMap.BilinForm ℂ (HdR X.A)) (yv : I → HdR X.A) (w : I → ℂ),
      IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ ∧ admitted X₀ N ∧
      ∀ i, U.IsCMVec i (yv i) (w i) ∧ w i ≠ 0 ∧ IsAlgebraic ℚ (w i / a i) ∧
        ∀ x₀ x, m.Corr x₀ x → m.Corr (N i x₀) ((ψ.flip (yv i)).smulRight (yv i) x) := by
  intro hPC hDR hDC E _ _ _ I _ φ L 𝔠 X₀ X p U v₀ v a hφ hp hv hex hdesc
  obtain ⟨y₀, yv, w, hy⟩ := GlobalTheory.T.cm_period_transcendence_relation hPC hDR hDC E I φ L 𝔠 X₀ X p U v₀ v a hp hφ hv hex hdesc
  have m := GlobalTheory.Published.AbelianDeRham.bcMor hp.grp
  have hne : ∀ i, y₀ i ≠ 0 := fun i ↦ (hy i).1
  replace hy : ∀ i, m.Corr (y₀ i) (yv i) ∧ U.IsCMVec i (yv i) (w i) ∧ w i ≠ 0 ∧ IsAlgebraic ℚ (w i / a i) :=
    fun i ↦ (hy i).2
  have hσ : Function.Injective (algebraMap Qb ℂ) := Subtype.val_injective
  obtain ⟨ψ₀, hψ₀⟩ := GlobalTheory.T.polarization_form_exists_free_de_rham hDR.1 X₀ U.c
  obtain ⟨ψ, hψ, hψc⟩ := polForm_bc (algebraMap Qb ℂ) hp m U.c hψ₀

  have eig : ∀ i (b : 𝓞 (FR E)) (β : Qb), algebraMap Qb ℂ β = φ i ((b : FR E) : E) →
      act (dp0 Qb) (𝟙 _) X₀.rm b (y₀ i) = β • y₀ i := by
    intro i b β hβ
    haveI := X₀.rm.hom b
    haveI := X.rm.hom b
    have h1 : m.Corr (act (dp0 Qb) (𝟙 _) X₀.rm b (y₀ i)) (push (dp0 ℂ) (𝟙 _) (X.rm.act b) (yv i)) := by
      rw [act_apply]
      exact GrpMor.Corr.push (m := m) m (X₀.rm.act b) (X.rm.act b) (hp.act b).symm (hy i).1
    have h2 : push (dp0 ℂ) (𝟙 _) (X.rm.act b) (yv i) = algebraMap Qb ℂ β • yv i := by
      rw [hβ]
      exact (hy i).2.1.1 _ (X.rm.act b) fun w' ↦ U.act b w'
    rw [h2] at h1
    exact corr_inj hσ h1 (corr_smul (hy i).1 β)
  have eigβ : ∀ i (b : 𝓞 (FR E)), ∃ β : Qb, algebraMap Qb ℂ β = φ i ((b : FR E) : E) := fun i b ↦
    ⟨⟨_, isAlg_emb (φ i) _⟩, rfl⟩

  have orth : ∀ (c : 𝔠.elt) (ψ' : LinearMap.BilinForm Qb (HdR X₀.A)),
      IsPolForm (dp0 Qb) (𝟙 _) X₀.A (X₀.diag c) ψ' → ∀ i j, ψ' (y₀ i) (y₀ j) = 0 := by
    intro c ψ' hψ' i j
    by_cases hij : i = j
    · subst hij; exact hψ'.isAlt _
    obtain ⟨b, hb⟩ := GlobalTheory.T.exists_ne_of_isCMType_of_ne φ hφ i j hij
    obtain ⟨βi, hβi⟩ := eigβ i b
    obtain ⟨βj, hβj⟩ := eigβ j b
    have := GlobalTheory.T.polarization_form_ring_action_symmetric hDR hDC X₀ c ψ' hψ' b (y₀ i) (y₀ j)
    rw [eig i b βi hβi, eig j b βj hβj, LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul] at this
    have hne' : βi ≠ βj := fun e ↦ hb (by rw [← hβi, ← hβj, e])
    have : (βi - βj) * ψ' (y₀ i) (y₀ j) = 0 := by rw [sub_mul, this, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne')
  let N : I → Module.End Qb (HdR X₀.A) := fun i ↦ (ψ₀.flip (y₀ i)).smulRight (y₀ i)
  have hN : ∀ i x, N i x = ψ₀ x (y₀ i) • y₀ i := fun _ _ ↦ rfl
  refine ⟨N, m, ψ, yv, w, hψ, ⟨?_, ?_, ?_⟩, fun i ↦ ⟨(hy i).2.1, (hy i).2.2.1, (hy i).2.2.2, ?_⟩⟩
  · intro i b
    obtain ⟨β, hβ⟩ := eigβ i b
    refine LinearMap.ext fun x ↦ ?_
    change N i (act (dp0 Qb) (𝟙 _) X₀.rm b x) = act (dp0 Qb) (𝟙 _) X₀.rm b (N i x)
    rw [hN, hN, GlobalTheory.T.polarization_form_ring_action_symmetric hDR hDC X₀ U.c ψ₀ hψ₀, eig i b β hβ, LinearMap.map_smul, map_smul, eig i b β hβ, smul_smul,
      smul_eq_mul, mul_comm]
  · intro i j
    refine LinearMap.ext fun x ↦ ?_
    change N i (N j x) = 0
    rw [hN, hN, LinearMap.map_smul₂, orth U.c ψ₀ hψ₀ j i, smul_zero, zero_smul]
  · intro c ψ' hψ'
    refine ⟨fun i x y ↦ ?_, fun i j x y ↦ ?_⟩
    · rw [hN, hN, LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
      have h0 : (ψ₀ (y₀ i)) (y₀ i) = 0 := hψ₀.isAlt (y₀ i)
      have h0' : (ψ' (y₀ i)) (y₀ i) = 0 := hψ'.isAlt (y₀ i)
      have hr := GlobalTheory.T.cm_periods_algebraic_nonzero hPC hDR E I φ L 𝔠 X₀ X p U hφ hp i (y₀ i) (hne i) (eig i) (ψ₀ (y₀ i)) (ψ' (y₀ i))
        h0 h0' (fun b β hβ z ↦ ⟨by
          rw [← GlobalTheory.T.polarization_form_ring_action_symmetric hDR hDC X₀ U.c ψ₀ hψ₀, eig i b β hβ, LinearMap.map_smul₂, smul_eq_mul], by
          rw [← GlobalTheory.T.polarization_form_ring_action_symmetric hDR hDC X₀ c ψ' hψ', eig i b β hβ, LinearMap.map_smul₂, smul_eq_mul]⟩) x y
      have a1 : ψ₀ x (y₀ i) = - ψ₀ (y₀ i) x := (LinearMap.IsAlt.neg hψ₀.isAlt (y₀ i) x).symm
      have a2 : ψ₀ y (y₀ i) = - ψ₀ (y₀ i) y := (LinearMap.IsAlt.neg hψ₀.isAlt (y₀ i) y).symm
      have a3 : ψ' x (y₀ i) = - ψ' (y₀ i) x := (LinearMap.IsAlt.neg hψ'.isAlt (y₀ i) x).symm
      rw [a1, a2, a3]
      linear_combination -hr
    · rw [hN, hN, LinearMap.map_smul₂, LinearMap.map_smul, orth c ψ' hψ' i j]
      simp
  · intro x₀ x hx
    have h1 := corr_smul (m := m) (hy i).1 (ψ₀ x₀ (y₀ i))
    rw [← hψc x₀ x (y₀ i) (yv i) hx (hy i).1] at h1
    exact h1

end GlobalTheory.CMEigen
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_differentials_algebraic : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
    (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
    (U : Unif φ L 0 X) (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ), IsCMType φ →
    X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    (∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom ∧ a i ≠ 0) →
    (∀ b : E, (∀ x ∈ L, b * x ∈ L) → ∃ α : X.A ⟶ X.A, IsMonHom α ∧
      ∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
    (∀ (b : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
      ∃ α₀ : X₀.A ⟶ X₀.A, IsMonHom α₀ ∧ α.left ≫ p = p ≫ α₀.left) →
    ∃ (N : I → Module.End Qb (HdR X₀.A))
      (m : GrpMor (dp0 Qb) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap Qb ℂ) (spMap (algebraMap Qb ℂ)) p)
      (ψ : LinearMap.BilinForm ℂ (HdR X.A)) (yv : I → HdR X.A) (w : I → ℂ),
      IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ ∧ admitted X₀ N ∧
      ∀ i, U.IsCMVec i (yv i) (w i) ∧ w i ≠ 0 ∧ IsAlgebraic ℚ (w i / a i) ∧
        ∀ x₀ x, m.Corr x₀ x → m.Corr (N i x₀) ((ψ.flip (yv i)).smulRight (yv i) x) := by
  atlas_forward_decl GlobalTheory.CMEigen.eigen_ops
end
