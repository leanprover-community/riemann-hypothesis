import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProjectiveBundleOfLatticeIsProjOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProjectiveBundlePointsOfRationalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedFrameFamilyLongerFlagGenericLine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueProjectiveBundleFlagRefinement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagRefinementBundleCompStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyFlagRefinementBundleOfGoodModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReducedCartierDivisorOfSncClosedStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomRangeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenpartsFrameFamilyOverVarietyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameStableOfIsLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenFrameBasePointLiftsUniqueFlagSpaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietiesComponentsSmoothGenericFibre

section
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle

theorem ProjBundle.affCover (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (J : Type) [Fintype J] [DecidableEq J]
    (EE : M.Lat J) (s : J → Ω') (h : ProjBundle M EE M' φ f s) : AffCover M M' φ f (Fintype.card J - 1) := by
  refine ⟨h.hom, fun z' => ?_⟩
  obtain ⟨U₀, b, hz, hb, hE⟩ := EE.loc (f z')
  obtain ⟨W, hW, hzW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := U₀) hz
  obtain ⟨hc, hch⟩ := h.chart W b hW ⟨_, hzW⟩ fun z hzz => hE z (hle hzz)
  obtain ⟨i, hi⟩ := hc z' hzW
  obtain ⟨U, hU, hUe, hR⟩ := hch i hi.1
  have hcard : Fintype.card {j // j ≠ i} = Fintype.card J - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  let e : Fin (Fintype.card J - 1) ≃ {j // j ≠ i} := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ y, y ∈ U ↔ f y ∈ W ∧ M'.Div ((b.map φ).mulVec s) i y := fun y =>
    Set.ext_iff.1 hUe y
  refine ⟨U, W, fun k => (b.map φ).mulVec s (e k).1 / (b.map φ).mulVec s i, hU, hW, (hmem z').2 ⟨hzW, hi⟩,
    fun y hy => ((hmem y).1 hy).1, fun P hP => ?_, ?_⟩
  · apply MvPolynomial.rename_injective e e.injective
    rw [map_zero]
    refine (h.gen b hb i).2 _ ?_
    rw [MvPolynomial.eval₂_rename]
    exact hP
  · rw [hR]
    refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_mono (Set.union_subset_union_right _ ?_))
    · rintro x (hx | ⟨j, rfl⟩)
      · exact Algebra.subset_adjoin (Or.inl hx)
      · by_cases hj : j = i
        · subst hj
          show _ / _ ∈ _
          rw [div_self hi.1]
          exact one_mem _
        · refine Algebra.subset_adjoin (Or.inr ⟨e.symm ⟨j, hj⟩, ?_⟩)
          simp only [Equiv.apply_symm_apply]
    · rintro _ ⟨k, rfl⟩
      exact ⟨(e k).1, rfl⟩

end GlobalTheory.FlagBundle
end

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineSpaceCoveredMorphism : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (J : Type) [Fintype J] [DecidableEq J] (EE : M.Lat J) (s : J → Ω'), ProjBundle M EE M' φ f s → AffCover M M' φ f (Fintype.card J - 1) := by
  atlas_forward_decl GlobalTheory.FlagBundle.ProjBundle.affCover
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

theorem affSmooth_mvPolynomial (R : Type) [CommRing R] [Nontrivial R] (r : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension r R (MvPolynomial (Fin r) R) := by
  have : Algebra.IsStandardSmooth R (MvPolynomial (Fin r) R) :=
    Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential.2
      ⟨inferInstance, _, KaehlerDifferential.mvPolynomialBasis R _, by
        rintro _ ⟨i, rfl⟩
        exact ⟨MvPolynomial.X i, (KaehlerDifferential.mvPolynomialBasis_apply R _ i).symm⟩⟩
  exact (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth _).2 (by
    rw [rank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis R _), Fintype.card_fin])

theorem affSmooth_of_range_eq {R S K : Type} [CommRing R] [Nontrivial R] [CommRing S] [CommRing K] {r : ℕ}
    (ψ : R →+* S) (j : S →+* K) (hj : Function.Injective j) (t : Fin r → K)
    (hg : Function.Injective (MvPolynomial.eval₂Hom (j.comp ψ) t))
    (h : (MvPolynomial.eval₂Hom (j.comp ψ) t).range = j.range) :
    ψ.IsStandardSmoothOfRelativeDimension r := by
  let g := MvPolynomial.eval₂Hom (j.comp ψ) t
  let e : MvPolynomial (Fin r) R ≃+* S :=
    (RingEquiv.ofBijective g.rangeRestrict
      ⟨fun _ _ h => hg (congrArg Subtype.val h), g.rangeRestrict_surjective⟩).trans
      ((RingEquiv.subringCongr h).trans (RingEquiv.ofBijective j.rangeRestrict
        ⟨fun _ _ h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩).symm)
  have he : ∀ P, j (e P) = g P := fun P =>
    congrArg Subtype.val ((RingEquiv.ofBijective j.rangeRestrict
        ⟨fun _ _ h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩).apply_symm_apply _)
  have : ψ = e.toRingHom.comp (algebraMap R (MvPolynomial (Fin r) R)) :=
    RingHom.ext fun a => hj (by
      show _ = j (e (MvPolynomial.C a))
      rw [he]
      exact (MvPolynomial.eval₂Hom_C (j.comp ψ) t a).symm)
  rw [this]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _ e
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap _).2 (affSmooth_mvPolynomial R r))

variable {F : Type} [Field F] {Ω Ω' : Type} [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']

theorem AffCover.smoothOfRelativeDimension {M : RatModel F Ω} {M' : RatModel F Ω'} {φ : Ω →ₐ[F] Ω'}
    {f : M'.Z ⟶ M.Z} {r : ℕ} (h : AffCover M M' φ f r) : SmoothOfRelativeDimension r f := by
  refine ⟨fun z => ?_⟩
  obtain ⟨U, W, t, hU, hW, hz, hUW, hind, hR⟩ := h.2 z
  have e : U ≤ f ⁻¹ᵁ W := hUW
  have nU : (U : Set M'.Z).Nonempty := ⟨z, hz⟩
  have nW : (W : Set M.Z).Nonempty := ⟨f z, hUW z hz⟩
  have : Nontrivial Γ(M.Z, W) := (M.res W nW).domain_nontrivial
  have hc : (M'.res U nU).comp (f.appLE W U e).hom = (φ : Ω →+* Ω').comp (M.res W nW) := RingHom.ext fun a => by
    show M'.res U nU _ = φ (M.res W nW a)
    rw [M.res_apply, M'.res_apply, ← h.1.valF_app nW a]
    exact M'.valF_resG e nU (f.app W a)
  refine ⟨W, hW, U, hU, hz, e, affSmooth_of_range_eq _ (M'.res U nU) (M'.res_injective U nU) t ?_ ?_⟩
  · rw [hc, injective_iff_map_eq_zero]
    intro P hP
    apply MvPolynomial.map_injective _ (M.res_injective W nW)
    rw [map_zero]
    apply hind
    rw [MvPolynomial.eval₂_map]
    exact hP
  · rw [hc, M'.range_res, hR]
    have hm : ∀ a, (φ : Ω →+* Ω').comp (M.res W nW) a ∈ φ '' (M.ringOn W : Set Ω) := fun a =>
      ⟨_, (RatModel.mem_ringOn_iff_exists nW).2 ⟨a, (M.res_apply W nW a).symm⟩, rfl⟩
    have hm' : ∀ x ∈ M.ringOn W,
        φ x ∈ (MvPolynomial.eval₂Hom ((φ : Ω →+* Ω').comp (M.res W nW)) t).range := fun x hx => by
      obtain ⟨a, rfl⟩ := (RatModel.mem_ringOn_iff_exists nW).1 hx
      exact ⟨MvPolynomial.C a, by rw [MvPolynomial.eval₂Hom_C, ← M.res_apply W nW]; rfl⟩
    apply le_antisymm
    · rintro _ ⟨P, rfl⟩
      rw [Subalgebra.mem_toSubring]
      induction P using MvPolynomial.induction_on with
      | C a => rw [MvPolynomial.eval₂Hom_C]; exact Algebra.subset_adjoin (Or.inl (hm a))
      | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
      | mul_X P i hP =>
        rw [map_mul, MvPolynomial.eval₂Hom_X']
        exact mul_mem hP (Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩))
    · intro x hx
      rw [Subalgebra.mem_toSubring] at hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        rcases hx with ⟨y, hy, rfl⟩ | ⟨i, rfl⟩
        · exact hm' y hy
        · exact ⟨MvPolynomial.X i, MvPolynomial.eval₂Hom_X' _ _ i⟩
      | algebraMap c => rw [← φ.commutes]; exact hm' _ (Subalgebra.algebraMap_mem _ c)
      | add x y _ _ hx hy => exact add_mem hx hy
      | mul x y _ _ hx hy => exact mul_mem hx hy

theorem affCover_smooth (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r d : ℕ)
    (h : AffCover M M' φ f r) (hd : SmoothOfRelativeDimension d M.s) :
    SmoothOfRelativeDimension (d + r) M'.s := by
  have := h.smoothOfRelativeDimension
  rw [← h.1.inducedModelMorphism_comp_structureMap, Nat.add_comm]
  infer_instance

end GlobalTheory.FlagBundle
end
end

section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineSpaceCovered_smoothOfRelativeDimension_add : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r d : ℕ), AffCover M M' φ f r → SmoothOfRelativeDimension d M.s → SmoothOfRelativeDimension (d + r) M'.s := by
  first | exact @GlobalTheory.FlagBundle.affCover_smooth | exact GlobalTheory.FlagBundle.affCover_smooth | (intros; apply GlobalTheory.FlagBundle.affCover_smooth <;> assumption)
end

section
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle.AffRad

theorem C_dvd_of_C_dvd_pow {A σ : Type} [CommRing A] {g : A} (hg : ∀ (x : A) (n : ℕ), g ∣ x ^ n → g ∣ x)
    {P : MvPolynomial σ A} {n : ℕ} (h : MvPolynomial.C g ∣ P ^ n) : MvPolynomial.C g ∣ P := by
  have hq : ∀ a : A, Ideal.Quotient.mk (Ideal.span {g}) a = 0 ↔ g ∣ a := fun a => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [MvPolynomial.C_dvd_iff_map_hom_eq_zero _ g hq] at h ⊢
  rw [map_pow] at h
  have hn := (MvPolynomial.isNilpotent_iff).1 ⟨n, h⟩
  ext i
  obtain ⟨k, hk⟩ := hn i
  rw [MvPolynomial.coeff_map] at hk ⊢
  rw [← map_pow, hq] at hk
  rw [MvPolynomial.coeff_zero, hq]
  exact hg _ _ hk

theorem exists_div_of_mem_O {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
    {V : M.Z.Opens} (hV : IsAffineOpen V) {z : M.Z} (hz : z ∈ V) {x : Ω} (hx : x ∈ M.O z) :
    ∃ a b : Ω, a ∈ M.ringOn V ∧ b ∈ M.ringOn V ∧ b ≠ 0 ∧ b⁻¹ ∈ M.O z ∧ x * b = a := by
  obtain ⟨U, f, hU, rfl⟩ := hx
  have hne : (V : Set M.Z).Nonempty := ⟨z, hz⟩
  obtain ⟨g, hgU, hwg⟩ := hV.exists_basicOpen_le (V := U) ⟨z, hU⟩ hz
  have hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hwg⟩
  have := hV.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g (resG M.Z hgU f)
  have h1 := congrArg (M.res _ hg) ha
  have h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t :=
    fun t => M.res_resG (M.Z.basicOpen_le g) hg t
  rw [map_mul, map_pow, h2, h2, RatModel.res_resG, RatModel.res_apply, RatModel.res_apply,
    RatModel.res_apply] at h1
  have hu := (RatModel.isUnit_O_iff _).1 ((RatModel.isUnit_valF_iff hz g).2 hwg)
  refine ⟨_, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩,
    pow_mem ((RatModel.mem_ringOn_iff_exists hne).2 ⟨g, rfl⟩) n, pow_ne_zero _ hu.1, ?_, h1⟩
  rw [← inv_pow]
  exact pow_mem hu.2 n

theorem keepsRad_of_affCover (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r : ℕ)
    (h : AffCover M M' φ f r) : KeepsRad M M' φ f := by
  rintro z' g ⟨hg0, hgO, hg⟩
  obtain ⟨hf, hc⟩ := h
  obtain ⟨U, W, t, hU, -, hz, hW, hinj, hR⟩ := hc z'
  have hφ0 : φ g ≠ 0 := (map_ne_zero φ).2 hg0
  refine ⟨hφ0, hf.map_mem_O hgO, fun x n hx hxn => ?_⟩
  let A := (M.O (f z')).toSubring
  let ψ : MvPolynomial (Fin r) A →+* Ω' := MvPolynomial.eval₂Hom ((φ : Ω →+* Ω').comp A.subtype) t
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro P hP
    have := hinj (MvPolynomial.map A.subtype P) (by rw [MvPolynomial.eval₂_map]; exact hP)
    exact (map_eq_zero_iff _ (MvPolynomial.map_injective _ A.subtype_injective)).1 this
  have hO : ∀ P, ψ P ∈ M'.O z' := fun P => by
    induction P using MvPolynomial.induction_on with
    | C a => rw [MvPolynomial.eval₂Hom_C]; exact hf.map_mem_O a.2
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      exact mul_mem hp (RatModel.ringOn_le_O hz (hR ▸ Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)))
  have hS : ∀ y ∈ M'.ringOn U, ∃ P, ψ P = y := by
    intro y hy
    rw [hR] at hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with ⟨w, hw, rfl⟩ | ⟨i, rfl⟩
      · exact ⟨MvPolynomial.C ⟨w, RatModel.ringOn_le_O (hW z' hz) hw⟩, MvPolynomial.eval₂Hom_C _ _ _⟩
      · exact ⟨MvPolynomial.X i, MvPolynomial.eval₂Hom_X' _ _ _⟩
    | algebraMap c =>
      exact ⟨MvPolynomial.C ⟨algebraMap F Ω c, (M.O (f z')).algebraMap_mem c⟩,
        (MvPolynomial.eval₂Hom_C _ _ _).trans (φ.commutes c)⟩
    | add a b _ _ ha hb => obtain ⟨P, rfl⟩ := ha; obtain ⟨Q, rfl⟩ := hb; exact ⟨P + Q, map_add _ _ _⟩
    | mul a b _ _ ha hb => obtain ⟨P, rfl⟩ := ha; obtain ⟨Q, rfl⟩ := hb; exact ⟨P * Q, map_mul _ _ _⟩
  have hrad : ∀ (y : A) (k : ℕ), (⟨g, hgO⟩ : A) ∣ y ^ k → (⟨g, hgO⟩ : A) ∣ y := by
    rintro y k ⟨c, hc⟩
    have e : (y : Ω) ^ k = g * c := congrArg Subtype.val hc
    have := hg y k y.2 (by rw [e, mul_div_cancel_left₀ _ hg0]; exact c.2)
    exact ⟨⟨_, this⟩, Subtype.ext (mul_div_cancel₀ _ hg0).symm⟩
  have hC : ψ (MvPolynomial.C ⟨g, hgO⟩) = φ g := MvPolynomial.eval₂Hom_C _ _ _
  obtain ⟨a, b, ha, hb, hb0, hbi, e1⟩ := exists_div_of_mem_O hU hz hx
  obtain ⟨c, d, hc, hd, hd0, hdi, e2⟩ := exists_div_of_mem_O hU hz hxn
  obtain ⟨a, rfl⟩ := hS a ha
  obtain ⟨b, rfl⟩ := hS b hb
  obtain ⟨c, rfl⟩ := hS c hc
  obtain ⟨d, rfl⟩ := hS d hd
  have hdvd : MvPolynomial.C (⟨g, hgO⟩ : A) ∣ (a * d) ^ (n + 1) := by
    refine ⟨c * b ^ n * a * d ^ n, hψ ?_⟩
    simp only [map_mul, map_pow, hC, ← e2]
    rw [← e1]
    field_simp
    ring
  obtain ⟨Q, hQ⟩ := C_dvd_of_C_dvd_pow hrad hdvd
  have e3 := congrArg ψ hQ
  rw [map_mul, map_mul, hC, ← e1] at e3
  have e4 : x / φ g = ψ Q * (ψ b)⁻¹ * (ψ d)⁻¹ := by
    field_simp
    linear_combination e3
  rw [e4]
  exact mul_mem (mul_mem (hO Q) hbi) hdi

end GlobalTheory.FlagBundle.AffRad
end

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preservesRadicalPrincipalIdeals_of_affineSpaceCovered : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r : ℕ), AffCover M M' φ f r → KeepsRad M M' φ f := by
  atlas_forward_decl GlobalTheory.FlagBundle.AffRad.keepsRad_of_affCover
end

section
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

noncomputable section

namespace GlobalTheory.FlagBundle.QuotDual

variable {ι : Type} {m k : ι → ℕ} {K : Type} [Field K]

abbrev restBlock (k : ι → ℕ) (τ : ι) (g : Mat m K) : Matrix (Rest m k τ) (Rest m k τ) K :=
  (g τ).submatrix Subtype.val Subtype.val

theorem restBlock_mul {O : Subring K} (τ : ι) (g : Mat m K) {h : Mat m K} (hh : Par k O h) :
    restBlock k τ (g * h) = restBlock k τ g * restBlock k τ h := by
  ext i j
  simp only [Matrix.submatrix_apply, Pi.mul_apply, Matrix.mul_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter fun l : Fin (m τ) => k τ ≤ (l : ℕ)) (by simp)
    (fun l => g τ i.1 l * h τ l j.1)]
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun l _ hl => ?_).symm
  have hl' : (l : ℕ) < k τ := by simpa using hl
  have hj := j.2
  rw [(hh τ).2.2.2 l j.1 hl' (by show (l : ℕ) < j.1; omega), mul_zero]

theorem restBlock_one (τ : ι) : restBlock k τ (1 : Mat m K) = 1 :=
  Matrix.submatrix_one _ Subtype.val_injective

theorem restBlock_inv_mul {O : Subring K} (τ : ι) {g : Mat m K} (hg : Par k O g) :
    restBlock k τ g⁻¹ * restBlock k τ g = 1 := by
  rw [← restBlock_mul τ _ hg, Mat.inv_mul hg.det_ne, restBlock_one]

theorem restBlock_inv {O : Subring K} (τ : ι) {g : Mat m K} (hg : Par k O g) :
    (restBlock k τ g)⁻¹ = restBlock k τ g⁻¹ :=
  Matrix.inv_eq_left_inv (restBlock_inv_mul τ hg)

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]

theorem span_mul_le {J : Type} [Fintype J] (O : Subalgebra F Ω) (P B : Matrix J J Ω) (hP : ∀ i j, P i j ∈ O) :
    Submodule.span O (Set.range (P * B)) ≤ Submodule.span O (Set.range B) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun l => ⟨P i l, hP i l⟩, ?_⟩
  ext j
  simp [Matrix.mul_apply, Finset.sum_apply, Subalgebra.smul_def]

variable {M : RatModel F Ω} {S : Fr M m k} {A₀ : Mat m Ω}

theorem par_generic (h₀ : A₀ ∈ S.S (genericPoint M.Z)) {z : M.Z} {A : Mat m Ω} (hA : A ∈ S.S z) :
    Par k (M.O (genericPoint M.Z)).toSubring (A * A₀⁻¹) :=
  (Fr.mem_iff h₀).1 (Fr.mem_genericPoint hA)

theorem det_dualBlock_ne (τ : ι) (h₀ : A₀ ∈ S.S (genericPoint M.Z)) {z : M.Z} {A : Mat m Ω} (hA : A ∈ S.S z) :
    (dualBlock k τ A₀ A).det ≠ 0 := by
  have h := par_generic h₀ hA
  have e := congrArg Matrix.det (restBlock_inv_mul τ h)
  rw [Matrix.det_mul, Matrix.det_one] at e
  show ((restBlock k τ (A * A₀⁻¹))⁻¹).transpose.det ≠ 0
  rw [Matrix.det_transpose, restBlock_inv τ h]
  exact left_ne_zero_of_mul_eq_one e

theorem span_dualBlock_le (τ : ι) (h₀ : A₀ ∈ S.S (genericPoint M.Z)) {z : M.Z} {A A' : Mat m Ω} (hA : A ∈ S.S z)
    (hA' : A' ∈ S.S z) : Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A')) ≤
      Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)) := by
  have hg := (Fr.mem_iff hA).1 hA'
  have e : A' * A₀⁻¹ = (A' * A⁻¹) * (A * A₀⁻¹) := by
    rw [← mul_assoc, mul_assoc A', Mat.inv_mul (Fr.det_ne hA), mul_one]
  have e2 : dualBlock k τ A₀ A' = (restBlock k τ (A' * A⁻¹)⁻¹).transpose * dualBlock k τ A₀ A := by
    show ((restBlock k τ (A' * A₀⁻¹))⁻¹).transpose = _ * ((restBlock k τ (A * A₀⁻¹))⁻¹).transpose
    rw [e, restBlock_mul τ _ (par_generic h₀ hA), Matrix.mul_inv_rev, Matrix.transpose_mul, restBlock_inv τ hg]
  rw [e2]
  exact span_mul_le _ _ _ fun i j => (hg.inv τ).1 _ _

theorem span_dualBlock_eq (τ : ι) (h₀ : A₀ ∈ S.S (genericPoint M.Z)) {z : M.Z} {A A' : Mat m Ω} (hA : A ∈ S.S z)
    (hA' : A' ∈ S.S z) : Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A')) =
      Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)) :=
  le_antisymm (span_dualBlock_le τ h₀ hA hA') (span_dualBlock_le τ h₀ hA' hA)

theorem exists_lat_dualBlock (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (ι : Type)
    (m k : ι → ℕ) (S : Fr M m k) (τ : ι) (A₀ : Mat m Ω) (h₀ : A₀ ∈ S.S (genericPoint M.Z)) :
    ∃ EE : M.Lat (Rest m k τ), ∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧
      EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)) := by
  refine ⟨⟨fun z => Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ (S.nonempty z).some)), fun z => ?_⟩,
    fun z A hA => ⟨det_dualBlock_ne τ h₀ hA, span_dualBlock_eq τ h₀ hA (S.nonempty z).some_mem⟩⟩
  obtain ⟨U, A, hz, hA, hU⟩ := S.loc z
  have hm : ∀ z' ∈ U, A ∈ S.S z' := fun z' hz' => (hU z' hz' A).2 (by rw [Mat.mul_inv hA]; exact Par.one)
  exact ⟨U, dualBlock k τ A₀ A, hz, det_dualBlock_ne τ h₀ (hm z hz),
    fun z' hz' => span_dualBlock_eq τ h₀ (hm z' hz') (S.nonempty z').some_mem⟩

end GlobalTheory.FlagBundle.QuotDual
end
end

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_dualBasisQuotientFrameBlock : ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (ι : Type) (m k : ι → ℕ) (S : Fr M m k) (τ : ι) (A₀ : Mat m Ω), A₀ ∈ S.S (genericPoint M.Z) → ∃ EE : M.Lat (Rest m k τ), ∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧ EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)) := by
  atlas_forward_decl GlobalTheory.FlagBundle.QuotDual.exists_lat_dualBlock
end

section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_variety_flagRefinementBundle_of_goodModel : ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) (ι : Type) (m k : ι → ℕ) (S : Fr M m k), Good M d → ∃ (Y : GlobalTheory.ProjVar.Var F) (φ : Ω →ₐ[F] Y.Fn) (f : Y.X ⟶ M.Z) (S' : Fr (ratOf Y) m k), Y.dim = d ∧ Refines S S' φ f := by
  first | exact @GlobalTheory.FlagBundle.exists_var_refines | exact GlobalTheory.FlagBundle.exists_var_refines | (intros; apply GlobalTheory.FlagBundle.exists_var_refines <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

noncomputable section

namespace GlobalTheory.FlagBundle.DivPull

variable {F : Type} [Field F] {B Y : GlobalTheory.ProjVar.Var F} {φ : B.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ B.X}

theorem regAt_map (h : (ratOf B).IsHom (ratOf Y) φ f) {y : Y.X} {g : B.Fn} (hg : RegAt (f y) g) :
    RegAt y (φ g) :=
  mem_O_ratOf.1 (h.map_mem_O (z := y) (mem_O_ratOf.2 hg))

theorem unitAt_map (h : (ratOf B).IsHom (ratOf Y) φ f) {y : Y.X} {g : B.Fn} (hg : UnitAt (f y) g) :
    UnitAt y (φ g) :=
  (unitAt_iff ((map_ne_zero φ).2 hg.ne_zero)).2
    ⟨regAt_map h hg.regAt, by rw [← map_inv₀]; exact regAt_map h hg.inv.regAt⟩

theorem unitAt_of_map (h : (ratOf B).IsHom (ratOf Y) φ f) {y : Y.X} {g : B.Fn} (hg : RegAt (f y) g)
    (hu : UnitAt y (φ g)) : UnitAt (f y) g := by
  have h0 : g ≠ 0 := (map_ne_zero φ).1 hu.ne_zero
  exact (unitAt_iff h0).2 ⟨hg, mem_O_ratOf.1
    (h.inv_mem_O (z := y) (mem_O_ratOf.2 hg) h0 (mem_O_ratOf.2 hu.inv.regAt))⟩

theorem exists_pullback (h : (ratOf B).IsHom (ratOf Y) φ f) (D : B.Dv) :
    ∃ D' : Y.Dv, ∀ (y : Y.X) (g : B.Fnˣ), D.IsEqn (f y) g →
      D'.IsEqn y (Units.map (φ : B.Fn →* Y.Fn) g) := by
  choose e he using fun y : Y.X => D.exists_isEqn (f y)
  have key : ∀ (y : Y.X) (g : B.Fnˣ), D.IsEqn (f y) g →
      germOf y (Units.map (φ : B.Fn →* Y.Fn) (e y)) = germOf y (Units.map (φ : B.Fn →* Y.Fn) g) := by
    intro y g hg
    rw [germOf_eq_iff]
    have := unitAt_map h ((he y).iff_unitAt.1 hg)
    rw [map_div₀] at this
    exact this
  refine ⟨show cartierGroup Y.X from ⟨fun y => germOf y (Units.map (φ : B.Fn →* Y.Fn) (e y)), fun y => ?_⟩, key⟩
  obtain ⟨U, hU, g, hg⟩ := D.exists_isEqn_nhds (f y)
  exact ⟨f ⁻¹ᵁ U, hU, Units.map (φ : B.Fn →* Y.Fn) g, fun z hz => key z g (hg _ hz)⟩

theorem exists_reduced_pullback : ∀ (F : Type) [Field F] (B Y : GlobalTheory.ProjVar.Var F) (φ : B.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ B.X) (D : B.Dv), (ratOf B).IsHom (ratOf Y) φ f → KeepsRad (ratOf B) (ratOf Y) φ f → D.Eff → (∀ (y : B.X) (g : B.Fnˣ), D.IsEqn y g → ∀ (a : B.Fn) (n : ℕ), RegAt y a → RegAt y (a ^ n / g) → RegAt y (a / g)) → ∃ D' : Y.Dv, D'.Eff ∧ (∀ y, y ∈ D'.supp ↔ f y ∈ D.supp) ∧ ∀ (y : Y.X) (g : Y.Fnˣ), D'.IsEqn y g → ∀ (a : Y.Fn) (n : ℕ), RegAt y a → RegAt y (a ^ n / g) → RegAt y (a / g) := by
  intro F _ B Y φ f D h hk hD hr
  obtain ⟨D', hD'⟩ := exists_pullback h D
  refine ⟨D', CartierDiv.eff_iff.2 fun y g hg => ?_, fun y => ?_, fun y g hg a n ha hn => ?_⟩
  · obtain ⟨e, he⟩ := D.exists_isEqn (f y)
    have h1 := ((hD' y e he).iff_unitAt.1 hg).regAt.mul (regAt_map h (CartierDiv.eff_iff.1 hD _ e he))
    have h0 : φ e ≠ 0 := (map_ne_zero φ).2 e.ne_zero
    have e1 : (g : Y.Fn) / φ e * φ e = g := div_mul_cancel₀ _ h0
    exact e1 ▸ h1
  · obtain ⟨e, he⟩ := D.exists_isEqn (f y)
    change ¬ D'.IsEqn y 1 ↔ ¬ D.IsEqn (f y) 1
    rw [not_iff_not, (hD' y e he).iff_unitAt, he.iff_unitAt, Units.val_one, Units.val_one, one_div, one_div]
    constructor
    · intro hu
      have := hu.inv
      rw [inv_inv] at this
      exact (unitAt_of_map h (CartierDiv.eff_iff.1 hD _ e he) this).inv
    · intro hu
      have := hu.inv
      rw [inv_inv] at this
      exact (unitAt_map h this).inv
  · obtain ⟨e, he⟩ := D.exists_isEqn (f y)
    have hR := hk y e ⟨e.ne_zero, mem_O_ratOf.2 (CartierDiv.eff_iff.1 hD _ e he), fun x m hx hm =>
      mem_O_ratOf.2 (hr _ e he x m (mem_O_ratOf.1 hx) (mem_O_ratOf.1 hm))⟩
    have hu : UnitAt y ((g : Y.Fn) / φ e) := (hD' y e he).iff_unitAt.1 hg
    have h0 : φ e ≠ 0 := (map_ne_zero φ).2 e.ne_zero
    have hg0 : (g : Y.Fn) ≠ 0 := g.ne_zero
    have e1 : a ^ n / g * ((g : Y.Fn) / φ e) = a ^ n / φ e := by field_simp
    have e2 : a / φ e * ((g : Y.Fn) / φ e)⁻¹ = a / g := by field_simp
    have h2 : RegAt y (a / φ e) :=
      mem_O_ratOf.1 (hR.2.2 a n (mem_O_ratOf.2 ha) (mem_O_ratOf.2 (e1 ▸ hn.mul hu.regAt)))
    exact e2 ▸ h2.mul hu.inv.regAt

end GlobalTheory.FlagBundle.DivPull
end
end

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reduced_effective_cartierDivisor_pullback : ∀ (F : Type) [Field F] (B Y : GlobalTheory.ProjVar.Var F) (φ : B.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ B.X) (D : B.Dv), (ratOf B).IsHom (ratOf Y) φ f → KeepsRad (ratOf B) (ratOf Y) φ f → D.Eff → (∀ (y : B.X) (g : B.Fnˣ), D.IsEqn y g → ∀ (a : B.Fn) (n : ℕ), RegAt y a → RegAt y (a ^ n / g) → RegAt y (a / g)) → ∃ D' : Y.Dv, D'.Eff ∧ (∀ y, y ∈ D'.supp ↔ f y ∈ D.supp) ∧ ∀ (y : Y.X) (g : Y.Fnˣ), D'.IsEqn y g → ∀ (a : Y.Fn) (n : ℕ), RegAt y a → RegAt y (a ^ n / g) → RegAt y (a / g) := by
  atlas_forward_decl GlobalTheory.FlagBundle.DivPull.exists_reduced_pullback
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam.TieUp

theorem exists_lift {ι : Type} {m k : ι → ℕ} {R K : Type} [CommRing R] [Field K] (a : R →+* K)
    (ha : Function.Injective a) {O : Subring K} (hO : ∀ x ∈ O, ∃ r, a r = x) {G : Mat m K} (hG : Par k O G) :
    ∃ G' : Mat m R, G'.map a = G ∧ ∀ τ, IsUnit (G' τ).det := by
  have h1 : ∀ τ i j, ∃ r, a r = G τ i j := fun τ i j => hO _ ((hG τ).1 i j)
  choose G' hG' using h1
  let G'' : Mat m R := fun τ => Matrix.of (G' τ)
  have e : G''.map a = G := by
    funext τ; ext i j; exact hG' τ i j
  refine ⟨G'', e, fun τ => ?_⟩
  obtain ⟨r, hr⟩ := hO _ (hG τ).2.2.1
  have hd : a (G'' τ).det = (G τ).det := by
    rw [← e]; exact a.map_det (G'' τ)
  refine IsUnit.of_mul_eq_one r (ha ?_)
  rw [map_mul, hd, hr, map_one, mul_inv_cancel₀ (hG.det_ne τ)]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (B Y : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z) (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn) (k : (E →+* ℂ) → ℕ) (S' : Fr (ratOf Y) Dw.mult k) (φ : B.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ B.X), Tied e B j f₀ S A₀ → Refines S S' φ f → ∃ (g₀ : EigFrame Z (constF e Y) (genericPt Y ≫ (f ≫ j) ≫ genι Z)) (A₁ : Mat Dw.mult Y.Fn), Tied e Y (f ≫ j) g₀ S' A₁ ∧ f₀.Coord (φ : B.Fn →+* Y.Fn) g₀ (A₁ * (A₀.map φ)⁻¹) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e B Y j f₀ S A₀ k S' φ f hT hR
  obtain ⟨A₁, hA₁⟩ := S'.nonempty (genericPoint Y.X)
  have hA₀d : ∀ τ, (A₀ τ).det ≠ 0 := Fr.det_ne hT.1
  have hA₁d : ∀ τ, (A₁ τ).det ≠ 0 := Fr.det_ne hA₁
  have hmapd : ∀ {A : Mat Dw.mult B.Fn}, (∀ τ, (A τ).det ≠ 0) →
      ∀ τ, (A.map (φ : B.Fn →+* Y.Fn) τ).det ≠ 0 := fun {A} hA τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hA τ)
  have hgen : genericPt Y ≫ f = spMap (φ : B.Fn →+* Y.Fn) ≫ genericPt B := hR.hom
  have hx : genericPt Y ≫ (f ≫ j) ≫ genι Z = spMap (φ : B.Fn →+* Y.Fn) ≫ genericPt B ≫ j ≫ genι Z := by
    rw [Category.assoc, ← Category.assoc, hgen, Category.assoc]
  have hc : constF e Y = (φ : B.Fn →+* Y.Fn).comp (constF e B) :=
    RingHom.ext fun a => (φ.commutes _).symm
  have hst₀ : f₀.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f₀ inferInstance
  obtain ⟨g₀, hg₀⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ f₀ Y.Fn (constF e Y)
    (genericPt Y ≫ (f ≫ j) ≫ genι Z) (φ : B.Fn →+* Y.Fn) inferInstance hst₀ hx hc).2
    (A₁ * (A₀.map (φ : B.Fn →+* Y.Fn))⁻¹) fun τ => by
      rw [Pi.mul_apply, Matrix.det_mul, Pi.inv_apply, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      exact Ne.isUnit (mul_ne_zero (hA₁d τ) (inv_ne_zero (hmapd hA₀d τ)))
  refine ⟨g₀, A₁, ⟨hA₁, fun y A' hA' => ?_⟩, hg₀⟩
  obtain ⟨A, hA⟩ := S.nonempty (f y)
  obtain ⟨φ₁, fA, hfA⟩ := hT.2 (f y) A hA
  have hAd : ∀ τ, (A τ).det ≠ 0 := Fr.det_ne hA
  have hA'd : ∀ τ, (A' τ).det ≠ 0 := Fr.det_ne hA'
  let aY : Y.X.presheaf.stalk y →+* Y.Fn := algebraMap (Y.X.presheaf.stalk y) Y.X.functionField
  let aB : B.X.presheaf.stalk (f y) →+* B.Fn := algebraMap (B.X.presheaf.stalk (f y)) B.X.functionField
  let σ : B.X.presheaf.stalk (f y) →+* Y.X.presheaf.stalk y := (f.stalkMap y).hom
  have hcomp : (φ : B.Fn →+* Y.Fn).comp aB = aY.comp σ :=
    RingHom.ext fun a => map_algebraMap_stalk hR.hom y a
  obtain ⟨G, hG, hGd⟩ := exists_lift aY (IsFractionRing.injective (Y.X.presheaf.stalk y) Y.X.functionField)
    (fun x hx => mem_O_ratOf.1 hx) (hR.sub y A' hA' A hA)
  have hstA : fA.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ fA inferInstance
  have hσ : spMap σ ≫ stalkPt B (f y) = stalkPt Y y ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
  have hx' : stalkPt Y y ≫ (f ≫ j) ≫ genι Z = spMap σ ≫ stalkPt B (f y) ≫ j ≫ genι Z := by
    rw [Category.assoc, ← Category.assoc, ← hσ, Category.assoc]
  obtain ⟨f', hf'⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ fA (Y.X.presheaf.stalk y) (σ.comp φ₁)
    (stalkPt Y y ≫ (f ≫ j) ≫ genι Z) σ inferInstance hstA hx' rfl).2 G hGd
  have hst' : f'.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f' inferInstance
  have haY : spMap aY ≫ stalkPt Y y = genericPt Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)
  have hx'' : genericPt Y ≫ (f ≫ j) ≫ genι Z = spMap aY ≫ stalkPt Y y ≫ (f ≫ j) ≫ genι Z := by
    rw [← haY, Category.assoc]
  have hc' : constF e Y = aY.comp (σ.comp φ₁) := by
    rw [← RingHom.comp_assoc, ← hcomp, RingHom.comp_assoc, hc, hfA.2.1]
  obtain ⟨T, hTc, -⟩ := ((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ f' Y.Fn (constF e Y)
    (genericPt Y ≫ (f ≫ j) ≫ genι Z) aY inferInstance hst' hx'' hc').1 g₀).1
  have h1 := GlobalTheory.ShFam.CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f' _ _ _ g₀ σ aY G T inferInstance hf' hTc
  have h2 := GlobalTheory.ShFam.CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f₀ _ _ _ g₀ aB (φ : B.Fn →+* Y.Fn) _ _
    inferInstance hfA hg₀
  rw [hcomp] at h2
  have hu := ((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ fA Y.Fn (constF e Y)
    (genericPt Y ≫ (f ≫ j) ≫ genι Z) (aY.comp σ) inferInstance hstA h1.1 h1.2.1).1 g₀).1.unique h1 h2
  have hG' : G.map aY = A' * (A.map (φ : B.Fn →+* Y.Fn))⁻¹ := hG
  rw [hG', Mat.map_mul, Mat.map_inv, ← mul_assoc, ← mul_assoc, mul_assoc A₁, Mat.inv_mul (hmapd hA₀d), mul_one] at hu
  have hT' : T = A₁ * A'⁻¹ := by
    have h3 := congrArg (fun M => M * A.map (φ : B.Fn →+* Y.Fn) * A'⁻¹) hu
    rwa [mul_assoc (T * A'), mul_assoc A₁, Mat.inv_mul (hmapd hAd), mul_one, mul_one, mul_assoc,
      Mat.mul_inv hA'd, mul_one] at h3
  exact ⟨σ.comp φ₁, f', hT' ▸ hTc⟩

end GlobalTheory.ShFam.TieUp
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautologicalFamily_refinement_compatible_lieAlgebraFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (B Y : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z) (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn) (k : (E →+* ℂ) → ℕ) (S' : Fr (ratOf Y) Dw.mult k) (φ : B.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ B.X), Tied e B j f₀ S A₀ → Refines S S' φ f → ∃ (g₀ : EigFrame Z (constF e Y) (genericPt Y ≫ (f ≫ j) ≫ genι Z)) (A₁ : Mat Dw.mult Y.Fn), Tied e Y (f ≫ j) g₀ S' A₁ ∧ f₀.Coord (φ : B.Fn →+* Y.Fn) g₀ (A₁ * (A₀.map φ)⁻¹) := by
  atlas_forward_decl GlobalTheory.ShFam.TieUp.main
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam.GradedDiv

section Diag

variable {ι : Type} {m : ι → ℕ} {K : Type} [Field K] {O O' : Subring K} {g h : Mat m K}

theorem diag_mul (hg : Par m O g) (hh : Par m O' h) (τ : ι) (i : Fin (m τ)) :
    (g * h) τ i i = g τ i i * h τ i i := by
  rw [Pi.mul_apply, Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun l _ hl => ?_) (by simp)
  rcases lt_or_gt_of_ne hl with h' | h'
  · rw [(hh τ).2.2.2 l i l.2 h', mul_zero]
  · rw [(hg τ).2.2.2 i l i.2 h', zero_mul]

theorem diag_ne_zero (hg : Par m O g) (τ : ι) (i : Fin (m τ)) : g τ i i ≠ 0 := by
  have := diag_mul hg hg.inv τ i
  rw [Mat.mul_inv hg.det_ne] at this
  exact left_ne_zero_of_mul_eq_one (this.symm.trans (Matrix.one_apply_eq i))

end Diag

theorem exists_div {F : Type} [Field F] {Y : GlobalTheory.ProjVar.Var F} {ι : Type} {m : ι → ℕ} (S : Fr (ratOf Y) m m)
    {A₀ : Mat m Y.Fn} (h₀ : A₀ ∈ S.S (genericPoint Y.X)) :
    ∃ gr : ∀ τ, Fin (m τ) → Y.Dv, ∀ y : Y.X, ∃ A ∈ S.S y, ∃ t : ∀ τ, Fin (m τ) → Y.Fnˣ,
      (∀ τ i, (A₀ * A⁻¹) τ i i = t τ i) ∧ (∀ τ i k, i < k → (A₀ * A⁻¹) τ i k = 0) ∧
        ∀ τ i, (gr τ i).IsEqn y (t τ i) := by
  have hP : ∀ {y : Y.X} {A : Mat m Y.Fn}, A ∈ S.S y →
      Par m ((ratOf Y).O (genericPoint Y.X)).toSubring (A₀ * A⁻¹) := fun hA =>
    (Fr.mem_iff (Fr.mem_genericPoint hA)).1 h₀
  let t : ∀ {y : Y.X} {A : Mat m Y.Fn}, A ∈ S.S y → ∀ τ, Fin (m τ) → Y.Fnˣ := fun hA τ i =>
    Units.mk0 _ (diag_ne_zero (hP hA) τ i)
  have hreg : ∀ {y : Y.X} {A A' : Mat m Y.Fn} (hA : A ∈ S.S y) (hA' : A' ∈ S.S y) τ i,
      RegAt y ((t hA' τ i : Y.Fn) / t hA τ i) := fun {y A A'} hA hA' τ i => by
    have hg := (Fr.mem_iff hA').1 hA
    have e := diag_mul (hP hA) hg τ i
    rw [← mul_assoc, mul_assoc A₀, Mat.inv_mul (Fr.det_ne hA), mul_one] at e
    have e' : (t hA' τ i : Y.Fn) / t hA τ i = (A * A'⁻¹) τ i i := by
      rw [div_eq_iff (t hA τ i).ne_zero, mul_comm]
      exact e
    rw [e']
    exact mem_O_ratOf.1 ((hg τ).1 i i)
  have hgerm : ∀ {y : Y.X} {A A' : Mat m Y.Fn} (hA : A ∈ S.S y) (hA' : A' ∈ S.S y) τ i,
      germOf y (t hA τ i) = germOf y (t hA' τ i) := fun {y A A'} hA hA' τ i => by
    rw [germOf_eq_iff, unitAt_iff (div_ne_zero (t hA' τ i).ne_zero (t hA τ i).ne_zero), inv_div]
    exact ⟨hreg hA hA' τ i, hreg hA' hA τ i⟩
  choose A hA using fun y : Y.X => S.nonempty y
  refine ⟨fun τ i => show cartierGroup Y.X from ⟨fun y => germOf y (t (hA y) τ i), fun y => ?_⟩,
    fun y => ⟨A y, hA y, t (hA y), fun _ _ => rfl, fun τ i k hik => (hP (hA y) τ).2.2.2 i k i.2 hik,
      fun _ _ => rfl⟩⟩
  obtain ⟨U, B, hy, hB, hU⟩ := S.loc y
  have hBm : ∀ z ∈ U, B ∈ S.S z := fun z hz => (hU z hz B).2 (by rw [Mat.mul_inv hB]; exact Par.one)
  exact ⟨U, hy, t (hBm y hy) τ i, fun z hz => hgerm (hA z) (hBm z hz) τ i⟩

theorem exists_gr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (Y : GlobalTheory.ProjVar.Var F) (π : Y.X ⟶ gen Z) (f₀ : EigFrame Z (constF e Y) (genericPt Y ≫ π ≫ genι Z)) (S : Fr (ratOf Y) Dw.mult Dw.mult) (A₀ : Mat Dw.mult Y.Fn), Tied e Y π f₀ S A₀ → ∃ gr : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Dv, ∀ y : Y.X, ∃ (φ : c.F →+* Y.X.presheaf.stalk y) (f : EigFrame Z φ (stalkPt Y y ≫ π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Fnˣ), f.Tri (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) f₀ t ∧ ∀ τ i, (gr τ i).IsEqn y (t τ i) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e Y π f₀ S A₀ hT
  obtain ⟨gr, hgr⟩ := exists_div S hT.1
  refine ⟨gr, fun y => ?_⟩
  obtain ⟨A, hA, t, h1, h2, h3⟩ := hgr y
  obtain ⟨φ, f, hf⟩ := hT.2 y A hA
  exact ⟨φ, f, t, (f.tri_iff _ f₀ t).2 ⟨_, hf, h1, h2⟩, h3⟩

end GlobalTheory.ShFam.GradedDiv
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_graded_line_divisors_full_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (Y : GlobalTheory.ProjVar.Var F) (π : Y.X ⟶ gen Z) (f₀ : EigFrame Z (constF e Y) (genericPt Y ≫ π ≫ genι Z)) (S : Fr (ratOf Y) Dw.mult Dw.mult) (A₀ : Mat Dw.mult Y.Fn), Tied e Y π f₀ S A₀ → ∃ gr : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Dv, ∀ y : Y.X, ∃ (φ : c.F →+* Y.X.presheaf.stalk y) (f : EigFrame Z φ (stalkPt Y y ≫ π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Fnˣ), f.Tri (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) f₀ t ∧ ∀ τ i, (gr τ i).IsEqn y (t τ i) := by
  first | exact @GlobalTheory.ShFam.GradedDiv.exists_gr | exact GlobalTheory.ShFam.GradedDiv.exists_gr | (intros; apply GlobalTheory.ShFam.GradedDiv.exists_gr <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam

theorem exists_frPt_ptF_over_of_eigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (L : Type) [Field L] (φ : c.F →+* L) (z : Sp L ⟶ Xo.XF c) (x : Sp L ⟶ Z.X) (g : EigFrame Z φ x), z ≫ pullback.snd _ _ = spMap φ → z ≫ Z.jQ ≫ genι Z = x → letI := φ.toAlgebra; ∃ y : FrPt Xo c L, GlobalTheory.AllWt.ptF y = z ∧ ∀ τ i, ∃ w : Sp (DualNumber L) ⟶ Z.oF.t.G.left, w ≫ Z.oF.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ z ∧ w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = g.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z L _ φ z x g hs hx
  letI := φ.toAlgebra
  obtain ⟨y, w, hy, hw⟩ := OpenReg.exists_frPt_of_eigFrame (Z := Z) z hs hx g
  refine ⟨y, pullback.hom_ext ?_ ?_, fun τ i => ⟨w τ i, hw τ i⟩⟩
  · exact (pullback.lift_fst _ _ _).trans hy
  · exact (pullback.lift_snd _ _ _).trans hs.symm

end GlobalTheory.ShFam
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framed_point_over_of_lie_eigenspace_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (L : Type) [Field L] (φ : c.F →+* L) (z : Sp L ⟶ Xo.XF c) (x : Sp L ⟶ Z.X) (g : EigFrame Z φ x), z ≫ pullback.snd _ _ = spMap φ → z ≫ Z.jQ ≫ genι Z = x → letI := φ.toAlgebra; ∃ y : FrPt Xo c L, GlobalTheory.AllWt.ptF y = z ∧ ∀ τ i, ∃ w : Sp (DualNumber L) ⟶ Z.oF.t.G.left, w ≫ Z.oF.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ z ∧ w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = g.v τ i := by
  first | exact @GlobalTheory.ShFam.exists_frPt_ptF_over_of_eigFrame | exact GlobalTheory.ShFam.exists_frPt_ptF_over_of_eigFrame | (intros; apply GlobalTheory.ShFam.exists_frPt_ptF_over_of_eigFrame <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_varieties_components_smooth_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F), FnAlgClosed Xo c → SmoothOfRelativeDimension Dw.dim (genStr Z) → ∃ (B : Comp Xo c → GlobalTheory.ProjVar.Var F) (j : ∀ i, (B i).X ⟶ gen Z), (∀ i, IsOpenImmersion (j i) ∧ (B i).dim = Dw.dim ∧ j i ≫ genStr Z ≫ spMap e.toRingHom = (B i).str ∧ ∀ p ∈ i.1, Z.jQ p ∈ Set.range (j i)) ∧ ∀ z : gen Z, ∃! i, z ∈ Set.range (j i) := by
  first | exact @GlobalTheory.GenFibreComp.exists_vars | exact GlobalTheory.GenFibreComp.exists_vars | (intros; apply GlobalTheory.GenFibreComp.exists_vars <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.FlagDimSum

theorem mul_add_choose_two (p q : ℕ) :
    p * q + p.choose 2 + q.choose 2 = (p + q).choose 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 : (q + 1).choose 2 = q + q.choose 2 := by
      rw [Nat.choose_succ_succ' q 1, Nat.choose_one_right]
    have h2 : (p + q + 1).choose 2 = (p + q) + (p + q).choose 2 := by
      rw [Nat.choose_succ_succ' (p + q) 1, Nat.choose_one_right]
    rw [← add_assoc, h1, h2, ← ih]
    ring

theorem dim_add_sum_choose : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H), Dw.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 =
      Module.finrank ℚ E / 2 * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) := by
  intro E _ _ _ H Dw
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ => τ (H.rt : E) = H.rt0)
  rw [Finset.card_univ, Embeddings.card] at h1
  have h2 := GlobalTheory.PeriodCoord.card_cmType H
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h2
  have h3 : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E) := by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
  have h4 : (Finset.univ.filter (fun τ : E →+* ℂ => ¬ τ (H.rt : E) = H.rt0)).card =
      Module.finrank ℚ E / 2 := by
    omega
  have hs : ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 =
      Module.finrank ℚ E / 2 * (Dw.p.choose 2 + Dw.q.choose 2) := by
    simp_rw [Datum.mult, apply_ite (fun n : ℕ => n.choose 2)]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, h4, h2, smul_eq_mul, smul_eq_mul, mul_add]
  rw [hs, Datum.dim, ← Nat.choose_two_right, ← mul_add_choose_two, mul_assoc, ← mul_add, ← add_assoc]

end GlobalTheory.FlagDimSum
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_space_dimension_eq_sum_choose : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H), Dw.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 = Module.finrank ℚ E / 2 * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) := by
  first | exact @GlobalTheory.FlagDimSum.dim_add_sum_choose | exact GlobalTheory.FlagDimSum.dim_add_sum_choose | (intros; apply GlobalTheory.FlagDimSum.dim_add_sum_choose <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

theorem step {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) {ι : Type} [Finite ι]
    {m k : ι → ℕ} (S : Fr M m k) (hM : Good M d) (τ : ι) (hk : k τ < m τ) (k' : ι → ℕ) (h1 : k' τ = k τ + 1)
    (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ') :
    ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra F Ω') (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z)
      (S' : Fr M' m k'), Good M' (d + (m τ - k τ - 1)) ∧ Refines S S' φ f := by
  obtain ⟨A₀, hA₀⟩ := S.nonempty (genericPoint M.Z)
  obtain ⟨EE, hE⟩ := GlobalTheory.T.exists_lattice_dualBasisQuotientFrameBlock F Ω M ι m k S τ A₀ hA₀
  have : Nonempty (Rest m k τ) := ⟨⟨⟨k τ, hk⟩, le_rfl⟩⟩
  obtain ⟨Ω', _, _, M', φ, f, s, hP, hpr⟩ := GlobalTheory.T.exists_projectiveBundleOfLattice_isProjOver F Ω M _ EE hM.1
  have hc : Fintype.card (Rest m k τ) = m τ - k τ := by
    rw [Fintype.card_subtype, ← Fin.card_Ici ⟨k τ, hk⟩]
    exact congrArg _ (Finset.ext fun j => by simp [Fin.le_def])
  have hA := GlobalTheory.T.isAffineSpaceCoveredMorphism F Ω Ω' M M' φ f _ EE s hP
  rw [hc] at hA
  have hp := GlobalTheory.T.projective_bundle_points_of_rational_model F Ω Ω' M M' φ f _ EE s hP
  obtain ⟨S', hS'⟩ := GlobalTheory.T.exists_adaptedFrameFamily_longerFlag_genericLine F Ω Ω' M M' φ f ι m k k' S τ hk A₀ EE s h1 h2 hA₀ hE hp
  refine ⟨Ω', _, _, M', φ, f, S', ⟨hpr, GlobalTheory.T.affineSpaceCovered_smoothOfRelativeDimension_add F Ω Ω' M M' φ f _ d hA hM.2.1, GlobalTheory.T.geometricallyIntegral_of_affCover F Ω Ω' M M' φ f _ hA hM.2.2⟩,
    fun τ' => ?_, hP.hom, fun z' A' hA' => ?_, GlobalTheory.T.preservesRadicalPrincipalIdeals_of_affineSpaceCovered F Ω Ω' M M' φ f _ hA,
    GlobalTheory.T.existsUnique_projectiveBundle_flagRefinement F Ω Ω' M M' φ f ι m k k' S S' τ hk A₀ EE s h1 h2 hA₀ hE hp hS'⟩
  · by_cases h : τ' = τ
    · subst h; exact h1 ▸ Nat.le_succ _
    · exact (h2 τ' h).ge
  · rw [hS'] at hA'
    exact hA'.1

theorem tower {F : Type} [Field F] {ι : Type} [Fintype ι] {m : ι → ℕ} (n : ℕ) :
    ∀ {Ω : Type} [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) {k : ι → ℕ} (S : Fr M m k), Good M d → k ≤ m →
      ∑ τ, (m τ - k τ) = n → ∃ (Y : GlobalTheory.ProjVar.Var F) (φ : Ω →ₐ[F] Y.Fn) (f : Y.X ⟶ M.Z) (S' : Fr (ratOf Y) m m),
        Y.dim = d + ∑ τ, (m τ - k τ).choose 2 ∧ Refines S S' φ f := by
  classical
  induction n with
  | zero =>
    intro Ω _ _ M d k S hM hk hn
    obtain rfl : k = m := funext fun τ => le_antisymm (hk τ)
      (Nat.sub_eq_zero_iff_le.1 (Finset.sum_eq_zero_iff.1 hn τ (Finset.mem_univ _)))
    obtain ⟨Y, φ, f, S', h1, h2⟩ := GlobalTheory.T.exists_variety_flagRefinementBundle_of_goodModel F Ω M d ι k k S hM
    exact ⟨Y, φ, f, S', by simpa using h1, h2⟩
  | succ n ih =>
    intro Ω _ _ M d k S hM hk hn
    obtain ⟨τ, -, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hn.trans_ne n.succ_ne_zero)
    have hτ' : k τ < m τ := by omega
    let k' := Function.update k τ (k τ + 1)
    have h1 : k' τ = k τ + 1 := Function.update_self _ _ _
    have h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ' := fun τ' h => Function.update_of_ne h _ _
    obtain ⟨Ω', _, _, M', φ, f, S', hM', hR⟩ := step M d S hM τ hτ' k' h1 h2
    have key : ∀ g : ℕ → ℕ, ∑ t, g (m t - k' t) + g (m τ - k τ) = ∑ t, g (m t - k t) + g (m τ - k τ - 1) := fun g => by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ τ), ← Finset.add_sum_erase _ (fun t => g (m t - k t)) (Finset.mem_univ τ),
        h1, Finset.sum_congr rfl fun t ht => by rw [h2 t (Finset.ne_of_mem_erase ht)], Nat.sub_add_eq]
      ring
    obtain ⟨Y, φ', f', S'', hd, hR'⟩ := ih M' _ S' hM' (fun t => by
      by_cases h : t = τ
      · subst h; rw [h1]; exact hτ'
      · rw [h2 t h]; exact hk t) (by have := key id; simp only [id] at this; omega)
    refine ⟨Y, φ'.comp φ, f' ≫ f, S'', ?_, GlobalTheory.T.isFlagRefinementBundle_comp F Ω Ω' M M' φ f Y.Fn (ratOf Y) φ' f' ι m k k' m S S' S'' hR hR'⟩
    have := key fun a => a.choose 2
    obtain ⟨a, ha⟩ : ∃ a, m τ - k τ = a + 1 := ⟨m τ - k τ - 1, by omega⟩
    rw [ha, Nat.choose_succ_succ' a 1, Nat.choose_one_right, Nat.add_sub_cancel] at this
    rw [hd, ha, Nat.add_sub_cancel]
    simp only [Nat.reduceAdd] at this
    omega

open Limits NumberField Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam

section Component

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
  {F : Type} [Field F] (e : F ≃+* c.F)

theorem genericPoint_mem {B : Scheme.{0}} [IsIntegral B] (j : B ⟶ gen Z) [IsOpenImmersion j] :
    j (genericPoint B) ∈ Set.range Z.jQ := by
  have := Z.jQ_open
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ := Z.jQ_dense.inter_open_nonempty _ j.isOpenEmbedding.isOpen_range ⟨_, genericPoint B, rfl⟩
  exact ((genericPoint_specializes b).map j.continuous).mem_open Z.jQ.isOpenEmbedding.isOpen_range hb

theorem exists_flagCpt (hS : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Z)) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z)
    [IsOpenImmersion j] (hj : j ≫ genStr Z ≫ spMap e.toRingHom = B.str) :
    ∃ (C : FlagCpt Z e) (f : C.Y.X ⟶ B.X), C.π = f ≫ j ∧ C.Y.dim = B.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 ∧
      ∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z) (x' : Sp K ⟶ B.X), x' ≫ j = x →
        x ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g := by
  have := Z.jQ_open
  obtain ⟨f₀, S, A₀, hT⟩ := GlobalTheory.T.exists_lieEigenparts_frame_family_over_variety E H Dw l Xo c O β Z F e B j hj
  obtain ⟨Y, φ, f, S', hd, hR⟩ := tower _ (ratOf B) B.dim S (good_ratOf B) (fun _ => Nat.zero_le _) rfl
  change Y.X ⟶ B.X at f
  obtain ⟨g₀, A₁, hT', hC⟩ := GlobalTheory.T.tautologicalFamily_refinement_compatible_lieAlgebraFrame E H Dw l Xo c O β Z F e B Y j f₀ S A₀ _ S' φ f hT hR
  obtain ⟨gr, hgr⟩ := GlobalTheory.T.exists_graded_line_divisors_full_flag E H Dw l Xo c O β Z F e Y (f ≫ j) g₀ S' A₁ hT'
  have hgen := genericPoint_mem Z j
  obtain ⟨D, hD1, hD2, hD3⟩ := GlobalTheory.T.exists_reduced_cartierDivisor_of_snc_closed (gen Z) B.X j (genBd Z) hS fun h => h hgen
  obtain ⟨D', hD1', hD2', hD3'⟩ := GlobalTheory.T.exists_reduced_effective_cartierDivisor_pullback F B Y φ f D hR.hom hR.rad hD1 hD3
  have hstr : (f ≫ j) ≫ genStr Z ≫ spMap e.toRingHom = Y.str := by
    rw [Category.assoc, hj]; exact hR.hom.inducedModelMorphism_comp_structureMap
  have hrange : Set.range (genericPt Y ≫ f ≫ j) ⊆ Set.range Z.jQ := by
    rintro _ ⟨w, rfl⟩
    have h : genericPt Y ≫ f = spMap φ.toRingHom ≫ genericPt B := hR.hom
    have h' : genericPt B (spMap φ.toRingHom w) = genericPoint B.X := (ratOf B).pt_apply _
    rw [← Category.assoc, h, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h']
    exact hgen
  let z : Sp Y.Fn ⟶ Xo.XF c := IsOpenImmersion.lift Z.jQ (genericPt Y ≫ f ≫ j) hrange
  have hz : z ≫ Z.jQ = genericPt Y ≫ f ≫ j := IsOpenImmersion.lift_fac _ _ _
  have hzs : z ≫ pullback.snd _ _ = spMap (constF e Y) := by
    have h1 : genericPt Y ≫ Y.str = spMap (algebraMap F Y.Fn) := (ratOf Y).pt_s
    have h2 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
      refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
      exact CommRingCat.hom_ext (RingHom.ext fun a => e.apply_symm_apply a)
    rw [← Z.jQ_over, ← Category.assoc, hz, ← Category.comp_id (pullback.snd Z.s (spMap β)), ← h2]
    refine Eq.trans ?_ ((congrArg (· ≫ spMap e.symm.toRingHom) h1).trans (Spec.map_comp _ _).symm)
    rw [← hstr]
    simp only [Category.assoc]
  obtain ⟨y0, hy1, hy2⟩ := GlobalTheory.T.exists_framed_point_over_of_lie_eigenspace_frame E H Dw l Xo c O β Z Y.Fn (constF e Y) z _ g₀ hzs (by
    rw [← Category.assoc, hz]; simp only [Category.assoc])
  let C : FlagCpt Z e :=
    { Y := Y, π := f ≫ j, π_str := hstr, y0 := y0, f0 := g₀, y0_x := by rw [hy1, hz], flagComponentFramedPoint_frame := by rw [hy1]; exact hy2, gr := gr,
      gr_spec := hgr, bd := D', bd_eff := hD1', bd_red := hD3'
      bd_supp := fun y => (hD2' y).trans ((hD2 _).trans (by rw [Scheme.Hom.comp_apply])) }
  exact ⟨C, f, rfl, by simpa using hd,
    GlobalTheory.T.eigenFrameBasePoint_lifts_unique_flagSpace E H Dw l Xo c O β Z F e C B j f₀ S A₀ S' A₁ φ f hj rfl hT hT' hC hR⟩

end Component

theorem nonempty_flagTor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ k, (U.X k).dom.Nonempty) → FnAlgClosed Xo c → SmoothOfRelativeDimension Dw.dim (genStr Z) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Z) → Nonempty (FlagTor Z e U) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U hσ hU hne hF hsm hS
  obtain ⟨q, hq⟩ := GlobalTheory.UnifComp.exists_equiv_comp E H Dw l Xo c σ N U hσ hU hne hF
  obtain ⟨B, j, hB, hcov⟩ := GlobalTheory.T.exists_varieties_components_smooth_genericFibre E H Dw l Xo c O β Z F e hF hsm
  have key := fun i : U.Comp =>
    haveI := (hB (q i)).1
    exists_flagCpt Z e hS (B (q i)) (j (q i)) (hB (q i)).2.2.1
  choose C f hπ hdim hl using key
  have lift : ∀ (K : Type) [Field K] (x : Sp K ⟶ gen Z) (i : Comp Xo c),
      x (IsLocalRing.closedPoint K) ∈ Set.range (j i) → ∃ x' : Sp K ⟶ (B i).X, x' ≫ j i = x := fun K _ x i h => by
    have := (hB i).1
    refine ⟨IsOpenImmersion.lift (j i) x ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨w, rfl⟩
    rwa [show w = IsLocalRing.closedPoint K from Subsingleton.elim (α := PrimeSpectrum K) _ _]
  refine ⟨⟨C, fun k => ?_, fun K _ _ χ x hx g => ?_, fun i x s => ?_⟩⟩
  · rw [hdim, (hB _).2.1, GlobalTheory.T.flag_space_dimension_eq_sum_choose E H Dw, hU.1]
  · obtain ⟨i₀, hi, hi'⟩ := hcov (x (IsLocalRing.closedPoint K))
    obtain ⟨i, rfl⟩ := q.surjective i₀
    obtain ⟨x', hx'⟩ := lift K x _ hi
    obtain ⟨p, ⟨hp1, hp2⟩, hp3⟩ := hl i K χ x x' hx' hx g
    refine ⟨⟨i, p⟩, ⟨by rw [hπ, ← Category.assoc, hp1, hx'], hp2⟩, ?_⟩
    rintro ⟨i', p'⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    rw [hπ, ← Category.assoc] at h1
    obtain rfl : i' = i := q.injective (hi' _ ⟨(p' ≫ f i') (IsLocalRing.closedPoint K), by
      rw [← h1]; exact (Scheme.Hom.comp_apply _ _ _).symm⟩)
    have := (hB (q i')).1
    rw [hp3 p' ⟨(cancel_mono (j (q i'))).1 (h1.trans hx'.symm), h2⟩]
  · let x₀ : Sp ℂ ⟶ gen Z := (GlobalTheory.AllWt.ptF (S := CAt σ) (U.un i x) ≫ Z.jQ :)
    have hx₀ : x₀ ≫ genStr Z = spMap σ :=
      (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) Z.jQ_over).trans (pullback.lift_snd _ _ _))
    obtain ⟨x', hx'⟩ := lift ℂ x₀ (q i) ((hB _).2.2.2 _ (hq i x _))
    obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z _ _ x₀ hx₀
    obtain ⟨p, ⟨hp1, -⟩, -⟩ := hl i _ _ x₀ x' hx' hx₀ g
    have : p ≫ (C i).π = x₀ := by rw [hπ, ← Category.assoc, hp1, hx']
    exact ⟨p s, (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun t : Sp ℂ ⟶ gen Z => t s) this)⟩

end GlobalTheory.FlagBundle
end
end
