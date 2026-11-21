import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPointDimOne
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTriplePullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasisStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenySumOfCmHoms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueHomExtensionSemiAbelian

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM GlobalTheory.EigenSplit

namespace GlobalTheory.GramAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem ex_smul (T : PAT H (Sp ℂ)) {s : 𝓞 E} {r : ℂ}
    (hdet : ∀ τ : 𝓞 E →+* ℂ, τ s ≠ r → LieMult T.t.act (𝟙 (Sp ℂ)) τ 0)
    (u : HolUnif T.pol.A T.pol.L T.pol.g) (h1 : ∀ v, IsTangent v → ∃! w, u.IsDiff w v)
    (h2 : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) (z : Fin T.pol.g → ℂ) :
    u.ex (r • z) = u.ex z ≫ T.t.act.act s := by
  classical
  have hid : IsGrpPullback T.t.G T.t.G (𝟙 _) (𝟙 T.t.G.left) :=
    @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl T.t.G) (inferInstanceAs (IsMonHom (𝟙 T.t.G)))
  have he₀ : PointUnif.IsExp (y := 𝟙 (Sp ℂ)) (G := T.t.G) u.ex :=
    PointUnif.isExp_push hid u h1 h2 (MulEquiv.refl _) fun x => (Category.comp_id _).symm
  obtain ⟨ρ, hρ⟩ := he₀.exists_rep T.t.act u.Λ u.discrete u.ker fun a => by
    obtain ⟨F, hF, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom T.t.G T.t.G T.ab T.ab _ _ _ _ u u h1 h2
      (T.t.act.act a) (T.t.act.hom a)
    exact ⟨F, hF⟩
  refine Eq.trans (congrArg u.ex ?_) (hρ s z)
  have hs := PointUnif.isSplitting_embeddings (E := E)
  rw [← sum_proj hs ρ z, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  have hm := proj_mem hs ρ φ z
  by_cases hφ : φ.comp (algebraMap (𝓞 E) E) s = r
  · rw [mem_eigenSub.1 hm, hφ]
  · have h0 := Submodule.finrank_eq_zero.1 (he₀.finrank_eigenSub _ ρ hρ (hdet _ hφ))
    rw [h0, Submodule.mem_bot] at hm
    rw [hm, map_zero, smul_zero]

theorem weilEq_one_complex (A A' B : PAT H (Sp ℂ)) {r : ℂ} (hr : r ^ 2 = -(H.d : ℂ))
    (hA : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ≠ r → LieMult A.t.act (𝟙 (Sp ℂ)) τ 0)
    (hA' : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ≠ -r → LieMult A'.t.act (𝟙 (Sp ℂ)) τ 0)
    {f : A.t.G ⟶ B.t.G} {f' : A'.t.G ⟶ B.t.G} (hf : Serre.IsLinearHom A.t.act B.t.act f)
    (hf' : Serre.IsLinearHom A'.t.act B.t.act f') :
    WeilEq B.t.PP.L f f' A.t.PP.L (𝟙 _) (1 : A'.t.G ⟶ A.t.G) (𝟙 (Sp ℂ)) := by
  have hT : ThetaUnifAV := thetaUnifAV_all
  have hL : Out.Laws := abelianSchemeLaws_all.1
  obtain ⟨u, HA, χA, -, hu, -⟩ := PureType.exists_isThetaUnif hT A.pol
  obtain ⟨u', HA', χA', -, hu', -⟩ := PureType.exists_isThetaUnif hT A'.pol
  obtain ⟨uB, HB, χB, -, hB, -⟩ := PureType.exists_isThetaUnif hT B.pol
  obtain ⟨-, -, -, -, hA1, hA2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT A.pol _ u HA χA hu
  obtain ⟨-, -, -, -, hA1', hA2', -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT A'.pol _ u' HA' χA' hu'
  obtain ⟨-, -, -, -, hB1, hB2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT B.pol _ uB HB χB hB
  obtain ⟨F, hF, -⟩ := HomLinear.exists_linear_of_isMonHom A.t.G B.t.G A.ab B.ab _ _ _ _ u uB hB1 hB2 f hf.isMonHom
  obtain ⟨F', hF', -⟩ := HomLinear.exists_linear_of_isMonHom A'.t.G B.t.G A'.ab B.ab _ _ _ _ u' uB hB1 hB2 f'
    hf'.isMonHom
  choose ρB hρB using fun s : 𝓞 E => (HomLinear.exists_linear_of_isMonHom B.t.G B.t.G B.ab B.ab _ _ _ _ uB uB hB1 hB2
    (B.t.act.act s) (B.t.act.hom s)).imp fun _ h => h.1
  have hadj : ∀ s z w, hermForm HB (ρB s z) w = hermForm HB z (ρB (H.bar s) w) := fun a =>
    (weilEq_iff_hermForm_eq hT hL B.pol B.pol B.pol B.pol uB uB uB uB HB HB χB χB hB hB (B.t.act.act a) (𝟙 _) (𝟙 _)
      (B.t.act.act (H.bar a)) (ρB a) LinearMap.id LinearMap.id (ρB (H.bar a)) (hρB a)
      (fun _ => (Category.comp_id _).symm) (fun _ => (Category.comp_id _).symm) (hρB _)).1
      (weilEq_of_lamEq hL ℂ B.pol B.pol B.pol B.pol _ _ _ _ (B.t.act.hom a) inferInstance inferInstance
        (B.t.act.hom _) (by
          unfold LamEq
          rw [Category.comp_id, Category.comp_id]
          exact B.t.adj a))
  have hu0 : ∀ {g : ℕ} (M N : (Fin g → ℂ) →ₗ[ℂ] (Fin B.pol.g → ℂ)), (∀ z, uB.ex (M z) = uB.ex (N z)) → M = N :=
    fun M N h => by
      refine sub_eq_zero.1 (PointUnif.linear_eq_zero_of_discrete uB.Λ uB.discrete _ fun z => (uB.ker _).1 ?_)
      have := uB.ex_add ((M - N) z) (N z)
      rw [LinearMap.sub_apply, sub_add_cancel, h] at this
      exact mul_eq_right.1 this.symm
  have e : ∀ z, ρB H.rt (F z) = r • F z := fun z => LinearMap.congr_fun (hu0 (ρB H.rt ∘ₗ F) (r • F) fun z => by
    rw [LinearMap.comp_apply, LinearMap.smul_apply, ← map_smul, hρB, hF, hF, ex_smul A hA u hA1 hA2,
      Category.assoc, Category.assoc]
    exact congrArg _ (hf.comm _).symm) z
  have hA'' : ∀ τ : 𝓞 E →+* ℂ, τ (H.bar H.rt) ≠ r → LieMult A'.t.act (𝟙 (Sp ℂ)) τ 0 := fun τ h =>
    hA' τ fun h' => h (by rw [EigDec.bar_rt, map_neg, h', neg_neg])
  have e' : ∀ z, ρB (H.bar H.rt) (F' z) = r • F' z := fun z =>
    LinearMap.congr_fun (hu0 (ρB (H.bar H.rt) ∘ₗ F') (r • F') fun z => by
      rw [LinearMap.comp_apply, LinearMap.smul_apply, ← map_smul, hρB, hF', hF', ex_smul A' hA'' u' hA1' hA2',
        Category.assoc, Category.assoc]
      exact congrArg _ (hf'.comm _).symm) z
  have hd : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  have hr0 : r ≠ 0 := fun h0 => by
    rw [h0] at hr
    have := congrArg Complex.re hr
    simp at this
    exact H.d_prime.ne_zero this
  have hrc : star r = -r := by
    have h1 := congrArg Complex.re hr
    have h2 := congrArg Complex.im hr
    simp [pow_two] at h1 h2
    have h3 : r.re = 0 := by
      by_contra h
      have : r.im = 0 := by
        have : r.re * r.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left h
      rw [this] at h1
      nlinarith [mul_self_nonneg r.re]
    exact Complex.ext (by simp [h3]) (by simp)
  refine (weilEq_iff_hermForm_eq hT hL A.pol A'.pol B.pol A.pol u u' uB u HB HA χB χA hB hu f f' (𝟙 _) 1 F F'
    LinearMap.id 0 hF hF' (fun _ => (Category.comp_id _).symm) fun z => ?_).2 fun z w => ?_
  · rw [LinearMap.zero_apply, HermWeil.ex_zero]
    exact (MonObj.comp_one _).symm
  · have h := hadj H.rt (F z) (F' w)
    rw [e, e'] at h
    simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, hrc] at h
    have h' : hermForm HB (F z) (F' w) = 0 := by
      refine mul_left_cancel₀ (mul_ne_zero two_ne_zero hr0) ?_
      unfold hermForm
      linear_combination h
    rw [h']
    simp [hermForm]

variable {K : Type} [Field K] [NumberField K]

theorem lamEq_one {ρ : 𝓞 K} (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) (A A' B : PAT H (Sp (𝓞 K))) {m m' : ℕ}
    (hA : HasType H A.t.act ρ m 0) (hA' : HasType H A'.t.act ρ 0 m')
    {f : A.t.G ⟶ B.t.G} {f' : A'.t.G ⟶ B.t.G} (hf : Serre.IsLinearHom A.t.act B.t.act f)
    (hf' : Serre.IsLinearHom A'.t.act B.t.act f') :
    LamEq B.t.PP.L f f' A.t.PP.L (𝟙 _) (1 : A'.t.G ⟶ A.t.G) := by
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hβi : Function.Injective (σ.comp (algebraMap (𝓞 K) K)) := σ.injective.comp (IsFractionRing.injective (𝓞 K) K)
  generalize σ.comp (algebraMap (𝓞 K) K) = β at hβi
  obtain ⟨⟨A₁, m₁, -⟩, h₁⟩ := GlobalTheory.LamT.pat_pullback E H (𝓞 K) ℂ β A
  obtain ⟨⟨A₂, m₂, -⟩, -⟩ := GlobalTheory.LamT.pat_pullback E H (𝓞 K) ℂ β A'
  obtain ⟨⟨B₁, mB, -⟩, hB⟩ := GlobalTheory.LamT.pat_pullback E H (𝓞 K) ℂ β B
  obtain ⟨-, -, wA, hwA⟩ := h₁ A₁ m₁ inferInstance
  obtain ⟨-, -, wB, hwB⟩ := hB B₁ mB inferInstance
  haveI := hf.isMonHom
  haveI := hf'.isMonHom
  haveI := A.ab.comm
  haveI : IsMonHom (1 : A'.t.G ⟶ A.t.G) := LamF.IsogSum.isMonHom_of_points _ fun T a b => by
    simp only [MonObj.comp_one, _root_.mul_one]
  obtain ⟨f₁, hm₁, e₁⟩ := GlobalTheory.PairingFibre.exists_hom m₁.cart mB.cart f
  obtain ⟨f₂, hm₂, e₂⟩ := GlobalTheory.PairingFibre.exists_hom m₂.cart mB.cart f'
  have lin : ∀ {A : PAT H (Sp (𝓞 K))} {A₁ : PAT H (Sp ℂ)} (mA : SABMap A₁.t A.t (spMap β)) (f : A.t.G ⟶ B.t.G)
      (f' : A₁.t.G ⟶ B₁.t.G), Serre.IsLinearHom A.t.act B.t.act f → IsMonHom f' →
      f'.left ≫ mB.φ = mA.φ ≫ f.left → Serre.IsLinearHom A₁.t.act B₁.t.act f' := by
    intro A A₁ mA f f' hf hm e
    refine ⟨hm, fun c => ?_⟩
    apply Over.OverMorphism.ext
    apply mB.cart.1.hom_ext
    · have hc := congrArg CommaMorphism.left (hf.comm c)
      simp only [Over.comp_left] at hc ⊢
      rw [Category.assoc, e, ← Category.assoc, mA.act c, Category.assoc, hc, Category.assoc, mB.act c,
        ← Category.assoc, ← Category.assoc, e]
    · simp only [Over.comp_left, Category.assoc, Over.w]
  have hlie : ∀ {A : PAT H (Sp (𝓞 K))} {A₁ : PAT H (Sp ℂ)} (mA : SABMap A₁.t A.t (spMap β)) (τ : 𝓞 E →+* ℂ) (n : ℕ),
      LieMult A.t.act (spMap β) τ n → LieMult A₁.t.act (𝟙 (Sp ℂ)) τ n := fun {A A₁} mA τ n => by
    have := GlobalTheory.lieMult_iff_of_isGrpPullback mA.cart A₁.t.act A.t.act mA.act (𝟙 (Sp ℂ)) τ n
    rw [Category.id_comp] at this
    exact this.2
  have hβρ : β ρ ^ 2 = -(H.d : ℂ) := by rw [← map_pow, hρ]; simp
  have hτ : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ^ 2 = -(H.d : ℂ) := fun τ => by rw [← map_pow, H.rt_sq]; simp
  have h := weilEq_one_complex A₁ A₂ B₁ hβρ (fun τ h => hlie m₁ τ 0 ((hA ℂ β hβi τ).2 h))
    (fun τ h => hlie m₂ τ 0 ((hA' ℂ β hβi τ).1
      ((sq_eq_sq_iff_eq_or_eq_neg.1 ((hτ τ).trans hβρ.symm)).resolve_right h)))
    (lin m₁ f f₁ hf hm₁ e₁) (lin m₂ f' f₂ hf' hm₂ e₂)
  have e₄ : (1 : A₂.t.G ⟶ A₁.t.G).left ≫ m₁.φ = m₂.φ ≫ (1 : A'.t.G ⟶ A.t.G).left := by
    have a : Geo.Tor.pushPt m₁.cart.1.w (1 : A₂.t.G ⟶ A₁.t.G) = 1 := map_one (Geo.Tor.pushHom m₁.cart _)
    have b : Geo.Tor.pushPt m₂.cart.1.w (𝟙 A₂.t.G) ≫ (1 : A'.t.G ⟶ A.t.G) = 1 := MonObj.comp_one _
    exact (congrArg (·.left) (a.trans b.symm)).trans (congrArg (· ≫ _) (Category.id_comp _))
  have h' := (GlobalTheory.PairingFibre.weilEq_iff (g₁ := 𝟙 _) m₁.cart m₂.cart mB.cart m₁.cart B.t.PP.isLB A.t.PP.isLB
    B₁.t.PP.isLB A₁.t.PP.isLB ⟨wB, hwB.1⟩ ⟨wA, hwA.1⟩ e₁ e₂ (by simp) e₄ (𝟙 (Sp ℂ))).1 h
  rw [Category.id_comp] at h'
  exact (PairingFibre.lamEq_weilEq_over_ring abelianSchemeLaws_all.1 (𝓞 K) A.pol A'.pol B.pol A.pol _ _ _ _
    hf.isMonHom hf'.isMonHom inferInstance inferInstance ℂ β).2 inferInstance hβi h'

variable {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q)

theorem dims : (∀ b, (X.A b).g = Module.finrank ℚ E / 2) ∧ X.B.g = Module.finrank ℚ E / 2 * (p + q) ∧
    0 < Module.finrank ℚ E / 2 := by
  have key : ∀ (T : PAT H (Sp (𝓞 K))) (m n : ℕ), HasType H T.t.act ρ m n → T.g = Module.finrank ℚ E / 2 * (m + n) :=
    fun T m n h => by
      obtain ⟨F⟩ := GlobalTheory.T.nonempty_polAVGenericFibreWithLieBasis abelianSchemeLaws_all.1.polBaseChange K T.pol
      exact (EigDec.eigen_decomposition E H K ρ T F m n X.split h X.ρ_sq).2.2.2.1
  refine ⟨fun b => ?_, key _ _ _ X.typeB, ?_⟩
  · cases b
    · simpa using key _ _ _ X.typeM
    · simpa using key _ _ _ X.typeP
  · have e := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at e
    have : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega

theorem lamEq_of_isGram {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) :
    (∀ a b, LamEq X.B.t.PP.L (phiP X a) (phiP X b) (X.A true).t.PP.L ((X.A true).t.act.act (gP a b)) (𝟙 _)) ∧
    ∀ a b, LamEq X.B.t.PP.L (phiQ X a) (phiQ X b) (X.A false).t.PP.L ((X.A false).t.act.act (gQ a b)) (𝟙 _) :=
  have hβ := σ₁.injective.comp (IsFractionRing.injective (𝓞 K) K)
  ⟨fun a b => (PairingFibre.lamEq_weilEq_over_ring abelianSchemeLaws_all.1 (𝓞 K) (X.A true).pol (X.A true).pol X.B.pol
      (X.A true).pol _ _ _ _ (X.lin (.inl a)).isMonHom (X.lin (.inl b)).isMonHom ((X.A true).t.act.hom _) inferInstance ℂ
      (σ₁.comp (algebraMap (𝓞 K) K))).2 inferInstance hβ (h.1 a b),
    fun a b => (PairingFibre.lamEq_weilEq_over_ring abelianSchemeLaws_all.1 (𝓞 K) (X.A false).pol (X.A false).pol X.B.pol
      (X.A false).pol _ _ _ _ (X.lin (.inr a)).isMonHom (X.lin (.inr b)).isMonHom ((X.A false).t.act.hom _) inferInstance ℂ
      (σ₁.comp (algebraMap (𝓞 K) K))).2 inferInstance hβ (h.2 a b)⟩

theorem exists_inverse : ∃ (N : ℕ) (ψ : Fin p → (X.B.pol.A ⟶ (X.A true).pol.A))
    (ψ' : Fin q → (X.B.pol.A ⟶ (X.A false).pol.A)), 0 < N ∧ (∀ i, IsMonHom (ψ i)) ∧ (∀ i, IsMonHom (ψ' i)) ∧
    (∀ (T : Over (Sp (𝓞 K))) (x : T ⟶ X.B.pol.A),
      (∏ i, x ≫ ψ i ≫ phiP X i) * (∏ i, x ≫ ψ' i ≫ phiQ X i) = x ^ N) ∧
    ∀ (T : Over (Sp (𝓞 K))) (a : Fin p → (T ⟶ (X.A true).pol.A)) (a' : Fin q → (T ⟶ (X.A false).pol.A)),
      (∀ i, ((∏ k, a k ≫ phiP X k) * ∏ k, a' k ≫ phiQ X k : T ⟶ X.B.pol.A) ≫ ψ i = a i ^ N) ∧
      ∀ i, ((∏ k, a k ≫ phiP X k) * ∏ k, a' k ≫ phiQ X k : T ⟶ X.B.pol.A) ≫ ψ' i = a' i ^ N := by
  haveI hP : ∀ i, IsMonHom (M := (X.A true).pol.A) (N := X.B.pol.A) (phiP X i) := fun i => (X.lin (.inl i)).isMonHom
  haveI hQ : ∀ i, IsMonHom (M := (X.A false).pol.A) (N := X.B.pol.A) (phiQ X i) := fun i => (X.lin (.inr i)).isMonHom
  obtain ⟨gA, gB, -⟩ := dims X
  obtain ⟨N, ψ, ψ', hN, h1, h2⟩ := LamF.exists_inverse_isogeny_of_sum thetaUnifAV_all abelianSchemeLaws_all.1
    (fun T K _ _ _ _ _ _ G G' _ _ hG hG' φ hφ => GlobalTheory.existsUnique_hom_extension_semiAbelian T K G G' hG hG' φ hφ)
    K σ₁ (X.A true).pol (X.A false).pol X.B.pol p q (phiP X) (phiQ X) hP hQ
    (by
      change X.B.g = p * (X.A true).g + q * (X.A false).g
      rw [gB, gA, gA]
      ring) fun y => by
      obtain ⟨x, hx⟩ := X.onto y
      refine ⟨fun i => x (Sum.inl i), fun i => x (Sum.inr i), hx.trans ?_⟩
      rw [List.ofFn_add, List.prod_append]
      congr 2
      · congr 1
        funext i
        exact congrArg (fun j => x j ≫ X.φ j) (finSumFinEquiv_symm_apply_castAdd i)
      · congr 1
        funext i
        exact congrArg (fun j => x j ≫ X.φ j) (finSumFinEquiv_symm_apply_natAdd i)
  have S := LamF.points_sums_eq_products.1 (Sp (𝓞 K))
  simp only [fun G T [GrpObj G] => (S G T).2.1, fun G T [GrpObj G] => (S G T).2.2.1,
    fun G T [GrpObj G] => (S G T).2.2.2, List.prod_ofFn] at h1 h2
  have hm : ∀ (T : Over (Sp (𝓞 K))) (x y : T ⟶ X.B.pol.A),
      ((∏ k, (x ≫ ψ k * y ≫ ψ k) ≫ phiP X k) * ∏ k, (x ≫ ψ' k * y ≫ ψ' k) ≫ phiQ X k : T ⟶ X.B.pol.A) =
        (∏ k, ((x * y) ≫ ψ k) ≫ phiP X k) * ∏ k, ((x * y) ≫ ψ' k) ≫ phiQ X k := fun T x y => by
    simp only [Category.assoc]
    rw [h1, mul_pow, ← h1, ← h1, _root_.mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    simp only [← Category.assoc]
    exact congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => MonObj.mul_comp _ _ _)
      (Finset.prod_congr rfl fun k _ => MonObj.mul_comp _ _ _)
  refine ⟨N * N, fun i => ψ i ^ N, fun i => ψ' i ^ N, Nat.mul_pos hN hN,
    fun i => LamF.IsogSum.isMonHom_of_points _ fun T x y => ?_,
    fun i => LamF.IsogSum.isMonHom_of_points _ fun T x y => ?_, fun T x => ?_, fun T a a' => ⟨fun i => ?_, fun i => ?_⟩⟩
  · simp only [MonObj.comp_pow]
    rw [← mul_pow, ← (h2 T (fun k => x ≫ ψ k * y ≫ ψ k) fun k => x ≫ ψ' k * y ≫ ψ' k).1 i, hm,
      (h2 T (fun k => (x * y) ≫ ψ k) fun k => (x * y) ≫ ψ' k).1 i]
  · simp only [MonObj.comp_pow]
    rw [← mul_pow, ← (h2 T (fun k => x ≫ ψ k * y ≫ ψ k) fun k => x ≫ ψ' k * y ≫ ψ' k).2 i, hm,
      (h2 T (fun k => (x * y) ≫ ψ k) fun k => (x * y) ≫ ψ' k).2 i]
  · rw [pow_mul, ← h1 T x, mul_pow, ← Finset.prod_pow, ← Finset.prod_pow]
    exact congrArg₂ (· * ·)
      (Finset.prod_congr rfl fun k _ => (congrArg _ (MonObj.pow_comp _ _ _)).trans (MonObj.comp_pow _ _ _))
      (Finset.prod_congr rfl fun k _ => (congrArg _ (MonObj.pow_comp _ _ _)).trans (MonObj.comp_pow _ _ _))
  · rw [MonObj.comp_pow, (h2 T a a').1, pow_mul]
  · rw [MonObj.comp_pow, (h2 T a a').2, pow_mul]

end GlobalTheory.GramAt
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.FlatCM GlobalTheory.PointMap
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GramAt

section Tate

variable {p : ℕ} {M : Type} [CommGroup M]

theorem lev_sum {J : Type} (s : Finset J) (t : J → Tate p M) (n : ℕ) :
    (∑ a ∈ s, t a).lev n = ∏ a ∈ s, (t a).lev n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, Tate.lev_add, ih]

theorem lev_nsmul (N : ℕ) (t : Tate p M) (n : ℕ) : (N • t).lev n = t.lev n ^ N := by
  induction N with
  | zero => simp
  | succ N ih => rw [succ_nsmul, Tate.lev_add, ih, pow_succ]

theorem tate_map_bijective [Fact p.Prime] {M' : Type} [CommGroup M'] {f : M →* M'} (hf : Function.Injective f)
    (h : ∀ (n : ℕ) (y : M'), y ^ p ^ n = 1 → ∃ x, f x = y) : Function.Bijective (Tate.map p f) := by
  refine ⟨Tate.map_injective hf, fun t => ?_⟩
  choose s hs using fun n => h n _ (t.lev_pow n)
  exact ⟨Tate.mk s fun n => ⟨hf (by rw [map_pow, hs, t.lev_pow, map_one]), hf (by rw [map_pow, hs, hs, t.lev_succ])⟩,
    Tate.ext hs⟩

end Tate

section Algebraic

variable {R Ω C : Type} [CommRing R] [Field Ω] [Field C] (α : R →+* Ω) (κ : Ω →+* C) {β : R →+* C}
  (hβ : κ.comp α = β)

def extPt : (Over.mk (spMap β) : Over (Sp R)) ⟶ Over.mk (spMap α) :=
  Over.homMk (spMap κ) (by subst hβ; exact (Spec.map_comp _ _).symm)

theorem extPt_injective (G : Over (Sp R)) : Function.Injective fun x : Over.mk (spMap α) ⟶ G => extPt α κ hβ ≫ x := by
  haveI : Epi (spMap κ) := by
    letI := κ.toAlgebra
    haveI : Flat (spMap κ) := (Flat.SpecMap_iff).2 (inferInstanceAs (Module.Flat Ω C))
    exact Flat.epi_of_flat_of_surjective _
  exact fun x y h => Over.OverMorphism.ext ((cancel_epi (spMap κ)).1 (congrArg (·.left) h))

theorem exists_extPt_eq [IsNoetherianRing R] [IsAlgClosed Ω] [IsAlgClosed C] [CharZero C] (B : Out.PolAV (Sp R)) {n : ℕ}
    (hn : 1 ≤ n) (y : Over.mk (spMap β) ⟶ B.A) (hy : y ^ n = 1) :
    ∃ x : Over.mk (spMap α) ⟶ B.A, x ^ n = 1 ∧ extPt α κ hβ ≫ x = y := by
  haveI : CharZero Ω := κ.charZero
  have h := (GlobalTheory.firstFiveLaws.1.mulN (Sp R) B n hn).2.2.2.2
  have h1 := h Ω (spMap α) (Nat.cast_ne_zero.2 (by omega))
  have h2 := h C (spMap β) (Nat.cast_ne_zero.2 (by omega))
  haveI : Finite {x : Over.mk (spMap β) ⟶ B.A // x ^ n = 1} := Nat.finite_of_card_ne_zero (by rw [h2]; positivity)
  let F : {x : Over.mk (spMap α) ⟶ B.A // x ^ n = 1} → {x : Over.mk (spMap β) ⟶ B.A // x ^ n = 1} := fun x =>
    ⟨extPt α κ hβ ≫ x.1, by rw [← MonObj.comp_pow, x.2, MonObj.comp_one]⟩
  have hF : Function.Injective F := fun x y e => Subtype.ext (extPt_injective α κ hβ _ (congrArg Subtype.val e))
  obtain ⟨x, hx⟩ := (hF.bijective_of_nat_card_le (h2.trans h1.symm).le).2 ⟨y, hy⟩
  exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

end Algebraic

theorem lamEq_polPull {S S' : Scheme.{0}} (s : S' ⟶ S) {X Y A B : Out.PolAV S} {f₁ : X.A ⟶ A.A} {f₂ : Y.A ⟶ A.A}
    {g₁ : X.A ⟶ B.A} {g₂ : Y.A ⟶ B.A} (h : LamEq A.L f₁ f₂ B.L g₁ g₂) :
    LamEq (X := (StrictPull.polPull X s).A) (Y := (StrictPull.polPull Y s).A) (StrictPull.polPull A s).L
      ((Over.pullback s).map f₁) ((Over.pullback s).map f₂)
      (StrictPull.polPull B s).L ((Over.pullback s).map g₁) ((Over.pullback s).map g₂) :=
  lamEq_baseChange _ _ s X.A Y.A A.A B.A _ _ (StrictPull.polPull A s).A (StrictPull.polPull B s).A
    (pullback.fst X.A.hom s) (pullback.fst Y.A.hom s) _ _ pullback.condition pullback.condition
    (isGrpPullback_pullback A.A s) (isGrpPullback_pullback B.A s) _ _ _ _ A.isLB B.isLB (StrictPull.polPull A s).isLB
    (StrictPull.polPull B s).isLB (PolBaseChange.lbIso_refl (StrictPull.polPull A s).isLB)
    (PolBaseChange.lbIso_refl (StrictPull.polPull B s).isLB) _ _ _ _ _ _ _ _ (pullback.lift_fst _ _ _)
    (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) h

theorem exists_pushEquiv₂ {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G']
    [GrpObj G''] {f : S' ⟶ S} {f' : S'' ⟶ S'} {φ : G'.left ⟶ G.left} {φ' : G''.left ⟶ G'.left}
    (h' : IsGrpPullback G'' G' f' φ') (h : IsGrpPullback G' G f φ) (g : S'' ⟶ S) (hg : g = f' ≫ f) :
    ∃ e : ((Over.mk (𝟙 S'') : Over S'') ⟶ G'') ≃* (Over.mk g ⟶ G), ∀ x, (e x).left = x.left ≫ φ' ≫ φ := by
  obtain ⟨e₁, h₁⟩ := LiePull.exists_pushEquiv h' (Over.mk (𝟙 _)) f' (Category.id_comp _).symm
  obtain ⟨e₂, h₂⟩ := LiePull.exists_pushEquiv h (Over.mk f') g hg
  exact ⟨e₁.trans e₂, fun x => (h₂ _).trans ((congrArg (· ≫ _) (h₁ x)).trans (Category.assoc _ _ _))⟩

theorem exists_pushEquiv_polPull {S S' S'' : Scheme.{0}} (B : Out.PolAV S) (f : S' ⟶ S) (f' : S'' ⟶ S') (g : S'' ⟶ S)
    (hg : g = f' ≫ f) :
    ∃ e : ((Over.mk (𝟙 S'') : Over S'') ⟶ (StrictPull.polPull (StrictPull.polPull B f) f').A) ≃* (Over.mk g ⟶ B.A),
      ∀ x, (e x).left = x.left ≫ pullback.fst (StrictPull.polPull B f).A.hom f' ≫ pullback.fst B.A.hom f :=
  exists_pushEquiv₂ (G' := (StrictPull.polPull B f).A) (isGrpPullback_pullback (StrictPull.polPull B f).A f')
    (isGrpPullback_pullback B.A f) g hg

section Good

variable {Λ : Type} [CommRing Λ] [StarRing Λ] {p : ℕ} [Fact p.Prime] {C : Type} [Field C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) (ε : Eps p C) {R : Type}
  [CommRing R] (j : R →+* O) {B B' : Out.PolAV (Sp R)} (o : B.OAct Λ) (o' : B'.OAct Λ)

def toBase : (goodPoint hv ε j B o).A.A.left ⟶ B.A.left :=
  (goodPoint hv ε j B o).gen ≫ pullback.fst B.A.hom (spMap j)

theorem homC_toBase (f : B.A ⟶ B'.A) :
    (homC hv ε j o o' f).left ≫ toBase hv ε j o' = toBase hv ε j o ≫ f.left := by
  have h2 : (homC hv ε j o o' f).left ≫ (goodPoint hv ε j B' o').gen =
      (goodPoint hv ε j B o).gen ≫ (homO hv ε j o o' f).left := pullback.lift_fst _ _ _
  have h3 : (homO hv ε j o o' f).left ≫ pullback.fst B'.A.hom (spMap j) = pullback.fst B.A.hom (spMap j) ≫ f.left :=
    pullback.lift_fst _ _ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h2).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) h3).trans (Category.assoc _ _ _).symm)))

theorem exists_ptsEquiv : ∃ e : ChTor.Pts (goodPoint hv ε j B o).A.A ≃*
    (Over.mk (spMap ((algebraMap O C).comp j)) ⟶ B.A), ∀ x, (e x).left = x.left ≫ toBase hv ε j o :=
  exists_pushEquiv_polPull B (spMap j) (spMap (algebraMap O C)) _ (Spec.map_comp (CommRingCat.ofHom j) _)

def ptsEquiv : ChTor.Pts (goodPoint hv ε j B o).A.A ≃* (Over.mk (spMap ((algebraMap O C).comp j)) ⟶ B.A) :=
  (exists_ptsEquiv hv ε j o).choose

theorem ptsEquiv_left (x : ChTor.Pts (goodPoint hv ε j B o).A.A) :
    (ptsEquiv hv ε j o x).left = x.left ≫ toBase hv ε j o := (exists_ptsEquiv hv ε j o).choose_spec x

theorem ptsEquiv_homC (f : B.A ⟶ B'.A) (x : ChTor.Pts (goodPoint hv ε j B o).A.A) :
    ptsEquiv hv ε j o' (x ≫ homC hv ε j o o' f) = ptsEquiv hv ε j o x ≫ f :=
  Over.OverMorphism.ext (by
    rw [ptsEquiv_left, Over.comp_left, Over.comp_left, ptsEquiv_left, Category.assoc, homC_toBase, Category.assoc])

variable [IsAlgClosed C] [CharZero C]

theorem exists_tateEquiv [IsNoetherianRing R] {Ω : Type} [Field Ω] [IsAlgClosed Ω] (α : R →+* Ω) (κ : Ω →+* C)
    (h : κ.comp α = (algebraMap O C).comp j) :
    ∃ e : ∀ (B : Out.PolAV (Sp R)) (o : B.OAct Λ), Tate p (Over.mk (spMap α) ⟶ B.A) ≃ₗ[ℤ_[p]] (goodPoint hv ε j B o).T,
      ∀ (B B' : Out.PolAV (Sp R)) (o : B.OAct Λ) (o' : B'.OAct Λ) (f : B.A ⟶ B'.A) [IsMonHom f] (t),
        e B' o' (Tate.map p (IndepPoint.ptsHom f _) t) = homT hv ε j o o' f (e B o t) := by
  let F := fun (B : Out.PolAV (Sp R)) (o : B.OAct Λ) =>
    (ptsEquiv hv ε j o).symm.toMonoidHom.comp (preHom (G := B.A) (extPt α κ h))
  have hF : ∀ B o, Function.Bijective (Tate.map p (F B o)) := fun B o =>
    tate_map_bijective ((ptsEquiv hv ε j o).symm.injective.comp (extPt_injective α κ h _)) fun n y hy => by
      obtain ⟨x, -, hx⟩ := exists_extPt_eq α κ h B (one_le_ppow p n) (ptsEquiv hv ε j o y)
        (by rw [← map_pow, hy, map_one])
      exact ⟨x, (ptsEquiv hv ε j o).symm_apply_eq.2 hx⟩
  refine ⟨fun B o => LinearEquiv.ofBijective _ (hF B o), fun B B' o o' f _ t => Tate.ext fun n => ?_⟩
  refine (ptsEquiv hv ε j o').symm_apply_eq.2 ?_
  rw [lev_homT, ptsEquiv_homC]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) ((ptsEquiv hv ε j o).apply_symm_apply _).symm)

theorem pairT_homT_of_lamEq {X Y A B : Out.PolAV (Sp R)} (oX : X.OAct Λ) (oY : Y.OAct Λ) (oA : A.OAct Λ)
    (oB : B.OAct Λ) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A) [IsMonHom f₁] [IsMonHom f₂]
    [IsMonHom g₁] [IsMonHom g₂] (h : LamEq A.L f₁ f₂ B.L g₁ g₂) (s : (goodPoint hv ε j X oX).T)
    (t : (goodPoint hv ε j Y oY).T) :
    pairT (goodPoint hv ε j A oA).A ε (homT hv ε j oX oA f₁ s) (homT hv ε j oY oA f₂ t) =
      pairT (goodPoint hv ε j B oB).A ε (homT hv ε j oX oB g₁ s) (homT hv ε j oY oB g₂ t) := by
  have hW := weilEq_of_lamEq GlobalTheory.firstFiveLaws.1 C (goodPoint hv ε j X oX).A (goodPoint hv ε j Y oY).A
    (goodPoint hv ε j A oA).A (goodPoint hv ε j B oB).A (homC hv ε j oX oA f₁) (homC hv ε j oY oA f₂)
    (homC hv ε j oX oB g₁) (homC hv ε j oY oB g₂) inferInstance inferInstance inferInstance inferInstance
    (lamEq_polPull _ (lamEq_polPull _ h))
  refine congrArg ε.equiv.symm (Tate.ext fun n => ?_)
  have hn := one_le_ppow p n
  exact (weilIs_iff hn ((homT hv ε j oX oB g₁ s).lev_pow n) ((homT hv ε j oY oB g₂ t).lev_pow n) _).1
    ((hW _ _ _ _ hn (s.lev_pow n) (t.lev_pow n)).1
      ((weilIs_iff hn ((homT hv ε j oX oA f₁ s).lev_pow n) ((homT hv ε j oY oA f₂ t).lev_pow n) _).2 rfl))

omit [IsAlgClosed C] [CharZero C] in
theorem homT_one [IsMonHom (1 : B.A ⟶ B'.A)] : homT hv ε j o o' 1 = 0 :=
  LinearMap.ext fun t => Tate.ext fun n => (ptsEquiv hv ε j o').injective (by
    rw [lev_homT, ptsEquiv_homC, MonObj.comp_one, LinearMap.zero_apply, Tate.lev_zero, map_one])

omit [IsAlgClosed C] [CharZero C] in

theorem ptsEquiv_lev_sum {A A' : Out.PolAV (Sp R)} (oA : A.OAct Λ) (oA' : A'.OAct Λ) {m m' : ℕ}
    (φ : Fin m → (A.A ⟶ B.A)) (φ' : Fin m' → (A'.A ⟶ B.A)) [∀ k, IsMonHom (φ k)] [∀ k, IsMonHom (φ' k)]
    (s : Fin m → (goodPoint hv ε j A oA).T) (s' : Fin m' → (goodPoint hv ε j A' oA').T) (n : ℕ) :
    ptsEquiv hv ε j o ((∑ k, homT hv ε j oA o (φ k) (s k) + ∑ k, homT hv ε j oA' o (φ' k) (s' k)).lev n) =
      (∏ k, ptsEquiv hv ε j oA ((s k).lev n) ≫ φ k) * ∏ k, ptsEquiv hv ε j oA' ((s' k).lev n) ≫ φ' k := by
  simp only [Tate.lev_add, lev_sum, map_mul, map_prod, lev_homT, ptsEquiv_homC]

omit [IsAlgClosed C] [CharZero C] in

theorem homT_inverse {A A' : Out.PolAV (Sp R)} (oA : A.OAct Λ) (oA' : A'.OAct Λ) {m m' N : ℕ}
    (φ : Fin m → (A.A ⟶ B.A)) (φ' : Fin m' → (A'.A ⟶ B.A)) [∀ k, IsMonHom (φ k)] [∀ k, IsMonHom (φ' k)]
    (ψ : Fin m → (B.A ⟶ A.A)) (ψ' : Fin m' → (B.A ⟶ A'.A)) [∀ k, IsMonHom (ψ k)] [∀ k, IsMonHom (ψ' k)]
    (h1 : ∀ (T : Over (Sp R)) (x : T ⟶ B.A), (∏ k, x ≫ ψ k ≫ φ k) * (∏ k, x ≫ ψ' k ≫ φ' k) = x ^ N)
    (h2 : ∀ (T : Over (Sp R)) (a : Fin m → (T ⟶ A.A)) (a' : Fin m' → (T ⟶ A'.A)),
      (∀ l, ((∏ k, a k ≫ φ k) * ∏ k, a' k ≫ φ' k) ≫ ψ l = a l ^ N) ∧
      ∀ l, ((∏ k, a k ≫ φ k) * ∏ k, a' k ≫ φ' k) ≫ ψ' l = a' l ^ N) :
    (∀ t, ∑ k, homT hv ε j oA o (φ k) (homT hv ε j o oA (ψ k) t) +
      ∑ k, homT hv ε j oA' o (φ' k) (homT hv ε j o oA' (ψ' k) t) = N • t) ∧
    ∀ (s : Fin m → (goodPoint hv ε j A oA).T) (s' : Fin m' → (goodPoint hv ε j A' oA').T),
      (∀ l, homT hv ε j o oA (ψ l) (∑ k, homT hv ε j oA o (φ k) (s k) + ∑ k, homT hv ε j oA' o (φ' k) (s' k)) =
        N • s l) ∧
      ∀ l, homT hv ε j o oA' (ψ' l) (∑ k, homT hv ε j oA o (φ k) (s k) + ∑ k, homT hv ε j oA' o (φ' k) (s' k)) =
        N • s' l := by
  refine ⟨fun t => Tate.ext fun n => (ptsEquiv hv ε j o).injective ?_, fun s s' =>
    ⟨fun l => Tate.ext fun n => (ptsEquiv hv ε j oA).injective ?_,
      fun l => Tate.ext fun n => (ptsEquiv hv ε j oA').injective ?_⟩⟩
  · rw [ptsEquiv_lev_sum, lev_nsmul, map_pow, ← h1]
    simp only [lev_homT, ptsEquiv_homC, Category.assoc]
  · rw [lev_homT, ptsEquiv_homC, lev_nsmul, map_pow, ptsEquiv_lev_sum, (h2 _ _ _).1]
  · rw [lev_homT, ptsEquiv_homC, lev_nsmul, map_pow, ptsEquiv_lev_sum, (h2 _ _ _).2]

end Good

section Points

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] [IsAlgClosed C] [CharZero C]

theorem pairV_baseChange [Algebra ℤ_[p] C] {X Y A B : Point p v O Λ} {f₁ : X.T →ₗ[ℤ_[p]] A.T} {f₂ : Y.T →ₗ[ℤ_[p]] A.T}
    {g₁ : X.T →ₗ[ℤ_[p]] B.T} {g₂ : Y.T →ₗ[ℤ_[p]] B.T}
    (h : ∀ s t, pairT A.A A.eps (f₁ s) (f₂ t) = pairT B.A B.eps (g₁ s) (g₂ t)) (x : X.V) (y : Y.V) :
    A.pairV (f₁.baseChange C x) (f₂.baseChange C y) = B.pairV (g₁.baseChange C x) (g₂.baseChange C y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul c s =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul d t => exact congrArg (· • (c * d)) (h s t)

theorem eq_zero_of_actT {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (hg : 0 < P.A.g)
    {a : 𝓞 E} (h : ∀ t, P.actT a t = 0) : a = 0 := by
  by_contra ha
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  have hn : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  haveI : Nontrivial P.T := Module.nontrivial_of_finrank_pos (R := ℤ_[p]) (by rw [P.hodgeTateLatticePoint_finrank_tateModule]; omega)
  obtain ⟨t, ht⟩ := exists_ne (0 : P.T)
  have e := congrArg (P.actT b) (h t)
  rw [map_zero, ← Module.End.mul_apply, ← map_mul, hb, map_natCast, Module.End.natCast_apply,
    ← Nat.cast_smul_eq_nsmul ℤ_[p], smul_eq_zero] at e
  exact ht (e.resolve_left (Nat.cast_ne_zero.2 hn))

variable {A A' B : Point p v O Λ} {m m' : ℕ} (φ : Fin m → (A.T →ₗ[ℤ_[p]] B.T)) (φ' : Fin m' → (A'.T →ₗ[ℤ_[p]] B.T))
  {N : ℕ} (hN : 0 < N) (ψ : Fin m → (B.T →ₗ[ℤ_[p]] A.T)) (ψ' : Fin m' → (B.T →ₗ[ℤ_[p]] A'.T))

omit [IsAlgClosed C] in
include hN in

theorem bijective_of_inverse [Algebra ℤ_[p] C] (h1 : ∀ t, ∑ k, φ k (ψ k t) + ∑ k, φ' k (ψ' k t) = N • t)
    (h2 : ∀ (s : Fin m → A.T) (s' : Fin m' → A'.T), (∀ l, ψ l (∑ k, φ k (s k) + ∑ k, φ' k (s' k)) = N • s l) ∧
      ∀ l, ψ' l (∑ k, φ k (s k) + ∑ k, φ' k (s' k)) = N • s' l) :
    Function.Bijective fun z : (Fin m → A.V) × (Fin m' → A'.V) =>
      ∑ k, (φ k).baseChange C (z.1 k) + ∑ k, (φ' k).baseChange C (z.2 k) := by
  classical
  have hC : (N : C) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have a1 : ∀ l k x, (ψ l).baseChange C ((φ k).baseChange C x) = if k = l then (N : C) • x else 0 := fun l k x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]; split_ifs <;> simp
    | tmul c t =>
      have := (h2 (Pi.single k t) 0).1 l
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)] at this
      simp only [Pi.single_eq_same, Pi.zero_apply, map_zero, Finset.sum_const_zero, add_zero] at this
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, this, Nat.cast_smul_eq_nsmul]
      split_ifs with h
      · rw [h, Pi.single_eq_same, TensorProduct.tmul_smul]
      · simp [Ne.symm h]
  have a2 : ∀ l k x, (ψ l).baseChange C ((φ' k).baseChange C x) = 0 := fun l k x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    | tmul c t =>
      have := (h2 0 (Pi.single k t)).1 l
      rw [Finset.sum_eq_single k (f := fun b => φ' b _) (fun b _ hb => by simp [hb]) (by simp)] at this
      simp only [Pi.single_eq_same, Pi.zero_apply, map_zero, Finset.sum_const_zero, zero_add, smul_zero] at this
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, this, TensorProduct.tmul_zero]
  have a3 : ∀ l k x, (ψ' l).baseChange C ((φ k).baseChange C x) = 0 := fun l k x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    | tmul c t =>
      have := (h2 (Pi.single k t) 0).2 l
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)] at this
      simp only [Pi.single_eq_same, Pi.zero_apply, map_zero, Finset.sum_const_zero, add_zero, smul_zero] at this
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, this, TensorProduct.tmul_zero]
  have a4 : ∀ l k x, (ψ' l).baseChange C ((φ' k).baseChange C x) = if k = l then (N : C) • x else 0 := fun l k x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]; split_ifs <;> simp
    | tmul c t =>
      have := (h2 0 (Pi.single k t)).2 l
      rw [Finset.sum_eq_single k (f := fun b => φ' b _) (fun b _ hb => by simp [hb]) (by simp)] at this
      simp only [Pi.single_eq_same, Pi.zero_apply, map_zero, Finset.sum_const_zero, zero_add] at this
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, this, Nat.cast_smul_eq_nsmul]
      split_ifs with h
      · rw [h, Pi.single_eq_same, TensorProduct.tmul_smul]
      · simp [Ne.symm h]
  have a5 : ∀ x : B.V, ∑ k, (φ k).baseChange C ((ψ k).baseChange C x) +
      ∑ k, (φ' k).baseChange C ((ψ' k).baseChange C x) = (N : C) • x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, smul_add, ← hx, ← hy]; abel
    | tmul c t =>
      simp only [LinearMap.baseChange_tmul, ← TensorProduct.tmul_sum, ← TensorProduct.tmul_add, h1]
      rw [Nat.cast_smul_eq_nsmul, TensorProduct.tmul_smul]
  refine ⟨fun z z' h => Prod.ext (funext fun l => ?_) (funext fun l => ?_), fun x => ?_⟩
  · have := congrArg ((ψ l).baseChange C) h
    simp only [map_add, map_sum, a1, a2, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact smul_right_injective _ hC (add_right_cancel this)
  · have := congrArg ((ψ' l).baseChange C) h
    simp only [map_add, map_sum, a3, a4, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact smul_right_injective _ hC (add_left_cancel this)
  · refine ⟨(fun k => (ψ k).baseChange C ((N : C)⁻¹ • x), fun k => (ψ' k).baseChange C ((N : C)⁻¹ • x)), ?_⟩
    exact (a5 _).trans (smul_inv_smul₀ hC x)

include hN in

theorem det_ne_zero_of_inverse {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] {A A' B : Point p v O (𝓞 E)}
    (hg : 0 < A.A.g) (φ : Fin m → (A.T →ₗ[ℤ_[p]] B.T)) (φ' : Fin m' → (A'.T →ₗ[ℤ_[p]] B.T))
    (g : Matrix (Fin m) (Fin m) (𝓞 E))
    (hφ : ∀ a b s t, pairT B.A B.eps (φ a s) (φ b t) = pairT A.A A.eps (A.actT (g a b) s) t)
    (hφ' : ∀ a b s t, pairT B.A B.eps (φ a s) (φ' b t) = 0)
    (h1 : ∀ t, ∃ (s : Fin m → A.T) (s' : Fin m' → A'.T), ∑ k, φ k (s k) + ∑ k, φ' k (s' k) = N • t)
    (h2 : ∀ s : Fin m → A.T, ∑ k, φ k (s k) = 0 → s = 0) : g.det ≠ 0 := fun h0 => by
  obtain ⟨w, hw, hwg⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  refine hw (funext fun a => eq_zero_of_actT A hg fun t => congrFun (h2 (fun k => A.actT (w k) t) ?_) a)
  refine (injective_iff_map_eq_zero _).1 B.pairT_bijective.1 _ (LinearMap.ext fun y => ?_)
  obtain ⟨s, s', hs⟩ := h1 y
  refine (smul_eq_zero_iff_right hN.ne').1 ?_
  rw [← map_nsmul, ← hs]
  simp only [map_add, map_sum, LinearMap.sum_apply, hφ, hφ', Finset.sum_const_zero, add_zero]
  refine Finset.sum_eq_zero fun b _ => ?_
  have e : ∑ k, g k b * w k = 0 := by simpa [Matrix.vecMul, dotProduct, mul_comm] using congrFun hwg b
  simp only [← Module.End.mul_apply, ← map_mul]
  rw [← LinearMap.sum_apply, ← map_sum, ← LinearMap.sum_apply, ← map_sum, e]
  simp

theorem star_gram {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] {A B : Point p v O (𝓞 E)}
    (hg : 0 < A.A.g) (φ : Fin m → (A.T →ₗ[ℤ_[p]] B.T)) (g : Matrix (Fin m) (Fin m) (𝓞 E))
    (hφ : ∀ a b s t, pairT B.A B.eps (φ a s) (φ b t) = pairT A.A A.eps (A.actT (g a b) s) t) (a b : Fin m) :
    star (g b a) = g a b := by
  refine sub_eq_zero.1 (eq_zero_of_actT A hg fun s => ?_)
  refine (injective_iff_map_eq_zero _).1 A.pairT_bijective.1 _ (LinearMap.ext fun t => ?_)
  have e : pairT A.A A.eps (A.actT (star (g b a)) s) t = pairT A.A A.eps s (A.actT (star (star (g b a))) t) :=
    pairT_act A.oA A.eps _ s t
  rw [map_sub, LinearMap.sub_apply, map_sub, LinearMap.sub_apply, ← hφ, e, star_star,
    ← (isAlt_pairT A.A A.eps).neg_eq, ← hφ, (isAlt_pairT B.A B.eps).neg_eq, sub_self, LinearMap.zero_apply]

end Points

end GlobalTheory.GramAt
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.FlatCM GlobalTheory.PointMap
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GramAt

section Object

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ}

section At

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C) (X : CMObj H K ρ σ₁ p q)

abbrev phiTP (a : Fin p) : letI := H.starRing; (pointA hv ε i X true).T →ₗ[ℤ_[ℓ]] (pointB hv ε i X).T :=
  patT (T := X.A true) hv ε i (X.lin (Sum.inl a))

abbrev phiTQ (b : Fin q) : letI := H.starRing; (pointA hv ε i X false).T →ₗ[ℤ_[ℓ]] (pointB hv ε i X).T :=
  patT (T := X.A false) hv ε i (X.lin (Sum.inr b))

variable [IsAlgClosed C] [CharZero C]

omit [NumberField K] in

theorem pairT_patT_gram {T T' : PAT H (Sp (𝓞 K))} {f f' : T.t.G ⟶ T'.t.G} (hf : Serre.IsLinearHom T.t.act T'.t.act f)
    (hf' : Serre.IsLinearHom T.t.act T'.t.act f') {g : 𝓞 E}
    (h : LamEq T'.t.PP.L f f' T.t.PP.L (T.t.act.act g) (𝟙 _)) : letI := H.starRing
    ∀ s t, pairT (patPoint hv ε i T').A ε (patT hv ε i hf s) (patT hv ε i hf' t) =
      pairT (patPoint hv ε i T).A ε ((patPoint hv ε i T).actT g s) t := by
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f' := hf'.isMonHom
  haveI := (patAct T).hom g
  intro s t
  have e := pairT_homT_of_lamEq (X := T.pol) (Y := T.pol) (A := T'.pol) (B := T.pol) hv ε (embO hv i) (patAct T) (patAct T)
    (patAct T') (patAct T) f f' ((patAct T).act g) (𝟙 _) h s t
  rw [homT_act, homT_id] at e
  exact e

theorem pairT_patT_orth (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) {A A' B : PAT H (Sp (𝓞 K))} {m m' : ℕ}
    (hA : HasType H A.t.act ρ m 0) (hA' : HasType H A'.t.act ρ 0 m') {f : A.t.G ⟶ B.t.G} {f' : A'.t.G ⟶ B.t.G}
    (hf : Serre.IsLinearHom A.t.act B.t.act f) (hf' : Serre.IsLinearHom A'.t.act B.t.act f') : letI := H.starRing
    ∀ s t, pairT (patPoint hv ε i B).A ε (patT hv ε i hf s) (patT hv ε i hf' t) = 0 := by
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := A.pol.A) (N := B.pol.A) f := hf.isMonHom
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := A'.pol.A) (N := B.pol.A) f' := hf'.isMonHom
  haveI : IsMonHom (1 : A'.pol.A ⟶ A.pol.A) := LamF.IsogSum.isMonHom_of_points _ fun T a b => by
    simp only [MonObj.comp_one, _root_.mul_one]
  intro s t
  have e := pairT_homT_of_lamEq (X := A.pol) (Y := A'.pol) (A := B.pol) (B := A.pol) hv ε (embO hv i) (patAct A)
    (patAct A') (patAct B) (patAct A) f f' (𝟙 _) 1 (lamEq_one hρ A A' B hA hA' hf hf') s t
  rw [homT_one, LinearMap.zero_apply, map_zero] at e
  exact e

theorem tateModule_gram_relations_blocks_orthogonal {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) :
    letI := H.starRing
    (∀ a b s t, pairT (pointB hv ε i X).A ε (phiTP hv ε i X a s) (phiTP hv ε i X b t) =
      pairT (pointA hv ε i X true).A ε ((pointA hv ε i X true).actT (gP a b) s) t) ∧
    (∀ a b s t, pairT (pointB hv ε i X).A ε (phiTQ hv ε i X a s) (phiTQ hv ε i X b t) =
      pairT (pointA hv ε i X false).A ε ((pointA hv ε i X false).actT (gQ a b) s) t) ∧
    ∀ a b s t, pairT (pointB hv ε i X).A ε (phiTP hv ε i X a s) (phiTQ hv ε i X b t) = 0 :=
  ⟨fun a b => pairT_patT_gram (T := X.A true) hv ε i (X.lin (.inl a)) (X.lin (.inl b)) ((lamEq_of_isGram X h).1 a b),
    fun a b => pairT_patT_gram (T := X.A false) hv ε i (X.lin (.inr a)) (X.lin (.inr b)) ((lamEq_of_isGram X h).2 a b),
    fun a b => pairT_patT_orth (A := X.A true) (A' := X.A false) hv ε i X.ρ_sq X.typeP X.typeM (X.lin (.inl a))
      (X.lin (.inr b))⟩

end At

theorem exists_inverse_tateModule_sum_up_to_integer (X : CMObj H K ρ σ₁ p q) : letI := H.starRing
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime] (C : Type) [Field C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O]
      [Algebra O C] (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C),
      ∃ (ψ : Fin p → ((pointB hv ε i X).T →ₗ[ℤ_[ℓ]] (pointA hv ε i X true).T))
        (ψ' : Fin q → ((pointB hv ε i X).T →ₗ[ℤ_[ℓ]] (pointA hv ε i X false).T)),
        (∀ t, ∑ k, phiTP hv ε i X k (ψ k t) + ∑ k, phiTQ hv ε i X k (ψ' k t) = N • t) ∧
        ∀ (s : Fin p → (pointA hv ε i X true).T) (s' : Fin q → (pointA hv ε i X false).T),
          (∀ l, ψ l (∑ k, phiTP hv ε i X k (s k) + ∑ k, phiTQ hv ε i X k (s' k)) = N • s l) ∧
          ∀ l, ψ' l (∑ k, phiTP hv ε i X k (s k) + ∑ k, phiTQ hv ε i X k (s' k)) = N • s' l := by
  letI := H.starRing
  haveI hP : ∀ i, IsMonHom (M := (X.A true).pol.A) (N := X.B.pol.A) (phiP X i) := fun i => (X.lin (.inl i)).isMonHom
  haveI hQ : ∀ i, IsMonHom (M := (X.A false).pol.A) (N := X.B.pol.A) (phiQ X i) := fun i => (X.lin (.inr i)).isMonHom
  obtain ⟨N, ψ, ψ', hN, hψ, hψ', h1, h2⟩ := exists_inverse X
  exact ⟨N, hN, fun ℓ _ C _ v O _ _ hv ε i => ⟨_, _, homT_inverse (B := X.B.pol) (A := (X.A true).pol)
    (A' := (X.A false).pol) hv ε (embO hv i) (patAct X.B) (patAct (X.A true)) (patAct (X.A false)) (phiP X) (phiQ X)
    ψ ψ' h1 h2⟩⟩

section At

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C) (X : CMObj H K ρ σ₁ p q) [IsAlgClosed C] [CharZero C]

theorem sumT_injective : letI := H.starRing
    Function.Injective fun z : (Fin p → (pointA hv ε i X true).T) × (Fin q → (pointA hv ε i X false).T) =>
      ∑ k, phiTP hv ε i X k (z.1 k) + ∑ k, phiTQ hv ε i X k (z.2 k) := by
  letI := H.starRing
  obtain ⟨N, hN, h⟩ := exists_inverse_tateModule_sum_up_to_integer X
  obtain ⟨ψ, ψ', -, h2⟩ := h ℓ C v O hv ε i
  have key : ∀ (P : Point ℓ v O (𝓞 E)) (x y : P.T), N • x = N • y → x = y := fun P x y e => by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[ℓ], ← Nat.cast_smul_eq_nsmul ℤ_[ℓ]] at e
    exact smul_right_injective _ (Nat.cast_ne_zero.2 hN.ne') e
  exact fun z z' e => Prod.ext
    (funext fun l => key _ _ _ (((h2 z.1 z.2).1 l).symm.trans ((congrArg (ψ l) e).trans ((h2 z'.1 z'.2).1 l))))
    (funext fun l => key _ _ _ (((h2 z.1 z.2).2 l).symm.trans ((congrArg (ψ' l) e).trans ((h2 z'.1 z'.2).2 l))))

include hv ε i in
theorem gram_det_of_emb {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) :
    gP.det ≠ 0 ∧ gQ.det ≠ 0 ∧ (∀ a b, H.bar (gP b a) = gP a b) ∧ ∀ a b, H.bar (gQ b a) = gQ a b := by
  letI := H.starRing
  obtain ⟨N, hN, hI⟩ := exists_inverse_tateModule_sum_up_to_integer X
  obtain ⟨ψ, ψ', h1, -⟩ := hI ℓ C v O hv ε i
  obtain ⟨hP, hQ, hO⟩ := tateModule_gram_relations_blocks_orthogonal hv ε i X h
  have hg : ∀ b, 0 < (pointA hv ε i X b).A.g := fun b => (dims X).2.2.trans_eq ((dims X).1 b).symm
  have hi := sumT_injective hv ε i X
  refine ⟨det_ne_zero_of_inverse hN (A := pointA hv ε i X true) (A' := pointA hv ε i X false) (B := pointB hv ε i X)
      (hg true) (phiTP hv ε i X) (phiTQ hv ε i X) gP hP hO (fun t => ⟨_, _, h1 t⟩) fun s hs => ?_,
    det_ne_zero_of_inverse hN (A := pointA hv ε i X false) (A' := pointA hv ε i X true) (B := pointB hv ε i X)
      (hg false) (phiTQ hv ε i X) (phiTP hv ε i X) gQ hQ (fun a b s t => ?_)
      (fun t => ⟨_, _, (add_comm _ _).trans (h1 t)⟩) fun s hs => ?_,
    star_gram (A := pointA hv ε i X true) (B := pointB hv ε i X) (hg true) (phiTP hv ε i X) gP hP,
    star_gram (A := pointA hv ε i X false) (B := pointB hv ε i X) (hg false) (phiTQ hv ε i X) gQ hQ⟩
  · exact congrArg Prod.fst (@hi (s, 0) (0, 0) (by simp only [hs, Pi.zero_apply, map_zero, Finset.sum_const_zero]))
  · exact ((isAlt_pairT (pointB hv ε i X).A ε).neg_eq _ _).symm.trans (neg_eq_zero.2 (hO b a t s))
  · exact congrArg Prod.snd (@hi (0, s) (0, 0) (by simp only [hs, Pi.zero_apply, map_zero, Finset.sum_const_zero]))

variable [Algebra ℤ_[ℓ] C]

theorem gram_V {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) :
    letI := H.starRing
    (∀ a b x y, (pointB hv ε i X).pairV (phiVP hv ε i X a x) (phiVP hv ε i X b y) =
      (pointA hv ε i X true).pairV ((pointA hv ε i X true).actV (gP a b) x) y) ∧
    (∀ a b x y, (pointB hv ε i X).pairV (phiVQ hv ε i X a x) (phiVQ hv ε i X b y) =
      (pointA hv ε i X false).pairV ((pointA hv ε i X false).actV (gQ a b) x) y) ∧
    ∀ a b x y, (pointB hv ε i X).pairV (phiVP hv ε i X a x) (phiVQ hv ε i X b y) = 0 := by
  letI := H.starRing
  obtain ⟨hP, hQ, hO⟩ := tateModule_gram_relations_blocks_orthogonal hv ε i X h
  refine ⟨fun a b x y => ?_, fun a b x y => ?_, fun a b x y => ?_⟩
  · have e := pairV_baseChange (A := pointB hv ε i X) (B := pointA hv ε i X true) (g₂ := LinearMap.id) (hP a b) x y
    rw [LinearMap.baseChange_id] at e
    exact e
  · have e := pairV_baseChange (A := pointB hv ε i X) (B := pointA hv ε i X false) (g₂ := LinearMap.id) (hQ a b) x y
    rw [LinearMap.baseChange_id] at e
    exact e
  · have e := pairV_baseChange (A := pointB hv ε i X) (B := pointB hv ε i X) (g₁ := 0) (g₂ := 0)
      (fun s t => (hO a b s t).trans (map_zero _).symm) x y
    rw [LinearMap.baseChange_zero, LinearMap.baseChange_zero, LinearMap.zero_apply, LinearMap.zero_apply, map_zero] at e
    exact e

theorem sumV_bijective : letI := H.starRing
    Function.Bijective fun z : (Fin p → (pointA hv ε i X true).V) × (Fin q → (pointA hv ε i X false).V) =>
      ∑ k, phiVP hv ε i X k (z.1 k) + ∑ k, phiVQ hv ε i X k (z.2 k) := by
  letI := H.starRing
  obtain ⟨N, hN, h⟩ := exists_inverse_tateModule_sum_up_to_integer X
  obtain ⟨ψ, ψ', h1, h2⟩ := h ℓ C v O hv ε i
  exact bijective_of_inverse (A := pointA hv ε i X true) (A' := pointA hv ε i X false) (B := pointB hv ε i X)
    (phiTP hv ε i X) (phiTQ hv ε i X) hN ψ ψ' h1 h2

end At

theorem gram_det (X : CMObj H K ρ σ₁ p q) {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)}
    (h : IsGram X gP gQ) :
    gP.det ≠ 0 ∧ gQ.det ≠ 0 ∧ (∀ a b, H.bar (gP b a) = gP a b) ∧ ∀ a b, H.bar (gQ b a) = gQ a b := by
  obtain ⟨ε⟩ : Nonempty (Eps 2 ℂ_[2]) := inferInstance
  exact gram_det_of_emb (PadicComplexInt.integers 2) ε (IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ_[2])).toRingHom X h

theorem exists_patT_equiv {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
    [Algebra O C] [IsAlgClosed C] [CharZero C] (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C) {C' : Type} [Field C']
    {v' : Valuation C' ℝ≥0} {O' : Type} [CommRing O'] [Algebra O' C'] [IsAlgClosed C'] [CharZero C']
    (hv' : v'.Integers O') (ε' : Eps ℓ C') (i' : K →+* C') : letI := H.starRing
    ∃ e : ∀ T : PAT H (Sp (𝓞 K)), (patPoint hv ε i T).T ≃ₗ[ℤ_[ℓ]] (patPoint hv' ε' i' T).T,
      (∀ T a t, e T ((patPoint hv ε i T).actT a t) = (patPoint hv' ε' i' T).actT a (e T t)) ∧
      ∀ (T T' : PAT H (Sp (𝓞 K))) (f : T.t.G ⟶ T'.t.G) (hf : Serre.IsLinearHom T.t.act T'.t.act f) (t),
        e T' (patT hv ε i hf t) = patT hv' ε' i' hf (e T t) := by
  letI := H.starRing
  have lift : ∀ {C : Type} [Field C] [IsAlgClosed C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
      (hv : v.Integers O) (i : K →+* C), ∃ κ : AlgebraicClosure K →+* C,
        κ.comp (algebraMap (𝓞 K) (AlgebraicClosure K)) = (algebraMap O C).comp (embO hv i) := by
    intro C _ _ v O _ _ hv i
    letI := i.toAlgebra
    refine ⟨(IsAlgClosed.lift (R := K) (S := AlgebraicClosure K) (M := C)).toRingHom, RingHom.ext fun a => ?_⟩
    rw [RingHom.comp_apply, RingHom.comp_apply, algebraMap_embO, IsScalarTower.algebraMap_apply (𝓞 K) K]
    exact AlgHom.commutes _ _
  obtain ⟨κ, hκ⟩ := lift hv i
  obtain ⟨κ', hκ'⟩ := lift hv' i'
  obtain ⟨e, he⟩ := exists_tateEquiv (Λ := 𝓞 E) hv ε (embO hv i) _ κ hκ
  obtain ⟨e', he'⟩ := exists_tateEquiv (Λ := 𝓞 E) hv' ε' (embO hv' i') _ κ' hκ'
  have key : ∀ (B B' : Out.PolAV (Sp (𝓞 K))) (o : B.OAct (𝓞 E)) (o' : B'.OAct (𝓞 E)) (f : B.A ⟶ B'.A) [IsMonHom f] (t),
      e' B' o' ((e B' o').symm (homT hv ε (embO hv i) o o' f t)) =
        homT hv' ε' (embO hv' i') o o' f (e' B o ((e B o).symm t)) := fun B B' o o' f _ t => by
    rw [← he', (e B' o').symm_apply_eq.2 ((congrArg _ ((e B o).apply_symm_apply t).symm).trans (he B B' o o' f _).symm)]
  refine ⟨fun T => (e T.pol (patAct T)).symm.trans (e' T.pol (patAct T)), fun T a t => ?_, fun T T' f hf t => ?_⟩
  · haveI := (patAct T).hom a
    have h := key T.pol T.pol (patAct T) (patAct T) ((patAct T).act a) t
    rw [homT_act, homT_act] at h
    exact h
  · haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
    exact key T.pol T'.pol (patAct T) (patAct T') f t

example (X : CMObj H K ρ σ₁ p q) {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)}
    (h : IsGram X gP gQ) (ℓ : ℕ) [Fact ℓ.Prime] (ε : Eps ℓ ℂ_[ℓ]) (i : K →+* ℂ_[ℓ]) :
    letI := H.starRing; letI := algPadicField ℓ
    ∀ a b x y, (pointB (PadicComplexInt.integers ℓ) ε i X).pairV (phiVP (PadicComplexInt.integers ℓ) ε i X a x)
      (phiVQ (PadicComplexInt.integers ℓ) ε i X b y) = 0 :=
  letI := algPadicField ℓ
  (gram_V (PadicComplexInt.integers ℓ) ε i X h).2.2

end Object

end GlobalTheory.GramAt
end
end
