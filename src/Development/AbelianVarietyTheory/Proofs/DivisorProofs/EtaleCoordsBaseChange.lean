import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing

namespace GlobalTheory.Vanishing

open H0

variable {Y T : Scheme.{0}} {k k' : Type} [CommRing k] [CommRing k'] {p : Y ⟶ Sp k} {q : T ⟶ Sp k'} {φ : k →+* k'}
  {r : T ⟶ Y} {P B N : LB Y} {P' B' N' : LB T} {O : Y.Opens} {W : T.Opens}

theorem pullChart_ofSec (a : ChartPull B' B r) (hq : r ≫ p = q ≫ spMap φ) (h : W ≤ r ⁻¹ᵁ O) (s : B.Sec) :
    pullChart a hq h (H0.ofSec p O s) = H0.ofSec q W (GlobalTheory.chartSec a s) :=
  LB.sec_ext fun i => fun_ext_ger fun z hz => by
    change germ i z hz.1 hz.2 _ = germ i z hz.1 hz.2 _
    rw [germ_pullChart, germ_ofSec]
    exact (congrArg _ (germ_ofSec _ _ _ _ s)).trans (ger_appLE r _ z hz.2 _).symm

theorem pullChart_mul (C : ProdChart P B N) (C' : ProdChart P' B' N') (a : ChartPull P' P r) (b : ChartPull B' B r)
    (c : ChartPull N' N r) (hC : ∀ t, ∃ s, a.idx (C'.a t) = C.a s ∧ b.idx (C'.b t) = C.b s ∧ c.idx (C'.c t) = C.c s)
    (hq : r ≫ p = q ≫ spMap φ) (h : W ≤ r ⁻¹ᵁ O) (σ : H0 p P O) (f : H0 p B O) :
    pullChart c hq h (C.mul σ f) = C'.mul (pullChart a hq h σ) (pullChart b hq h f) :=
  C'.sec_ext fun t z hz ha hb hc => by
    obtain ⟨s, e₁, e₂, e₃⟩ := hC t
    have key (y hy i j l) (e₁ : i = C.a s) (e₂ : j = C.b s) (e₃ : l = C.c s) (hi hj hl) :
        germ l y hy hl (C.mul σ f) = germ i y hy hi σ * germ j y hy hj f := by
      subst e₁ e₂ e₃
      exact C.germ_mul σ f s y hy hi hj hl
    rw [C'.germ_mul _ _ t z hz ha hb hc, germ_pullChart, germ_pullChart, germ_pullChart, ← map_mul]
    exact congrArg _ (key _ _ _ _ _ e₁ e₂ e₃ _ _ _)

end GlobalTheory.Vanishing

namespace GlobalTheory.HermTools

theorem csq_extend {K E V V' : Type*} [Field K] [Field E] [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module E V'] {j : K →+* E} {ι : V →ₛₗ[j] V'} (hι : IsExtension ι) [FiniteDimensional K V] (h : HermFam K V)
    (τ : E →+* ℂ) {κ : Type*} [Fintype κ] (c : κ → ℂ) (v : κ → V) :
    csq (extend hι h) τ c (fun i => ι (v i)) = csq h (τ.comp j) c v := by
  simp only [csq, form_extend]

theorem cnrm_extend_comb {K E V V' : Type*} [Field K] [Field E] [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module E V'] {j : K →+* E} {ι : V →ₛₗ[j] V'} (hι : IsExtension ι) [FiniteDimensional K V] (h : HermFam K V)
    (τ : E →+* ℂ) {κ μ : Type*} [Fintype κ] [Fintype μ] (c : κ → ℂ) (a : κ → μ → E) (v : μ → V) :
    cnrm (extend hι h) τ c (fun i => ∑ l, a i l • ι (v l)) =
      cnrm h (τ.comp j) (fun l => ∑ i, c i * τ (a i l)) v :=
  congrArg Real.sqrt ((csq_comb _ _ _ _ _).trans (csq_extend hι h τ _ v))

end GlobalTheory.HermTools

namespace GlobalTheory.Adelic.HermSys

variable {F : Type} [Field F] [NumberField F] {T : HermSys F} (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem normAt_baseChange (τ : E →+* ℂ) (u : Fin T.N → F) :
    (T.baseChange E).normAt τ (fun j => algebraMap F E (u j)) = T.normAt (τ.comp (algebraMap F E)) u := rfl

theorem NormsLe.baseChange (h : T.NormsLe) : (T.baseChange E).NormsLe :=
  fun k τ => (normAt_baseChange E τ (T.w.col k)).trans_le (h k _)

end GlobalTheory.Adelic.HermSys

namespace GlobalTheory.HilbertSamuel

variable {F : Type} [Field F] [NumberField F]

theorem meanLog_baseChange (E : Type) [Field E] [NumberField E] [Algebra F E] (β : (F →+* ℂ) → ℝ) :
    meanLog E (fun τ => β (τ.comp (algebraMap F E))) = meanLog F β := by
  have h₁ : (Module.finrank F E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [meanLog, meanLog, ← Module.finrank_mul_finrank ℚ F E, Nat.cast_mul,
    Adelic.HeightExt.sum_comp_algebraMap fun σ => Real.log (β σ), mul_comm (Module.finrank ℚ F : ℝ),
    mul_div_mul_left _ _ h₁]

namespace Geo

variable (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem toExt_mulW (j : ℕ) (u : Fin G.N → F) (f : G.Sec j) :
    G.toExt E (j + 1) (G.mulW j u f) = (G.baseChange E).mulW j (algebraMap F E ∘ u) (G.toExt E j f) := by
  refine (pullChart_mul _ (oneChart (isLB_tens (G.baseChange E).K.isLB (G.baseChange E).isLBA) (G.baseChange E).isLB
    (Nat.cast_succ j).symm) (GlobalTheory.chartPullPull G.L (G.fst E)) (G.chartAdj E j) (G.chartAdj E (j + 1))
    (fun t => ⟨((t.1.1 PUnit.unit, t.1.2 PUnit.unit), t.2 PUnit.unit), rfl, rfl, rfl⟩) _ le_rfl _ f).trans ?_
  refine congrArg (fun s => ProdChart.mul _ s _) ?_
  rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (map_smulₛₗ _ _ _).trans (congrArg _ (pullChart_ofSec _ _ _ (G.b k)))

def chartAdj₂ (j : ℕ) : ChartPull ((G.baseChange E).adj₂ j) (G.adj₂ j) (G.fst E) :=
  chartPullTwist (chartPullTens (GlobalTheory.chartPullPull G.K.bundle _) (GlobalTheory.chartPullPull G.L₂ _))
    (GlobalTheory.chartPullPull G.L _) (j + G.D)

def toExt₂ (j : ℕ) : H0 G.str (G.adj₂ j) ⊤ →ₛₗ[algebraMap F E]
    H0 (G.baseChange E).str ((G.baseChange E).adj₂ j) ⊤ :=
  pullChart (G.chartAdj₂ E j) (G.isPullback_fst E).w le_top

theorem isExtension_toExt₂ (j : ℕ) : IsExtension (G.toExt₂ E j) :=
  isExtension_pullChart_top (G.isPullback_fst E) (isLB_tw (isLB_tens G.K.isLB G.isLB₂) G.isLB _)
    (isLB_tw (isLB_tens (G.baseChange E).K.isLB (G.baseChange E).isLB₂) (G.baseChange E).isLB _)
    (G.chartAdj₂ E j) G.geom.alg.variety.proj (G.baseChange E).geom.alg.variety.proj

theorem toExt_mulE (j : ℕ) (f : H0 G.str (G.adj₂ j) ⊤) :
    G.toExt E j (G.mulE j f) = (G.baseChange E).mulE j (G.toExt₂ E j f) := by
  refine (restr_pullChart (G.chartAdj E j) (G.isPullback_fst E).w (W := ⊤) le_top le_rfl le_top le_top _).symm.trans
    (congrArg _ ?_)
  refine (pullChart_mul _ (quotChart (G.baseChange E).K.isLB (G.baseChange E).isLBA (G.baseChange E).isLB₂
    (G.baseChange E).isLB rfl) (chartPullQuot (GlobalTheory.chartPullPull G.LA (G.fst E))
    (chartPullTwist (GlobalTheory.chartPullPull G.L₂ _) (GlobalTheory.chartPullPull G.L _) _)) (G.chartAdj₂ E j) (G.chartAdj E j)
    (fun t => ⟨(t.1 PUnit.unit, t.2.1 PUnit.unit, t.2.2.1 PUnit.unit, t.2.2.2 PUnit.unit), rfl, rfl, rfl⟩)
    _ le_top _ f).trans ?_
  exact congrArg (fun s => ProdChart.mul _ s _) (pullChart_ofSec _ _ _ G.e)

end Geo

namespace Data

variable {X : Data F} (E : Type) [Field E] [NumberField E] [Algebra F E]

variable (X) in

theorem toExtV_inclE {j : ℕ} (hj : j ≤ X.T) (f : H0 X.str (X.adj₂ j) ⊤) :
    X.toExtV E j (X.inclE hj f) = (X.baseChange E).inclE hj (X.toExt₂ E j f) :=
  Subtype.ext (X.toExt_mulE E j f)

variable (X) in

theorem toExtV_mem {j : ℕ} {x : X.V j} (hx : x ∈ X.M j) : X.toExtV E j x ∈ (X.baseChange E).M j :=
  (Submodule.subset_span ⟨x, hx, rfl⟩ : extMap (X.toExt E j) (X.V j) x ∈
    Submodule.span (𝓞 E) (extMap (X.toExt E j) (X.V j) '' X.M j))

theorem MulStable.baseChange (h : X.MulStable) : (X.baseChange E).MulStable := fun j hj w hw f hf => by
  let X' := X.baseChange E
  let S := (X'.M (j + 1)).map ((X'.V (j + 1)).subtype.restrictScalars (𝓞 E))
  change X'.mulW j w f ∈ S
  induction hw using Submodule.span_induction with
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [← algebraMap_smul E, map_smul, LinearMap.smul_apply, algebraMap_smul]; exact S.smul_mem _ ha
  | mem w hw =>
    obtain ⟨k, rfl⟩ := hw
    induction hf using Submodule.span_induction with
    | zero => exact (map_zero (X'.mulW j _)).symm ▸ zero_mem _
    | add a b _ _ ha hb => exact (map_add (X'.mulW j _) _ _).symm ▸ add_mem ha hb
    | smul c a _ ha =>
      exact (map_smul (X'.mulW j _) (algebraMap _ E c) _).symm ▸ S.smul_mem c ha
    | mem f hf =>
      obtain ⟨f, hf, rfl⟩ := hf
      obtain ⟨g, hg, e⟩ := h j hj _ (Submodule.subset_span ⟨k, rfl⟩) f hf
      exact ⟨_, X.toExtV_mem E hg, (congrArg (X.toExt E (j + 1)) e).trans (X.toExt_mulW E j _ _)⟩

variable {E} in

theorem MulStable.mulBoundAt_baseChange (h : X.MulStable) {τ : E →+* ℂ} {β : ℝ}
    (hb : X.MulBoundAt (τ.comp (algebraMap F E)) β) : (X.baseChange E).MulBoundAt τ β := by
  intro j hj u m c f g e
  let b := Module.finBasis F (X.V j)
  let b' := (X.isExtension_extMap E j).basis b
  let G : Fin X.N × Fin _ → X.V (j + 1) := fun t => ⟨_, h.mem hj (Pi.single t.1 1) (b t.2)⟩
  obtain ⟨a, rfl⟩ : ∃ a : Fin m → Fin _ → E, f = fun i => ∑ l, a i l • X.toExtV E j (b l) :=
    ⟨fun i l => b'.repr (f i) l, funext fun i => (b'.sum_repr (f i)).symm.trans
      (Finset.sum_congr rfl fun l _ => congrArg _ (IsExtension.basis_apply _ _ _))⟩
  have hG (t) : (X.toExtV E (j + 1) (G t) : (X.baseChange E).Sec (j + 1)) =
      (X.baseChange E).mulW j (Pi.single t.1 1) (X.toExtV E j (b t.2)) :=
    (X.toExt_mulW E j _ _).trans (congrArg (fun w => (X.baseChange E).mulW j w _)
      (funext fun l : Fin X.N => (by simp [Pi.single_apply] :
        algebraMap F E (Pi.single (M := fun _ => F) t.1 1 l) = Pi.single (M := fun _ => E) t.1 1 l)))
  change Fin X.N → ℂ at u
  obtain rfl : g = fun t : Fin X.N × Fin m => ∑ s, (if s.1 = t.1 then a t.2 s.2 else 0) • X.toExtV E (j + 1) (G s) :=
    funext fun t : Fin X.N × Fin m => Subtype.ext <| (e t.1 t.2).trans <| by
      simp only [Fintype.sum_prod_type, ite_smul, zero_smul, Finset.sum_ite_irrel, Finset.sum_const_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hG]
  refine (cnrm_extend_comb (X.isExtension_extMap E (j + 1)) _ τ _ _ G).trans_le
    (le_of_eq_of_le (congrArg (cnrm _ _ · G) (funext fun s => ?_))
    ((hb j hj u _ (fun l => ∑ i, c i * τ (a i l)) b G fun _ _ => rfl).trans_eq
      (congrArg _ (cnrm_extend_comb (X.isExtension_extMap E j) _ τ c a b).symm)))
  change ∑ t : Fin X.N × Fin m, u t.1 * c t.2 * τ (if s.1 = t.1 then a t.2 s.2 else 0) = _
  simp [Fintype.sum_prod_type, apply_ite τ, Finset.mul_sum, mul_assoc]

theorem MulStable.mulBound_baseChange (h : X.MulStable) {β : (F →+* ℂ) → ℝ} (hb : ∀ σ, X.MulBoundAt σ (β σ)) :
    (X.baseChange E).MulBound fun τ => β (τ.comp (algebraMap F E)) :=
  (h.baseChange E).mulBound fun _ => h.mulBoundAt_baseChange (hb _)

variable (X) in

theorem latRank_M_baseChange (j : ℕ) : latRank E ((X.baseChange E).M j) = latRank F (X.M j) := by
  rw [latRank_M, latRank_M, finrank_V_baseChange]

theorem ShortFamily.baseChange {j : ℕ} {Λ : ℝ} (h : X.ShortFamily j Λ) : (X.baseChange E).ShortFamily j Λ := by
  obtain ⟨v, h₁, h₂, h₃⟩ := h
  have e := X.latRank_M_baseChange E j
  exact ⟨fun i => X.toExtV E j (v (i.cast e)), fun i => X.toExtV_mem E (h₁ _),
    ((X.isExtension_extMap E j).indep _ v h₂).comp _ (Fin.cast_injective e),
    fun i τ => (X.nrm_toExtV E j τ _).trans_le (h₃ _ _)⟩

theorem ShortFamilyMean.baseChange {j : ℕ} {Λ : ℝ} (h : X.ShortFamilyMean j Λ) :
    (X.baseChange E).ShortFamilyMean j Λ := by
  obtain ⟨v, h₁, h₂, h₃⟩ := h
  have e := X.latRank_M_baseChange E j
  refine ⟨fun i => X.toExtV E j (v (i.cast e)), fun i => X.toExtV_mem E (h₁ _),
    ((X.isExtension_extMap E j).indep _ v h₂).comp _ (Fin.cast_injective e), fun i => le_of_eq_of_le ?_ (h₃ (i.cast e))⟩
  exact (congrArg _ (funext fun τ => X.nrm_toExtV E j τ _)).trans
    (meanLog_baseChange E fun σ => (X.nm j).nrm σ (v (i.cast e)))

variable (X) in

theorem baseChange_mul_short :
    (∀ j u f, X.toExt E (j + 1) (X.mulW j u f) =
      (X.baseChange E).mulW j (algebraMap F E ∘ u) (X.toExt E j f)) ∧
    (∀ j f, X.toExt E j (X.mulE j f) = (X.baseChange E).mulE j (X.toExt₂ E j f)) ∧
    (X.MulStable → (X.baseChange E).MulStable) ∧
    (X.MulStable → ∀ (τ : E →+* ℂ) β, X.MulBoundAt (τ.comp (algebraMap F E)) β → (X.baseChange E).MulBoundAt τ β) ∧
    (X.MulStable → ∀ β : (F →+* ℂ) → ℝ, (∀ σ, X.MulBoundAt σ (β σ)) →
      (X.baseChange E).MulBound fun τ => β (τ.comp (algebraMap F E))) ∧
    (∀ j Λ, X.ShortFamily j Λ → (X.baseChange E).ShortFamily j Λ) ∧
    (∀ j Λ, X.ShortFamilyMean j Λ → (X.baseChange E).ShortFamilyMean j Λ) ∧
    (X.NormsLe → (X.baseChange E).NormsLe) ∧
    ∀ β : (F →+* ℂ) → ℝ, meanLog E (fun τ => β (τ.comp (algebraMap F E))) = meanLog F β :=
  ⟨X.toExt_mulW E, X.toExt_mulE E, fun h => h.baseChange E, fun h _ _ => h.mulBoundAt_baseChange,
    fun h _ => h.mulBound_baseChange E, fun _ _ h => h.baseChange E, fun _ _ h => h.baseChange E,
    fun h => h.baseChange E, meanLog_baseChange E⟩

end Data

end GlobalTheory.HilbertSamuel
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField Set MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing GlobalTheory.TopForm GlobalTheory.ChartGlue

namespace GlobalTheory

section BaseChange

variable {k k' : Type} [CommRing k] [CommRing k'] {ρ : k →+* k'} {Y Y' : Scheme.{0}} {p : Y ⟶ Sp k}
  {p' : Y' ⟶ Sp k'} {r : Y' ⟶ Y} {σ : k →+* ℂ} {τ : k' →+* ℂ} {D : ℕ} {m : CxPts p' τ → CxPts p σ}

theorem CxPts.ev_appLE_of_comp (hm : ∀ z, (m z).1 = z.1 ≫ r) {U : Y.Opens} {W : Y'.Opens} (h : W ≤ r ⁻¹ᵁ U)
    (g : Γ(Y, U)) {z : CxPts p' τ} (hz : z ∈ ptsIn p' τ W) :
    ev p' τ W ((r.appLE U W h).hom g) z = ev p σ U g (m z) :=
  (ev_res h hz _).trans (ev_of_comp hm U g z).symm

def CxPts.bcMap (w : r ≫ p = p' ≫ spMap ρ) (τ : k' →+* ℂ) (z : CxPts p' τ) : CxPts p (τ.comp ρ) :=
  ⟨z.1 ≫ r, by
    rw [Category.assoc, w, ← Category.assoc, z.2, spMap, spMap, spMap, ← Spec.map_comp]
    rfl⟩

theorem CxPts.bijective_bcMap (H : IsPullback r p' p (spMap ρ)) (τ : k' →+* ℂ) :
    Function.Bijective (bcMap H.w τ) := by
  refine ⟨fun z z' h => Subtype.ext (H.hom_ext (congrArg Subtype.val h) (z.2.trans z'.2.symm)), fun y => ?_⟩
  have e : y.1 ≫ p = spMap τ ≫ spMap ρ := by
    rw [y.2, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  exact ⟨⟨H.lift y.1 (spMap τ) e, H.lift_snd _ _ _⟩, Subtype.ext (H.lift_fst _ _ _)⟩

theorem etale_coords_baseChange (H : IsPullback r p' p (spMap ρ)) {U : Y.Opens} (hU : IsAffineOpen U)
    {x : Fin D → Γ(Y, U)} (hx : (MvPolynomial.eval₂Hom (algX p U) x).Etale) :
    (MvPolynomial.eval₂Hom (algX p' (r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤))
      fun a => (r.appLE U _ inf_le_left).hom (x a)).Etale := by
  letI := ρ.toAlgebra
  letI := MvPolynomial.algebraMvPolynomial (R := k) (S := k') (σ := Fin D)
  have h₁ := (CommRingCat.isPushout_of_isPushout k k' (MvPolynomial (Fin D) k) (MvPolynomial (Fin D) k')).flip
  have h₂ := isPushout_sections p p' r H U hU
  have e₁ : CommRingCat.ofHom (algX p U) = CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin D) k)) ≫
      CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX p U) x) := by
    ext a
    exact (MvPolynomial.eval₂Hom_C _ _ a).symm
  have e₂ : CommRingCat.ofHom (algX p' (r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤)) =
      CommRingCat.ofHom (algebraMap k' (MvPolynomial (Fin D) k')) ≫
      CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX p' (r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤))
        fun a => (r.appLE U _ inf_le_left).hom (x a)) := by
    ext a
    exact (MvPolynomial.eval₂Hom_C _ _ a).symm
  rw [e₁, e₂] at h₂
  have h₃ := h₂.of_left (CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_)) h₁
  · have := RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
    exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty RingHom.Etale) h₃.flip hx
  · change (r.appLE U _ _).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)) =
      MvPolynomial.eval₂Hom _ _ (MvPolynomial.map ρ (MvPolynomial.C a))
    rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
    exact RingHom.congr_fun (appLE_comp_algX H.w (inf_le_left : r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤ ≤ _)) a
  · change (r.appLE U _ _).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X a)) =
      MvPolynomial.eval₂Hom _ _ (MvPolynomial.map ρ (MvPolynomial.X a))
    rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']

theorem AlgChart.exists_baseChange (H : IsPullback r p' p (spMap ρ)) (hm : ∀ z, (m z).1 = z.1 ≫ r)
    (c : AlgChart p σ D) {z : CxPts p' τ} (hz : m z ∈ c.e.source) :
    ∃ c' : AlgChart p' τ D, z ∈ c'.e.source ∧ ∃ h : c'.U ≤ r ⁻¹ᵁ c.U,
      ∀ a, c'.x a = (r.appLE c.U c'.U h).hom (c.x a) := by
  have hU : IsAffineOpen (r ⁻¹ᵁ c.U ⊓ p' ⁻¹ᵁ ⊤) := by
    rw [show r ⁻¹ᵁ c.U ⊓ p' ⁻¹ᵁ ⊤ = r ⁻¹ᵁ c.U from inf_top_eq _]
    exact isAffineOpen_preimage_of_isPullback H c.affine
  obtain ⟨⟨e, U, hU', x, hx, h₁, h₂, h₃⟩, hy, hU', hx'⟩ := AlgChart.exists_of_etale hU _
    (etale_coords_baseChange H c.affine c.etale)
    (mem_ptsIn_inf.2 ⟨(mem_ptsIn_preimage hm).2 (c.source_subset hz), mem_ptsIn_top⟩ : z ∈ ptsIn p' τ _)
  dsimp only at hU'
  subst hU'
  dsimp only at hx'
  subst hx'
  exact ⟨_, hy, inf_le_left, fun _ => rfl⟩

variable [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p']

theorem AlgChart.rv_baseChange (H : IsPullback r p' p (spMap ρ)) (hm : ∀ z, (m z).1 = z.1 ≫ r) (K : CanonLB p D)
    {c : AlgChart p σ D} {c' : AlgChart p' τ D} (h : c'.U ≤ r ⁻¹ᵁ c.U)
    (hx : ∀ a, c'.x a = (r.appLE c.U c'.U h).hom (c.x a)) {a : (K.baseChange H).bundle.ι} {z : CxPts p' τ}
    (hz : z ∈ ptsIn p' τ c'.U) (ha : z ∈ ptsIn p' τ ((K.baseChange H).bundle.U a)) :
    rv τ c'.isFrame ((K.baseChange H).isFrame a) z = rv σ c.isFrame (K.isFrame (a PUnit.unit)) (m z) := by
  have hl : (K.baseChange H).bundle.U a ≤ r ⁻¹ᵁ K.bundle.U (a PUnit.unit) := (GlobalTheory.chartPullPull K.bundle r).le a
  have e := c.rv_mul_jacobian K ((mem_ptsIn_preimage hm).1 (ptsIn_mono h hz))
    ((mem_ptsIn_preimage hm).1 (ptsIn_mono hl ha))
  have e' := c'.rv_mul_jacobian (K.baseChange H) hz ha
  have hW : (K.baseChange H).bundle.U a ⊓ c'.U ≤ r ⁻¹ᵁ (K.bundle.U (a PUnit.unit) ⊓ c.U) := inf_le_inf hl h
  have e₂ := K.jacobian_baseChange H a inf_le_left (W := (K.baseChange H).bundle.U a ⊓ c'.U) inf_le_left hW
    fun i => resG Y inf_le_right (c.x i)
  rw [← ev_appLE_of_comp hm hW _ (mem_ptsIn_inf.2 ⟨ha, hz⟩), ← e₂] at e
  simp only [hx, LB.resG_appLE] at e'
  simp only [LB.appLE_resG] at e
  exact left_inv_eq_right_inv e' ((mul_comm _ _).trans e)

variable {B : LB Y} {B' : LB Y'}

theorem AnRead.topInt_baseChange [SecondCountableTopology (CxPts p σ)] [SecondCountableTopology (CxPts p' τ)]
    (H : IsPullback r p' p (spMap ρ)) (hm : ∀ z, (m z).1 = z.1 ≫ r) (hb : Function.Bijective m)
    (R : AnRead p σ D) (R' : AnRead p' τ D) (K : CanonLB p D) (b : ChartPull B' B r)
    {φ : Weight p σ B} {φ' : Weight p' τ B'}
    (hφ : ∀ i z, z ∈ ptsIn p' τ (B'.U i) → φ'.φ i z = φ.φ (b.idx i) (m z))
    {f : (tens K.bundle B).ι → CxPts p σ → ℂ} (hf : f ∈ fibSec p σ _)
    {f' : (tens (K.baseChange H).bundle B').ι → CxPts p' τ → ℂ}
    (hf' : ∀ a i z, z ∈ ptsIn p' τ ((K.baseChange H).bundle.U a) → z ∈ ptsIn p' τ (B'.U i) →
      f' (a, i) z = f (a PUnit.unit, b.idx i) (m z)) :
    R'.topInt (K.baseChange H) φ' f' = R.topInt K φ f := by
  have hc := continuous_of_comp hm
  have key (z : CxPts p' τ) : ∃ S, IsOpen S ∧ m z ∈ S ∧ ∀ A, MeasurableSet A → A ⊆ S →
      R'.topMeasure (K.baseChange H) φ' f' (m ⁻¹' A) = R.topMeasure K φ f A := by
    obtain ⟨c, hz⟩ := AlgChart.exists_mem_source (D := D) (m z)
    obtain ⟨c', hz', h, hx⟩ := c.exists_baseChange H hm hz
    have he (w) (h₁ : w ∈ c'.e.source) (h₂ : m w ∈ c.e.source) : c.e (m w) = c'.e w := by
      ext a
      rw [c.apply_eq _ h₂, c'.apply_eq _ h₁, hx, ev_appLE_of_comp hm h _ (c'.source_subset h₁)]
    have ho := isOpen_over c'.e (c.e.open_source.preimage hc)
    refine ⟨_, c.e.isOpen_inter_preimage ho, ⟨hz, ?_⟩, fun A hA hAS => ?_⟩
    · rw [mem_preimage, he z hz' hz]
      exact mem_over c'.e hz' hz
    have hs (w) (hw : m w ∈ A) : w ∈ c'.e.source := by
      obtain ⟨h₁, h₂, h₃⟩ := hAS hw
      have h₄ := c'.e.map_target h₂
      rw [hb.1 (c.e.injOn h₁ h₃ ((he _ h₄ h₃).trans (c'.e.right_inv h₂)).symm)]
      exact h₄
    have hA' : MeasurableSet (m ⁻¹' A) := hc.measurable hA
    have hi : c.e '' A = c'.e '' (m ⁻¹' A) := by
      conv_lhs => rw [← image_preimage_eq A hb.2, image_image]
      exact image_congr fun w hw => he w (hs w hw) (hAS hw).1
    rw [R'.topMeasure_apply _ _ _ c' hA' hs, R.topMeasure_apply _ _ _ c hA (hAS.trans inter_subset_left), hi]
    refine setLIntegral_congr_fun (measurableSet_image c'.e hA' hs) ?_
    rintro _ ⟨w, hw, rfl⟩
    have h₁ := hs w hw
    have h₂ := (hAS hw).1
    have ha := mem_pick (K.baseChange H).isLB w
    have hi := mem_pick φ'.isLB w
    dsimp only
    rw [c'.e.left_inv h₁, ← he w h₁ h₂, c.e.left_inv h₂, c.topDens_eq K φ hf h₂
      ((mem_ptsIn_preimage hm).1 (ptsIn_mono ((GlobalTheory.chartPullPull K.bundle r).le _) ha))
      ((mem_ptsIn_preimage hm).1 (ptsIn_mono (b.le _) hi)), AlgChart.topDens, AlgChart.topCoeff,
      hφ _ _ hi, hf' _ _ _ ha hi, AlgChart.rv_baseChange H hm K h hx (c'.source_subset h₁) ha]
    rfl
  choose S hS hzS hμ using key
  have e : (R'.topMeasure (K.baseChange H) φ' f').map m = R.topMeasure K φ f :=
    ext_of_cover S hS (fun y => by obtain ⟨z, rfl⟩ := hb.2 y; exact ⟨z, hzS z⟩) fun z A hA h =>
      (Measure.map_apply hc.measurable hA).trans (hμ z A hA h)
  rw [topInt, topInt, ← e, Measure.map_apply hc.measurable MeasurableSet.univ, preimage_univ]

omit [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p'] in

theorem Vanishing.cval_pullChart (hm : ∀ z, (m z).1 = z.1 ≫ r) (b : ChartPull B' B r) (w : r ≫ p = p' ≫ spMap ρ)
    (f : H0 p B ⊤) {i : B'.ι} {z : CxPts p' τ} (hz : z ∈ ptsIn p' τ (B'.U i)) :
    cval τ (pullChart (W := ⊤) b w le_top f) i z = cval σ f (b.idx i) (m z) :=
  ev_appLE_of_comp hm (inf_le_inf le_top (b.le i)) _ (mem_ptsIn_inf.2 ⟨mem_ptsIn_top, hz⟩)

end BaseChange

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem Adelic.HermSys.weight_baseChange (T : Adelic.HermSys F) (hb : T.BasePointFree) (hh : T.Hermitian)
    (hb' : (T.baseChange E).BasePointFree) (hh' : (T.baseChange E).Hermitian) {τ : E →+* ℂ}
    {m : CxPts (T.baseChange E).str τ → CxPts T.str (τ.comp (algebraMap F E))}
    (hm : ∀ z, (m z).1 = z.1 ≫ T.bcFst E) (i : (T.baseChange E).L.ι) {z : CxPts (T.baseChange E).str τ}
    (hz : z ∈ ptsIn _ τ ((T.baseChange E).L.U i)) :
    ((T.baseChange E).weight hb' hh' τ).φ i z =
      (T.weight hb hh (τ.comp (algebraMap F E))).φ (i PUnit.unit) (m z) := by
  rw [Adelic.HermSys.weight_φ, Adelic.HermSys.weight_φ]
  exact congrArg (fun v => Real.log (archSize (T.A (τ.comp (algebraMap F E))) v ^ 2)) (funext fun j =>
    ev_appLE_of_comp hm ((GlobalTheory.chartPullPull T.L (T.bcFst E)).le i) _ hz)

namespace HilbertSamuel

theorem Geo.sqInt_baseChange (G : Geo F) (j : ℕ) (τ : E →+* ℂ) {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (f : ι → H0 G.str (G.adj₂ j) ⊤) :
    (G.baseChange E).sqInt j τ (∑ i, c i • cval τ (G.toExt₂ E j (f i))) =
      G.sqInt j (τ.comp (algebraMap F E)) (∑ i, c i • cval (τ.comp (algebraMap F E)) (f i)) := by
  have H := G.isPullback_fst E
  have hm : ∀ z, (bcMap H.w τ z).1 = z.1 ≫ G.fst E := fun _ => rfl
  have : SmoothOfRelativeDimension G.D (G.baseChange E).str := (G.baseChange E).smooth
  refine AnRead.topInt_baseChange H hm (bijective_bcMap H τ) _ _ G.K
    (chartPullTwist (GlobalTheory.chartPullPull G.L₂ _) (GlobalTheory.chartPullPull G.L _) (j + G.D)) (fun i z hz => ?_)
    (assocVal_mem_holSec (R := AnRead.all _ _ G.D)
      (Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (cval_mem_holSec _ _ _))).1 fun a i z ha hi => ?_
  · have h := mem_ptsIn_inf.1 hz
    refine congrArg₂ (· + ·) (G.second.weight_baseChange E _ _ _ _ hm _ h.1)
      ((Weight.zpow_φ _ _ _ _).trans (Eq.trans (congrArg _ ?_) (Weight.zpow_φ _ _ _ _).symm))
    exact G.toHermSys.weight_baseChange E _ _ _ _ hm _ (mem_pow_iff.1 h.2)
  · have h := mem_ptsIn_inf.1 hi
    have hz : z ∈ ptsIn _ τ (((G.baseChange E).adj₂ j).U ((a, i.1), i.2)) :=
      mem_ptsIn_inf.2 ⟨mem_ptsIn_inf.2 ⟨ha, h.1⟩, h.2⟩
    change (∑ l, c l • cval τ (G.toExt₂ E j (f l))) ((a, i.1), i.2) z =
      (∑ l, c l • cval _ (f l)) ((G.chartAdj₂ E j).idx ((a, i.1), i.2)) (bcMap H.w τ z)
    simp only [Finset.sum_apply, Pi.smul_apply]
    exact ((congrFun (Finset.sum_apply _ _ _) z).trans (Finset.sum_apply _ _ _)).trans
      (Finset.sum_congr rfl fun l _ => congrArg (c l • ·) (cval_pullChart hm (G.chartAdj₂ E j) H.w (f l) hz))

theorem Data.IntegralBound.baseChange {X : Data F} {β κ : (F →+* ℂ) → ℝ} (h : X.IntegralBound β κ) :
    (X.baseChange E).IntegralBound (fun τ => β (τ.comp (algebraMap F E))) fun τ => κ (τ.comp (algebraMap F E)) := by
  intro j hj τ m c f
  have := finite_top X.geom.alg.variety.proj (isLB_tw (isLB_tens X.K.isLB X.isLB₂) X.isLB ((j : ℤ) + X.D))
  let b := Module.finBasis F (H0 X.str (X.adj₂ j) ⊤)
  let b' := (X.isExtension_toExt₂ E j).basis b
  obtain ⟨a, rfl⟩ : ∃ a : Fin m → Fin _ → E, f = fun i => ∑ l, a i l • X.toExt₂ E j (b l) :=
    ⟨fun i l => b'.repr (f i) l, funext fun i => (b'.sum_repr (f i)).symm.trans
      (Finset.sum_congr rfl fun l _ => congrArg _ (IsExtension.basis_apply _ _ _))⟩
  have e₁ : (fun i => (X.baseChange E).inclE hj (∑ l, a i l • X.toExt₂ E j (b l))) =
      fun i => ∑ l, a i l • X.toExtV E j (X.inclE hj (b l)) := funext fun i =>
    (map_sum _ _ _).trans (Finset.sum_congr rfl fun l _ =>
      (map_smul _ _ _).trans (congrArg _ (X.toExtV_inclE E hj _).symm))
  have e₂ : ∑ i, c i • cval τ (∑ l, a i l • X.toExt₂ E j (b l)) =
      ∑ l, (∑ i, c i * τ (a i l)) • cval τ (X.toExt₂ E j (b l)) := by
    simp only [map_sum, map_smulₛₗ, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  refine (congrArg (csq _ τ c) e₁).trans_le (((csq_comb _ _ _ _ _).trans
    (csq_extend (X.isExtension_extMap E j) _ τ _ _)).trans_le ((h j hj _ _ _ b).trans_eq (congrArg _ ?_)))
  exact congrArg ENNReal.toReal ((congrArg _ e₂).trans (X.sqInt_baseChange E j τ _ b)).symm

end HilbertSamuel

end GlobalTheory
end
end
