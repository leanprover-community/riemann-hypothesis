import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricOnSet
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernIntegralEqDegree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeGramNearPoint

section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_metric_on_set : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} [SmoothOfRelativeDimension Dw.dim (genStr Z)] {σ : c.F →+* ℂ} (G : EigMet Z σ) (S : Set (CxPts (genStr Z) σ)), (∀ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (F : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (τ : E →+* ℂ) (a b : Fin (Dw.mult τ)), LogKS.chart V ≫ genStr Z = spMap φ → ∀ y₀ ∈ S, y₀ ∈ ptsIn (genStr Z) σ V.1 → ∃ (T : Set (CxPts (genStr Z) σ)) (g : CxPts (genStr Z) σ → ℂ), IsOpen T ∧ y₀ ∈ T ∧ (manifold Z σ).SmoothOn T (fun y => (g y).re) ∧ (manifold Z σ).SmoothOn T (fun y => (g y).im) ∧ ∀ y ∈ T, ∀ (hy : y ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ (y.1 ≫ genι Z)), F.IsMap (evHom hy) f → G.gram y f τ a b = g y) → G.SmoothOn (manifold Z σ) S := by
  first | exact @GlobalTheory.ShFam.EigMet.smoothOn_of_locally | exact GlobalTheory.ShFam.EigMet.smoothOn_of_locally | (intros; apply GlobalTheory.ShFam.EigMet.smoothOn_of_locally <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConjChart

open ReciprocityTheory.L2DbarEstimates (V)

noncomputable def conjCoord (d : ℕ) : V d ≃ₜ V d where
  toFun v := WithLp.toLp 2 (star v.ofLp)
  invFun v := WithLp.toLp 2 (star v.ofLp)
  left_inv v := by simp
  right_inv v := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem differentiableAt_conj_comp {d : ℕ} {F : V d → ℂ} {v : V d}
    (h : DifferentiableAt ℂ F (conjCoord d v)) :
    DifferentiableAt ℂ (fun w => starRingEnd ℂ (F (conjCoord d w))) v := by
  have h1 : DifferentiableAt ℂ (F ∘ (EuclideanSpace.equiv (Fin d) ℂ).symm) (star v.ofLp) :=
    h.comp (star v.ofLp) (EuclideanSpace.equiv (Fin d) ℂ).symm.differentiableAt
  have h2 := h1.star_star
  rw [star_star] at h2
  exact h2.comp v (EuclideanSpace.equiv (Fin d) ℂ).differentiableAt

section

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ}

noncomputable def conjPts (p : Y ⟶ Sp k) (h : σ = (starRingEnd ℂ).comp σ') : CxPts p σ' ≃ₜ CxPts p σ :=
  (Points.conjHomeomorph Y).subtype fun y => by
    have e : spMap σ = spMap (starRingEnd ℂ) ≫ spMap σ' := by
      rw [h, spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    change y ≫ p = _ ↔ (spMap (starRingEnd ℂ) ≫ y) ≫ p = _
    rw [e, Category.assoc]
    exact (Points.conjHomeomorph (Sp k)).injective.eq_iff.symm

theorem mem_ptsIn_of_conj {y : CxPts p σ} {y' : CxPts p σ'} (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    {U : Y.Opens} (hy : y ∈ ptsIn p σ U) : y' ∈ ptsIn p σ' U := by
  change ⊤ ≤ y'.1 ⁻¹ᵁ U
  rw [h]
  exact fun x _ => hy (Set.mem_univ _)

noncomputable def conjChart (h : σ = (starRingEnd ℂ).comp σ') {d : ℕ} (c : AlgChart p σ' d) : AlgChart p σ d where
  e := ((conjPts p h).symm.transOpenPartialHomeomorph c.e).transHomeomorph (conjCoord d)
  U := c.U
  affine := c.affine
  x := c.x
  etale := c.etale
  source_subset y hy := by
    obtain ⟨z, rfl⟩ := (conjPts p h).surjective y
    have hz : (conjPts p h).symm (conjPts p h z) ∈ c.e.source := hy
    rw [Homeomorph.symm_apply_apply] at hz
    exact mem_ptsIn_of_conj rfl (c.source_subset hz)
  apply_eq y hy a := by
    obtain ⟨z, rfl⟩ := (conjPts p h).surjective y
    have hz : (conjPts p h).symm (conjPts p h z) ∈ c.e.source := hy
    change starRingEnd ℂ (c.e ((conjPts p h).symm (conjPts p h z)) a) = _
    rw [Homeomorph.symm_apply_apply] at hz ⊢
    rw [c.apply_eq z hz]
    exact (CxPts.ev_conj rfl (c.source_subset hz) _).symm
  holo W f v hv := by
    have h1 : conjCoord d v ∈ c.e.target := hv.1
    have h2 : conjPts p h (c.e.symm (conjCoord d v)) ∈ ptsIn p σ W := hv.2
    have h3 : c.e.symm (conjCoord d v) ∈ ptsIn p σ' W := by
      have := mem_ptsIn_of_conj (y' := (conjPts p h).symm (conjPts p h (c.e.symm (conjCoord d v)))) rfl h2
      rwa [Homeomorph.symm_apply_apply] at this
    have ho := GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn W)
    have hd := differentiableAt_conj_comp ((c.holo W f).differentiableAt (ho.mem_nhds ⟨h1, h3⟩))
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [(ho.preimage (conjCoord d).continuous).mem_nhds ⟨h1, h3⟩] with w hw
    exact CxPts.ev_conj (y' := conjPts p h (c.e.symm (conjCoord d w))) rfl hw.2 f

end

theorem continuous_and_exists_conj_chart :
    ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d p] (σ σ' : k →+* ℂ) (j : CxPts p σ' → CxPts p σ), σ = (starRingEnd ℂ).comp σ' → IsConjMap j → Continuous j ∧ ∀ c' : AlgChart p σ' d, ∃ c : AlgChart p σ d, (∀ z, j z ∈ c.e.source ↔ z ∈ c'.e.source) ∧ ∀ z ∈ c'.e.source, ∀ a, c.e (j z) a = starRingEnd ℂ (c'.e z a) := by
  intro k _ Y p d _ σ σ' j h hj
  obtain rfl : j = conjPts p h := funext fun z => Subtype.ext (hj z)
  refine ⟨(conjPts p h).continuous, fun c => ⟨conjChart h c, fun z => ?_, fun z _ a => ?_⟩⟩
  · change (conjPts p h).symm (conjPts p h z) ∈ c.e.source ↔ _
    rw [Homeomorph.symm_apply_apply]
  · change starRingEnd ℂ (c.e ((conjPts p h).symm (conjPts p h z)) a) = _
    rw [Homeomorph.symm_apply_apply]

end GlobalTheory.ConjChart
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open ReciprocityTheory.L2DbarEstimates (V bas wd wdb leviV)
open Filter Topology
open scoped ContDiff

namespace GlobalTheory.ShFam

attribute [local instance] Over.cartesianMonoidalCategory

def conjV (n : ℕ) : V n ≃ₗᵢ[ℝ] V n := LinearIsometryEquiv.piLpCongrRight 2 fun _ => Complex.conjLIE

theorem conjV_apply (n : ℕ) (v : V n) (a : Fin n) : conjV n v a = starRingEnd ℂ (v a) := rfl

theorem conjV_bas (n : ℕ) (j : Fin n) : conjV n (bas n j) = bas n j := by
  ext a
  simp only [conjV_apply, bas, EuclideanSpace.single_apply]
  split_ifs <;> simp

theorem conjV_I_smul_bas (n : ℕ) (j : Fin n) : conjV n (Complex.I • bas n j) = -(Complex.I • bas n j) := by
  ext a
  simp only [conjV_apply, bas, PiLp.smul_apply, PiLp.neg_apply, EuclideanSpace.single_apply, smul_eq_mul]
  split_ifs <;> simp

theorem fderiv_comp_conjV (n : ℕ) (F : V n → ℂ) (y w : V n) :
    fderiv ℝ (F ∘ conjV n) y w = fderiv ℝ F (conjV n y) (conjV n w) := by
  change fderiv ℝ (F ∘ (conjV n).toContinuousLinearEquiv) y w = _
  rw [ContinuousLinearEquiv.comp_right_fderiv]
  rfl

theorem wd_comp_conjV (n : ℕ) (j : Fin n) (F : V n → ℂ) (y : V n) :
    wd n j (F ∘ conjV n) y = wdb n j F (conjV n y) := by
  simp only [wd, wdb, fderiv_comp_conjV, conjV_bas, conjV_I_smul_bas, map_neg]
  ring

theorem wdb_comp_conjV (n : ℕ) (j : Fin n) (F : V n → ℂ) (y : V n) :
    wdb n j (F ∘ conjV n) y = wd n j F (conjV n y) := by
  simp only [wd, wdb, fderiv_comp_conjV, conjV_bas, conjV_I_smul_bas, map_neg]
  ring

theorem leviV_comp_conjV (n : ℕ) (g : V n → ℝ) (y : V n) (ξ : Fin n → ℂ) :
    leviV n ((fun v => (g v : ℂ)) ∘ conjV n) y ξ =
      starRingEnd ℂ (leviV n (fun v => (g v : ℂ)) (conjV n y) (star ξ)) := by
  set G : V n → ℂ := fun v => (g v : ℂ) with hGdef
  have hG : ∀ k, wd n k G = fun w => starRingEnd ℂ (wdb n k G w) := fun k => by
    have e : G = fun w => starRingEnd ℂ (G w) := funext fun w => (Complex.conj_ofReal _).symm
    funext w
    conv_lhs => rw [e]
    exact ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wd_conj' n k G w
  have h1 : ∀ k, wdb n k (G ∘ conjV n) = (wd n k G) ∘ conjV n := fun k =>
    funext fun w => wdb_comp_conjV n k G w
  have h2 : ∀ j k w, wd n j (wdb n k (G ∘ conjV n)) w =
      starRingEnd ℂ (wd n j (wdb n k G) (conjV n w)) := fun j k w => by
    rw [h1, wd_comp_conjV, hG, ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wdb_conj']
  simp only [leviV, h2, map_sum, map_mul, Complex.conj_conj, Pi.star_apply, Complex.star_def]

theorem smoothOn_comp_ddcForm_of_isConjMap : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ)
    [SmoothOfRelativeDimension d p] (σ σ' : k →+* ℂ) (j : CxPts p σ' → CxPts p σ), IsConjMap j →
    ∀ (W : Set (CxPts p σ)) (φ : CxPts p σ → ℝ), IsOpen W → (AnRead.all p σ d).SmoothOn W φ →
    IsOpen (j ⁻¹' W) ∧ (AnRead.all p σ' d).SmoothOn (j ⁻¹' W) (φ ∘ j) ∧
    ∀ (c' : AlgChart p σ' d), ∀ z ∈ c'.e.source, ∃ c : AlgChart p σ d, j z ∈ c.e.source ∧
      ∀ (ψ : CxPts p σ → ℝ) (ξ : Fin d → ℂ), ddcForm (ψ ∘ j) c' z ξ = ddcForm ψ c (j z) (star ξ) := by
  intro k _ Y p d _ σ σ' j hj W φ hW hφ
  rcases isEmpty_or_nonempty (CxPts p σ') with hE | ⟨⟨z0⟩⟩
  · refine ⟨?_, fun c' => ?_, fun c' z => (hE.false z).elim⟩
    · rw [Set.eq_empty_of_isEmpty (j ⁻¹' W)]
      exact isOpen_empty
    · rw [Set.eq_empty_of_isEmpty (j ⁻¹' W)]
      simp
  · have hσ : σ = (starRingEnd ℂ).comp σ' := by
      have h1 := (j z0).2
      rw [hj z0, Category.assoc, z0.2, spMap, spMap, spMap, ← Spec.map_comp] at h1
      have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
      exact h2.symm
    obtain ⟨hcont, hch⟩ := GlobalTheory.ConjChart.continuous_and_exists_conj_chart k Y p d σ σ' j hσ hj
    have key : ∀ c' : AlgChart p σ' d, ∃ c : AlgChart p σ d, (∀ z, j z ∈ c.e.source ↔ z ∈ c'.e.source) ∧
        (∀ z ∈ c'.e.source, c.e (j z) = conjV d (c'.e z)) ∧
        ∀ v ∈ c'.e.target, j (c'.e.symm v) = c.e.symm (conjV d v) := fun c' => by
      obtain ⟨c, hs, he⟩ := hch c'
      have e1 : ∀ z ∈ c'.e.source, c.e (j z) = conjV d (c'.e z) := fun z hz => by
        ext a
        rw [he z hz a, conjV_apply]
      refine ⟨c, hs, e1, fun v hv => ?_⟩
      have hz : c'.e.symm v ∈ c'.e.source := c'.e.map_target hv
      rw [← c.e.left_inv ((hs _).2 hz), e1 _ hz, c'.e.right_inv hv]
    refine ⟨hW.preimage hcont, fun c' => ?_, fun c' z hz => ?_⟩
    · obtain ⟨c, hs, e1, e2⟩ := key c'
      show ContDiffOn ℝ ∞ ((φ ∘ j) ∘ c'.e.symm) (c'.e.target ∩ c'.e.symm ⁻¹' (j ⁻¹' W))
      have hc := hφ.chart hW c
      refine ((hc.comp (conjV d).contDiff.contDiffOn fun v hv => ?_).congr fun v hv => ?_)
      · have hz : c'.e.symm v ∈ c'.e.source := c'.e.map_target hv.1
        refine ⟨?_, ?_⟩
        · have e3 : conjV d v = c.e (j (c'.e.symm v)) := by rw [e1 _ hz, c'.e.right_inv hv.1]
          rw [e3]
          exact c.e.map_source ((hs _).2 hz)
        · show c.e.symm (conjV d v) ∈ W
          rw [← e2 v hv.1]
          exact hv.2
      · show (φ ∘ j) (c'.e.symm v) = (φ ∘ c.e.symm) (conjV d v)
        simp only [Function.comp_apply, e2 v hv.1]
    · obtain ⟨c, hs, e1, e2⟩ := key c'
      refine ⟨c, (hs z).2 hz, fun ψ ξ => ?_⟩
      have h := leviV_comp_conjV d (fun v => ψ (c.e.symm v)) (c'.e z) ξ
      simp only [ddcForm, AlgChart.levi]
      congr 1
      rw [e1 z hz]
      refine Eq.trans (congrArg Complex.re (ReciprocityTheory.L2DbarEstimates.leviV_congr ?_ ξ))
        (Eq.trans (congrArg Complex.re h) (Complex.conj_re _))
      refine eventually_of_mem (c'.e.open_target.mem_nhds (c'.e.map_source hz)) fun v hv => ?_
      simp only [Function.comp_apply, e2 v hv]

end GlobalTheory.ShFam
end
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.HodgeConj

theorem spMap_conj_conj' : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 (Sp ℂ) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => by simp))

theorem spMap_dual_conj_conj' :
    spMap (dualMap (starRingEnd ℂ)) ≫ spMap (dualMap (starRingEnd ℂ)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => by ext <;> simp [dualMap]))

theorem smul_gram_map_conj {n : ℕ} (c : ℝ) (M : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ((c : ℂ) • (Mᴴ * M)) a b = starRingEnd ℂ (((c : ℂ) • ((M.map (starRingEnd ℂ))ᴴ * M.map (starRingEnd ℂ))) a b) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum]

theorem smoothOn_hodge_of_conj : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ σ' : κ.c.F →+* ℂ), σ = (starRingEnd ℂ).comp σ' → (x.hodge σ').SmoothOn (manifold s.T.Z σ') {y | ¬ LiesIn y (genBd s.T.Z)} → (x.hodge σ).SmoothOn (manifold s.T.Z σ) {y | ¬ LiesIn y (genBd s.T.Z)} := by
  intro D A N j S κ s x σ σ' hσ h'
  have hφ : σ' = (starRingEnd ℂ).comp σ := RingHom.ext fun a => by
    rw [hσ]; simp
  have hpt : ∀ y : CxPts (genStr s.T.Z) σ, (spMap (starRingEnd ℂ) ≫ y.1) ≫ genStr s.T.Z = spMap σ' := fun y => by
    have h0 : y.1 ≫ genStr s.T.Z = spMap σ := y.2
    rw [Category.assoc, h0, hσ, spMap, spMap, spMap, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a => by simp)
  let jm : CxPts (genStr s.T.Z) σ → CxPts (genStr s.T.Z) σ' := fun y => ⟨spMap (starRingEnd ℂ) ≫ y.1, hpt y⟩
  have hj : IsConjMap jm := fun _ => rfl
  intro V φ F τ a b hV
  obtain ⟨g', h1, h2, h3⟩ := h' V φ F τ a b hV
  set W' : Set (CxPts (genStr s.T.Z) σ') := {y | ¬ LiesIn y (genBd s.T.Z)} ∩ ptsIn _ σ' V.1 with hW'
  have hWo : IsOpen W' := (isOpen_not_liesIn _).inter (isOpen_ptsIn _)
  have hsub : {y | ¬ LiesIn y (genBd s.T.Z)} ∩ ptsIn _ σ V.1 ⊆ jm ⁻¹' W' := fun y hy =>
    ⟨fun h => hy.1 ((liesIn_iff_of_comp (y := y) (y' := jm y) rfl _).1 h),
      (mem_ptsIn_iff_of_conj (y := y) (y' := jm y) rfl).2 hy.2⟩
  have k1 := (smoothOn_comp_ddcForm_of_isConjMap _ _ (genStr s.T.Z) _ σ' σ jm hj W' _ hWo h1).2.1.mono hsub
  have k2 := (smoothOn_comp_ddcForm_of_isConjMap _ _ (genStr s.T.Z) _ σ' σ jm hj W' _ hWo h2).2.1.mono hsub
  refine ⟨fun y => starRingEnd ℂ (g' (jm y)), k1.congr fun y _ => by simp, (show (manifold s.T.Z σ).SmoothOn _ (fun y => -(g' (jm y)).im) from fun i => (k2 i).neg).congr
    fun y _ => by simp, fun y hy hyV f hf => ?_⟩
  have hnb : ¬ LiesIn y (genBd s.T.Z) := hy
  have hjy : jm y ∈ ptsIn _ σ' V.1 := (mem_ptsIn_iff_of_conj (y := y) (y' := jm y) rfl).2 hyV
  have hjnb : ¬ LiesIn (jm y) (genBd s.T.Z) := fun h => hnb ((liesIn_iff_of_comp (y := y) (y' := jm y) rfl _).1 h)
  have hx : (jm y).1 ≫ genι s.T.Z = spMap (starRingEnd ℂ) ≫ y.1 ≫ genι s.T.Z := Category.assoc _ _ _
  obtain ⟨f', hf'⟩ := f.exists_isMap (starRingEnd ℂ) hφ hx
  have e : evHom hjy = (starRingEnd ℂ).comp (evHom hyV) := RingHom.ext fun c => by
    rw [← ev_eq, ev_conj' (y := y) (y' := jm y) rfl, ev_eq hyV]
    rfl
  have hF' : F.IsMap (evHom hjy) f' := fun τ i => by
    refine (hf' τ i).trans ((congrArg (spMap (dualMap (starRingEnd ℂ)) ≫ ·) (hf τ i)).trans ?_)
    refine (GlobalTheory.GradedPieces.dual_comp (evHom hyV) (starRingEnd ℂ) (F.v τ i)).trans ?_
    rw [e]
  have k3 := h3 (jm y) hjnb hjy f' hF'
  obtain ⟨hh, hhH⟩ := (FinalTheorems.exists_isHodgeFrame_iff (s := s) (y := y)).2 hnb
  obtain ⟨hh', hhm⟩ := hh.exists_isMap (starRingEnd ℂ) hφ hx
  have hhH' : IsHodgeFrame s.U (jm y) hh' := hhH.conj hσ
    (by show y.1 = spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) ≫ y.1
        rw [← Category.assoc, spMap_conj_conj', Category.id_comp])
    fun τ i => by rw [hhm τ i, ← Category.assoc, spMap_dual_conj_conj', Category.id_comp]
  have hco : hh'.co f' τ = (hh.co f τ).map (starRingEnd ℂ) := hhm.co τ hf' hx
  show _ = starRingEnd ℂ (g' (jm y))
  rw [← k3, x.hodge_gram hhH' f' τ, x.hodge_gram hhH f τ, hco]
  exact smul_gram_map_conj _ _ a b

end GlobalTheory.ShFam.HodgeConj
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_smooth_conj : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ σ' : κ.c.F →+* ℂ), σ = (starRingEnd ℂ).comp σ' → (x.hodge σ').SmoothOn (manifold s.T.Z σ') {y | ¬ LiesIn y (genBd s.T.Z)} → (x.hodge σ).SmoothOn (manifold s.T.Z σ) {y | ¬ LiesIn y (genBd s.T.Z)} := by
  first | exact @GlobalTheory.ShFam.HodgeConj.smoothOn_hodge_of_conj | exact GlobalTheory.ShFam.HodgeConj.smoothOn_hodge_of_conj | (intros; apply GlobalTheory.ShFam.HodgeConj.smoothOn_hodge_of_conj <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenframe_gram_near_point : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ → ∀ (V : (gen s.T.Z).affineOpens) (φ : κ.c.F →+* Γ(gen s.T.Z, V.1)) (F : EigFrame s.T.Z φ (LogKS.chart V ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) (a b : Fin (S.Dw.mult τ)), LogKS.chart V ≫ genStr s.T.Z = spMap φ → ∀ y₀ : CxPts (genStr s.T.Z) σ, ¬ LiesIn y₀ (genBd s.T.Z) → y₀ ∈ ptsIn (genStr s.T.Z) σ V.1 → ∃ (T : Set (CxPts (genStr s.T.Z) σ)) (g : CxPts (genStr s.T.Z) σ → ℂ), IsOpen T ∧ y₀ ∈ T ∧ (manifold s.T.Z σ).SmoothOn T (fun y => (g y).re) ∧ (manifold s.T.Z σ).SmoothOn T (fun y => (g y).im) ∧ ∀ y ∈ T, ∀ (hy : y ∈ ptsIn (genStr s.T.Z) σ V.1) (f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)), F.IsMap (evHom hy) f → (x.hodge σ).gram y f τ a b = g y := by
  first | exact @GlobalTheory.ShFam.ToroidalCompactificationData.hodge_gram_smooth_near | exact GlobalTheory.ShFam.ToroidalCompactificationData.hodge_gram_smooth_near | (intros; apply GlobalTheory.ShFam.ToroidalCompactificationData.hodge_gram_smooth_near <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option autoImplicit false

theorem GlobalTheory.ShFam.ToroidalCompactificationData.hodge_smoothOn : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), (x.hodge σ).SmoothOn (manifold s.T.Z σ) {y | ¬ LiesIn y (genBd s.T.Z)} := by
  intro D A N j S κ s x σ
  have good : ∀ σ, Formalism.L2.PjFree.GoodEmb κ.c σ →
      (x.hodge σ).SmoothOn (manifold s.T.Z σ) {y | ¬ LiesIn y (genBd s.T.Z)} :=
    fun σ hσ => GlobalTheory.T.eigen_metric_on_set (x.hodge σ) _ fun V φ F τ a b hV y₀ hy₀ hV₀ =>
      GlobalTheory.T.eigenframe_gram_near_point D A N j S κ s x σ hσ V φ F τ a b hV y₀ hy₀ hV₀
  by_cases hσ : Formalism.L2.PjFree.GoodEmb κ.c σ
  · exact good σ hσ
  · have h1 : Formalism.L2.PjFree.GoodEmb κ.c ((starRingEnd ℂ).comp σ) := by
      simpa only [Formalism.L2.PjFree.goodOf, if_neg hσ] using Formalism.L2.PjFree.goodEmb_goodOf κ.c σ
    exact GlobalTheory.T.hodge_smooth_conj D A N j S κ s x σ _ (RingHom.ext fun _ => (Complex.conj_conj _).symm) (good _ h1)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_metric_smooth_off_boundary : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), (x.hodge σ).SmoothOn (manifold s.T.Z σ) {y | ¬ LiesIn y (genBd s.T.Z)} := by
  first | exact @GlobalTheory.ShFam.ToroidalCompactificationData.hodge_smoothOn | exact GlobalTheory.ShFam.ToroidalCompactificationData.hodge_smoothOn | (intros; apply GlobalTheory.ShFam.ToroidalCompactificationData.hodge_smoothOn <;> assumption)
end
