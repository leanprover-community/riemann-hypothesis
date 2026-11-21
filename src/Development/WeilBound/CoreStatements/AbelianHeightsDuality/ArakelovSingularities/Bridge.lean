import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.ExtLBAmb
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernIntegralEqDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusOfFormMixedProjectionStatement

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier

namespace GlobalTheory.AmbMetric

variable {k : Type} [CommRing k]

theorem exists_local_ext {P X : Scheme.{0}} {q : P ⟶ Sp k} {p : X ⟶ Sp k} (i : X ⟶ P) [IsClosedImmersion i]
    (hi : i ≫ q = p) {σ : k →+* ℂ} (f : CxPts p σ → ℝ) (x₀ : CxPts p σ) (hf : CInfAt f x₀) :
    ∃ (V : Set (CxPts q σ)) (θ : CxPts q σ → ℝ), IsOpen V ∧ PtsOver.map i hi (spMap σ) x₀ ∈ V ∧
      (∀ y ∈ V, CInfAt θ y) ∧ ∀ x, PtsOver.map i hi (spMap σ) x ∈ V → θ (PtsOver.map i hi (spMap σ) x) = f x := by
  classical
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := hf
  have hu₀ : x₀.1 (IsLocalRing.closedPoint ℂ) ∈ W := mem_ptsIn.1 h₁
  obtain ⟨U, hU, hiu, -⟩ := exists_isAffineOpen_mem_and_subset (X := P)
    (x := i (x₀.1 (IsLocalRing.closedPoint ℂ))) (U := ⊤) trivial
  have hU' : IsAffineOpen (i ⁻¹ᵁ U) := hU.preimage i
  obtain ⟨h, hhV, hxh⟩ := hU'.exists_basicOpen_le (V := W ⊓ i ⁻¹ᵁ U)
    ⟨x₀.1 (IsLocalRing.closedPoint ℂ), ⟨hu₀, hiu⟩⟩ hiu
  obtain ⟨H, hH⟩ := i.app_surjective U hU h
  have hUa : IsAffineOpen (P.basicOpen H) := hU.basicOpen H
  have hpre : i ⁻¹ᵁ P.basicOpen H = X.basicOpen h := by
    rw [Scheme.preimage_basicOpen]
    exact congrArg X.basicOpen hH
  have hle : i ⁻¹ᵁ P.basicOpen H ≤ W := hpre.le.trans (hhV.trans inf_le_left)
  choose G hG using fun a => i.app_surjective (P.basicOpen H) hUa (resG X hle (g a))
  have hmem (x : CxPts p σ) : PtsOver.map i hi (spMap σ) x ∈ ptsIn q σ (P.basicOpen H) ↔
      x ∈ ptsIn p σ (i ⁻¹ᵁ P.basicOpen H) := by
    rw [mem_ptsIn, mem_ptsIn]
    rfl
  have hev (x : CxPts p σ) (hx : PtsOver.map i hi (spMap σ) x ∈ ptsIn q σ (P.basicOpen H)) (a : ι) :
      ev q σ (P.basicOpen H) (G a) (PtsOver.map i hi (spMap σ) x) = ev p σ W (g a) x := by
    rw [← ev_app i hi (P.basicOpen H) (G a) x]
    have e : (i.app (P.basicOpen H)) (G a) = resG X hle (g a) := hG a
    rw [e, ev_res hle ((hmem x).1 hx)]
  have hemb := PtsOver.isClosedEmbedding_map (C := ℂ) i hi (spMap σ)
  have hN : {x | f x = F fun a => ev p σ W (g a) x} ∈ 𝓝 x₀ := h₅
  rw [hemb.isInducing.nhds_eq_comap] at hN
  obtain ⟨t, ht, hts⟩ := Filter.mem_comap.1 hN
  obtain ⟨V', hV't, hV'o, hx₀V'⟩ := mem_nhds_iff.1 ht
  have hcont : ContinuousOn (fun y (a : ι) => ev q σ (P.basicOpen H) (G a) y) (ptsIn q σ (P.basicOpen H)) :=
    continuousOn_pi.2 fun a => continuousOn_ev (G a)
  refine ⟨V' ∩ (ptsIn q σ (P.basicOpen H) ∩ (fun y (a : ι) => ev q σ (P.basicOpen H) (G a) y) ⁻¹' O),
    fun y => F fun a => ev q σ (P.basicOpen H) (G a) y,
    hV'o.inter (hcont.isOpen_inter_preimage (isOpen_ptsIn _) h₂), ?_, ?_, ?_⟩
  · have hx₀ : PtsOver.map i hi (spMap σ) x₀ ∈ ptsIn q σ (P.basicOpen H) := by
      rw [hmem, mem_ptsIn, hpre]
      exact hxh
    refine ⟨hx₀V', hx₀, ?_⟩
    simp only [Set.mem_preimage, hev x₀ hx₀]
    exact h₃
  · rintro y ⟨-, hy₁, hy₂⟩
    exact ⟨P.basicOpen H, ι, inferInstance, G, F, O, hy₁, h₂, hy₂, h₄, EventuallyEq.rfl⟩
  · rintro x ⟨hx₁, hx₂, -⟩
    have e : f x = F fun a => ev p σ W (g a) x := hts (hV't hx₁)
    rw [e]
    exact congrArg F (funext fun a => hev x hx₂ a)

end GlobalTheory.AmbMetric
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff

namespace GlobalTheory.AmbMetric

variable {k : Type} [CommRing k]

section Calc

variable {P : Scheme.{0}} {q : P ⟶ Sp k} {σ : k →+* ℂ} {y : CxPts q σ}

theorem cInfAt_mul {f g : CxPts q σ → ℝ} (hf : CInfAt f y) (hg : CInfAt g y) : CInfAt (fun z => f z * g z) y :=
  hf.comp₂ hg (G := fun x => x.1 * x.2) (contDiff_fst.mul contDiff_snd)

theorem cInfAt_one_sub {f : CxPts q σ → ℝ} (hf : CInfAt f y) : CInfAt (fun z => 1 - f z) y :=
  hf.comp₂ hf (G := fun x => 1 - x.1) (contDiff_const.sub contDiff_fst)

theorem cInfAt_prod {ι : Type} (s : Finset ι) {f : ι → CxPts q σ → ℝ} (hf : ∀ i ∈ s, CInfAt (f i) y) :
    CInfAt (fun z => ∏ i ∈ s, f i z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const (p := q) 1 y
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact cInfAt_mul (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end Calc

theorem exists_bump {P : Scheme.{0}} {q : P ⟶ Sp k} {N : ℕ} {σ : k →+* ℂ} (R : AnRead q σ N)
    [T2Space (CxPts q σ)] (y : CxPts q σ) (W : Set (CxPts q σ)) (hW : IsOpen W) (hy : y ∈ W) :
    ∃ β : CxPts q σ → ℝ, (∀ z, CInfAt β z) ∧ (∀ z, 0 ≤ β z ∧ β z ≤ 1) ∧ tsupport β ⊆ W ∧
      ∀ᶠ z in 𝓝 y, β z = 1 := by
  classical
  obtain ⟨c, hc⟩ := R.cover y
  set e := (R.chart c).e with he
  have hT : IsOpen (e.target ∩ e.symm ⁻¹' W) := e.isOpen_inter_preimage_symm hW
  have hyT : e y ∈ e.target ∩ e.symm ⁻¹' W := ⟨e.map_source hc, by rw [mem_preimage, e.left_inv hc]; exact hy⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hT (e y) hyT
  let β₀ : ContDiffBump (e y) := ⟨ε / 4, ε / 2, by linarith, by linarith⟩
  have hcb : Metric.closedBall (e y) (ε / 2) ⊆ e.target ∩ e.symm ⁻¹' W :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  set C := e.symm '' Metric.closedBall (e y) (ε / 2) with hC
  have hCc : IsCompact C := (isCompact_closedBall (e y) (ε / 2)).image_of_continuousOn
    (e.continuousOn_symm.mono fun v hv => (hcb hv).1)
  have hCsub : C ⊆ e.source ∩ W := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨e.map_target (hcb hv).1, (hcb hv).2⟩
  let β : CxPts q σ → ℝ := fun w => if w ∈ e.source then β₀ (e w) else 0
  have hsupp : Function.support β ⊆ C := by
    intro w hw
    simp only [Function.mem_support, β] at hw
    split_ifs at hw with hws
    · have : e w ∈ Metric.ball (e y) (ε / 2) := by
        rw [← β₀.support_eq]; exact hw
      exact ⟨e w, Metric.ball_subset_closedBall this, e.left_inv hws⟩
    · exact absurd rfl hw
  have hts : tsupport β ⊆ C := closure_minimal hsupp hCc.isClosed
  refine ⟨β, fun z => ?_, fun z => ?_, hts.trans fun w hw => (hCsub hw).2, ?_⟩
  · by_cases hz : z ∈ e.source
    · refine cInfAt_of_chart e.open_source (R.chart c) ?_ hz hz
      refine (β₀.contDiff.contDiffOn (s := e.target ∩ e.symm ⁻¹' e.source)).congr fun v hv => ?_
      have hv1 : e.symm v ∈ e.source := hv.2
      show (if e.symm v ∈ e.source then β₀ (e (e.symm v)) else 0) = β₀ v
      rw [if_pos hv1, e.right_inv hv.1]
    · have hzC : z ∉ C := fun h => hz (hCsub h).1
      refine (cInfAt_const (p := q) 0 z).congr ?_
      filter_upwards [hCc.isClosed.isOpen_compl.mem_nhds hzC] with w hw
      by_contra h
      exact hw (hsupp h)
  · simp only [β]
    split_ifs
    · exact ⟨β₀.nonneg, β₀.le_one⟩
    · exact ⟨le_rfl, zero_le_one⟩
  · have ho : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 4)) :=
      e.isOpen_inter_preimage Metric.isOpen_ball
    filter_upwards [ho.mem_nhds ⟨hc, Metric.mem_ball_self (by linarith)⟩] with w hw
    simp only [β, if_pos hw.1]
    exact β₀.one_of_mem_closedBall (Metric.ball_subset_closedBall hw.2)

theorem exists_partition {P : Scheme.{0}} {q : P ⟶ Sp k} {N : ℕ} {σ : k →+* ℂ} (R : AnRead q σ N)
    [CompactSpace (CxPts q σ)] [T2Space (CxPts q σ)] {J : Type} (V : J → Set (CxPts q σ)) (hV : ∀ j, IsOpen (V j))
    (hc : ∀ y, ∃ j, y ∈ V j) :
    ∃ (n : ℕ) (c : Fin n → J) (ρ : Fin n → CxPts q σ → ℝ), (∀ a y, CInfAt (ρ a) y) ∧ (∀ a y, 0 ≤ ρ a y) ∧
      (∀ a, tsupport (ρ a) ⊆ V (c a)) ∧ ∀ y, ∑ a, ρ a y = 1 := by
  classical
  choose j hj using hc
  choose β hβs hβb hβt hβ1 using fun y => exists_bump R y (V (j y)) (hV (j y)) (hj y)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : CxPts q σ => interior {y | β x y = 1})
    (fun _ => isOpen_interior) (fun y _ => mem_iUnion.2 ⟨y, mem_interior_iff_mem_nhds.2 (hβ1 y)⟩)
  let pt : Fin t.card → CxPts q σ := fun a => (t.equivFin.symm a : CxPts q σ)
  let ψ : Fin t.card → CxPts q σ → ℝ := fun a => β (pt a)
  have hsum : ∀ x, ∑ a, ψ a x * ∏ b ∈ Finset.univ with b < a, (1 - ψ b x) = 1 - ∏ a, (1 - ψ a x) := fun x => by
    rw [Finset.prod_one_sub_ordered]; ring
  refine ⟨t.card, fun a => j (pt a), fun a x => ψ a x * ∏ b ∈ Finset.univ with b < a, (1 - ψ b x),
    fun a y => ?_, fun a y => ?_, fun a => ?_, fun x => ?_⟩
  · exact cInfAt_mul (hβs _ y) (cInfAt_prod _ fun b _ => cInfAt_one_sub (hβs _ y))
  · exact mul_nonneg (hβb _ y).1 (Finset.prod_nonneg fun b _ => sub_nonneg.2 (hβb _ y).2)
  · exact (tsupport_mul_subset_left (f := ψ a)).trans (hβt (pt a))
  · rw [hsum]
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    have h1 : ψ (t.equivFin ⟨u, hu⟩) x = 1 := by
      have : pt (t.equivFin ⟨u, hu⟩) = u := by simp [pt]
      simp only [ψ, this]
      exact (interior_subset hxu : x ∈ {y | β u y = 1})
    rw [Finset.prod_eq_zero (Finset.mem_univ (t.equivFin ⟨u, hu⟩)) (by rw [h1]; ring)]
    ring

end GlobalTheory.AmbMetric
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts

namespace GlobalTheory.AmbMetric

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {σ σ' : k →+* ℂ}

noncomputable def conjPts (p : Y ⟶ Sp k) (h : σ = (starRingEnd ℂ).comp σ') : CxPts p σ' ≃ₜ CxPts p σ :=
  (Points.conjHomeomorph Y).subtype fun y => by
    have e : spMap σ = spMap (starRingEnd ℂ) ≫ spMap σ' := by
      rw [h, spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    change y ≫ p = _ ↔ (spMap (starRingEnd ℂ) ≫ y) ≫ p = _
    rw [e, Category.assoc]
    exact (Points.conjHomeomorph (Sp k)).injective.eq_iff.symm

end GlobalTheory.AmbMetric
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open scoped ContDiff

namespace GlobalTheory.AmbMetric

variable {k : Type} [CommRing k]

section Generic

variable {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {y : CxPts p σ}

theorem cInfAt_logSq_ev {W : Y.Opens} (u : Γ(Y, W)ˣ) (hy : y ∈ ptsIn p σ W) :
    CInfAt (fun z => Real.log (‖ev p σ W u.val z‖ ^ 2)) y := by
  refine ⟨W, Unit, inferInstance, fun _ => u.val, fun v => Real.log (‖v ()‖ ^ 2), {v | v () ≠ 0}, hy,
    isOpen_ne_fun (continuous_apply ()) continuous_const, ev_ne_zero hy u.isUnit, ?_,
    Filter.EventuallyEq.rfl⟩
  refine ContDiffOn.log ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ ())).contDiffOn ?_
  intro v hv
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)

theorem cInfAt_sum {ι : Type} (s : Finset ι) {f : ι → CxPts p σ → ℝ} (hf : ∀ i ∈ s, CInfAt (f i) y) :
    CInfAt (fun z => ∑ i ∈ s, f i z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const (0 : ℝ) y
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end Generic

section Transport

variable {X : Scheme.{0}} {p : X ⟶ Sp k}

private theorem phi_sub_logSq_eq_of_mem_overlap (A : LB X) (hA : A.IsLB) (L : HermLB p) (w : A.Iso L.B)
    (hw : LB.Gen.IsGen w) (σ : k →+* ℂ) (a a' : L.B.ι) (b : A.ι) (y : CxPts p σ)
    (ha : y ∈ ptsIn p σ (L.B.U a)) (ha' : y ∈ ptsIn p σ (L.B.U a')) (hb : y ∈ ptsIn p σ (A.U b)) :
    (L.φ σ).φ a y - y.logSq (L.B.U a ⊓ A.U b) (w.s (a, b)) =
      (L.φ σ).φ a' y - y.logSq (L.B.U a' ⊓ A.U b) (w.s (a', b)) := by
  have hV : y ∈ ptsIn p σ ((L.B.div A).U (a, b) ⊓ (L.B.div A).U (a', b)) := by
    simp only [LB.div, mem_ptsIn, TopologicalSpace.Opens.mem_inf] at ha ha' hb ⊢
    tauto
  have hg := congrArg (y.logSq _) (hw (a, b) (a', b))
  rw [logSq_res _ hV, logSq_mul hV, logSq_res _ hV] at hg
  dsimp only [LB.div] at hg hV
  rw [logSq_mul hV, logSq_inv hV, logSq_res _ hV, logSq_res _ hV] at hg
  have hbb : y.logSq (A.U b ⊓ A.U b) (A.g b b) = 0 := by
    have h0 := congrArg (y.logSq _) (hA.g_self b)
    rw [logSq_res _ (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at hb ⊢; tauto),
      logSq_one (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at hb ⊢; tauto)] at h0
    exact h0
  have ht := (L.φ σ).trans a a' y ha ha'
  have hl : Real.log (‖gv p σ L.B a a' y‖ ^ 2) = y.logSq (L.B.U a ⊓ L.B.U a') (L.B.g a a') := rfl
  rw [hl] at ht
  rw [hbb] at hg
  linarith

private theorem logSq_inf_eq_add_logSq_transition (A : LB X) (L : HermLB p) (w : A.Iso L.B)
    (hw : LB.Gen.IsGen w) (σ : k →+* ℂ) (a : L.B.ι) (b b' : A.ι) (y : CxPts p σ)
    (ha : y ∈ ptsIn p σ (L.B.U a)) (hb : y ∈ ptsIn p σ (A.U b)) (hb' : y ∈ ptsIn p σ (A.U b')) :
    y.logSq (L.B.U a ⊓ A.U b') (w.s (a, b')) =
      y.logSq (L.B.U a ⊓ A.U b) (w.s (a, b)) + y.logSq (A.U b ⊓ A.U b') (A.g b b') := by
  have hV : y ∈ ptsIn p σ ((L.B.div A).U (a, b) ⊓ (L.B.div A).U (a, b')) := by
    simp only [LB.div, mem_ptsIn, TopologicalSpace.Opens.mem_inf] at ha hb hb' ⊢
    tauto
  have hg := congrArg (y.logSq _) (hw (a, b) (a, b'))
  rw [logSq_res _ hV, logSq_mul hV, logSq_res _ hV] at hg
  dsimp only [LB.div] at hg hV
  rw [logSq_mul hV, logSq_inv hV, logSq_res _ hV, logSq_res _ hV] at hg
  have haa : y.logSq (L.B.U a ⊓ L.B.U a) (L.B.g a a) = 0 := by
    have h0 := congrArg (y.logSq _) (L.isLB.g_self a)
    rw [logSq_res _ (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at ha ⊢; tauto),
      logSq_one (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at ha ⊢; tauto)] at h0
    exact h0
  rw [haa] at hg
  linarith

theorem exists_transport (A : LB X) (hA : A.IsLB) (L : HermLB p) (hL : LBIso A L.B) :
    ∃ (χ : ∀ σ : k →+* ℂ, Weight p σ A) (hc : ∀ σ, (χ σ).IsCInf) (hj : ∀ σ σ', (χ σ).IsConj (χ σ')),
      (⟨A, hA, χ, hc, hj⟩ : HermLB p).Isometric L := by
  obtain ⟨w, hw⟩ := hL
  have hcov : ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ a, y ∈ ptsIn p σ (L.B.U a) := by
    intro σ y
    have h : ∀ x : X, ∃ a, x ∈ L.B.U a := by
      intro x
      have hx : x ∈ (⨆ i, L.B.U i) := by
        rw [L.isLB.cover]
        trivial
      exact TopologicalSpace.Opens.mem_iSup.mp hx
    exact (h _).imp fun a ha => mem_ptsIn.mpr ha
  let F : ∀ σ : k →+* ℂ, A.ι → CxPts p σ → ℝ := fun σ b y =>
    (L.φ σ).φ (hcov σ y).choose y -
      y.logSq (L.B.U (hcov σ y).choose ⊓ A.U b) (w.s ((hcov σ y).choose, b))
  have hF : ∀ (σ : k →+* ℂ) (b : A.ι) (y : CxPts p σ) (a : L.B.ι), y ∈ ptsIn p σ (L.B.U a) →
      y ∈ ptsIn p σ (A.U b) → F σ b y = (L.φ σ).φ a y - y.logSq (L.B.U a ⊓ A.U b) (w.s (a, b)) :=
    fun σ b y a ha hb => phi_sub_logSq_eq_of_mem_overlap A hA L w hw σ _ a b y (hcov σ y).choose_spec ha hb
  have htr : ∀ (σ : k →+* ℂ) (i j : A.ι), ∀ y ∈ ptsIn p σ (A.U i), y ∈ ptsIn p σ (A.U j) →
      F σ j y = F σ i y - Real.log (‖gv p σ A i j y‖ ^ 2) := by
    intro σ i j y hi hj
    obtain ⟨a, ha⟩ := hcov σ y
    rw [hF σ j y a ha hj, hF σ i y a ha hi]
    have h2 := logSq_inf_eq_add_logSq_transition A L w hw σ a i j y ha hi hj
    have hl : Real.log (‖gv p σ A i j y‖ ^ 2) = y.logSq (A.U i ⊓ A.U j) (A.g i j) := rfl
    rw [hl]
    linarith
  let χ : ∀ σ : k →+* ℂ, Weight p σ A := fun σ => ⟨hA, F σ, htr σ⟩
  have hc : ∀ σ, (χ σ).IsCInf := by
    intro σ b y hb
    obtain ⟨a, ha⟩ := hcov σ y
    have hS : ptsIn p σ (L.B.U a) ∩ ptsIn p σ (A.U b) ∈ 𝓝 y :=
      ((isOpen_ptsIn _).inter (isOpen_ptsIn _)).mem_nhds ⟨ha, hb⟩
    have h2 := cInfAt_logSq_ev (W := L.B.U a ⊓ A.U b) (w.s (a, b)) (mem_ptsIn_inf.mpr ⟨ha, hb⟩)
    have h1 : CInfAt (fun z => (L.φ σ).φ a z - z.logSq (L.B.U a ⊓ A.U b) (w.s (a, b))) y :=
      ((L.cInf σ a y ha).add h2.neg).congr (Filter.Eventually.of_forall fun z => sub_eq_add_neg _ _)
    exact h1.congr (Filter.mem_of_superset hS fun z hz => hF σ b z a hz.1 hz.2)
  have hj : ∀ σ σ', (χ σ).IsConj (χ σ') := by
    intro σ σ' b y y' hyy' hb
    obtain ⟨a, ha⟩ := hcov σ y
    have ha' := (mem_ptsIn_iff_of_conj hyy').mpr ha
    have hb' := (mem_ptsIn_iff_of_conj hyy').mpr hb
    show F σ' b y' = F σ b y
    rw [hF σ' b y' a ha' hb', hF σ b y a ha hb, L.conj σ σ' a y y' hyy' ha]
    congr 1
    unfold CxPts.logSq
    rw [ev_conj hyy' (mem_ptsIn_inf.mpr ⟨ha, hb⟩), Complex.norm_conj]
  refine ⟨χ, hc, hj, w, hw, ?_⟩
  intro σ a b y ha hb
  have h3 := hF σ b y a ha hb
  show (L.φ σ).φ a y = F σ b y + y.logSq (L.B.U a ⊓ A.U b) (w.s (a, b))
  linarith

end Transport

section Glue

variable {P X : Scheme.{0}} {q : P ⟶ Sp k} {p : X ⟶ Sp k}

theorem mem_ptsIn_pull (i : X ⟶ P) (hi : i ≫ q = p) {σ : k →+* ℂ} (B : LB P) (c : B.ι) (x : CxPts p σ)
    (h : PtsOver.map i hi (spMap σ) x ∈ ptsIn q σ (B.U c)) : x ∈ ptsIn p σ ((B.pull i).U fun _ => c) := by
  have h1 := (mem_ptsIn_preimage (m := PtsOver.map i hi (spMap σ)) (fun z => rfl)).mpr h
  rw [mem_ptsIn] at h1 ⊢
  simp only [LB.pull, LB.LinComb]
  rw [← SetLike.mem_coe]
  simpa [LB.wchart] using h1

theorem gv_pull (i : X ⟶ P) (hi : i ≫ q = p) {σ : k →+* ℂ} (B : LB P) (c c' : B.ι) (x : CxPts p σ)
    (h : x ∈ ptsIn p σ ((B.pull i).U fun _ => c)) (h' : x ∈ ptsIn p σ ((B.pull i).U fun _ => c')) :
    gv p σ (B.pull i) (fun _ => c) (fun _ => c') x = gv q σ B c c' (PtsOver.map i hi (spMap σ) x) :=
  (gv_linComb (m := fun _ => PtsOver.map i hi (spMap σ) x) (fun _ => rfl) h h').trans (by simp)

private theorem logSq_cocycle {Y : Scheme.{0}} {r : Y ⟶ Sp k} {σ : k →+* ℂ} (B : LB Y)
    (hB : B.IsLB) (c₁ c₂ c₃ : B.ι) (z : CxPts r σ) (h₁ : z ∈ ptsIn r σ (B.U c₁))
    (h₂ : z ∈ ptsIn r σ (B.U c₂)) (h₃ : z ∈ ptsIn r σ (B.U c₃)) :
    z.logSq (B.U c₁ ⊓ B.U c₂) (B.g c₁ c₂) + z.logSq (B.U c₂ ⊓ B.U c₃) (B.g c₂ c₃) =
      z.logSq (B.U c₁ ⊓ B.U c₃) (B.g c₁ c₃) := by
  have h0 := congrArg (z.logSq _) (hB.cocycle c₁ c₂ c₃)
  rw [logSq_mul (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at h₁ h₂ h₃ ⊢; tauto),
    logSq_res _ (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at h₁ h₂ h₃ ⊢; tauto),
    logSq_res _ (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at h₁ h₂ h₃ ⊢; tauto),
    logSq_res _ (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at h₁ h₂ h₃ ⊢; tauto)] at h0
  exact h0

theorem exists_weight_ext_sigma (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ q = p) {N : ℕ} (hP : IsArithVar q N)
    (hs : GenSmooth q N) (B : LB P) (hB : B.IsLB) (σ : k →+* ℂ) (χ : Weight p σ (B.pull i)) (hχ : χ.IsCInf) :
    ∃ ψ : Weight q σ B, ψ.IsCInf ∧ ∀ (c : B.ι) (x : CxPts p σ),
      PtsOver.map i hi (spMap σ) x ∈ ptsIn q σ (B.U c) → ψ.φ c (PtsOver.map i hi (spMap σ) x) = χ.φ (fun _ => c) x := by
  haveI : CompactSpace (CxPts q σ) := compactSpace σ hP.isProjOver
  haveI : T2Space (CxPts q σ) := t2Space_cxPts_of_isProjOver σ hP.isProjOver
  obtain ⟨R⟩ := hs σ
  set m := PtsOver.map i hi (spMap σ) with hm
  have hmc : IsClosed (range m) := (PtsOver.isClosedEmbedding_map i hi (spMap σ)).isClosed_range
  have hcov : ∀ y : CxPts q σ, ∃ c, y ∈ ptsIn q σ (B.U c) := by
    intro y
    have h : ∀ x : P, ∃ c, x ∈ B.U c := by
      intro x
      have hx : x ∈ (⨆ c, B.U c) := by
        rw [hB.cover]
        trivial
      exact TopologicalSpace.Opens.mem_iSup.mp hx
    exact (h _).imp fun c hc => mem_ptsIn.mpr hc
  have loc : ∀ y : CxPts q σ, ∃ (c : B.ι) (V : Set (CxPts q σ)) (θ : CxPts q σ → ℝ),
      IsOpen V ∧ y ∈ V ∧ V ⊆ ptsIn q σ (B.U c) ∧ (∀ z ∈ V, CInfAt θ z) ∧
        ∀ x : CxPts p σ, m x ∈ V → θ (m x) = χ.φ (fun _ => c) x := by
    intro y
    obtain ⟨c, hc⟩ := hcov y
    by_cases hy : y ∈ range m
    · obtain ⟨x₀, rfl⟩ := hy
      have hx₀ := mem_ptsIn_pull i hi B c x₀ hc
      obtain ⟨V, θ, hV, hV₀, hθ, heq⟩ := exists_local_ext i hi (χ.φ fun _ => c) x₀ (hχ (fun _ => c) x₀ hx₀)
      exact ⟨c, V ∩ ptsIn q σ (B.U c), θ, hV.inter (isOpen_ptsIn _), ⟨hV₀, hc⟩, inter_subset_right,
        fun z hz => hθ z hz.1, fun x hx => heq x hx.1⟩
    · refine ⟨c, (range m)ᶜ ∩ ptsIn q σ (B.U c), fun _ => 0, hmc.isOpen_compl.inter (isOpen_ptsIn _),
        ⟨hy, hc⟩, inter_subset_right, fun z _ => cInfAt_const 0 z, ?_⟩
      intro x hx
      exact absurd (mem_range_self x) hx.1
  choose cc V θ hVo hyV hVsub hθ hθx using loc
  obtain ⟨n, a, ρ, hρs, hρ0, hρsupp, hρ1⟩ := exists_partition R V hVo (fun y => ⟨y, hyV y⟩)
  have hzero : ∀ t z, ρ t z ≠ 0 → z ∈ V (a t) := fun t z h0 =>
    hρsupp t (subset_tsupport _ (Function.mem_support.mpr h0))
  let Ψ : B.ι → CxPts q σ → ℝ := fun c z =>
    ∑ t : Fin n, ρ t z * (θ (a t) z - z.logSq (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c))
  have htr : ∀ (c c' : B.ι), ∀ z ∈ ptsIn q σ (B.U c), z ∈ ptsIn q σ (B.U c') →
      Ψ c' z = Ψ c z - Real.log (‖gv q σ B c c' z‖ ^ 2) := by
    intro c c' z hz hz'
    have key : ∀ t : Fin n, ρ t z * (θ (a t) z - z.logSq (B.U (cc (a t)) ⊓ B.U c') (B.g (cc (a t)) c')) =
        ρ t z * (θ (a t) z - z.logSq (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c)) -
          ρ t z * z.logSq (B.U c ⊓ B.U c') (B.g c c') := by
      intro t
      by_cases h0 : ρ t z = 0
      · simp [h0]
      have hzc := hVsub (a t) (hzero t z h0)
      have h3 := logSq_cocycle B hB (cc (a t)) c c' z hzc hz hz'
      rw [← h3]
      ring
    have hl : Real.log (‖gv q σ B c c' z‖ ^ 2) = z.logSq (B.U c ⊓ B.U c') (B.g c c') := rfl
    show ∑ t : Fin n, _ = ∑ t : Fin n, _ - _
    rw [Finset.sum_congr rfl (fun t _ => key t), Finset.sum_sub_distrib, ← Finset.sum_mul, hρ1, one_mul, hl]
  refine ⟨⟨hB, Ψ, htr⟩, ?_, ?_⟩
  · intro c z hz
    show CInfAt (fun w => ∑ t : Fin n, ρ t w *
      (θ (a t) w - w.logSq (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c))) z
    apply cInfAt_sum
    intro t _
    by_cases hzV : z ∈ V (a t)
    · have hzc := hVsub (a t) hzV
      have h2 := cInfAt_logSq_ev (W := B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c)
        (mem_ptsIn_inf.mpr ⟨hzc, hz⟩)
      have h1 : CInfAt (fun w => θ (a t) w - w.logSq (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c)) z :=
        ((hθ (a t) z hzV).add h2.neg).congr (Filter.Eventually.of_forall fun w => sub_eq_add_neg _ _)
      exact cInfAt_mul (hρs t z) h1
    · have hns : z ∉ tsupport (ρ t) := fun h => hzV (hρsupp t h)
      have hev := (notMem_tsupport_iff_eventuallyEq.mp hns)
      refine (cInfAt_const 0 z).congr ?_
      filter_upwards [hev] with w hw
      simp only [Pi.zero_apply] at hw
      simp [hw]
  · intro c x hx
    show ∑ t : Fin n, ρ t (m x) * (θ (a t) (m x) -
      CxPts.logSq (m x) (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c)) = χ.φ (fun _ => c) x
    have key : ∀ t : Fin n, ρ t (m x) * (θ (a t) (m x) -
        CxPts.logSq (m x) (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c)) = ρ t (m x) * χ.φ (fun _ => c) x := by
      intro t
      by_cases h0 : ρ t (m x) = 0
      · simp [h0]
      have hzV := hzero t (m x) h0
      have hzc := hVsub (a t) hzV
      rw [hθx (a t) x hzV]
      have hxa := mem_ptsIn_pull i hi B (cc (a t)) x hzc
      have hxc := mem_ptsIn_pull i hi B c x hx
      have htrχ := χ.trans (fun _ => cc (a t)) (fun _ => c) x hxa hxc
      rw [gv_pull i hi B (cc (a t)) c x hxa hxc] at htrχ
      have hl : Real.log (‖gv q σ B (cc (a t)) c (PtsOver.map i hi (spMap σ) x)‖ ^ 2) =
          CxPts.logSq (m x) (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c) := rfl
      rw [hl] at htrχ
      rw [htrχ]
    rw [Finset.sum_congr rfl (fun t _ => key t), ← Finset.sum_mul, hρ1, one_mul]

end Glue

section Conj

variable {P X : Scheme.{0}} {q : P ⟶ Sp k} {p : X ⟶ Sp k}

theorem cInfAt_conj {σ : k →+* ℂ} {f : CxPts q ((starRingEnd ℂ).comp σ) → ℝ} {y : CxPts q σ}
    (h : CInfAt f (conjPts q rfl y)) : CInfAt (fun z => f (conjPts q rfl z)) y := by
  obtain ⟨W, ι, hι, g, F, O, hyW, hO, hmem, hF, hev⟩ := h
  have hy' : y ∈ ptsIn q σ W := (mem_ptsIn_iff_of_conj (y := y) (y' := conjPts q rfl y) rfl).mp hyW
  have evrel : ∀ z ∈ ptsIn q σ W, ∀ a, ev q ((starRingEnd ℂ).comp σ) W (g a) (conjPts q rfl z) =
      starRingEnd ℂ (ev q σ W (g a) z) := fun z hz a => ev_conj rfl hz (g a)
  have hc1 : ContDiff ℝ ∞ (fun z : ℂ => starRingEnd ℂ z) := by
    have h0 := Complex.conjCLE.contDiff (n := ∞)
    convert h0 using 1
    funext z
    simp
  let c : (ι → ℂ) → (ι → ℂ) := fun v a => starRingEnd ℂ (v a)
  have hc : ContDiff ℝ ∞ c := contDiff_pi.mpr fun a => hc1.comp (contDiff_apply ℝ ℂ a)
  refine ⟨W, ι, hι, g, fun v => F (c v), c ⁻¹' O, hy', hO.preimage hc.continuous, ?_,
    hF.comp hc.contDiffOn (mapsTo_preimage c O), ?_⟩
  · show (fun a => starRingEnd ℂ (ev q σ W (g a) y)) ∈ O
    have he : (fun a => starRingEnd ℂ (ev q σ W (g a) y)) =
        fun a => ev q ((starRingEnd ℂ).comp σ) W (g a) (conjPts q rfl y) :=
      funext fun a => (evrel y hy' a).symm
    rw [he]
    exact hmem
  · have h1 := hev.comp_tendsto ((conjPts q rfl).continuous.tendsto y)
    have h2 : ptsIn q σ W ∈ 𝓝 y := (isOpen_ptsIn W).mem_nhds hy'
    filter_upwards [h1, h2] with z hz hzW
    simp only [Function.comp] at hz
    rw [hz]
    show F _ = F _
    congr 1
    funext a
    exact evrel z hzW a

theorem exists_weight_ext (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ q = p) {N : ℕ} (hP : IsArithVar q N)
    (hs : GenSmooth q N) (B : LB P) (hB : B.IsLB) (χ : ∀ σ : k →+* ℂ, Weight p σ (B.pull i))
    (hχ : ∀ σ, (χ σ).IsCInf) (hχc : ∀ σ σ', (χ σ).IsConj (χ σ')) :
    ∃ ψ : ∀ σ : k →+* ℂ, Weight q σ B, (∀ σ, (ψ σ).IsCInf) ∧ (∀ σ σ', (ψ σ).IsConj (ψ σ')) ∧
      ∀ (σ : k →+* ℂ) (c : B.ι) (x : CxPts p σ), PtsOver.map i hi (spMap σ) x ∈ ptsIn q σ (B.U c) →
        (ψ σ).φ c (PtsOver.map i hi (spMap σ) x) = (χ σ).φ (fun _ => c) x := by
  choose ψ0 hψ0c hψ0e using fun σ => exists_weight_ext_sigma i hi hP hs B hB σ (χ σ) (hχ σ)
  have hcongr : ∀ (c : B.ι) (σ1 σ2 : k →+* ℂ), σ1 = σ2 → ∀ (z1 : CxPts q σ1) (z2 : CxPts q σ2),
      (z1 : Sp ℂ ⟶ P) = z2 → (ψ0 σ1).φ c z1 = (ψ0 σ2).φ c z2 := by
    intro c σ1 σ2 h z1 z2 hz
    subst h
    rw [Subtype.ext hz]
  have hLconj : ∀ (σ : k →+* ℂ) (c c' : B.ι) (y : CxPts q σ), y ∈ ptsIn q σ (B.U c ⊓ B.U c') →
      Real.log (‖gv q ((starRingEnd ℂ).comp σ) B c c' (conjPts q rfl y)‖ ^ 2) =
        Real.log (‖gv q σ B c c' y‖ ^ 2) := by
    intro σ c c' y hy
    unfold CxPts.gv
    rw [ev_conj rfl hy, Complex.norm_conj]
  let Ψ : ∀ σ : k →+* ℂ, B.ι → CxPts q σ → ℝ := fun σ c y =>
    ((ψ0 σ).φ c y + (ψ0 ((starRingEnd ℂ).comp σ)).φ c (conjPts q rfl y)) / 2
  have htr : ∀ (σ : k →+* ℂ) (c c' : B.ι), ∀ y ∈ ptsIn q σ (B.U c), y ∈ ptsIn q σ (B.U c') →
      Ψ σ c' y = Ψ σ c y - Real.log (‖gv q σ B c c' y‖ ^ 2) := by
    intro σ c c' y hc hc'
    have hc2 := (mem_ptsIn_iff_of_conj (y := y) (y' := conjPts q rfl y) rfl).mpr hc
    have hc2' := (mem_ptsIn_iff_of_conj (y := y) (y' := conjPts q rfl y) rfl).mpr hc'
    have e1 := (ψ0 σ).trans c c' y hc hc'
    have e2 := (ψ0 ((starRingEnd ℂ).comp σ)).trans c c' _ hc2 hc2'
    rw [hLconj σ c c' y (mem_ptsIn_inf.mpr ⟨hc, hc'⟩)] at e2
    show (_ + _) / 2 = (_ + _) / 2 - _
    rw [e1, e2]
    ring
  refine ⟨fun σ => ⟨hB, Ψ σ, htr σ⟩, ?_, ?_, ?_⟩
  · intro σ c y hy
    have hy2 := (mem_ptsIn_iff_of_conj (y := y) (y' := conjPts q rfl y) rfl).mpr hy
    have h1 := hψ0c σ c y hy
    have h2 := cInfAt_conj (f := (ψ0 ((starRingEnd ℂ).comp σ)).φ c) (hψ0c _ c _ hy2)
    exact h1.comp₂ h2 (G := fun v => (v.1 + v.2) / 2) (by fun_prop)
  · intro σ σ' c y y' hyy' hy
    have hσ := eq_conj_of_conj hyy'
    subst hσ
    have hy' : y' = conjPts q rfl y := Subtype.ext hyy'
    subst hy'
    show ((ψ0 _).φ c (conjPts q rfl y) + (ψ0 _).φ c (conjPts q rfl (conjPts q rfl y))) / 2 =
      ((ψ0 σ).φ c y + (ψ0 _).φ c (conjPts q rfl y)) / 2
    rw [hcongr c ((starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ)) σ (RingHom.ext fun x => by simp)
      (conjPts q rfl (conjPts q rfl y)) y ((conjHomeomorph P).left_inv _)]
    ring
  · intro σ c x hx
    have hxp := mem_ptsIn_pull i hi B c x hx
    have hmx : conjPts q rfl (PtsOver.map i hi (spMap σ) x) =
        PtsOver.map i hi (spMap ((starRingEnd ℂ).comp σ)) (conjPts p rfl x) := by
      apply Subtype.ext
      show spMap (starRingEnd ℂ) ≫ ((x : Sp ℂ ⟶ X) ≫ i) = (spMap (starRingEnd ℂ) ≫ (x : Sp ℂ ⟶ X)) ≫ i
      exact (Category.assoc _ _ _).symm
    have hx2 : PtsOver.map i hi (spMap ((starRingEnd ℂ).comp σ)) (conjPts p rfl x) ∈
        ptsIn q ((starRingEnd ℂ).comp σ) (B.U c) := by
      rw [← hmx]
      exact (mem_ptsIn_iff_of_conj rfl).mpr hx
    show ((ψ0 σ).φ c (PtsOver.map i hi (spMap σ) x) +
      (ψ0 _).φ c (conjPts q rfl (PtsOver.map i hi (spMap σ) x))) / 2 = (χ σ).φ (fun _ => c) x
    rw [hψ0e σ c x hx, hmx, hψ0e _ c (conjPts p rfl x) hx2, hχc σ _ (fun _ => c) x (conjPts p rfl x) rfl hxp]
    ring

end Conj

end GlobalTheory.AmbMetric
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.TwistTop
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.Published.Amb

variable {k : Type} [CommRing k] {X : Scheme.{0}}

private theorem comb_isometric_of_isometric {p : X ⟶ Sp k} {ι : Type} [Fintype ι] {L L' : ι → HermLB p}
    (hL : ∀ j, (L j).Isometric (L' j)) (n : ι → ℤ) : (comb L n).Isometric (comb L' n) := by
  unfold comb
  induction (Finset.univ : Finset ι).toList with
  | nil => exact HermLB.Isometric.refl _
  | cons i l ih =>
    simp only [List.foldr_cons]
    refine HermLB.Isometric.tens ?_ ih
    unfold zp
    exact HermLB.Isometric.tens (HermLB.Isometric.pow (hL i) _) (HermLB.Isometric.dual (HermLB.Isometric.pow (hL i) _))

theorem mixOn_congr [IsIntegral X] [IsLocallyNoetherian X] {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D) {ι : Type}
    [Fintype ι] {M M' : HermLB p} {L L' : ι → HermLB p} (hM : M.Isometric M') (hL : ∀ j, (L j).Isometric (L' j))
    (H : MixOn p D ι M L) : MixOn p D ι M' L' := by
  intro Φ hΦ n h hh r hr
  have hfam : ∀ o : Option ι, (o.elim M' L').Isometric (o.elim M L) := by
    intro o
    cases o with
    | none => exact HermLB.Isometric.symm hM
    | some j => exact HermLB.Isometric.symm (hL j)
  have hΦ' : IsArFun (fun o : Option ι => o.elim M L) D Φ :=
    ⟨fun n' => HermLB.Isometric.isSelfInter hX (comb_isometric_of_isometric hfam n') (hΦ.1 n'), hΦ.2⟩
  have hcomb : (comb L' n).Isometric (comb L n) := comb_isometric_of_isometric (fun j => HermLB.Isometric.symm (hL j)) n
  have hh' : (comb L n).IsArithHeight h := HermLB.Isometric.isArithHeight hX hcomb hh
  obtain ⟨r0, hr0, hdiv, hlog⟩ := HermLB.Isometric.exists_isRatSec (HermLB.Isometric.symm hM) hr
  obtain ⟨hint, heq⟩ := H Φ hΦ' n h hh' r0 hr0
  have hms : ∀ σ, MeasurableSet (offSupp p σ (M'.div hr)) := fun σ => (isOpen_offSupp _).measurableSet
  refine ⟨fun σ => ?_, ?_⟩
  · have hi := hint σ
    rw [HermLB.Isometric.chernIntegrableOn_eq (HermLB.Isometric.symm hcomb) σ D, hdiv] at hi
    exact hi.congr (hms σ) (hlog σ)
  · rw [heq, hdiv, sub_right_inj]
    simp only [HermLB.archInt]
    rw [hdiv]
    apply finsum_congr
    intro σ
    rw [HermLB.Isometric.chernInt_eq (HermLB.Isometric.symm hcomb) σ D]
    exact Weight.chernInt_congr (hms σ) (hlog σ)

theorem pull_congr {Y P : Scheme.{0}} {p : P ⟶ Sp k} {q : Y ⟶ Sp k} (M : HermLB p) {f g : Y ⟶ P} (e : f = g)
    (hf : f ≫ p = q) (hg : g ≫ p = q) : M.pull f hf = M.pull g hg := by
  subst e; rfl

theorem dim_closure_image {P : Scheme.{0}} (i : X ⟶ P) [IsClosedImmersion i] (x : X) :
    topologicalKrullDim (closure ({i x} : Set P)) = topologicalKrullDim (closure ({x} : Set X)) := by
  have hi : Topology.IsClosedEmbedding i := i.isClosedEmbedding
  have hE : Topology.IsEmbedding (fun z : closure ({x} : Set X) => i z.1) :=
    hi.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hset : closure ({i x} : Set P) = Set.range (fun z : closure ({x} : Set X) => i z.1) := by
    rw [← Set.image_singleton, hi.closure_image_eq]
    ext y
    simp
  rw [hset]
  exact (IsHomeomorph.topologicalKrullDim_eq _ hE.toHomeomorph.isHomeomorph).symm

end GlobalTheory.Published.Amb
end
end
