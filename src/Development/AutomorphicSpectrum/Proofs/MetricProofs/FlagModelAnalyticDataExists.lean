import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularWeightMonotoneRegularization
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlatWeightExtends
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagBundlePartialBlockMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedAtlasProjection
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBundleMetricLine
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothFunctionAsDegreeZeroMetric
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SamePotBlock
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBlocks
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviPullEq
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialBlockDecomposition
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumSqCompBlockMap
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MCoordIdealCompLeImageZ

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.Transport

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem isOpen_compl_bdry (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ)
    (hs : IsSection A L s) : IsOpen (bdry s)ᶜ := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  have hyt : A.chart j y ∈ (A.chart j).target := (A.chart j).map_source hj
  have hsy : (A.chart j).symm (A.chart j y) = y := (A.chart j).left_inv hj
  have han : AnalyticAt ℂ (s y ∘ (A.chart j).symm) (A.chart j y) :=
    hs.1 y j (A.chart j y) ⟨hyt, by
      show (A.chart j).symm (A.chart j y) ∈ L.U y
      rw [hsy]; exact L.mem_U y⟩
  have hcy : ContinuousAt (fun z => (s y ∘ (A.chart j).symm) (A.chart j z)) y :=
    ContinuousAt.comp (f := A.chart j) han.continuousAt ((A.chart j).continuousAt hj)
  have hne : (s y ∘ (A.chart j).symm) (A.chart j y) ≠ 0 := by
    show s y ((A.chart j).symm (A.chart j y)) ≠ 0
    rw [hsy]; exact hy
  have h1 : ∀ᶠ z in 𝓝 y, (s y ∘ (A.chart j).symm) (A.chart j z) ≠ 0 := hcy.eventually_ne hne
  filter_upwards [h1, (A.chart j).open_source.mem_nhds hj,
    (L.isOpen_U y).mem_nhds (L.mem_U y)] with z h1 h2 h3
  have h1' : s y z ≠ 0 := by
    have : s y ((A.chart j).symm (A.chart j z)) ≠ 0 := h1
    rwa [(A.chart j).left_inv h2] at this
  intro hz
  have hz' : s z z = 0 := hz
  have hg := hs.2 y z z ⟨h3, L.mem_U z⟩
  rw [hz'] at hg
  simp only [norm_zero, zero_mul] at hg
  have hpos : 0 < ‖s y z‖ * Real.exp (-L.φ y z) :=
    mul_pos (norm_pos_iff.2 h1') (Real.exp_pos _)
  exact hpos.ne' hg

theorem contDiffAt_two {A : FinHolAtlas e X} {U : Set X} {f : X → ℝ} (h : A.SmoothOn U f)
    (hU : IsOpen U) (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target)
    (hyU : (A.chart j).symm y ∈ U) : ContDiffAt ℝ 2 (f ∘ (A.chart j).symm) y :=
  ((h j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds ⟨hy, hyU⟩)).of_le
    ENat.LEInfty.out

theorem levi_eq_of_sub_re (A : FinHolAtlas e X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) {W : Set X} (hW : IsOpen W) (hyW : (A.chart j).symm y ∈ W)
    {G : X → ℂ} (hG : A.HoloOn W G) {a b : X → ℝ} (hab : ∀ z ∈ W, a z - b z = (G z).re)
    (hb : ContDiffAt ℝ 2 (b ∘ (A.chart j).symm) y) (w : Fin e → ℂ) :
    levi (a ∘ (A.chart j).symm) y w = levi (b ∘ (A.chart j).symm) y w := by
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hy, hyW⟩
  have hre : ContDiffAt ℝ 2 (fun z => ((G ∘ (A.chart j).symm) z).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y hGa.restrictScalars.contDiffAt
  have hev : (a ∘ (A.chart j).symm) =ᶠ[𝓝 y]
      fun z => (b ∘ (A.chart j).symm) z + 1 * ((G ∘ (A.chart j).symm) z).re := by
    have hmem : ∀ᶠ z in 𝓝 y, (A.chart j).symm z ∈ W :=
      ((A.chart j).continuousAt_symm hy).eventually_mem (hW.mem_nhds hyW)
    filter_upwards [hmem] with z hz
    have := hab _ hz
    simp only [Function.comp]
    linarith
  rw [levi_congr hev, levi_add_smul 1 hb hre, levi_re_analytic hGa]
  ring

theorem exists_re_base {A : FinHolAtlas e X} {P : LocPot X} (hP : IsPotential A P) {x u : X}
    (hu : u ∈ P.U x) : ∃ W : Set X, IsOpen W ∧ u ∈ W ∧ ∃ G : X → ℂ, A.HoloOn W G ∧
      ∀ z ∈ W, P.φ x z - P.φ u z = (G z).re := by
  obtain ⟨W, oW, mW, G, hG, hW⟩ := hP.2 x u u ⟨hu, P.mem_U u⟩
  refine ⟨W ∩ P.U x ∩ P.U u, (oW.inter (P.isOpen_U x)).inter (P.isOpen_U u),
    ⟨⟨mW, hu⟩, P.mem_U u⟩, G, fun k => (hG k).mono fun y hy => ⟨hy.1, hy.2.1.1⟩, ?_⟩
  rintro z hz
  exact hW z hz

theorem exists_re_change {A : FinHolAtlas e X} {th th' : LocPot X} (hth : IsPotential A th)
    (hsame : SamePot A Set.univ th th') {x u : X} (hu : u ∈ th.U x) :
    ∃ W : Set X, IsOpen W ∧ u ∈ W ∧ ∃ G : X → ℂ, A.HoloOn W G ∧
      ∀ z ∈ W, th.φ x z - th'.φ u z = (G z).re := by
  obtain ⟨W, oW, mW, G₁, h₁, e₁⟩ := exists_re_base hth hu
  obtain ⟨V, oV, mV, G₂, h₂, e₂⟩ := hsame u (Set.mem_univ _)
  refine ⟨W ∩ V, oW.inter oV, ⟨mW, mV⟩, fun z => G₁ z + G₂ z, fun k => ?_, ?_⟩
  · exact ((h₁ k).mono fun y hy => ⟨hy.1, hy.2.1⟩).add ((h₂ k).mono fun y hy => ⟨hy.1, hy.2.2⟩)
  · rintro z ⟨a, b⟩
    have h1 := e₁ z a
    have h2 := e₂ z b
    simp only [Complex.add_re]
    linarith

theorem isPshOn_transport {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ} {th th' : LocPot X}
    {ph : X → ℝ} (hs : IsSection A L s) (hth : IsPotential A th) (hth' : IsPotential A th')
    (hsame : SamePot A Set.univ th th') (hsm : A.SmoothOn (bdry s)ᶜ ph)
    (hpsh : IsPshOn A (bdry s)ᶜ (th' + LocPot.ofFun ph)) :
    IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun ph) := by
  intro x j y hy w
  obtain ⟨hyt, hyU, hyb⟩ := hy
  have hyx : (A.chart j).symm y ∈ th.U x := hyU.1
  obtain ⟨W, oW, mW, G, hG, hW⟩ := exists_re_change hth hsame hyx
  have h0 := hpsh ((A.chart j).symm y) j y
    ⟨hyt, ⟨th'.mem_U _, Set.mem_univ _⟩, hyb⟩ w
  have hb : ContDiffAt ℝ 2 ((th' + LocPot.ofFun ph).φ ((A.chart j).symm y) ∘ (A.chart j).symm) y :=
    (contDiffAt_two (hth'.1 _) (th'.isOpen_U _) j hyt (th'.mem_U _)).add
      (contDiffAt_two hsm (isOpen_compl_bdry A L s hs) j hyt hyb)
  rw [levi_eq_of_sub_re A j hyt oW mW hG (a := (th + LocPot.ofFun ph).φ x)
    (b := (th' + LocPot.ofFun ph).φ ((A.chart j).symm y)) (fun z hz => by
      have h1 := hW z hz
      show th.φ x z + ph z - (th'.φ _ z + ph z) = _
      linarith) hb w]
  exact h0

theorem isPsh_transport {A : FinHolAtlas e X} {Θ th th' : LocPot X} {f : X → ℝ} {c : ℝ}
    (hΘ : IsPotential A Θ) (hth : IsPotential A th) (hth' : IsPotential A th')
    (hsame : SamePot A Set.univ th th') (hf : A.Smooth f)
    (hpsh : IsPsh A (th' + LocPot.ofFun f + Θ.rsmul c)) :
    IsPsh A (th + LocPot.ofFun f + Θ.rsmul c) := by
  intro x j y hy w
  obtain ⟨hyt, hyU⟩ := hy
  have hyx : (A.chart j).symm y ∈ th.U x := hyU.1.1
  have hyΘ : (A.chart j).symm y ∈ Θ.U x := hyU.2
  obtain ⟨W₁, o₁, m₁, G₁, h₁, e₁⟩ := exists_re_change hth hsame hyx
  obtain ⟨W₂, o₂, m₂, G₂, h₂, e₂⟩ := exists_re_base hΘ hyΘ
  have h0 := hpsh ((A.chart j).symm y) j y
    ⟨hyt, ⟨⟨th'.mem_U _, Set.mem_univ _⟩, Θ.mem_U _⟩⟩ w
  have hb : ContDiffAt ℝ 2
      ((th' + LocPot.ofFun f + Θ.rsmul c).φ ((A.chart j).symm y) ∘ (A.chart j).symm) y :=
    ((contDiffAt_two (hth'.1 _) (th'.isOpen_U _) j hyt (th'.mem_U _)).add
      (contDiffAt_two hf isOpen_univ j hyt (Set.mem_univ _))).add
      (contDiffAt_const.mul (contDiffAt_two (hΘ.1 _) (Θ.isOpen_U _) j hyt (Θ.mem_U _)))
  have hG : A.HoloOn (W₁ ∩ W₂) fun z => G₁ z + (c : ℂ) * G₂ z := fun k =>
    ((h₁ k).mono fun y hy => ⟨hy.1, hy.2.1⟩).add
      ((analyticOnNhd_const (v := (c : ℂ))).mul ((h₂ k).mono fun y hy => ⟨hy.1, hy.2.2⟩))
  rw [levi_eq_of_sub_re A j hyt (o₁.inter o₂) ⟨m₁, m₂⟩ hG
    (a := (th + LocPot.ofFun f + Θ.rsmul c).φ x)
    (b := (th' + LocPot.ofFun f + Θ.rsmul c).φ ((A.chart j).symm y)) (fun z hz => by
      have h1 := e₁ z hz.1
      have h2 := e₂ z hz.2
      show th.φ x z + f z + c * Θ.φ x z -
        (th'.φ _ z + f z + c * Θ.φ _ z) = _
      simp only [Complex.add_re, Complex.re_ofReal_mul]
      rw [← h1, ← h2]
      ring) hb w]
  exact h0

theorem singWeight_regFamily_transport : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X)
    (s : X → X → ℂ) (th th' : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C₅ C t₀ : ℝ),
    IsPotential A Θ → IsSection A L s → IsPotential A th → IsPotential A th' → SamePot A Set.univ th th' →
    (IsSingWeight A L s th' ph C₅ → IsSingWeight A L s th ph C₅) ∧
      (IsRegFamily A Θ L s th' ph phT C t₀ → IsRegFamily A Θ L s th ph phT C t₀) := by
  intro e X _ A Θ L s th th' ph phT C₅ C t₀ hΘ hs hth hth' hsame
  constructor
  · rintro ⟨_, hsm, hpsh, hb⟩
    exact ⟨hth, hsm, isPshOn_transport hs hth hth' hsame hsm hpsh, hb⟩
  · rintro ⟨h0, h1, hreg⟩
    refine ⟨h0, h1, fun t ht ht' => ?_⟩
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hreg t ht ht'
    exact ⟨a1, a2, a3, a4, isPsh_transport hΘ hth hth' hsame a1 a5, a6, a7, a8⟩

end GlobalTheory.CompanionTheory.Ar.PB.Transport
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA.Flat

theorem levi_log_norm {e : ℕ} {G : (Fin e → ℂ) → ℂ} {u : Fin e → ℂ} (hG : AnalyticAt ℂ G u) (h0 : G u ≠ 0)
    (w : Fin e → ℂ) : levi (fun y => Real.log ‖G y‖) u w = 0 := by
  have h1 : AnalyticAt ℂ (fun y => Complex.log (G y / G u)) u :=
    (hG.div_const (c := G u)).clog (by simp [div_self h0])
  have h2 : (fun y => Real.log ‖G y‖) =ᶠ[𝓝 u]
      fun y => (Complex.log (G y / G u)).re + Real.log ‖G u‖ * (fun _ => (1 : ℝ)) y := by
    filter_upwards [hG.continuousAt.eventually_ne h0] with y hy
    rw [Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.2 hy) (norm_ne_zero_iff.2 h0)]
    ring
  have h3 : ContDiffAt ℝ 2 (fun y => (Complex.log (G y / G u)).re) u :=
    Complex.reCLM.contDiff.contDiffAt.comp u (h1.restrictScalars (𝕜 := ℝ)).contDiffAt
  rw [levi_congr h2, levi_add_smul _ h3 contDiffAt_const, levi_re_analytic h1]
  simp [levi]

theorem blk_none_of_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
    {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j) {p : Ψ × Fin N} (h : (p.2 : ℕ) + 1 = N) :
    M.blk p = none := (M.blk_none p).2 fun hq => hq.2 h

theorem dy_eq_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
    {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j) {p : Ψ × Fin N} (h : (p.2 : ℕ) + 1 = N)
    {k : K} (hk : ¬ ∀ p', M.blk p' ≠ some k) : M.dy p k = 0 := by
  unfold FlagModel.dy
  rw [dif_neg hk, blk_none_of_top M h]
  simp

theorem gramLog_top {N : ℕ} (j : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) :
    gramLog (sigForm N j) N g = Real.log ‖g.det‖ := by
  have e : (gramHead (sigForm N j) N g).det = (gramOf (sigForm N j) g).det := by
    unfold gramHead
    exact Matrix.det_submatrix_equiv_self
      (Equiv.subtypeUnivEquiv (p := fun a : Fin N => (a : ℕ) < N) fun a => a.2) _
  have hd : ‖(Matrix.diagonal fun i => ((sigForm N j i : ℝ) : ℂ)).det‖ = 1 := by
    rw [Matrix.det_diagonal, norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    unfold sigForm
    split_ifs <;> simp
  unfold gramLog
  rw [e, gramOf, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul, hd, Matrix.det_conjTranspose, norm_star,
    mul_one, ← pow_two, Real.log_pow]
  push_cast
  ring

theorem stepPot_top {N : ℕ} {j : ℕ} (hj : j ≤ N) (i : Fin N) (h : (i : ℕ) + 1 = N)
    (g : Matrix (Fin N) (Fin N) ℂ) : stepPot N j i g = Real.log ‖g.det‖ := by
  unfold stepPot
  split_ifs with h1
  · have e1 : N - j + ((i : ℕ) + 1) = N := by omega
    have e2 : N - j = 0 := by omega
    rw [e1, gramLog_top, e2]
    have : gramLog (sigForm N j) 0 g = 0 := by
      unfold gramLog
      haveI : IsEmpty {a : Fin N // (a : ℕ) < 0} := ⟨fun a => by have := a.2; omega⟩
      simp
    rw [this, sub_zero]
  · have e1 : (i : ℕ) + 1 - j = N - j := by omega
    rw [e1, gramLog_top]
    ring

theorem minorIJ_one_self {N : ℕ} (S : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) S S = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (S.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem detFac_one {N : ℕ} (j : ℕ) (i : Fin N) : detFac j i (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
  unfold detFac
  simp only [minorIJ_one_self]
  simp

theorem blockPot_top {N j : ℕ} (hj : j ≤ N) (i : Fin N) (h : (i : ℕ) + 1 = N) {Pi G : Matrix (Fin N) (Fin N) ℂ}
    (hP : IsPeriodGram j Pi G) (hG : IsBlockDiag j G) (hG' : G.PosDef) :
    blockPot j i G 1 = Real.log ‖Pi.det‖ := by
  have := (stepPot_mul_eq_blockPot N j i Pi G 1 hj hP hG hG' isBlockDiag_one (by simp)).2
  rw [mul_one, stepPot_top hj i h, detFac_one, norm_one, Real.log_one, add_zero] at this
  exact this.symm

theorem sameOrbit_symm {K : Type} {ι : K → Type} {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun q => ?_⟩
  simp only [inv_mul_cancel_left₀ (hc q.1)]

theorem sameOrbit_trans {K : Type} {ι : K → Type} {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z')
    (h' : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, hd, rfl⟩ := h'
  exact ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), funext fun q => by simp only [mul_assoc]⟩

section Val

variable {Kb : Type} [Fintype Kb] {ιb : Kb → Type} [∀ k, Fintype (ιb k)] {Ω : Type} [Field Ω]

theorem eval_ne_zero_of_not_mem {z : (Σ k, ιb k) → ℂ} {h : MRing ιb} {d : Kb → ℕ} (hh : IsMultiHomog h d)
    (hq : h ∉ mCoordIdeal z) : eval z (map (Int.castRingHom ℂ) h) ≠ 0 := fun e => hq
  (mem_mCoordIdeal_of_aeval_eq_zero z hh (by
    have : aeval z h = eval z (map (Int.castRingHom ℂ) h) := by
      rw [eval_map, aeval_def]
      exact congrArg (fun f => eval₂ f z h) (Subsingleton.elim _ _)
    rw [this, e]))

theorem aeval_ne_zero_of_eval {x : (Σ k, ιb k) → Ω} {z : (Σ k, ιb k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x))
    {h : MRing ιb} {d : Kb → ℕ} (hh : IsMultiHomog h d) (hne : eval z (map (Int.castRingHom ℂ) h) ≠ 0) :
    aeval x h ≠ 0 := fun e => hne (eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero x hh e))

theorem isValueAt_of_orbit {x : (Σ k, ιb k) → Ω} {s : Ω} {d : Kb → ℕ} {g h : MRing ιb} (hg : IsMultiHomog g d)
    (hh : IsMultiHomog h d) (a : aeval x h ≠ 0) (he : aeval x g = s * aeval x h) {z z' : (Σ k, ιb k) → ℂ}
    (ho : SameOrbit z z') (hne : eval z' (map (Int.castRingHom ℂ) h) ≠ 0) :
    IsValueAt x s z (eval z' (map (Int.castRingHom ℂ) g) / eval z' (map (Int.castRingHom ℂ) h)) := by
  obtain ⟨c, hc, rfl⟩ := ho
  have hp : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  refine ⟨d, g, h, hg, hh, a, he, ?_, ?_⟩
  · rw [eval_smul_of_isMultiHomog hh]
    exact mul_ne_zero hp hne
  · rw [eval_smul_of_isMultiHomog hg, eval_smul_of_isMultiHomog hh, mul_div_mul_left _ _ hp]

theorem val_local {n : ℕ} {x : (Σ k, ιb k) → Ω} (Rb : AnLogRes (mCoordIdeal x) ⊤ n) (b₀ : Rb.X) {s : Ω}
    (hs0 : s ≠ 0) (hs : RegAt x (mCoordIdeal (Rb.lift b₀ b₀)) s)
    (hs' : RegAt x (mCoordIdeal (Rb.lift b₀ b₀)) s⁻¹) :
    ∃ (V : Set Rb.X) (f : Rb.X → ℂ), IsOpen V ∧ b₀ ∈ V ∧ Rb.A.HoloOn V f ∧ (∀ b ∈ V, f b ≠ 0) ∧
      ∀ b ∈ V, ∀ z, SameOrbit z (Rb.lift b b) → valAt x s z = f b := by
  obtain ⟨d, g, h, hg, hh, hQ, he⟩ := hs
  obtain ⟨d', g', h', hg', hh', hQ', he'⟩ := hs'
  have hz₀ : Rb.lift b₀ b₀ ∈ mcPts (mCoordIdeal x) := Rb.mem b₀ b₀ (Rb.mem_U b₀)
  have n1 := eval_ne_zero_of_not_mem hh hQ
  have n2 := eval_ne_zero_of_not_mem hh' hQ'
  have a1 := aeval_ne_zero_of_eval hz₀ hh n1
  have a2 := aeval_ne_zero_of_eval hz₀ hh' n2
  let E : MRing ιb → Rb.X → ℂ := fun f b => eval (Rb.lift b₀ b) (map (Int.castRingHom ℂ) f)
  have hE : ∀ f, Rb.A.HoloOn (Rb.U b₀) (E f) := holoOn_eval_lift Rb b₀
  have hC : ∀ f, ContinuousOn (E f) (Rb.U b₀) := fun f b hb =>
    (BlockPot.continuousAt_of_holoOn (hE f) hb).continuousWithinAt
  have hO : ∀ f, IsOpen (Rb.U b₀ ∩ E f ⁻¹' {0}ᶜ) := fun f =>
    (hC f).isOpen_inter_preimage (Rb.isOpen_U b₀) isOpen_compl_singleton
  refine ⟨(Rb.U b₀ ∩ E h ⁻¹' {0}ᶜ) ∩ (Rb.U b₀ ∩ E h' ⁻¹' {0}ᶜ), fun b => E g b / E h b, (hO h).inter (hO h'),
    ⟨⟨Rb.mem_U b₀, n1⟩, ⟨Rb.mem_U b₀, n2⟩⟩, ?_, ?_, ?_⟩
  · intro c u hu
    exact (hE g c u ⟨hu.1, hu.2.1.1⟩).div (hE h c u ⟨hu.1, hu.2.1.1⟩) hu.2.1.2
  · rintro b ⟨⟨hb, hb1⟩, -, hb2⟩ e
    have hm := Rb.mem b₀ b hb
    have v1 : IsValueAt x s (Rb.lift b₀ b) (E g b / E h b) :=
      isValueAt_of_orbit hg hh a1 he ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩ hb1
    have v2 : IsValueAt x s⁻¹ (Rb.lift b₀ b) (E g' b / E h' b) :=
      isValueAt_of_orbit hg' hh' a2 he' ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩ hb2
    have v3 := isValueAt_mul v1 v2
    rw [mul_inv_cancel₀ hs0] at v3
    have v4 : IsValueAt x 1 (Rb.lift b₀ b) 1 :=
      ⟨d, h, h, hh, hh, a1, by rw [one_mul], hb1, (div_self hb1).symm⟩
    have := isValueAt_unique hm v3 v4
    simp only at e
    rw [e, zero_mul] at this
    exact zero_ne_one this
  · rintro b ⟨⟨hb, hb1⟩, -⟩ z hz
    have ho : SameOrbit z (Rb.lift b₀ b) :=
      sameOrbit_trans hz (sameOrbit_symm (Rb.compat b₀ b b ⟨hb, Rb.mem_U b⟩))
    exact valAt_eq (mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal x) ho (Rb.mem b₀ b hb))
      (isValueAt_of_orbit hg hh a1 he ho hb1)

end Val

theorem exists_nhd_off_bdry {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {L : LocPot X}
    {s : X → X → ℂ} (hsec : IsSection A L s) {b₀ : X} (h : b₀ ∉ bdry s) :
    ∃ V : Set X, IsOpen V ∧ b₀ ∈ V ∧ V ⊆ (bdry s)ᶜ := by
  have hc : ContinuousOn (s b₀) (L.U b₀) := fun b hb =>
    (BlockPot.continuousAt_of_holoOn (hsec.1 b₀) hb).continuousWithinAt
  refine ⟨_, hc.isOpen_inter_preimage (L.isOpen_U b₀) isOpen_compl_singleton, ⟨L.mem_U b₀, h⟩, ?_⟩
  rintro b ⟨hb, hb'⟩ (e : s b b = 0)
  have h1 := hsec.2 b₀ b b ⟨hb, L.mem_U b⟩
  rw [e, norm_zero, zero_mul] at h1
  exact hb' (norm_eq_zero.1 ((mul_eq_zero.1 h1).resolve_right (Real.exp_pos _).ne'))

theorem holoOn_det {e N : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {V : Set X}
    {P : X → Matrix (Fin N) (Fin N) ℂ} (h : ∀ a b, A.HoloOn V fun x => P x a b) :
    A.HoloOn V fun x => (P x).det := by
  intro c u hu
  have e1 : ((fun x => (P x).det) ∘ (A.chart c).symm) = fun t =>
      ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, P ((A.chart c).symm t) (σ i) i := by
    funext t
    simp only [Function.comp_apply, Matrix.det_apply', Int.cast_inj]
  rw [e1]
  refine Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul ?_
  exact Finset.analyticAt_fun_prod _ fun i _ => h (σ i) i c u hu

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

theorem base_flat {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) {p : Ψ × Fin N} (hN : (p.2 : ℕ) + 1 = N)
    {b₀ : BM.Rb.X} (hb₀ : b₀ ∉ bdry BM.s) :
    ∃ (l : Fin BM.q) (V : Set BM.Rb.X) (f : BM.Rb.X → ℂ), IsOpen V ∧ b₀ ∈ V ∧ V ⊆ BM.O l \ bdry BM.s ∧
      BM.Rb.A.HoloOn V f ∧ (∀ b ∈ V, f b ≠ 0) ∧ ∀ b ∈ V, ∀ z, SameOrbit z (BM.Rb.lift b b) →
        blockPot j p.2 (BM.G l p.1 b) 1 - Real.log ‖valAt M.x ((BM.F l).υ p) z‖ = Real.log ‖f b‖ := by
  obtain ⟨l, hl⟩ := BM.O_cover b₀
  have hbl : b₀ ∈ BM.O l \ bdry BM.s := ⟨hl, hb₀⟩
  have hnone := blk_none_of_top M hN
  obtain ⟨h0, h1, h2⟩ := (BM.good l b₀ hl).2.2 p hnone
  obtain ⟨V₁, f₁, o₁, m₁, H₁, n₁, e₁⟩ := val_local BM.Rb b₀ h0 h1 h2
  obtain ⟨V₂, Pi, m₂, o₂, H₂, P₂⟩ := BM.period l b₀ hbl
  obtain ⟨V₃, o₃, m₃, s₃⟩ := exists_nhd_off_bdry BM.sec hb₀
  have hsub : V₁ ∩ V₂ ∩ V₃ ∩ BM.O l ⊆ BM.O l \ bdry BM.s := fun b hb => ⟨hb.2, s₃ hb.1.2⟩
  have hdet := holoOn_det (H₂ p.1)
  refine ⟨l, V₁ ∩ V₂ ∩ V₃ ∩ BM.O l, fun b => (Pi p.1 b).det / f₁ b, ((o₁.inter o₂).inter o₃).inter (BM.O_open l),
    ⟨⟨⟨m₁, m₂⟩, m₃⟩, hl⟩, hsub, ?_, ?_, ?_⟩
  · intro c u hu
    have hu₁ : (BM.Rb.A.chart c).symm u ∈ V₁ := hu.2.1.1.1
    have hu₂ : (BM.Rb.A.chart c).symm u ∈ V₂ := hu.2.1.1.2
    exact (hdet c u ⟨hu.1, hu₂⟩).div (H₁ c u ⟨hu.1, hu₁⟩) (n₁ _ hu₁)
  · intro b hb
    exact div_ne_zero (P₂ p.1 b hb.1.1.2).1.1.ne_zero (n₁ b hb.1.1.1)
  · intro b hb z hz
    have hbG := BM.G_pos l p.1 b (hsub hb)
    rw [blockPot_top M.j_le p.2 hN (P₂ p.1 b hb.1.1.2) hbG.1 hbG.2, e₁ b hb.1.1.1 z hz, norm_div,
      Real.log_div (norm_ne_zero_iff.2 (P₂ p.1 b hb.1.1.2).1.1.ne_zero) (norm_ne_zero_iff.2 (n₁ b hb.1.1.1))]

def cz (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι k) → ℂ) (k : K) : ℂ :=
  if h : ∀ p', M.blk p' ≠ some k then z ⟨k, F.c ⟨k, h⟩⟩ else 1

theorem coord_ne {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) {l : Fin BM.q} {b : BM.Rb.X}
    (hb : b ∈ BM.O l) {z : (Σ k, ι k) → ℂ} (ho : SameOrbit (basePart M.blk z) (BM.Rb.lift b b))
    (k : NonPluckerBlocks M.blk) : z ⟨k.1, (BM.F l).c k⟩ ≠ 0 := by
  obtain ⟨t, ht, e⟩ := ho
  have h1 : BM.Rb.lift b b ⟨k, (BM.F l).c k⟩ ≠ 0 := fun h => (BM.good l b hb).1 k (by
    show mConeMap _ (X ⟨k, (BM.F l).c k⟩) = 0
    rw [mConeMap, aeval_X, h, map_zero, zero_mul])
  have h2 := congrFun e ⟨k, (BM.F l).c k⟩
  simp only [basePart] at h2
  rw [h2]
  exact mul_ne_zero (ht k) h1

theorem log_hom_eq {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) {p : Ψ × Fin N} (hN : (p.2 : ℕ) + 1 = N)
    {l : Fin BM.q} {b : BM.Rb.X} (hb : b ∈ BM.O l \ bdry BM.s) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) (ho : SameOrbit (basePart M.blk z) (BM.Rb.lift b b)) :
    ∃ zb, SameOrbit zb (BM.Rb.lift b b) ∧ Real.log ((BM.hom p).h z) =
      ∑ k, (M.dy p k : ℝ) * Real.log ‖cz M (BM.F l) z k‖ + blockPot j p.2 (BM.G l p.1 b) 1 -
        Real.log ‖valAt M.x ((BM.F l).υ p) zb‖ := by
  have hc : ∀ k, cz M (BM.F l) z k ≠ 0 := by
    intro k
    unfold cz
    split_ifs with h
    · exact coord_ne BM hb.1 ho ⟨k, h⟩
    · exact one_ne_zero
  set t : K → ℂ := fun k => (cz M (BM.F l) z k)⁻¹ with ht
  have ht0 : ∀ k, t k ≠ 0 := fun k => inv_ne_zero (hc k)
  set z' : (Σ k, ι k) → ℂ := fun q => t q.1 * z q with hz'
  have hm : z' ∈ mcPts (mCoordIdeal y) :=
    mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal y) ⟨t, ht0, rfl⟩ hz
  have ho' : SameOrbit (basePart M.blk z') (BM.Rb.lift b b) := by
    refine sameOrbit_trans ⟨fun k => t k.1, fun k => ht0 _, rfl⟩ ho
  have hone : ∀ k, basePart M.blk z' ⟨k, (BM.F l).c k⟩ = 1 := by
    intro k
    have e : cz M (BM.F l) z k.1 = z ⟨k.1, (BM.F l).c k⟩ := dif_pos k.2
    show t k.1 * z ⟨k.1, (BM.F l).c k⟩ = 1
    rw [ht]
    simp only
    rw [e]
    exact inv_mul_cancel₀ (coord_ne BM hb.1 ho k)
  have h1 := (BM.induced l b hb p z' hm ho' hone 1 isBlockDiag_one (by simp)).2 (blk_none_of_top M hN)
  have h2 := (BM.hom p).smul t z ht0
  have hpos := (BM.hom p).pos z hz.1
  refine ⟨_, ho', ?_⟩
  rw [← sub_eq_zero]
  have h3 : Real.log ((BM.hom p).h z') = ∑ k, (M.dy p k : ℝ) * Real.log ‖t k‖ + Real.log ((BM.hom p).h z) := by
    show Real.log ((BM.hom p).h fun q => t q.1 * z q) = _
    rw [h2, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (ht0 k))) hpos.ne',
      Real.log_prod fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (ht0 k))]
    simp only [Real.log_zpow, BM.hom_deg]
  have h4 : ∑ k, (M.dy p k : ℝ) * Real.log ‖t k‖ = - ∑ k, (M.dy p k : ℝ) * Real.log ‖cz M (BM.F l) z k‖ := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [ht, norm_inv, Real.log_inv]
    ring
  rw [h3, h4] at h1
  linarith

theorem torus_move {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) {p : Ψ × Fin N} (hN : (p.2 : ℕ) + 1 = N)
    {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)] {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)}
    (hb : IsBlockMap κ v) (hr : ∀ k, (∀ p', M.blk p' ≠ some k) → k ∈ Set.range κ) {e : ℕ}
    (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (ph : R.X → ℝ)
    (H1 : ∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧
      SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x)))
    (H2 : ∀ x, pr x ∉ bdry BM.s → ∀ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x →
      Real.log ((BM.hom p).h z) = Real.log ((fsHerm ι (M.dy p)).h z) + ph x)
    {x₀ t : R.X} (ht : t ∈ R.U x₀) (hbd : pr t ∉ bdry BM.s) :
    ∃ z₁ ∈ mcPts (mCoordIdeal y), z₁ ∘ v = R.lift x₀ t ∧ SameOrbit (basePart M.blk z₁) (BM.Rb.lift (pr t) (pr t)) ∧
      Real.log (refNorm (fun k => M.dy p (κ k)) (R.lift x₀ t)) + ph t = Real.log ((BM.hom p).h z₁) := by
  obtain ⟨z, hz, hzv, ho⟩ := H1 t
  obtain ⟨c, hc, ec⟩ := R.compat x₀ t t ⟨ht, R.mem_U t⟩
  set ct : K → ℂ := Function.extend κ c 1 with hct
  have hκ : ∀ k, ct (κ k) = c k := fun k => hb.1.extend_apply _ _ _
  have hct0 : ∀ k, ct k ≠ 0 := by
    intro k
    by_cases hk : ∃ k', κ k' = k
    · obtain ⟨k', rfl⟩ := hk
      rw [hκ]
      exact hc k'
    · rw [hct, Function.extend_apply' _ _ _ hk]
      exact one_ne_zero
  have hm : (fun q => ct q.1 * z q) ∈ mcPts (mCoordIdeal y) :=
    mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal y) ⟨ct, hct0, rfl⟩ hz
  have hv : (fun q => ct q.1 * z q) ∘ v = R.lift x₀ t := by
    funext q
    have e1 := congrFun ec q
    have e2 := congrFun hzv q
    simp only [Function.comp_apply] at e2 ⊢
    rw [e1, hb.2.2.1 q, hκ, e2]
  have ha : ∀ k, k ∉ Set.range κ → M.dy p k = 0 := fun k hk => dy_eq_zero M hN fun h => hk (hr k h)
  refine ⟨fun q => ct q.1 * z q, hm, hv, sameOrbit_trans ⟨fun k => ct k.1, fun k => hct0 _, rfl⟩ ho, ?_⟩
  have e1 : refNorm (fun k => M.dy p (κ k)) (R.lift x₀ t) = refNorm (M.dy p) fun q => ct q.1 * z q := by
    rw [← hv]
    exact (BlockPot.refNorm_block hb ha _).symm
  have e2 : refNorm (M.dy p) (fun q => ct q.1 * z q) = (∏ k, ‖ct k‖ ^ M.dy p k) * refNorm (M.dy p) z :=
    refNorm_smul _ ct z
  have e3 := (BM.hom p).smul ct z hct0
  rw [BM.hom_deg] at e3
  have hP : (∏ k, ‖ct k‖ ^ M.dy p k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hct0 k))
  rw [e1, e2, e3, Real.log_mul hP (refNorm_pos _ hz.1).ne', Real.log_mul hP ((BM.hom p).pos z hz.1).ne',
    H2 t hbd z hz hzv, fsHerm_h]
  ring

end Flag

section Main

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

theorem local_log_norm {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) {p : Ψ × Fin N}
    (hN : (p.2 : ℕ) + 1 = N) {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)] {κ : Kk → K}
    {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v) (hr : ∀ k, (∀ p', M.blk p' ≠ some k) → k ∈ Set.range κ)
    {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr)
    (ph : R.X → ℝ)
    (H1 : ∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧
      SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x)))
    (H2 : ∀ x, pr x ∉ bdry BM.s → ∀ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x →
      Real.log ((BM.hom p).h z) = Real.log ((fsHerm ι (M.dy p)).h z) + ph x)
    {x₀ t₀ : R.X} (ht₀ : t₀ ∈ R.U x₀) (hbd : pr t₀ ∉ bdry BM.s) :
    ∃ (W : Set R.X) (H : R.X → ℂ), IsOpen W ∧ t₀ ∈ W ∧ R.A.HoloOn W H ∧ (∀ t ∈ W, H t ≠ 0) ∧
      ∀ t ∈ W, Real.log (refNorm (fun k => M.dy p (κ k)) (R.lift x₀ t)) + ph t = Real.log ‖H t‖ := by
  obtain ⟨l, V, f, oV, mV, sV, HV, nV, eV⟩ := base_flat BM hN hbd

  have hw : ∀ k : NonPluckerBlocks M.blk, ∃ q, v q = ⟨k.1, (BM.F l).c k⟩ := fun k => hb.2.2.2 _ (hr k.1 k.2)
  choose w hw using hw
  have hE : ∀ k, R.A.HoloOn (R.U x₀) fun t => R.lift x₀ t (w k) := fun k => R.holo x₀ (w k)
  have hO : ∀ k, IsOpen (R.U x₀ ∩ (fun t => R.lift x₀ t (w k)) ⁻¹' {0}ᶜ) := fun k =>
    ContinuousOn.isOpen_inter_preimage (fun t ht => (BlockPot.continuousAt_of_holoOn (hE k) ht).continuousWithinAt)
      (R.isOpen_U x₀) isOpen_compl_singleton
  set W₀ : Set R.X := R.U x₀ ∩ pr ⁻¹' V with hW₀
  set W : Set R.X := W₀ ∩ ⋂ k, (R.U x₀ ∩ (fun t => R.lift x₀ t (w k)) ⁻¹' {0}ᶜ) with hW
  have oW : IsOpen W := ((R.isOpen_U x₀).inter (oV.preimage hp.1)).inter (isOpen_iInter_of_finite hO)
  have hbase : ∀ t ∈ W, ∃ z₁ ∈ mcPts (mCoordIdeal y), z₁ ∘ v = R.lift x₀ t ∧
      SameOrbit (basePart M.blk z₁) (BM.Rb.lift (pr t) (pr t)) ∧
      Real.log (refNorm (fun k => M.dy p (κ k)) (R.lift x₀ t)) + ph t = Real.log ((BM.hom p).h z₁) :=
    fun t ht => torus_move BM hN hb hr R pr ph H1 H2 ht.1.1 (sV ht.1.2).2
  let ℓ : K → R.X → ℂ := fun k t => if h : ∀ p', M.blk p' ≠ some k then R.lift x₀ t (w ⟨k, h⟩) else 1
  have hℓ0 : ∀ t ∈ W, ∀ k, ℓ k t ≠ 0 := by
    intro t ht k
    simp only [ℓ]
    split_ifs with h
    · exact (Set.mem_iInter.1 ht.2 ⟨k, h⟩).2
    · exact one_ne_zero
  have hℓH : ∀ k, R.A.HoloOn W (ℓ k) := by
    intro k c u hu
    by_cases h : ∀ p', M.blk p' ≠ some k
    · have e : ℓ k ∘ (R.A.chart c).symm = (fun t => R.lift x₀ t (w ⟨k, h⟩)) ∘ (R.A.chart c).symm := by
        funext t
        simp only [ℓ, Function.comp_apply, dif_pos h]
      rw [e]
      exact hE ⟨k, h⟩ c u ⟨hu.1, hu.2.1.1⟩
    · have e : ℓ k ∘ (R.A.chart c).symm = fun _ => 1 := by
        funext t
        simp only [ℓ, Function.comp_apply, dif_neg h]
      rw [e]
      exact analyticAt_const
  have hfH : R.A.HoloOn W fun t => f (pr t) :=
    fun c u hu => BlockPot.holoOn_comp hp HV c u ⟨hu.1, hu.2.1.2⟩
  have hcz : ∀ z₁, ∀ t, z₁ ∘ v = R.lift x₀ t → ∀ k, cz M (BM.F l) z₁ k = ℓ k t := by
    intro z₁ t hz k
    simp only [cz, ℓ]
    split_ifs with h
    · rw [← hz, Function.comp_apply, hw]
    · rfl
  have mW : t₀ ∈ W := by
    refine ⟨⟨ht₀, mV⟩, Set.mem_iInter.2 fun k => ⟨ht₀, ?_⟩⟩
    obtain ⟨z₁, -, hz, ho, -⟩ := torus_move BM hN hb hr R pr ph H1 H2 ht₀ hbd
    have := coord_ne BM (sV mV).1 ho k
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [← hz, Function.comp_apply, hw]
    exact this
  refine ⟨W, fun t => (∏ k, ℓ k t ^ M.dy p k) * f (pr t), oW, mW, ?_, ?_, ?_⟩
  · intro c u hu
    refine AnalyticAt.mul (Finset.analyticAt_fun_prod _ fun k _ => ?_) (hfH c u hu)
    exact (hℓH k c u hu).zpow (hℓ0 _ hu.2 k)
  · intro t ht
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hℓ0 t ht k)) (nV _ ht.1.2)
  · intro t ht
    obtain ⟨z₁, hz₁, hv, ho, he⟩ := hbase t ht
    obtain ⟨zb, hzb, hf⟩ := log_hom_eq BM hN (sV ht.1.2) hz₁ ho
    have hb' := eV _ ht.1.2 zb hzb
    rw [he, hf, norm_mul, norm_prod,
      Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => norm_ne_zero_iff.2 (zpow_ne_zero _ (hℓ0 t ht k)))
        (norm_ne_zero_iff.2 (nV _ ht.1.2)),
      Real.log_prod fun k _ => norm_ne_zero_iff.2 (zpow_ne_zero _ (hℓ0 t ht k)), ← hb']
    simp only [norm_zpow, Real.log_zpow, hcz z₁ t hv]
    ring

end Main

theorem flat_off_boundary : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ)
    (BM : BaseMetric M n) (p : Ψ × Fin N), (p.2 : ℕ) + 1 = N → ∀ (Kk : Type) [Fintype Kk] (ιk : Kk → Type)
    [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v →
    (∀ k, (∀ p', M.blk p' ≠ some k) → k ∈ Set.range κ) →
    ∀ (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr)
      (ph : R.X → ℝ),
    (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧ SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x))) →
    (∀ x, pr x ∉ bdry BM.s → ∀ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x →
      Real.log ((BM.hom p).h z) = Real.log ((fsHerm ι (M.dy p)).h z) + ph x) →
    IsPshOn R.A (bdry fun x y => BM.s (pr x) (pr y))ᶜ
        (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun ph) ∧
      IsPshOn R.A (bdry fun x y => BM.s (pr x) (pr y))ᶜ
        ((potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun ph).rsmul (-1)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p hN Kk _ ιk _ κ v hb hr e R pr hp ph H1 H2
  have key : ∀ (x₀ : R.X) (c : Fin R.A.n) (u : Fin e → ℂ), u ∈ (R.A.chart c).target →
      (R.A.chart c).symm u ∈ R.U x₀ → (R.A.chart c).symm u ∉ bdry (fun x y => BM.s (pr x) (pr y)) →
      ∃ G : (Fin e → ℂ) → ℂ, AnalyticAt ℂ G u ∧ G u ≠ 0 ∧
        (fun t => Real.log (refNorm (fun k => M.dy p (κ k)) (R.lift x₀ ((R.A.chart c).symm t))) +
          ph ((R.A.chart c).symm t)) =ᶠ[𝓝 u] fun t => Real.log ‖G t‖ := by
    intro x₀ c u hu h1 h2
    obtain ⟨W, H, oW, mW, HW, nW, eW⟩ := local_log_norm BM hN hb hr R pr hp ph H1 H2 h1 h2
    refine ⟨H ∘ (R.A.chart c).symm, HW c u ⟨hu, mW⟩, nW _ mW, ?_⟩
    filter_upwards [((R.A.chart c).isOpen_inter_preimage_symm oW).mem_nhds ⟨hu, mW⟩] with t ht
    exact eW _ ht.2
  constructor
  · intro x₀ c u hu w
    obtain ⟨G, hG, hG0, hE⟩ := key x₀ c u hu.1 hu.2.1.1 hu.2.2
    refine (levi_congr (φ := (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun ph).φ x₀ ∘
      (R.A.chart c).symm) hE w).trans_ge ?_
    rw [levi_log_norm hG hG0]
  · intro x₀ c u hu w
    obtain ⟨G, hG, hG0, hE⟩ := key x₀ c u hu.1 hu.2.1.1 hu.2.2
    have hE' : ((potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun ph).rsmul (-1)).φ x₀ ∘
        (R.A.chart c).symm =ᶠ[𝓝 u] fun t => Real.log ‖(G t)⁻¹‖ := by
      filter_upwards [hE] with t ht
      have ht' : ((potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun ph).rsmul (-1)).φ x₀
          ((R.A.chart c).symm t) = -1 * (Real.log (refNorm (fun k => M.dy p (κ k)) (R.lift x₀ ((R.A.chart c).symm t))) +
            ph ((R.A.chart c).symm t)) := rfl
      rw [Function.comp_apply, ht', ht, norm_inv, Real.log_inv]
      ring
    rw [levi_congr hE' w, levi_log_norm (G := fun t => (G t)⁻¹) (hG.inv hG0) (inv_ne_zero hG0)]

end GlobalTheory.CompanionTheory.Ar.PB.FA.Flat
end
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA.StepMap

theorem orbit_symm {K : Type} {ι : K → Type} {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext q
  show z' q = (c q.1)⁻¹ * (c q.1 * z' q)
  rw [← mul_assoc, inv_mul_cancel₀ (hc q.1), one_mul]

theorem orbit_trans {K : Type} {ι : K → Type} {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z')
    (h' : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext q
  show c q.1 * (c' q.1 * z'' q) = c q.1 * c' q.1 * z'' q
  rw [mul_assoc]

theorem not_mem_mcPts_top {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] (z : (Σ k, ι k) → ℂ) :
    z ∉ mcPts (⊤ : Ideal (MRing ι)) := by
  intro hz
  have h1 := (show (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧
    ∀ f ∈ (⊤ : Ideal (MRing ι)), eval z (map (Int.castRingHom ℂ) f) = 0 from hz).2 1 Submodule.mem_top
  simp at h1

theorem factor : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (p : Ψ × Fin N) (n e e' : ℕ)
    (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (R : AnLogRes (mCoordIdeal y) ⊤ e)
    (Rp : AnLogRes (mCoordIdeal (y ∘ stepV M p)) ⊤ e') (pr : R.X → Rb.X) (prp : Rp.X → Rb.X) (h : R.X → Rp.X),
    (∀ x, SameOrbit (basePart M.blk (R.lift x x)) (Rb.lift (pr x) (pr x))) →
    (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ stepV M p = Rp.lift x x ∧
      SameOrbit (basePart M.blk z) (Rb.lift (prp x) (prp x))) →
    (∀ x, SameOrbit (Rp.lift (h x) (h x)) (R.lift x x ∘ stepV M p)) →
    (∀ x, prp (h x) = pr x) ∧ ∀ x x', pr x = pr x' →
      (∀ k, M.blk p = some k → ∃ a : ℂ, ∀ m : ι k, R.lift x x ⟨k, m⟩ = a * R.lift x' x' ⟨k, m⟩) → h x = h x' := by
  intro K _ ι _ Φ _ y Ψ N j M p n e e' Rb R Rp pr prp hh H1 H2 H3
  have hnz : ∀ x k, ∃ i, R.lift x x ⟨k, i⟩ ≠ 0 := fun x => (R.mem x x (R.mem_U x)).1
  have hb : ∀ z w : (Σ k, ι k) → ℂ, SameOrbit (z ∘ stepV M p) (w ∘ stepV M p) →
      SameOrbit (basePart M.blk z) (basePart M.blk w) := by
    rintro z w ⟨c, hc, hzw⟩
    exact ⟨fun k => c ⟨k.1, Or.inl k.2⟩, fun k => hc _,
      funext fun q => congrFun hzw ⟨⟨q.1.1, Or.inl q.1.2⟩, q.2⟩⟩
  refine ⟨fun x => ?_, fun x x' hpr hsc => ?_⟩
  · obtain ⟨z, -, hz1, hz2⟩ := H2 (hh x)
    have o1 : SameOrbit (z ∘ stepV M p) (R.lift x x ∘ stepV M p) := by
      rw [hz1]
      exact H3 x
    exact Rb.inj _ _ (not_mem_mcPts_top _)
      (orbit_trans (orbit_trans (orbit_symm hz2) (hb _ _ o1)) (H1 x))
  · apply Rp.inj _ _ (not_mem_mcPts_top _)
    refine orbit_trans (H3 x) (orbit_trans ?_ (orbit_symm (H3 x')))
    have h1' := H1 x'
    rw [← hpr] at h1'
    obtain ⟨cb, hcb, hbeq⟩ := orbit_trans (H1 x) (orbit_symm h1')
    refine ⟨fun k => if hk : (∀ p', M.blk p' ≠ some k.1) then cb ⟨k.1, hk⟩
      else (hsc k.1 (k.2.resolve_left hk)).choose, fun k => ?_, ?_⟩
    · dsimp only
      split_ifs with hk
      · exact hcb _
      · intro h0
        obtain ⟨i, hi⟩ := hnz x k.1
        apply hi
        rw [(hsc k.1 (k.2.resolve_left hk)).choose_spec i, h0, zero_mul]
    · funext q
      show R.lift x x ⟨q.1.1, q.2⟩ = _ * R.lift x' x' ⟨q.1.1, q.2⟩
      dsimp only
      split_ifs with hk
      · exact congrFun hbeq ⟨⟨q.1.1, hk⟩, q.2⟩
      · exact (hsc q.1.1 (q.1.2.resolve_left hk)).choose_spec q.2

end GlobalTheory.CompanionTheory.Ar.PB.FA.StepMap
end
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA

private theorem grading_map_coeff_eq_monomial {K σ : Type} (s : σ → K)
    (φ : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial K (MvPolynomial σ ℤ))
    (hφ : ∀ q, φ (MvPolynomial.X q) = MvPolynomial.C (MvPolynomial.X q) * MvPolynomial.X (s q))
    (g : MvPolynomial σ ℤ) : ∀ a : K →₀ ℕ,
    φ ((φ g).coeff a) = MvPolynomial.monomial a ((φ g).coeff a) := by
  classical
  induction g using MvPolynomial.induction_on
  · rename_i r
    intro a
    have h1 : φ (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by
      simpa [MvPolynomial.algebraMap_apply] using φ.commutes r
    rw [h1, MvPolynomial.coeff_C]
    split_ifs with h
    · subst h
      rw [h1, MvPolynomial.C_apply]
    · simp
  · rename_i f1 f2 hf hg
    intro a
    simp only [map_add, MvPolynomial.coeff_add, hf, hg]
  · rename_i f n hf
    intro a
    rw [map_mul φ f (MvPolynomial.X n), hφ, mul_left_comm, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_mul_X']
    split_ifs with h
    · have he : Finsupp.single (s n) 1 ≤ a := by
        rw [Finsupp.single_le_iff]
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp h)
      have hX : (MvPolynomial.X (s n) : MvPolynomial K (MvPolynomial σ ℤ)) =
          MvPolynomial.monomial (Finsupp.single (s n) 1) 1 := rfl
      rw [map_mul, hφ, hf, mul_assoc, hX, MvPolynomial.monomial_mul, MvPolynomial.C_mul_monomial,
        one_mul, add_tsub_cancel_of_le he]
    · simp

private theorem smul_mem_lemma_2 {K : Type} {ι : K → Type} {Φ : Type} [Field Φ]
    (y : (Σ k, ι k) → Φ) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ f ∈ mCoordIdeal y, MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0)
    (c : K → ℂ) (f : MRing ι) (hf : f ∈ mCoordIdeal y) :
    MvPolynomial.eval (fun r : (Σ k, ι k) => c r.1 * z r) (MvPolynomial.map (Int.castRingHom ℂ) f) = 0 := by
  classical
  let φ : MvPolynomial ((k : K) × ι k) ℤ →ₐ[ℤ] MvPolynomial K (MvPolynomial ((k : K) × ι k) ℤ) :=
    MvPolynomial.aeval (fun q => MvPolynomial.C (MvPolynomial.X q) * MvPolynomial.X q.1)
  have hφ : ∀ q, φ (MvPolynomial.X q) = MvPolynomial.C (MvPolynomial.X q) * MvPolynomial.X q.1 :=
    fun q => MvPolynomial.aeval_X _ _
  have hA : ∀ g, mConeMap y g =
      MvPolynomial.map (MvPolynomial.aeval (R := ℤ) y).toRingHom (φ g) := by
    intro g
    have key : (mConeMap y : MvPolynomial _ ℤ →ₐ[ℤ] MvPolynomial K Φ) =
        ((MvPolynomial.map (MvPolynomial.aeval (R := ℤ) y).toRingHom).toIntAlgHom).comp φ := by
      apply MvPolynomial.algHom_ext
      intro q
      show mConeMap y (MvPolynomial.X q) =
        MvPolynomial.map (MvPolynomial.aeval (R := ℤ) y).toRingHom (φ (MvPolynomial.X q))
      rw [hφ]
      simp [mConeMap]
    rw [key]
    rfl
  have hf' : mConeMap y f = 0 := RingHom.mem_ker.mp hf
  have hcomp : ∀ a, (φ f).coeff a ∈ mCoordIdeal y := by
    intro a
    have h1 : (MvPolynomial.aeval (R := ℤ) y).toRingHom ((φ f).coeff a) = 0 := by
      have := congrArg (MvPolynomial.coeff a) (hA f)
      rw [hf', MvPolynomial.coeff_zero, MvPolynomial.coeff_map] at this
      exact this.symm
    show (φ f).coeff a ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker, hA, grading_map_coeff_eq_monomial Sigma.fst φ hφ f a, MvPolynomial.map_monomial, h1,
      map_zero]
  have hB : MvPolynomial.eval (fun r : (Σ k, ι k) => c r.1 * z r) (MvPolynomial.map (Int.castRingHom ℂ) f) =
      MvPolynomial.eval c (MvPolynomial.map (MvPolynomial.aeval (R := ℤ) z).toRingHom (φ f)) := by
    rw [MvPolynomial.eval_map, ← algebraMap_int_eq, ← MvPolynomial.aeval_def]
    have key : (MvPolynomial.aeval (R := ℤ) (fun r : (Σ k, ι k) => c r.1 * z r)) =
        ((MvPolynomial.eval c).toIntAlgHom).comp
          (((MvPolynomial.map (MvPolynomial.aeval (R := ℤ) z).toRingHom).toIntAlgHom).comp φ) := by
      apply MvPolynomial.algHom_ext
      intro q
      show MvPolynomial.aeval (R := ℤ) (fun r : (Σ k, ι k) => c r.1 * z r) (MvPolynomial.X q) =
        MvPolynomial.eval c (MvPolynomial.map (MvPolynomial.aeval (R := ℤ) z).toRingHom (φ (MvPolynomial.X q)))
      rw [hφ]
      simp [mul_comm]
    rw [key]
    rfl
  rw [hB]
  have hzero : MvPolynomial.map (MvPolynomial.aeval (R := ℤ) z).toRingHom (φ f) = 0 := by
    ext a
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
    have := hz _ (hcomp a)
    rwa [MvPolynomial.eval_map, ← algebraMap_int_eq, ← MvPolynomial.aeval_def] at this
  rw [hzero, map_zero]

theorem weight_descends_of_sameOrbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (p : Ψ × Fin N) (e e' : ℕ)
    (R : AnLogRes (mCoordIdeal y) ⊤ e) (Rp : AnLogRes (mCoordIdeal (y ∘ stepV M p)) ⊤ e') (h : R.X → Rp.X)
    (A B : HermLine ι) (ph : Rp.X → ℝ) (W : Set Rp.X), A.a = B.a →
    (∀ x, SameOrbit (Rp.lift (h x) (h x)) (R.lift x x ∘ stepV M p)) →
    (∀ x ∈ W, ∀ z ∈ mcPts (mCoordIdeal y), z ∘ stepV M p = Rp.lift x x →
      Real.log (A.h z) = Real.log (B.h z) + ph x) →
    ∀ x, h x ∈ W → Real.log (A.h (R.lift x x)) = Real.log (B.h (R.lift x x)) + ph (h x) := by
  intro K _ ι _ Φ _ y Ψ N j M p e e' R Rp h A B ph W hab horb hW x hx
  classical
  obtain ⟨c, hc0, hceq⟩ := horb x
  have hwmem : R.lift x x ∈ mcPts (mCoordIdeal y) := R.mem x x (R.mem_U x)
  let c' : K → ℂ := fun k =>
    if hk : ((∀ p' : Ψ × Fin N, M.blk p' ≠ Option.some k) ∨ M.blk p = Option.some k) then c ⟨k, hk⟩ else 1
  have hc'0 : ∀ k, c' k ≠ 0 := by
    intro k
    by_cases hk : ((∀ p' : Ψ × Fin N, M.blk p' ≠ Option.some k) ∨ M.blk p = Option.some k)
    · simp only [c', dif_pos hk]
      exact hc0 _
    · simp only [c', dif_neg hk]
      exact one_ne_zero
  let z : (Σ k, ι k) → ℂ := fun r => c' r.1 * R.lift x x r
  have hzstep : z ∘ stepV M p = Rp.lift (h x) (h x) := by
    rw [hceq]
    funext q
    have hq : (∀ p' : Ψ × Fin N, M.blk p' ≠ Option.some q.1.1) ∨ M.blk p = Option.some q.1.1 := q.1.2
    show c' q.1.1 * R.lift x x ⟨q.1.1, q.2⟩ = c q.1 * R.lift x x ⟨q.1.1, q.2⟩
    congr 1
    simp only [c', dif_pos hq]
  have hzmem : z ∈ mcPts (mCoordIdeal y) := by
    refine ⟨fun k => ?_, fun f hf => ?_⟩
    · obtain ⟨i, hi⟩ := hwmem.1 k
      exact ⟨i, mul_ne_zero (hc'0 k) hi⟩
    · exact smul_mem_lemma_2 y (R.lift x x) hwmem.2 c' f hf
  have key := hW (h x) hx z hzmem hzstep
  have hAz : A.h z = (∏ k, ‖c' k‖ ^ A.a k) * A.h (R.lift x x) := A.smul c' _ hc'0
  have hBz : B.h z = (∏ k, ‖c' k‖ ^ A.a k) * B.h (R.lift x x) := by
    rw [hab]
    exact B.smul c' _ hc'0
  have hP : (∏ k, ‖c' k‖ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc'0 k)))
  have hApos := A.pos _ hwmem.1
  have hBpos := B.pos _ hwmem.1
  rw [hAz, hBz, Real.log_mul hP hApos.ne', Real.log_mul hP hBpos.ne'] at key
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.FA
end
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.FA.StepLine

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

theorem pullDeg_zero {K K' : Type} (κ : K → K') : pullDeg κ (0 : K → ℤ) = 0 := by
  funext k
  by_cases h : ∃ a, κ a = k
  · simp [pullDeg, Function.extend_def, h]
  · simp [pullDeg, Function.extend_def, h]

theorem isSmoothHerm_pullHerm {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
    [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : IsBlockMap κ v) {B : HermLine ι} (hB : IsSmoothHerm B) : IsSmoothHerm (pullHerm hv B) := by
  have hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k', ι' k') → ℂ => fun q => z (v q)) :=
    contDiff_pi.2 fun q => contDiff_apply ℝ ℂ (v q)
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B.h ∘ fun z : (Σ k', ι' k') → ℂ => fun q => z (v q))
    {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  refine ContDiffOn.comp hB hlin.contDiffOn ?_
  intro z hz k
  obtain ⟨i', hi'⟩ := hz (κ k)
  obtain ⟨q, hq⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : q.1 = k := hv.1 (by rw [← hv.2.2.1 q, hq])
  obtain ⟨k₀, m⟩ := q
  simp only at h2
  subst h2
  exact ⟨m, by simpa [hq] using hi'⟩

theorem exists_stepLine : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (p : Ψ × Fin N)
    (B : HermLine (stepIdx M p)), B.a = 0 → ∃ A : HermLine ι, A.a = M.dy p ∧ M.OnStep p A ∧
      (IsSmoothHerm B → IsSmoothHerm A) ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
        Real.log (A.h z) = Real.log ((fsHerm ι (M.dy p)).h z) + Real.log (B.h (z ∘ stepV M p)) := by
  intro K _ ι _ Φ _ y Ψ N j M p B hB
  have hdy : ∀ k, M.dy p k ≠ 0 → k ∈ Set.range (Subtype.val : PartialFlagBlocks M p → K) := by
    intro k hk
    by_cases h : ∀ p', M.blk p' ≠ some k
    · exact ⟨⟨k, Or.inl h⟩, rfl⟩
    · by_cases h' : M.blk p = some k
      · exact ⟨⟨k, Or.inr h'⟩, rfl⟩
      · exact absurd (show M.dy p k = 0 by unfold FlagModel.dy; rw [dif_neg h, if_neg h']) hk
  refine ⟨(fsHerm ι (M.dy p)).tensor (pullHerm (isBlockMap_stepV M p) B), ?_, ?_, ?_, ?_⟩
  · show M.dy p + pullDeg _ B.a = M.dy p
    rw [hB, pullDeg_zero, add_zero]
  · intro z z' hb hs
    have hc : z ∘ stepV M p = z' ∘ stepV M p := by
      funext ⟨⟨k, hk⟩, m⟩
      rcases hk with h | h
      · exact congrFun hb ⟨⟨k, h⟩, m⟩
      · exact hs k h m
    show (fsHerm ι (M.dy p)).h z * B.h (z ∘ stepV M p) = (fsHerm ι (M.dy p)).h z' * B.h (z' ∘ stepV M p)
    rw [StepW.fsHerm_h_blockMap K ι (PartialFlagBlocks M p) (stepIdx M p) Subtype.val (stepV M p) (M.dy p) z
        (isBlockMap_stepV M p) hdy,
      StepW.fsHerm_h_blockMap K ι (PartialFlagBlocks M p) (stepIdx M p) Subtype.val (stepV M p) (M.dy p) z'
        (isBlockMap_stepV M p) hdy, hc]
  · intro hS
    exact isSmoothHerm_tensor (FlagHeightMultilinear.isSmoothHerm_fsHerm _)
      (isSmoothHerm_pullHerm (isBlockMap_stepV M p) hS)
  · intro z hz
    have h1 := (fsHerm ι (M.dy p)).pos z hz
    have h2 := (pullHerm (isBlockMap_stepV M p) B).pos z hz
    exact Real.log_mul h1.ne' h2.ne'

end GlobalTheory.CompanionTheory.Ar.PB.FA.StepLine
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

theorem central_regular {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {nb : ℕ} (m : Fin nb → ℕ) (W : Fin nb → Set X)
    (hL : IsPotential A L) (hs : IsSection A L s) (snc : IsSNC A L s m W) (hn : ∀ y, logNormSec L s y ≤ 0)
    (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ) (th : LocPot X) (u : X → ℝ) (C₅ : ℝ)
    (hsw : IsSingWeight A L s th u C₅) (hneg : IsPshOn A (bdry s)ᶜ ((th + LocPot.ofFun u).rsmul (-1))) :
    ∃ (u' : X → ℝ) (C₀ : ℝ), A.Smooth u' ∧ (∀ y ∉ bdry s, u' y = u y) ∧ IsPsh A (th + LocPot.ofFun u') ∧
      IsPsh A ((th + LocPot.ofFun u').rsmul (-1)) ∧ IsSingWeight A L s th u' C₀ ∧
      IsRegFamily A Θ L s th u' (fun _ => u') C₀ (Real.exp (-Real.exp 1)) ∧
      IsRegFamilyC2 A s u' fun _ => u' := by
  obtain ⟨hth, hsm, hpsh, hb⟩ := hsw
  have hlog : ∀ y, 1 ≤ Real.log (rW L s y) := fun y => by
    have h1 : Real.exp 1 ≤ rW L s y := by
      have := hn y
      unfold rW
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) h1
  have hbd : ∀ y ∉ bdry s, |u y| ≤ |C₅| * Real.log (rW L s y) := fun y hy => by
    obtain ⟨h1, h2⟩ := hb y hy
    have h3 := hlog y
    have h4 : C₅ ≤ |C₅| := le_abs_self _
    have h5 : -|C₅| ≤ C₅ := neg_abs_le _
    have h6 : 0 ≤ |C₅| := abs_nonneg _
    rw [abs_le]
    constructor <;> nlinarith
  obtain ⟨u', hu', heq, hp1, hp2⟩ := GlobalTheory.CompanionTheory.Ar.PB.Flat.flat_weight_extends e X A L s nb m W hL hs snc hn th u |C₅| hth hsm hpsh hneg hbd
  obtain ⟨C₀, h1, h2, h3⟩ := (GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members e X A Θ L s nb m W hL hs snc hn hΘ hΘp).2.2 th u' hth hu' hp1
  exact ⟨u', C₀, hu', heq, hp1, hp2, h1, h2, h3⟩

theorem deg0_orbit {κ : Type} [Fintype κ] {ρ : κ → Type} [∀ k, Fintype (ρ k)] (B : HermLine ρ) (hB : B.a = 0)
    {z z' : (Σ k, ρ k) → ℂ} (h : SameOrbit z z') : B.h z = B.h z' := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [B.smul c z' hc, hB]
  simp

theorem dy_eq_zero (M : FlagModel y Ψ N j) (p : Ψ × Fin N) (k : K)
    (hk : k ∉ Set.range (Subtype.val : PartialFlagBlocks M p → K)) : M.dy p k = 0 := by
  have h1 : ¬ ∀ p', M.blk p' ≠ some k := fun h => hk ⟨⟨k, Or.inl h⟩, rfl⟩
  have h2 : M.blk p ≠ some k := fun h => hk ⟨⟨k, Or.inr h⟩, rfl⟩
  unfold FlagModel.dy
  rw [dif_neg h1, if_neg h2]

theorem step_member (hR : RegGlobalStatement) (hP : PullbackStatement) [Fintype Ψ] [DecidableEq Ψ]
    (M : FlagModel y Ψ N j) {n e : ℕ} (BM : BaseMetric M n) (R : AnLogRes (mCoordIdeal y) ⊤ e)
    (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr)
    (hdim : e = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2))
    (hb : ∀ x, SameOrbit (basePart M.blk (R.lift x x)) (BM.Rb.lift (pr x) (pr x)))
    (pL : IsPotential R.A (BM.L.pullback pr hp.1))
    (sL : IsSection R.A (BM.L.pullback pr hp.1) fun x y => BM.s (pr x) (pr y))
    (nL : IsSNC R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.m fun k => pr ⁻¹' BM.W k)
    (p : Ψ × Fin N) :
    ∃ (ph : R.X → ℝ) (phT : ℝ → R.X → ℝ) (line : ℝ → HermLine ι) (C₅ C t₀ : ℝ),
      IsStepMember BM R pr hp p ph phT line C₅ C t₀ := by
  have hv := isBlockMap_stepV M p
  obtain ⟨e', Rp, -, prp, hq, hpts, hch⟩ := GlobalTheory.T.flag_bundle_partial_block_map K ι Φ y Ψ N j M n e BM.Rb hdim (· = p) (PartialFlagBlocks M p)
    (stepIdx M p) Subtype.val (stepV M p) hv (mem_range_step M p)
  obtain ⟨pL', sL', nL', B, hB⟩ := GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection e' n Rp.X BM.Rb.X Rp.A BM.Rb.A BM.Bat prp hq BM.L BM.s BM.nb BM.m
    BM.W BM.potL BM.sec BM.snc BM.norm_le hch
  have hkeep : ∀ k, ((∀ p', M.blk p' ≠ some k) ∨ M.blk p = some k) →
      k ∈ Set.range (Subtype.val : PartialFlagBlocks M p → K) := fun k hk => ⟨⟨k, hk⟩, rfl⟩
  obtain ⟨ph', C₅, hw1, -, hsw, hgb⟩ := GlobalTheory.T.partial_flag_bundle_metric_line K ι Φ y Ψ N j M n e BM p (PartialFlagBlocks M p) (stepIdx M p)
    Subtype.val (stepV M p) hv hkeep e' Rp prp hq B hpts pL' sL' nL' hB
  have hn' : ∀ x, logNormSec (BM.L.pullback prp hq.1) (fun x y => BM.s (prp x) (prp y)) x ≤ 0 :=
    fun x => BM.norm_le (prp x)
  have hn : ∀ x, logNormSec (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x ≤ 0 :=
    fun x => BM.norm_le (pr x)
  obtain ⟨hA', hfs', hΘ'⟩ := GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential (PartialFlagBlocks M p) (stepIdx M p) _ e' Rp
  obtain ⟨hA, hfs, hΘ⟩ := GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential K ι _ e R
  obtain ⟨h, hh, hso⟩ := GlobalTheory.CompanionTheory.Ar.PB.Proj.holoMap_of_blockProj (PartialFlagBlocks M p) (stepIdx M p) K ι Subtype.val (stepV M p) _ _ ⊤ e' e Rp R hv
    (GlobalTheory.CompanionTheory.Ar.PB.FA.ImageIdeal.mCoordIdeal_comp_le_imageZ K ι (PartialFlagBlocks M p) (stepIdx M p) Subtype.val (stepV M p) Φ y hv)
  obtain ⟨hfac, hinj⟩ := GlobalTheory.CompanionTheory.Ar.PB.FA.StepMap.factor K ι Φ y Ψ N j M p n e e' BM.Rb R Rp pr prp h hb hpts hso
  have hreg : ∃ (ph₂ : Rp.X → ℝ) (phT₂ : ℝ → Rp.X → ℝ) (C₅₂ C t₀ : ℝ),
      IsSingWeight Rp.A (BM.L.pullback prp hq.1) (fun x y => BM.s (prp x) (prp y))
        (potOf Rp (fsHerm (stepIdx M p) fun k => M.dy p k.1)) ph₂ C₅₂ ∧
      IsRegFamily Rp.A (potOf Rp (fsHerm (stepIdx M p) fun _ => 1)) (BM.L.pullback prp hq.1)
        (fun x y => BM.s (prp x) (prp y)) (potOf Rp (fsHerm (stepIdx M p) fun k => M.dy p k.1)) ph₂ phT₂ C t₀ ∧
      IsRegFamilyC2 Rp.A (fun x y => BM.s (prp x) (prp y)) ph₂ phT₂ ∧
      (∀ x, prp x ∉ bdry BM.s → ph₂ x = ph' x) ∧
      ((p.2 : ℕ) + 1 = N → Rp.A.Smooth ph₂ ∧ (∀ t, phT₂ t = ph₂) ∧
        IsPsh Rp.A (potOf Rp (fsHerm (stepIdx M p) (fun k => M.dy p k.1)) + LocPot.ofFun ph₂) ∧
        IsPsh Rp.A ((potOf Rp (fsHerm (stepIdx M p) (fun k => M.dy p k.1)) + LocPot.ofFun ph₂).rsmul (-1))) := by
    by_cases hc : (p.2 : ℕ) + 1 = N
    · have flat := GlobalTheory.CompanionTheory.Ar.PB.FA.Flat.flat_off_boundary K ι Φ y Ψ N j M n BM p hc (PartialFlagBlocks M p) (stepIdx M p) Subtype.val (stepV M p) hv
        (fun k hk => hkeep k (Or.inl hk)) e' Rp prp hq ph' hpts hw1
      obtain ⟨u', C₀, hu', heq, p1, p2, s1, r1, c1⟩ := central_regular Rp.A
        (potOf Rp (fsHerm (stepIdx M p) fun _ => 1)) _ _ BM.m _ pL' sL' nL' hn' (hA' _ hfs') hΘ' _ ph' C₅ hsw flat.2
      exact ⟨u', fun _ => u', C₀, C₀, _, s1, r1, c1, heq, fun _ => ⟨hu', fun _ => rfl, p1, p2⟩⟩
    · obtain ⟨C, t₀, phT, r, c⟩ := hR Rp.A B (potOf Rp (fsHerm (stepIdx M p) fun _ => 1)) _ _ BM.m _ (hA' _ hfs') hΘ'
        pL' sL' nL' hn' hB _ ph' C₅ hsw hgb
      exact ⟨ph', phT, C₅, C, t₀, hsw, r, c, fun _ _ => rfl, fun h => absurd h hc⟩
  obtain ⟨ph₂, phT₂, C₅₂, C, t₀, s2, r2, c2, heq, hcen⟩ := hreg
  have hw := GlobalTheory.CompanionTheory.Ar.PB.FA.weight_descends_of_sameOrbit K ι Φ y Ψ N j M p e e' R Rp h (BM.hom p) (fsHerm ι (M.dy p)) ph'
    {x | prp x ∉ bdry BM.s} (BM.hom_deg p) hso hw1
  obtain rfl : pr = prp ∘ h := funext fun x => (hfac x).symm
  obtain ⟨C', t₀', h1, h2, h3⟩ := hP Rp.A R.A h hh (potOf Rp (fsHerm (stepIdx M p) fun _ => 1)) _
    (potOf R (fsHerm ι fun _ => 1)) _ BM.m _ BM.m _ (hA' _ hfs') hΘ' (hA _ hfs) hΘ pL' sL' nL' hn' nL _ ph₂ phT₂ C₅₂ C t₀
    s2 r2 c2
  have hfsd : IsPotential R.A (potOf R (fsHerm ι (M.dy p))) := hA _ (GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.isSmoothHerm_fsHerm _)
  have hsp := GlobalTheory.CompanionTheory.Ar.PB.FA.BlockPot.samePot_block K ι (PartialFlagBlocks M p) (stepIdx M p) Subtype.val (stepV M p) _ _ _ _ e e' R Rp h hh (M.dy p) hv
    (dy_eq_zero M p) hso
  have tr := GlobalTheory.CompanionTheory.Ar.PB.Transport.singWeight_regFamily_transport e R.X R.A (potOf R (fsHerm ι fun _ => 1)) _ _ _ _ (ph₂ ∘ h) (fun t => phT₂ t ∘ h) C₅₂ C'
    t₀' (hA _ hfs) sL hfsd h1.1 hsp
  obtain ⟨T, hT⟩ : ∃ T, T = min (min t₀ t₀') (Real.exp (-1)) := ⟨_, rfl⟩
  have hT0 : 0 < T := by
    rw [hT]
    exact lt_min (lt_min r2.1 h2.1) (Real.exp_pos _)
  have hT1 : T ≤ t₀ := by rw [hT]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hT2 : T ≤ t₀' := by rw [hT]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hT3 : T ≤ Real.exp (-1) := by rw [hT]; exact min_le_right _ _
  have reg' := (GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members e R.X R.A _ _ _ BM.nb BM.m _ pL sL nL hn (hA _ hfs) hΘ).2.1 _ _ _ _ _ |C'| T le_rfl hT0 hT2
    hT3 (tr.2 h2) hfsd
  have hB2 : ∀ t, ∃ Bt : HermLine (stepIdx M p), Bt.a = 0 ∧ (0 < t → t ≤ T → IsSmoothHerm Bt ∧
      ∀ x, Real.log (Bt.h (Rp.lift x x)) = phT₂ t x) := by
    intro t
    by_cases ht : 0 < t ∧ t ≤ T
    · obtain ⟨Bt, a0, hs, hl⟩ := GlobalTheory.CompanionTheory.Ar.PB.exists_hermLine_log_eq_of_smooth _ _ _ e' Rp (phT₂ t) (r2.2.2 t ht.1 (ht.2.trans hT1)).1
      exact ⟨Bt, a0, fun _ _ => ⟨hs, hl⟩⟩
    · exact ⟨fsHerm _ 0, rfl, fun h1 h2 => absurd ⟨h1, h2⟩ ht⟩
  choose Bf hBa hBs using hB2
  choose line hla hlon hls hll using fun t => GlobalTheory.CompanionTheory.Ar.PB.FA.StepLine.exists_stepLine K ι Φ y Ψ N j M p (Bf t) (hBa t)
  refine ⟨ph₂ ∘ h, fun t => phT₂ t ∘ h, line, C₅₂, |C'|, T, tr.1 h1, reg', h3, hla, hlon, ?_, ?_, ?_, ?_⟩
  · intro t h0 ht
    obtain ⟨hs, hl⟩ := hBs t h0 ht
    refine ⟨hls t hs, fun x => ?_⟩
    rw [hll t _ (R.mem x x (R.mem_U x)).1, ← deg0_orbit (Bf t) (hBa t) (hso x), hl]
    rfl
  · intro x hx
    rw [hw x hx]
    simp only [Function.comp]
    rw [heq _ hx]
  · intro x x' hx hk
    have e1 := hinj x x' hx hk
    exact ⟨by simp only [Function.comp, e1], fun t => by simp only [Function.comp, e1]⟩
  · intro hc t
    obtain ⟨hsm, hc1, p1, p2⟩ := hcen hc
    have hpp := GlobalTheory.CompanionTheory.Ar.PB.PshPull.isPsh_pull e e' R.X Rp.X R.A Rp.A h hh _ _ ph₂ hfsd (hA' _ (GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.isSmoothHerm_fsHerm _)) hsm hsp
    refine ⟨?_, ?_, ?_⟩
    · show IsPsh R.A ((_ + LocPot.ofFun (phT₂ t ∘ h)).rsmul (-1))
      rw [hc1 t]
      exact hpp.2 p2
    · show IsPsh R.A (_ + LocPot.ofFun (phT₂ t ∘ h))
      rw [hc1 t]
      exact hpp.1 p1
    · show phT₂ t ∘ h = _
      rw [hc1 t]

open scoped ContDiff

theorem degree_id_self {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) : IsDegreeOff A A id 1 ∅ := by
  have hA : A.IsAnalyticSubset ∅ := fun x =>
    ⟨Set.univ, isOpen_univ, trivial, 1, fun _ _ => 1, fun _ _ _ _ => analyticAt_const, by ext; simp⟩
  refine ⟨hA, interior_empty, hA, interior_empty, fun x _ => by simp, fun j k y hy _ hk => ?_⟩
  set E := (A.chart j).symm.trans (A.chart k) with he
  have hs : y ∈ E.source := ⟨hy, hk⟩
  have hf : DifferentiableAt ℂ (A.chart k ∘ (A.chart j).symm) y := (A.holo j k y ⟨hy, hk⟩).differentiableAt
  have ht := E.map_source hs
  have hg : DifferentiableAt ℂ (A.chart j ∘ (A.chart k).symm) ((A.chart k ∘ (A.chart j).symm) y) :=
    (A.holo k j _ ⟨ht.1, ht.2⟩).differentiableAt
  have hc := fderiv_comp y hg hf
  have hid : (A.chart j ∘ (A.chart k).symm) ∘ (A.chart k ∘ (A.chart j).symm) =ᶠ[𝓝 y] id := by
    filter_upwards [E.open_source.mem_nhds hs] with w hw
    exact E.left_inv hw
  rw [hid.fderiv_eq, fderiv_id] at hc
  intro h0
  have := congrArg (fun L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) => LinearMap.det (L : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) hc
  simp only [ContinuousLinearMap.coe_id, LinearMap.det_id] at this
  erw [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp] at this
  have h0' : LinearMap.det (fderiv ℂ (A.chart k ∘ (A.chart j).symm) y : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0 := h0
  rw [h0', mul_zero] at this
  exact one_ne_zero this

theorem common_bound {σ : Type} [Finite σ] (f : σ → ℝ) : ∃ M : ℝ, ∀ a, f a ≤ M := by
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  exact ⟨M, fun a => hM ⟨a, rfl⟩⟩

theorem common_scale {σ : Type} [Finite σ] (f : σ → ℝ) (hf : ∀ a, 0 < f a) : ∃ t : ℝ, 0 < t ∧ ∀ a, t ≤ f a := by
  obtain ⟨M, hM⟩ := common_bound fun a => (f a)⁻¹
  by_cases he : Nonempty σ
  · obtain ⟨a₀⟩ := he
    have hM0 : 0 < M := lt_of_lt_of_le (inv_pos.2 (hf a₀)) (hM a₀)
    refine ⟨M⁻¹, inv_pos.2 hM0, fun a => ?_⟩
    exact inv_le_of_inv_le₀ (hf a) (hM a)
  · exact ⟨1, one_pos, fun a => absurd ⟨a⟩ he⟩

theorem IsStepMember.mono {M : FlagModel y Ψ N j} {n e : ℕ} {BM : BaseMetric M n}
    {R : AnLogRes (mCoordIdeal y) ⊤ e} {pr : R.X → BM.Rb.X} {hp : HoloMap R.A BM.Rb.A pr} {p : Ψ × Fin N}
    {ph : R.X → ℝ} {phT : ℝ → R.X → ℝ} {line : ℝ → HermLine ι} {C₅ C t₀ D₅ D T : ℝ}
    (m₁ : ∀ th ph C₅ C₅', C₅ ≤ C₅' → IsSingWeight R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) th ph C₅ →
      IsSingWeight R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) th ph C₅')
    (m₂ : ∀ th ph phT C t₀ C' t₀', |C| ≤ C' → 0 < t₀' → t₀' ≤ t₀ → t₀' ≤ Real.exp (-1) →
      IsRegFamily R.A (potOf R (fsHerm ι fun _ => 1)) (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) th ph phT C t₀ →
      IsPotential R.A th →
      IsRegFamily R.A (potOf R (fsHerm ι fun _ => 1)) (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) th ph phT C' t₀')
    (h : IsStepMember BM R pr hp p ph phT line C₅ C t₀) (h₅ : C₅ ≤ D₅) (hD : |C| ≤ D) (hT0 : 0 < T) (hT : T ≤ t₀)
    (hT1 : T ≤ Real.exp (-1)) : IsStepMember BM R pr hp p ph phT line D₅ D T := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  exact ⟨m₁ _ _ _ _ h₅ a1, m₂ _ _ _ _ _ _ _ hD hT0 hT hT1 a2 a1.1, a3, a4, a5, fun t h0 h1 => a6 t h0 (h1.trans hT), a7⟩

theorem flagAn_of_res (hR : RegGlobalStatement) (hP : PullbackStatement) [Fintype Ψ] [DecidableEq Ψ]
    (M : FlagModel y Ψ N j) {n : ℕ} (d : ℕ) (BM : BaseMetric M n) (R : AnLogRes (mCoordIdeal y) ⊤ (d + 1))
    (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr) (harith : IsArithVar (mCoordIdeal y) (d + 2))
    (hdim : d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2))
    (hb : ∀ x, SameOrbit (basePart M.blk (R.lift x x)) (BM.Rb.lift (pr x) (pr x)))
    (hch : ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin (d + 1) → ℂ)) (kb : Fin BM.Rb.A.n) (σ : Fin n ↪ Fin (d + 1)),
      IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (BM.Rb.A.chart kb).source ∧
        ∀ i, BM.Rb.A.chart kb (pr x') i = ψ x' (σ i))) :
    Nonempty (FlagAn BM d) := by
  obtain ⟨pL, sL, nL, B, hB⟩ := GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection (d + 1) n R.X BM.Rb.X R.A BM.Rb.A BM.Bat pr hp BM.L BM.s BM.nb BM.m BM.W
    BM.potL BM.sec BM.snc BM.norm_le hch
  have hn : ∀ x, logNormSec (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x ≤ 0 :=
    fun x => BM.norm_le (pr x)
  obtain ⟨hA, hfs, hΘ⟩ := GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential K ι _ (d + 1) R
  have hfsa : ∀ a : K → ℤ, IsSmoothHerm (fsHerm ι a) := GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.isSmoothHerm_fsHerm
  choose ph phT line C₅ C t₀ hm using fun p => step_member hR hP M BM R pr hp hdim hb pL sL nL p
  obtain ⟨m₁, m₂, m₃⟩ := GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members (d + 1) R.X R.A (potOf R (fsHerm ι fun _ => 1)) _ _ BM.nb BM.m _ pL sL nL hn
    (hA _ hfs) hΘ
  have hsm0 : R.A.Smooth (0 : R.X → ℝ) := fun jj => by
    show ContDiffOn ℝ ∞ (fun _ => (0 : ℝ)) _
    exact contDiffOn_const
  have hpsh0 : IsPsh R.A (potOf R (fsHerm ι fun _ => 1) + LocPot.ofFun (0 : R.X → ℝ)) := by
    intro x jj z hz w
    have e1 : (potOf R (fsHerm ι fun _ => 1) + LocPot.ofFun (0 : R.X → ℝ)).φ x ∘ (R.A.chart jj).symm =
        (potOf R (fsHerm ι fun _ => 1)).φ x ∘ (R.A.chart jj).symm := by
      funext u
      show (potOf R (fsHerm ι fun _ => 1)).φ x _ + (0 : ℝ) = _
      rw [add_zero]
      rfl
    rw [e1]
    by_cases hw : w = 0
    · rw [hw, levi_zero]
    · exact (hΘ x jj z ⟨hz.1, hz.2.1⟩ w hw).le
  obtain ⟨C₀, s0, r0, c0⟩ := m₃ _ 0 (hA _ hfs) hsm0 hpsh0
  obtain ⟨D₅, hD₅⟩ := common_bound fun o : Option (Ψ × Fin N) => o.elim C₀ C₅
  obtain ⟨D, hD⟩ := common_bound fun o : Option (Ψ × Fin N) => o.elim |C₀| fun p => |C p|
  obtain ⟨T, hT0, hT⟩ := common_scale (fun o : Option (Option (Ψ × Fin N)) =>
    o.elim (Real.exp (-1)) fun o' => o'.elim (Real.exp (-Real.exp 1)) t₀) (by
      rintro (_ | _ | p)
      · exact Real.exp_pos _
      · exact Real.exp_pos _
      · exact (hm p).2.1.1)
  have hT1 : T ≤ Real.exp (-1) := hT none
  have hm' : ∀ p, IsStepMember BM R pr hp p (ph p) (phT p) (line p) D₅ D T := fun p =>
    IsStepMember.mono m₁ m₂ (hm p) (hD₅ (some p)) (hD (some p)) hT0 (hT (some (some p))) hT1
  have s0' := m₁ _ _ _ _ (hD₅ none) s0
  have r0' := m₂ _ _ _ _ _ _ _ (hD none) hT0 (hT (some none)) hT1 r0 (hA _ hfs)
  let S : AnSys (d + 1) (Option (Ψ × Fin N)) :=
    { X := R.X
      A := R.A
      Θ := potOf R (fsHerm ι fun _ => 1)
      L := BM.L.pullback pr hp.1
      s := fun x y => BM.s (pr x) (pr y)
      nb := BM.nb
      m := BM.m
      W := fun k => pr ⁻¹' BM.W k
      potΘ := hA _ hfs
      posΘ := hΘ
      potL := pL
      sec := sL
      snc := nL
      norm_le := hn
      th := fun o => o.elim (potOf R (fsHerm ι fun _ => 1)) fun p => potOf R (fsHerm ι (M.dy p))
      ph := fun o => o.elim 0 ph
      phT := fun o => o.elim (fun _ => 0) phT
      C₅ := D₅
      C := D
      t₀ := T
      sing := by
        rintro (_ | p)
        · exact s0'
        · exact (hm' p).1
      reg := by
        rintro (_ | p)
        · exact r0'
        · exact (hm' p).2.1
      c2 := by
        rintro (_ | p)
        · exact c0
        · exact (hm' p).2.2.1 }
  let Re : Realis S (mCoordIdeal y) :=
    { arith := harith
      J := ⊤
      R := R
      π := id
      holo := ⟨continuous_id, fun jj k => R.A.holo jj k⟩
      deg := 1
      deg_pos := one_pos
      br := ∅
      degree := degree_id_self R.A
      ref := fun o => o.elim (fsHerm ι fun _ => 1) fun p => fsHerm ι (M.dy p)
      ref_smooth := by
        rintro (_ | p)
        · exact hfs
        · exact hfsa _
      ref_pot := by
        rintro (_ | p) <;>
        exact fun x _ => ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ => analyticOnNhd_const,
          fun z _ => (sub_self _).trans Complex.zero_re.symm⟩
      line := fun o t => o.elim (fsHerm ι fun _ => 1) fun p => line p t
      line_deg := by
        rintro (_ | p) t
        · rfl
        · exact (hm' p).2.2.2.1 t
      line_smooth := by
        rintro (_ | p) t h0 h1
        · exact hfs
        · exact ((hm' p).2.2.2.2.2.1 t h0 h1).1
      line_eq := by
        rintro (_ | p) t h0 h1 x
        · show _ = _ + (0 : ℝ)
          rw [add_zero]
          rfl
        · exact ((hm' p).2.2.2.2.2.1 t h0 h1).2 x }
  refine ⟨{ S := S, Re := Re, J_top := rfl, deg_one := rfl, br_empty := rfl, ref_some := fun _ => rfl, ref_none := rfl,
            line_none := fun _ => rfl, ph_none := ⟨rfl, fun _ => rfl⟩, pos_none := ?_, pr := pr, pr_holo := hp,
            pr_eq := hb, L_eq := rfl, s_eq := rfl, hom_eq := ?_, step := ?_, step_ph := ?_, flat := ?_ }⟩
  · refine ⟨1, one_pos, fun t x jj z _ w => ?_⟩
    have e1 : (S.potT none t + S.Θ.rsmul (-1)).φ x ∘ (S.A.chart jj).symm = fun _ => (0 : ℝ) := by
      funext u
      show ((potOf R (fsHerm ι fun _ => 1)).φ x _ + (0 : ℝ)) + (-1) * (potOf R (fsHerm ι fun _ => 1)).φ x _ = 0
      ring
    rw [e1]
    simp [levi]
  · exact fun p x hx => (hm' p).2.2.2.2.2.2.1 x hx
  · exact fun p t => (hm' p).2.2.2.2.1 t
  · exact fun p x x' h1 h2 => (hm' p).2.2.2.2.2.2.2.1 x x' h1 h2
  · exact fun p h1 t => (hm' p).2.2.2.2.2.2.2.2 h1 t

theorem flagAn_exists : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n), IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → Nonempty (FlagAn BM d) := by
  intro hI K _ ι _ Φ _ y Ψ _ _ N j M n d BM harith hd
  obtain ⟨e, R, he, pr, hp, hpts, hch⟩ := GlobalTheory.T.flag_bundle_partial_block_map K ι Φ y Ψ N j M n (d + 1) BM.Rb hd (fun _ => True) K ι id id
    isBlockMap_id (fun k => ⟨fun _ => by
      by_cases h : ∀ p', M.blk p' ≠ some k
      · exact Or.inl h
      · push_neg at h
        obtain ⟨p, hp⟩ := h
        exact Or.inr ⟨p, trivial, hp⟩, fun _ => ⟨k, rfl⟩⟩)
  obtain rfl := he fun _ => trivial
  refine flagAn_of_res hI.regGlobal hI.pullback M d BM R pr hp harith hd (fun x => ?_) hch
  obtain ⟨z, -, hz, ho⟩ := hpts x
  have hz' : z = R.lift x x := hz
  rw [← hz']
  exact ho

end GlobalTheory.CompanionTheory.Ar.PB.FA
end
end
