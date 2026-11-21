import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetEigenFramePlurisubharmonic
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlurisubharmonicLocalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeMiddle
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousHermitianMatrixFamilyStatement

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_data_hodge_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (a : Fin Dc.nCharts), ∀ t₀ ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1), ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (L : ActPeriods E (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) a₀ g Λ) (π : Equiv.Perm (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)))) (ρ : ℝ) (σ : CMType H → (𝓞 E →+* ℂ)) (pt : (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → (Sp ℂ ⟶ Or.𝔐.X)) (d : MuFrameAt Hd ((Dc.chart a).γ t₀)) (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (b : CMType H → Fin (Dc.N - Dc.j) → (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → Fin g → ℂ), 0 < ρ ∧ IsCMFam σ ∧ Or.IsSmallPart d s ∧ IsEigFrames (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1) L.B σ b ∧ (∀ u ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1), t₀ + (ρ : ℂ) • (u ∘ π) ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1) ∧ InFrameDomain Dc.y d.c d.f ((Dc.chart a).γ (t₀ + (ρ : ℂ) • (u ∘ π))) ∧ CoordsAt Or.𝔐.ξ Dc.y (pt u) ((Dc.chart a).γ (t₀ + (ρ : ℂ) • (u ∘ π))) ∧ Or.𝔐.LabVal (pt u) Or.sm σ ∧ (Or.𝔐.Interior (pt u) ↔ u ∈ Flat.punct _ a₀ 1)) ∧ (∀ w (hw : w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le), ∃ v : CMType H × Fin (Dc.N - Dc.j) → (epsAt (pt (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) ⟶ Or.𝔐.t.G), (∀ i, Or.𝔐.M.ValAt _ (s i.1 i.2) (v i)) ∧ FibreLatVec Or.𝔐.t _ (L.riem w hw) (fun i => b i.1 i.2 (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.ChartFree.exists_actPeriods_chart | exact GlobalTheory.CompanionTheory.Ar.Cusp.ChartFree.exists_actPeriods_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.ChartFree.exists_actPeriods_chart <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.CuspCorrespondence

open ReciprocityTheory.AnForm.A (IsPsh)
open _root_.Metric

theorem isPsh_half {n : ℕ} {U : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℝ} (h : IsPsh U f) :
    IsPsh U (fun z => f z / 2) := by
  refine ⟨fun z hz y hy => ?_, fun z w hd => ?_⟩
  · have h1 : ∀ᶠ x in 𝓝[U] z, f x < 2 * y := h.1 z hz (2 * y) (by simp only at hy; linarith)
    filter_upwards [h1] with x hx
    linarith
  · obtain ⟨h1, h2⟩ := h.2 z w hd
    have e : Real.circleAverage (fun ζ : ℂ => f (z + ζ • w) / 2) 0 1 =
        Real.circleAverage (fun ζ : ℂ => f (z + ζ • w)) 0 1 / 2 := by
      have := Real.circleAverage_fun_smul (c := 0) (R := 1) (a := (1 / 2 : ℝ)) (f := fun ζ : ℂ => f (z + ζ • w))
      simp only [smul_eq_mul] at this
      rw [show (fun ζ : ℂ => f (z + ζ • w) / 2) = fun ζ : ℂ => 1 / 2 * f (z + ζ • w) by
        funext ζ; ring, this]
      ring
    refine ⟨?_, ?_⟩
    · have : CircleIntegrable ((1 / 2 : ℝ) • fun ζ : ℂ => f (z + ζ • w)) 0 1 := h1.const_smul
      refine (circleIntegrable_congr (fun ζ _ => ?_)).1 this
      simp [div_eq_inv_mul]
    · rw [e]; linarith

def aff {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) : Fin n → ℂ :=
  t₀ + (ρ : ℂ) • (u ∘ π)

def affInv {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) : Fin n → ℂ :=
  ((ρ : ℂ)⁻¹ • (t - t₀)) ∘ π.symm

theorem aff_affInv {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) :
    aff t₀ ρ π (affInv t₀ ρ π t) = t := by
  have h : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  funext i
  simp [aff, affInv, Function.comp, h]

theorem norm_affInv {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) {t : Fin n → ℂ}
    (ht : t ∈ ball t₀ ρ) : affInv t₀ ρ π t ∈ ball 0 1 := by
  rw [mem_ball, dist_eq_norm, sub_eq_add_neg] at ht
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
  intro i
  have h1 : ‖(t - t₀) (π.symm i)‖ < ρ := by
    have : ‖t + -t₀‖ < ρ := ht
    rw [pi_norm_lt_iff hρ] at this
    simpa [sub_eq_add_neg] using this (π.symm i)
  simp only [affInv, Function.comp, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hρ]
  rw [inv_mul_lt_iff₀ hρ]
  simpa using h1

theorem affInv_add {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (z w : Fin n → ℂ) (ζ : ℂ) :
    affInv t₀ ρ π (z + ζ • w) = affInv t₀ ρ π z + ζ • (((ρ : ℂ)⁻¹ • w) ∘ π.symm) := by
  funext i
  simp [affInv, Function.comp]
  ring

theorem isPsh_comp_affInv {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n))
    {ψ : (Fin n → ℂ) → ℝ} (h : IsPsh (ball 0 1) ψ) : IsPsh (ball t₀ ρ) (fun t => ψ (affInv t₀ ρ π t)) := by
  have hc : Continuous (affInv t₀ ρ π) := by
    unfold affInv
    fun_prop
  refine ⟨h.1.comp (g := affInv t₀ ρ π) hc.continuousOn (fun t ht => norm_affInv t₀ hρ π ht), fun z w hd => ?_⟩
  have hd' : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → affInv t₀ ρ π z + ζ • (((ρ : ℂ)⁻¹ • w) ∘ π.symm) ∈ ball 0 1 := by
    intro ζ hζ
    rw [← affInv_add]
    exact norm_affInv t₀ hρ π (hd ζ hζ)
  have e : (fun ζ : ℂ => ψ (affInv t₀ ρ π (z + ζ • w))) =
      fun ζ : ℂ => ψ (affInv t₀ ρ π z + ζ • (((ρ : ℂ)⁻¹ • w) ∘ π.symm)) := by
    funext ζ; rw [affInv_add]
  simp only [e]
  exact h.2 _ _ hd'

theorem exists_log_norm {n : ℕ} {t₀ : Fin n → ℂ} {F : (Fin n → ℂ) → ℂ} (hF : AnalyticAt ℂ F t₀) (h0 : F t₀ ≠ 0) :
    ∃ r > (0 : ℝ), ∃ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G (ball t₀ r) ∧
      ∀ t ∈ ball t₀ r, Real.log ‖F t‖ = (G t).re + Real.log ‖F t₀‖ := by
  have hH : AnalyticAt ℂ (fun t => F t / F t₀) t₀ := hF.div analyticAt_const h0
  have h1 : ∀ᶠ t in 𝓝 t₀, F t / F t₀ ∈ Complex.slitPlane := by
    have : F t₀ / F t₀ ∈ Complex.slitPlane := by rw [div_self h0]; exact Complex.one_mem_slitPlane
    exact hH.continuousAt.eventually_mem (Complex.isOpen_slitPlane.mem_nhds this)
  have h2 : ∀ᶠ t in 𝓝 t₀, AnalyticAt ℂ (fun t => F t / F t₀) t := hH.eventually_analyticAt
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  refine ⟨r, hr, fun t => Complex.log (F t / F t₀), fun t ht => ?_, fun t ht => ?_⟩
  · exact ((hb t ht).2.differentiableAt.clog (hb t ht).1).differentiableWithinAt
  · have hne : F t / F t₀ ≠ 0 := Complex.slitPlane_ne_zero (hb t ht).1
    have hFt : F t ≠ 0 := fun h => hne (by simp [h])
    rw [Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.2 hFt) (norm_ne_zero_iff.2 h0)]
    ring

theorem analyticAt_eval {A : Type} {n : ℕ} {q : (Fin n → ℂ) → A → ℂ} {t₀ : Fin n → ℂ}
    (hq : ∀ i, AnalyticAt ℂ (fun t => q t i) t₀) (p : MvPolynomial A ℤ) :
    AnalyticAt ℂ (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) p)) t₀ := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p r hp hr =>
    have e : (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) (p + r))) =
        (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) p)) +
          fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) r) := by
      funext t; simp
    rw [e]; exact hp.add hr
  | mul_X p i hp =>
    have e : (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) (p * MvPolynomial.X i))) =
        (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) p)) * fun t => q t i := by
      funext t; simp
    rw [e]; exact hp.mul (hq i)

open scoped ComplexOrder in

theorem gram_det_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ) (hu : LinearIndependent ℂ u) :
    0 < (R.gram u).det.re := by
  have hH : (R.Hmᵀ).IsHermitian := by
    ext i j
    exact R.herm.apply j i
  have hM : (R.Hmᵀ).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
    have h1 := R.pos x hx
    have e : star x ⬝ᵥ (R.Hmᵀ *ᵥ x) = x ⬝ᵥ R.Hm *ᵥ star x := by
      rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
    have him : (star x ⬝ᵥ (R.Hmᵀ *ᵥ x)).im = 0 := hH.im_star_dotProduct_mulVec_self x
    rw [Complex.pos_iff]
    exact ⟨by rw [e]; exact h1, him.symm⟩
  let C : Matrix (Fin g) (Fin m) ℂ := (Matrix.of u)ᵀ
  have hC : Function.Injective C.mulVec := Matrix.mulVec_injective_iff.2 hu
  have e : R.gram u = Cᴴ * R.Hmᵀ * C := by
    ext a b
    simp only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, Pi.star_apply, C]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hp := (hM.conjTranspose_mul_mul_same hC).det_pos
  rw [← e] at hp
  exact (Complex.pos_iff.1 hp).1

theorem hodgeInnerProduct_of_fibreLatticeVector {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {X : Scheme.{0}} {t : SAB H X} {z : Sp ℂ ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    {R : RiemLat E g Λ} {A₀ : Type} {x : A₀ → Fin g → ℂ} {v : A₀ → (epsAt z ⟶ t.G)}
    (h : FibreLatVec t z R x v) (tan : ∀ i, IsTanAt t.G z (v i)) (i j : A₀) :
    HodgeIP t.G t.PP.L z (v i) (v j) (Real.pi * R.ip (x i) (x j)) := by
  obtain ⟨A, _, φ, u, χ, h1, h2, -, -, -, h3⟩ := h
  obtain ⟨v', e', d'⟩ := h3 i
  obtain ⟨w', f', g'⟩ := h3 j
  exact ⟨t.PP.isLB, tan i, tan j, A, inferInstance, φ, g, u, R.Hm, χ, v', w', x i, x j, h1, h2, e', f', d', g', rfl⟩

section Free

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]

theorem isOpen_offBd (D : ComponentData II Ψ K J Ω W) (a : Fin D.nCharts) : IsOpen (offBd D a) := by
  have e : offBd D a = ball 0 1 ∩ ⋂ i : Fin (Fintype.card Ψ * D.j * (D.N - D.j)),
      {t | (i : ℕ) < (D.chart a).a → t i ≠ 0} := by
    ext t
    simp only [offBd, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    refine and_congr_right fun ht => ?_
    rw [(D.chart a).boundary t ht]
    push_neg
    rfl
  rw [e]
  refine isOpen_ball.inter (isOpen_iInter_of_finite fun i => ?_)
  by_cases h : (i : ℕ) < (D.chart a).a
  · simpa [h] using isOpen_ne_fun (continuous_apply i) continuous_const
  · simp [h]

end Free

end GlobalTheory.CompanionTheory.Ar.Cusp.CuspCorrespondence
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp.CorrPsh

open ReciprocityTheory.AnForm.A (IsPsh)
open _root_.Metric GlobalTheory.CompanionTheory.Ar.Cusp.CuspCorrespondence
open GroundTheory.Heights₂.Heights.Regular (logCover expCover)

theorem affInv_self {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) : affInv t₀ ρ π t₀ = 0 := by
  funext i
  simp [affInv]

theorem loc_of_formula {n : ℕ} (t₀ : Fin n → ℂ) {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (π : Equiv.Perm (Fin n))
    {ψ f : (Fin n → ℂ) → ℝ} {G : (Fin n → ℂ) → ℂ} (h : IsPsh (ball 0 1) ψ) (hc : ContinuousOn ψ (ball 0 1))
    (hG : DifferentiableOn ℂ G (ball 0 r)) (hf : ∀ u ∈ ball 0 r, f (aff t₀ ρ π u) = (G u).re + ψ u / 2) :
    ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ IsPsh V f ∧ ContinuousOn f V := by
  have hd : Differentiable ℂ (affInv t₀ ρ π) := by
    unfold affInv
    fun_prop
  let V : Set (Fin n → ℂ) := ball t₀ ρ ∩ affInv t₀ ρ π ⁻¹' ball 0 r
  have hV : IsOpen V := isOpen_ball.inter (isOpen_ball.preimage hd.continuous)
  have hG' : DifferentiableOn ℂ (fun t => G (affInv t₀ ρ π t)) V := hG.comp hd.differentiableOn fun t ht => ht.2
  have heq : Set.EqOn (fun t => ψ (affInv t₀ ρ π t) / 2 + (G (affInv t₀ ρ π t)).re + 0) f V := fun t ht => by
    have := hf _ ht.2
    rw [aff_affInv t₀ hρ π] at this
    simp only [this]
    ring
  have P0 := isPsh_comp_affInv t₀ hρ π h
  have P1 := isPsh_half (⟨P0.1.mono Set.inter_subset_left, fun z w hd => P0.2 z w fun ζ hζ => (hd ζ hζ).1⟩ :
    IsPsh V _)
  refine ⟨V, hV, ⟨mem_ball_self hρ, by simpa [affInv_self] using hr⟩,
    GroundTheory.Heights₂.Heights.NineStatements.isPsh_congr' heq
      (GroundTheory.Heights₂.Heights.NineStatements.isPsh_add_re_add_const hV P1 hG' 0), ContinuousOn.congr ?_ heq.symm⟩
  exact (((hc.comp hd.continuous.continuousOn fun t ht => norm_affInv t₀ hρ π ht.1).div_const 2).add
    (Complex.continuous_re.comp_continuousOn hG'.continuousOn)).add continuousOn_const

theorem logDet_cont {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] {Ψ : Type} [Fintype Ψ] {n m : ℕ} {U : Set (Fin n → ℂ)} {R : (Fin n → ℂ) → RiemLat E g Λ}
    {b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ} (hR : IsHolFam U R) (hb : ∀ τ i, ContinuousOn (b τ i) U)
    (hl : ∀ t ∈ U, ∀ τ, LinearIndependent ℂ fun i => b τ i t) :
    ContinuousOn (fun t => (R t).logDet fun τ i => b τ i t) U := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨t₁, ht₁⟩
  · exact continuousOn_empty _
  rw [continuousOn_iff_continuous_restrict]
  have hH : Continuous fun x : U => (R x).Hm :=
    GlobalTheory.T.continuous_hermitian_matrix_family E g Λ U (fun x => R x) (R t₁).form (fun x => hR.1 x x.2 t₁ ht₁)
      fun v => continuousOn_iff_continuous_restrict.1 (hR.2 v).continuousOn
  refine continuous_finset_sum _ fun τ _ => Continuous.log ?_ fun x => (gram_det_pos _ _ (hl x x.2 τ)).ne'
  refine Complex.continuous_re.comp (Continuous.matrix_det (continuous_matrix fun p q => ?_))
  have hb' : ∀ i, Continuous fun x : U => b τ i x := fun i => continuousOn_iff_continuous_restrict.1 (hb τ i)
  exact (hb' q).dotProduct (hH.matrix_mulVec (hb' p).star)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {Xo : ∀ l : Tor.Level H, Moduli D l} {l : Tor.Level H} {c : Coeff l}
  {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem} {K : Type} [Fintype K]
  {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : CMType H → Type}
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} {S₀ : Finset ℕ}

theorem unit_factor (a : Fin Dc.nCharts) (t₀ : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) (ht₀ : t₀ ∈ ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1)
    (d : MuFrameAt Hd ((Dc.chart a).γ t₀)) (hv0 : valAt Dc.y d.u ((Dc.chart a).γ t₀) ≠ 0) :
    ∃ r > (0 : ℝ), ∃ G : (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → ℂ, DifferentiableOn ℂ G (ball t₀ r) ∧
      ∀ t ∈ ball t₀ r, t ∈ ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1 →
        Real.log (‖valAt Dc.y d.u ((Dc.chart a).γ t)‖ * ∏ k, ‖(Dc.chart a).γ t ⟨k, d.c k⟩‖ ^ Hd.aMu k) = (G t).re := by
  have hex : ∃ v, IsValueAt Dc.y d.u ((Dc.chart a).γ t₀) v := by
    by_contra hn
    exact hv0 (dif_neg hn)
  obtain ⟨v₀, dg, pg, ph, hpg, hph, hne, heq, hhne, hv₀⟩ := hex
  have hq : ∀ p, AnalyticAt ℂ (fun t => (Dc.chart a).γ t p) t₀ := fun p =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).analyticAt _).comp
      ((Dc.chart a).analytic t₀ ht₀)
  have hGa := analyticAt_eval hq pg
  have hHa := analyticAt_eval hq ph
  have hval0 : v₀ ≠ 0 := by
    have e : GroundTheory.Heights₂.Heights.LowerBoundFree.valAt Dc.y d.u ((Dc.chart a).γ t₀) = v₀ :=
      valAt_eq ((Dc.chart a).mem t₀ ht₀) ⟨dg, pg, ph, hpg, hph, hne, heq, hhne, hv₀⟩
    rwa [e] at hv0
  have hg0 : MvPolynomial.eval ((Dc.chart a).γ t₀) (MvPolynomial.map (Int.castRingHom ℂ) pg) ≠ 0 := by
    intro h
    apply hval0
    rw [hv₀, h, zero_div]
  let F : (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → ℂ := fun t =>
    MvPolynomial.eval ((Dc.chart a).γ t) (MvPolynomial.map (Int.castRingHom ℂ) pg) /
      MvPolynomial.eval ((Dc.chart a).γ t) (MvPolynomial.map (Int.castRingHom ℂ) ph) *
      ∏ k, (Dc.chart a).γ t ⟨k, d.c k⟩ ^ Hd.aMu k
  have hF : AnalyticAt ℂ F t₀ :=
    (hGa.div hHa hhne).mul (Finset.analyticAt_fun_prod _ fun k _ => (hq _).zpow (d.inDom.1 k))
  have hF0 : F t₀ ≠ 0 :=
    mul_ne_zero (div_ne_zero hg0 hhne) (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (d.inDom.1 k))
  obtain ⟨r, hr, Gf, hGf, hlog⟩ := exists_log_norm hF hF0
  obtain ⟨r₂, hr₂, hH2⟩ := Metric.eventually_nhds_iff_ball.1 (hHa.continuousAt.eventually_ne hhne)
  have hV1 : ball t₀ (min r r₂) ⊆ ball t₀ r := ball_subset_ball (min_le_left _ _)
  have hV2 : ball t₀ (min r r₂) ⊆ ball t₀ r₂ := ball_subset_ball (min_le_right _ _)
  refine ⟨min r r₂, lt_min hr hr₂, fun t => Gf t + (Real.log ‖F t₀‖ : ℂ), (hGf.mono hV1).add_const _,
    fun t ht ht1 => ?_⟩
  have hval : GroundTheory.Heights₂.Heights.LowerBoundFree.valAt Dc.y d.u ((Dc.chart a).γ t) =
      MvPolynomial.eval ((Dc.chart a).γ t) (MvPolynomial.map (Int.castRingHom ℂ) pg) /
        MvPolynomial.eval ((Dc.chart a).γ t) (MvPolynomial.map (Int.castRingHom ℂ) ph) :=
    valAt_eq ((Dc.chart a).mem t ht1) ⟨dg, pg, ph, hpg, hph, hne, heq, hH2 t (hV2 ht), rfl⟩
  have hn : ‖GroundTheory.Heights₂.Heights.LowerBoundFree.valAt Dc.y d.u ((Dc.chart a).γ t)‖ *
      ∏ k, ‖(Dc.chart a).γ t ⟨k, d.c k⟩‖ ^ Hd.aMu k = ‖F t‖ := by
    simp only [F, norm_mul, norm_prod, norm_zpow, hval]
  rw [hn, hlog t (hV1 ht), Complex.add_re, Complex.ofReal_re]

theorem point_formula (Or : CptOrigin Y S₀ Dc Hd) {z : Sp ℂ ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ}
    (co : CoordsAt Or.𝔐.ξ Dc.y z w) (hI : Or.𝔐.Interior z) (hG : Top.Given) (d : MuFrameAt Hd w)
    {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} (hs : Or.IsSmallPart d s)
    {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ)
    (x : CMType H → Fin (Dc.N - Dc.j) → Fin g → ℂ) (hx : ∀ τ, LinearIndependent ℂ (x τ))
    (v : CMType H × Fin (Dc.N - Dc.j) → (epsAt z ⟶ Or.𝔐.t.G)) (hv : ∀ i, Or.𝔐.M.ValAt z (s i.1 i.2) (v i))
    (hfib : FibreLatVec Or.𝔐.t z R (fun i => x i.1 i.2) v) :
    phMu Hd w = Real.log (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) +
      ((Fintype.card (CMType H) : ℝ) * (((Dc.N - Dc.j : ℕ) : ℝ) * Real.log Real.pi) + R.logDet x) / 2 := by
  obtain ⟨-, hP⟩ := GlobalTheory.T.component_data_intersection_bound hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or z w co
  obtain ⟨-, hP2⟩ := hP d
  obtain ⟨-, -, hform⟩ := hP2 s hs
  let Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ := fun τ =>
    Matrix.of fun p q => (Real.pi : ℂ) * R.ip (x τ p) (x τ q)
  have hΓ : ∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ) := fun τ =>
    ⟨fun p => v (τ, p), fun p => hv (τ, p), fun p q =>
      hodgeInnerProduct_of_fibreLatticeVector hfib (fun i => (hv i).isTanAt) (τ, p) (τ, q)⟩
  have hdet : ∀ τ, Real.log (Γ τ).det.re = ((Dc.N - Dc.j : ℕ) : ℝ) * Real.log Real.pi +
      Real.log (R.gram (x τ)).det.re := by
    intro τ
    have hpos := gram_det_pos R (x τ) (hx τ)
    have e1 : Γ τ = (Real.pi : ℂ) • R.gram (x τ) := by
      ext p q; rfl
    rw [e1, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
      Real.log_mul (pow_ne_zero _ Real.pi_ne_zero) hpos.ne', Real.log_pow]
  have h1 := hform hI Γ hΓ
  simp only [hdet, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
  exact h1

theorem fibreLat_of_vec {X : Scheme.{0}} {t : SAB H X} {z : Sp ℂ ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] {R : RiemLat E g Λ} {A₀ : Type} {x : A₀ → Fin g → ℂ} {v : A₀ → (epsAt z ⟶ t.G)}
    (h : FibreLatVec t z R x v) : FibreLat t z R := by
  obtain ⟨A, i, φ, u, χ, h1, h2, h3, h4, h5, -⟩ := h
  exact ⟨A, i, φ, u, χ, h1, h2, h3, h4, h5, fun i => i.elim⟩

theorem chart_formula (hG : Top.Given) (Or : CptOrigin Y S₀ Dc Hd) {U : ((Σ k, J k) → ℂ) → ℝ}
    (hU : Or.𝔐.IsCuspWeight Or.sm U) (a : Fin Dc.nCharts)
    (t₀ : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) (ht₀ : t₀ ∈ ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1) :
    ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (L : ActPeriods E (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) a₀ g Λ)
      (π : Equiv.Perm (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)))) (ρ r : ℝ) (σ : CMType H → (𝓞 E →+* ℂ))
      (b : CMType H → Fin (Dc.N - Dc.j) → (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → Fin g → ℂ) (G : (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → ℂ),
      0 < ρ ∧ 0 < r ∧ r ≤ 1 ∧ IsCMFam σ ∧ IsEigFrames (ball 0 1) L.B σ b ∧ DifferentiableOn ℂ G (ball 0 r) ∧
      (∀ u ∈ ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1, aff t₀ ρ π u ∈ ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1 ∧
        (aff t₀ ρ π u ∈ offBd Dc a ↔ u ∈ Flat.punct _ a₀ 1)) ∧
      ∀ w (hw : w ∈ logCover L.a_le), expCover a₀ w ∈ ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) r →
        expCover a₀ w ∈ Flat.punct _ a₀ 1 →
        phMu Hd ((Dc.chart a).γ (aff t₀ ρ π (expCover a₀ w))) =
          (G (expCover a₀ w)).re + (L.riem w hw).logDet (fun τ i => b τ i (expCover a₀ w)) / 2 ∧
        U ((Dc.chart a).γ (aff t₀ ρ π (expCover a₀ w))) = (L.riem w hw).cuspW σ := by
  classical
  obtain ⟨a₀, g, Λ, i₁, i₂, L, π, ρ, σ, pt, d, s, b, hρ, hσ, hs, hb, hu, hw⟩ :=
    GlobalTheory.T.component_data_hodge_bound hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or a t₀ ht₀
  obtain ⟨-, -, co0, -, int0⟩ := hu 0 (mem_ball_self one_pos)
  have hT0 : t₀ + (ρ : ℂ) • ((0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) ∘ π) = t₀ := by
    funext i; simp
  rw [hT0] at co0
  obtain ⟨-, hP⟩ := GlobalTheory.T.component_data_intersection_bound hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or (pt 0) _ co0
  obtain ⟨-, hP2⟩ := hP d
  obtain ⟨-, hv0, -⟩ := hP2 s hs
  obtain ⟨r, hr, G, hGd, hlog⟩ := unit_factor a t₀ ht₀ d hv0
  have hd : Differentiable ℂ (aff t₀ ρ π) := by
    unfold aff
    fun_prop
  have h0 : aff t₀ ρ π 0 = t₀ := hT0
  obtain ⟨r', hr', hb'⟩ := Metric.eventually_nhds_iff_ball.1
    ((hd.continuous.tendsto 0).eventually (by rw [h0]; exact ball_mem_nhds t₀ hr : ball t₀ r ∈ 𝓝 (aff t₀ ρ π 0)))
  let C : ℝ := (Fintype.card (CMType H) : ℝ) * (((Dc.N - Dc.j : ℕ) : ℝ) * Real.log Real.pi)
  have hm1 : ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) (min r' 1) ⊆ ball 0 r' := ball_subset_ball (min_le_left _ _)
  have hm2 : ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) (min r' 1) ⊆ ball 0 1 := ball_subset_ball (min_le_right _ _)
  refine ⟨a₀, g, Λ, i₁, i₂, L, π, ρ, min r' 1, σ, b, fun u => G (aff t₀ ρ π u) + ((C / 2 : ℝ) : ℂ), hρ,
    lt_min hr' one_pos, min_le_right _ _, hσ, hb,
    (hGd.comp hd.differentiableOn fun u hu' => hb' u (hm1 hu')).add_const _, fun u hu' => ?_, fun w hlw h1 h2 => ?_⟩
  · obtain ⟨e1, -, co, -, hint⟩ := hu u hu'
    refine ⟨e1, ?_⟩
    rw [← hint]
    exact ⟨fun h => not_not.1 fun hn => h.2 ((Or.bd _ _ co).2 hn), fun h => ⟨e1, fun hb => (Or.bd _ _ co).1 hb h⟩⟩
  · obtain ⟨v, hv, hfib⟩ := hw w hlw
    obtain ⟨e1, dom, co, hL, hint⟩ := hu _ (hm2 h1)
    have hI := hint.2 h2
    refine ⟨?_, WeightSheet.eq_cuspW_of_fibre Or hU co hI _ (fibreLat_of_vec hfib) hL⟩
    have k := point_formula Or co hI hG { d with inDom := dom } hs (L.riem w hlw)
      (fun τ i => b τ i (expCover a₀ w)) (fun τ => (hb.2 _ (hm2 h1) τ).1) v hv hfib
    have k2 := hlog _ (hb' _ (hm1 h1)) e1
    refine k.trans ?_
    rw [Complex.add_re, Complex.ofReal_re, ← k2]
    simp only [C, aff]
    ring

theorem near_all (hG : Top.Given) (Or : CptOrigin Y S₀ Dc Hd) {U : ((Σ k, J k) → ℂ) → ℝ}
    (hU : Or.𝔐.IsCuspWeight Or.sm U) (a : Fin Dc.nCharts) (t₀ : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) (ht₀ : t₀ ∈ offBd Dc a) :
    (∃ V : Set (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ), IsOpen V ∧ t₀ ∈ V ∧ IsPsh V (fun t => phMu Hd ((Dc.chart a).γ t)) ∧
      ContinuousOn (fun t => phMu Hd ((Dc.chart a).γ t)) V) ∧
    ∃ V : Set (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ), IsOpen V ∧ t₀ ∈ V ∧ IsPsh V (fun t => corrW Hd U ((Dc.chart a).γ t)) ∧
      ContinuousOn (fun t => corrW Hd U ((Dc.chart a).γ t)) V := by
  classical
  obtain ⟨a₀, g, Λ, i₁, i₂, L, π, ρ, r, σ, b, G, hρ, hr, hr1, hσ, hb, hGd, hu, hw⟩ :=
    chart_formula hG Or hU a t₀ ht₀.1
  have h0 : (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) ∈ ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1 := mem_ball_self one_pos
  have hT0 : aff t₀ ρ π 0 = t₀ := by
    funext i; simp [aff]
  have ha0 : a₀ = 0 := by
    by_contra hne
    have hle := L.a_le
    exact ((hu 0 h0).2.1 (by rw [hT0]; exact ht₀)).2 ⟨0, by omega⟩ (Nat.pos_of_ne_zero hne) rfl
  subst ha0
  have he : ∀ u : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ, expCover 0 u = u := by
    intro u; funext k; simp [expCover]
  have hlc : ∀ u ∈ ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1, u ∈ logCover L.a_le := by
    intro u hu'
    exact ⟨fun i => i.elim0, fun k _ => (pi_norm_lt_iff one_pos).1 (mem_ball_zero_iff.1 hu') k⟩
  let R : (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → RiemLat E g Λ := fun u =>
    if h : u ∈ logCover L.a_le then L.riem u h else L.riem 0 (hlc 0 h0)
  have hR : ∀ u (h : u ∈ logCover L.a_le), R u = L.riem u h := fun u h => dif_pos h
  have hHol : IsHolFam (ball 0 1) R := by
    refine ⟨fun t ht t' ht' => ?_, fun x => ?_⟩
    · rw [hR t (hlc t ht), hR t' (hlc t' ht')]
      rfl
    · refine ((L.hol x).mono (fun u hu' => hlc u hu')).congr fun u hu' => ?_
      rw [hR u (hlc u hu')]
      rfl
  have hEig : IsEigFrames (ball 0 1) (fun t => (R t).B) σ b := by
    refine ⟨hb.1, fun t ht τ => ?_⟩
    have e : (R t).B = L.B t := by
      rw [hR t (hlc t ht)]
      show L.B (expCover 0 t) = L.B t
      rw [he]
    simp only [e]
    exact hb.2 t ht τ
  obtain ⟨p1, p2, p3⟩ := GlobalTheory.T.log_det_eigen_frame_plurisubharmonic E g Λ (CMType H) _ (ball 0 1) R σ (Dc.N - Dc.j) b isOpen_ball hHol hσ hEig
  have c1 := logDet_cont hHol (fun τ i => (hb.1 τ i).continuousOn) fun t ht τ => (hb.2 t ht τ).1
  have key : ∀ u ∈ ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) r,
      phMu Hd ((Dc.chart a).γ (aff t₀ ρ π u)) = (G u).re + (R u).logDet (fun τ i => b τ i u) / 2 ∧
        U ((Dc.chart a).γ (aff t₀ ρ π u)) = (R u).cuspW σ := by
    intro u hu'
    have hu1 := ball_subset_ball hr1 hu'
    have := hw u (hlc u hu1) (by rw [he]; exact hu')
      (by rw [he]; exact ⟨hu1, fun i hi => absurd hi (Nat.not_lt_zero _)⟩)
    rw [he] at this
    rw [hR u (hlc u hu1)]
    exact this
  refine ⟨loc_of_formula t₀ hρ hr π p1 c1 hGd fun u hu' => (key u hu').1,
    loc_of_formula t₀ hρ hr π p2 (c1.add p3) hGd fun u hu' => ?_⟩
  simp only [corrW, (key u hu').1, (key u hu').2]
  ring

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cusp_intersection_positive : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (U : ((Σ k, J k) → ℂ) → ℝ), Or.𝔐.IsCuspWeight Or.sm U → ChartPsh Dc (phMu Hd) ∧ ChartCont Dc (phMu Hd) ∧ ChartPsh Dc (corrW Hd U) ∧ ChartCont Dc (corrW Hd U) := by
  intro hG E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or U hU
  refine ⟨fun a => GlobalTheory.T.plurisubharmonic_local _ _ _ (isOpen_offBd Dc a) fun t ht => ?_, fun a t ht => ?_,
    fun a => GlobalTheory.T.plurisubharmonic_local _ _ _ (isOpen_offBd Dc a) fun t ht => ?_, fun a t ht => ?_⟩
  · obtain ⟨V, h1, h2, h3, -⟩ := (near_all hG Or hU a t ht).1
    exact ⟨V, h1, h2, h3⟩
  · obtain ⟨V, h1, h2, -, h3⟩ := (near_all hG Or hU a t ht).1
    exact (h3.continuousAt (h1.mem_nhds h2)).continuousWithinAt
  · obtain ⟨V, h1, h2, h3, -⟩ := (near_all hG Or hU a t ht).2
    exact ⟨V, h1, h2, h3⟩
  · obtain ⟨V, h1, h2, -, h3⟩ := (near_all hG Or hU a t ht).2
    exact (h3.continuousAt (h1.mem_nhds h2)).continuousWithinAt

end GlobalTheory.CompanionTheory.Ar.Cusp.CorrPsh
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_intersection_positive : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (U : ((Σ k, J k) → ℂ) → ℝ), Or.𝔐.IsCuspWeight Or.sm U → ChartPsh Dc (phMu Hd) ∧ ChartCont Dc (phMu Hd) ∧ ChartPsh Dc (corrW Hd U) ∧ ChartCont Dc (corrW Hd U) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.cusp_intersection_positive | exact GlobalTheory.CompanionTheory.Relay.cusp_intersection_positive | (intros; apply GlobalTheory.CompanionTheory.Relay.cusp_intersection_positive <;> assumption)
end
