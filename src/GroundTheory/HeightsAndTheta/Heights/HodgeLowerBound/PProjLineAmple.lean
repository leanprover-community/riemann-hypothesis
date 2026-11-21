import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsProjLineAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFS
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsLaplacianLogGrowth

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped nonZeroDivisors

theorem ringKrullDim_mRing_line : ringKrullDim (MRing (PBlk 2)) = 3 := by
  have hZ : ringKrullDim ℤ = 1 := IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField
  have hc : Nat.card (Σ _ : Unit, PBlk 2 ()) = 2 := by simp
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, hZ, hc]
  rfl

theorem eq_bot_of_isArithVar_line {W : Ideal (MRing (PBlk 2))} {d : ℕ} (hd : 1 ≤ d)
    (h : IsArithVar W (d + 1)) : W = ⊥ ∧ d = 1 := by
  obtain ⟨-, -, -, hdim⟩ := h
  simp only [Fintype.card_unit] at hdim
  by_cases hW : W = ⊥
  · refine ⟨hW, ?_⟩
    subst hW
    rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _), ringKrullDim_mRing_line] at hdim
    have h3 : ((3 : ℕ) : WithBot ℕ∞) = ((d + 1 + 1 : ℕ) : WithBot ℕ∞) := hdim
    have : (3 : ℕ) = d + 1 + 1 := by exact_mod_cast h3
    omega
  · exfalso
    obtain ⟨f, hfW, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    have hnzd : f ∈ (MRing (PBlk 2))⁰ := mem_nonZeroDivisors_of_ne_zero hf0
    have hle := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk W) Ideal.Quotient.mk_surjective hnzd
      (Ideal.Quotient.eq_zero_iff_mem.mpr hfW)
    rw [hdim, ringKrullDim_mRing_line] at hle
    have h4 : ((d + 1 + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ ((3 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hle
    have : d + 1 + 1 + 1 ≤ 3 := by exact_mod_cast h4
    omega

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace LineChart

def lineLift (w : ((k : Unit) → PBlk 2 k) → ℂ) : (Σ k : Unit, PBlk 2 k) → ℂ := fun p => w fun _ => p.2

theorem segre_line (z : (Σ k : Unit, PBlk 2 k) → ℂ) (i : (k : Unit) → PBlk 2 k) :
    segre z i = z ⟨(), i ()⟩ := by
  simp [segre]

theorem segre_lineLift (w : ((k : Unit) → PBlk 2 k) → ℂ) : segre (lineLift w) = w := by
  funext i
  rw [segre_line]
  rfl

theorem lineLift_segre (z : (Σ k : Unit, PBlk 2 k) → ℂ) : lineLift (segre z) = z := by
  funext p
  obtain ⟨⟨⟩, i⟩ := p
  simp only [lineLift, segre_line]

theorem mem_mcPts_bot (z : (Σ k : Unit, PBlk 2 k) → ℂ) :
    z ∈ mcPts (⊥ : Ideal (MRing (PBlk 2))) ↔ ∃ i, z ⟨(), i⟩ ≠ 0 := by
  constructor
  · rintro ⟨h, -⟩
    exact h ()
  · intro h
    refine ⟨fun k => ?_, fun f hf => ?_⟩
    · cases k
      exact h
    · rw [Ideal.mem_bot] at hf
      subst hf
      simp

theorem lineLift_mem {w : ((k : Unit) → PBlk 2 k) → ℂ} (hw : w ≠ 0) :
    lineLift w ∈ mcPts (⊥ : Ideal (MRing (PBlk 2))) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  refine (mem_mcPts_bot _).2 ⟨i (), ?_⟩
  simpa [lineLift] using hi

theorem injective_of_good {Ψ : (((k : Unit) → PBlk 2 k) → ℂ) →ₗ[ℂ] (Fin (1 + 1) → ℂ)}
    (hΨ : IsGoodProj (⊥ : Ideal (MRing (PBlk 2))) Ψ) : Function.Injective Ψ := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  by_contra hne
  exact hΨ _ (lineLift_mem hne) (by rw [segre_lineLift]; exact hw)

theorem exists_good :
    ∃ Ψ : (((k : Unit) → PBlk 2 k) → ℂ) →ₗ[ℂ] (Fin (1 + 1) → ℂ), IsGoodProj (⊥ : Ideal (MRing (PBlk 2))) Ψ := by
  let Ψ0 := LinearEquiv.funCongrLeft ℂ ℂ (Equiv.funUnique Unit (Fin 2)).symm
  refine ⟨Ψ0.toLinearMap, fun z hz h0 => ?_⟩
  obtain ⟨i, hi⟩ := (mem_mcPts_bot z).1 hz
  have hs : segre z = 0 := Ψ0.map_eq_zero_iff.mp h0
  exact hi (by rw [← segre_line z (fun _ => i), hs]; rfl)

theorem geomDeg_eq_integral (A : HermLine (PBlk 2)) :
    ∃ L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ),
      geomDeg (⊥ : Ideal (MRing (PBlk 2))) A 1 =
        ∫ y : Fin 1 → ℂ, maDensity (fun _ y' => Real.log (A.h (lineLift (L (Fin.cons 1 y'))))) y := by
  have hex := exists_good
  set Ψ := hex.choose with hΨdef
  have hΨ : IsGoodProj (⊥ : Ideal (MRing (PBlk 2))) Ψ := hex.choose_spec
  have hinj := injective_of_good hΨ
  have hrank : Module.finrank ℂ (((k : Unit) → PBlk 2 k) → ℂ) = Module.finrank ℂ (Fin (1 + 1) → ℂ) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
    simp
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  set E := LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩ with hE
  set L := E.symm with hL
  have hΨL : ∀ v, Ψ (L v) = v := E.apply_symm_apply
  have hLΨ : ∀ w, L (Ψ w) = w := E.symm_apply_apply
  refine ⟨L, ?_⟩
  have hLdiff : Differentiable ℂ fun v => L v := (LinearMap.toContinuousLinearMap L.toLinearMap).differentiable
  have hcons : Differentiable ℂ fun y' : Fin 1 → ℂ => (Fin.cons 1 y' : Fin (1 + 1) → ℂ) := by
    rw [differentiable_pi]
    intro c
    refine Fin.cases ?_ (fun i => ?_) c
    · simp only [Fin.cons_zero]
      exact differentiable_const _
    · simp only [Fin.cons_succ]
      exact differentiable_apply i
  set γ0 : (Fin 1 → ℂ) → (Σ k : Unit, PBlk 2 k) → ℂ := fun y' => lineLift (L (Fin.cons 1 y')) with hγ0
  have hγ0d : ∀ y', DifferentiableAt ℂ γ0 y' := by
    intro y'
    rw [differentiableAt_pi]
    intro p
    exact ((differentiable_apply (fun _ => p.2)).comp (hLdiff.comp hcons)) y'
  have hγ0mem : ∀ y', γ0 y' ∈ mcPts (⊥ : Ideal (MRing (PBlk 2))) := by
    intro y'
    have hv : (Fin.cons 1 y' : Fin (1 + 1) → ℂ) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
    exact lineLift_mem ((L.map_ne_zero_iff).mpr hv)
  unfold geomDeg ptsIntegral
  rw [dif_pos hex]
  unfold ptsIntegralAt
  congr 1
  funext y
  have hfib : fibre (⊥ : Ideal (MRing (PBlk 2))) Ψ y = {L (Fin.cons 1 y)} := by
    ext w
    simp only [fibre, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, -, -, hw⟩
      rw [← hw, hLΨ]
    · rintro rfl
      exact ⟨γ0 y, hγ0mem y, segre_lineLift _, hΨL _⟩
  have hsheet : IsSheet (⊥ : Ideal (MRing (PBlk 2))) Ψ y (L (Fin.cons 1 y)) γ0 :=
    ⟨segre_lineLift _, Eventually.of_forall fun y' => ⟨hγ0d y', hγ0mem y', by rw [segre_lineLift, hΨL]⟩⟩
  rw [hfib, finsum_mem_singleton]
  unfold sheetDensity
  split_ifs with hγ
  · have hev : (fun y' => Real.log (A.h (hγ.choose y'))) =ᶠ[𝓝 y]
        fun y' => Real.log (A.h (lineLift (L (Fin.cons 1 y')))) := by
      filter_upwards [hγ.choose_spec.2] with y' hy'
      have hs : segre (hγ.choose y') = L (Fin.cons 1 y') := by
        rw [← hLΨ (segre (hγ.choose y')), hy'.2.2]
      rw [← hs, lineLift_segre]
    rw [one_mul]
    exact maDensity_congr_of_eventuallyEq fun _ => hev
  · exact absurd ⟨γ0, hsheet⟩ hγ

end LineChart

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian MeasureTheory

namespace LineChart

theorem isOpen_nonzero : IsOpen {z : (Σ k : Unit, PBlk 2 k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have he : {z : (Σ k : Unit, PBlk 2 k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} =
      {y : (Σ _ : Unit, Fin 2) → ℂ | ∃ i, y ⟨(), i⟩ ≠ 0} := by
    ext z
    constructor
    · intro h
      exact h ()
    · intro h k
      cases k
      exact h
  rw [he]
  exact Line.isOpen_nonzeroL

theorem contDiff_log_h {A : HermLine (PBlk 2)} (hA : IsSmoothHerm A) {g : ℂ → (Σ k : Unit, PBlk 2 k) → ℂ}
    (hg : ContDiff ℝ 2 g) (hne : ∀ w, ∃ i, g w ⟨(), i⟩ ≠ 0) : ContDiff ℝ 2 fun w => Real.log (A.h (g w)) := by
  refine contDiff_iff_contDiffAt.2 fun w => ?_
  have hmem : g w ∈ {z : (Σ k : Unit, PBlk 2 k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := fun k => by
    cases k
    exact hne w
  have hh : ContDiffAt ℝ 2 A.h (g w) :=
    (hA.contDiffAt (isOpen_nonzero.mem_nhds hmem)).of_le (WithTop.coe_le_coe.2 le_top)
  exact (hh.comp w hg.contDiffAt).log (A.pos _ hmem).ne'

theorem contDiff_cons_one : ContDiff ℂ 2 fun w : ℂ => (Fin.cons 1 (fun _ => w) : Fin (1 + 1) → ℂ) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact contDiff_const
  · simp only [Fin.cons_succ]
    exact contDiff_id

theorem contDiff_cons_last : ContDiff ℂ 2 fun t : ℂ => (Fin.cons t (fun _ => 1) : Fin (1 + 1) → ℂ) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact contDiff_id
  · simp only [Fin.cons_succ]
    exact contDiff_const

theorem contDiff_lineLift_comp (L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ))
    {c : ℂ → Fin (1 + 1) → ℂ} (hc : ContDiff ℂ 2 c) : ContDiff ℝ 2 fun w => lineLift (L (c w)) := by
  have hL : ContDiff ℂ 2 fun w => L (c w) :=
    (LinearMap.toContinuousLinearMap L.toLinearMap).contDiff.comp hc
  have h : ContDiff ℂ 2 fun w => lineLift (L (c w)) :=
    contDiff_pi.2 fun p => (contDiff_apply ℂ ℂ (fun _ => p.2)).comp hL
  exact h.restrict_scalars ℝ

theorem lineLift_ne {L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ)} {v : Fin (1 + 1) → ℂ}
    (hv : v ≠ 0) : ∃ i, lineLift (L v) ⟨(), i⟩ ≠ 0 :=
  (mem_mcPts_bot _).1 (lineLift_mem ((L.map_ne_zero_iff).mpr hv))

def chartPot (A : HermLine (PBlk 2)) (L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ)) (w : ℂ) : ℝ :=
  Real.log (A.h (lineLift (L (Fin.cons 1 fun _ => w))))

def chartPotInf (A : HermLine (PBlk 2)) (L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ))
    (t : ℂ) : ℝ :=
  Real.log (A.h (lineLift (L (Fin.cons t fun _ => 1))))

theorem contDiff_chartPot {A : HermLine (PBlk 2)} (hA : IsSmoothHerm A)
    (L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ)) : ContDiff ℝ 2 (chartPot A L) :=
  contDiff_log_h hA (contDiff_lineLift_comp L contDiff_cons_one)
    fun _ => lineLift_ne fun h => one_ne_zero (congrFun h 0)

theorem contDiff_chartPotInf {A : HermLine (PBlk 2)} (hA : IsSmoothHerm A)
    (L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ)) : ContDiff ℝ 2 (chartPotInf A L) :=
  contDiff_log_h hA (contDiff_lineLift_comp L contDiff_cons_last)
    fun _ => lineLift_ne fun h => one_ne_zero (congrFun h 1)

theorem chartPot_eq (A : HermLine (PBlk 2)) (L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ))
    {w : ℂ} (hw : w ≠ 0) : chartPot A L w = (A.a () : ℝ) * Real.log ‖w‖ + chartPotInf A L w⁻¹ := by
  have hv : (Fin.cons 1 (fun _ => w) : Fin (1 + 1) → ℂ) = w • Fin.cons w⁻¹ (fun _ => 1) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [mul_inv_cancel₀ hw]
    · simp
  have hz : lineLift (L (Fin.cons 1 (fun _ => w))) =
      fun p => (fun _ : Unit => w) p.1 * lineLift (L (Fin.cons w⁻¹ fun _ => 1)) p := by
    rw [hv, map_smul]
    rfl
  have hmem : ∀ k, ∃ i, lineLift (L (Fin.cons w⁻¹ fun _ => 1)) ⟨k, i⟩ ≠ 0 := fun k => by
    cases k
    exact lineLift_ne fun h => one_ne_zero (congrFun h 1)
  unfold chartPot chartPotInf
  rw [hz, A.smul (fun _ => w) _ (fun _ => hw)]
  simp only [Finset.univ_unique, Finset.prod_singleton]
  rw [Real.log_mul (zpow_ne_zero _ (norm_ne_zero_iff.mpr hw)) (A.pos _ hmem).ne', Real.log_zpow]

theorem maDensity_eq_laplacian {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (y : Fin 1 → ℂ) :
    maDensity (fun _ y' => u (y' 0)) y = Δ u (y 0) / (2 * Real.pi) := by
  set E : (Fin 1 → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0 with hE
  have hf : (fun y' : Fin 1 → ℂ => u (y' 0)) = u ∘ E := rfl
  have key : ∀ v : Fin 1 → ℂ, fderiv ℝ (fderiv ℝ (fun y' : Fin 1 → ℂ => u (y' 0))) y v v =
      iteratedFDeriv ℝ 2 u (y 0) ![v 0, v 0] := by
    intro v
    have h2 := iteratedFDeriv_two_apply (𝕜 := ℝ) (u ∘ E) y ![v, v]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
    rw [hf, ← h2, E.iteratedFDeriv_comp_right hu y le_rfl]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [maDensity_one (fun y' => u (y' 0)) y, key, key, laplacian_eq_iteratedFDeriv_complexPlane]
  simp

theorem geomDeg_eq_degree (hL : LaplacianLogGrowth.Statement) {A : HermLine (PBlk 2)} (hA : IsSmoothHerm A) :
    geomDeg (⊥ : Ideal (MRing (PBlk 2))) A 1 = (A.a () : ℝ) := by
  obtain ⟨L, hEq⟩ := geomDeg_eq_integral A
  rw [hEq]
  have hφ : (fun (_ : Fin 1) (y' : Fin 1 → ℂ) => Real.log (A.h (lineLift (L (Fin.cons 1 y'))))) =
      fun _ y' => chartPot A L (y' 0) := by
    funext j y'
    unfold chartPot
    have hy : (fun _ : Fin 1 => y' 0) = y' := funext fun i => by rw [Subsingleton.elim i 0]
    rw [hy]
  have hu := contDiff_chartPot hA L
  rw [hφ]
  simp_rw [maDensity_eq_laplacian hu]
  have hfu := (volume_preserving_funUnique (Fin 1) ℂ).integral_comp'
    (fun w : ℂ => Δ (chartPot A L) w / (2 * Real.pi))
  rw [show (∫ y : Fin 1 → ℂ, Δ (chartPot A L) (y 0) / (2 * Real.pi)) = _ from hfu, integral_div]
  obtain ⟨-, hint⟩ := hL (chartPot A L) (chartPotInf A L) (A.a () : ℝ) 1 hu one_pos
    (contDiff_chartPotInf hA L).contDiffOn fun w hw => by
      have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num) hw)
      exact chartPot_eq A L hw0
  rw [hint]
  have := Real.pi_pos
  field_simp

end LineChart

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo

theorem ProjLineAmple.proof (hL : LaplacianLogGrowth.Statement) : ProjLineAmple.Statement := by
  intro A hA ha W d hd hW _
  obtain ⟨rfl, rfl⟩ := eq_bot_of_isArithVar_line hd hW
  rw [LineChart.geomDeg_eq_degree hL hA]
  exact_mod_cast ha

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
