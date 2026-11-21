import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.LOfOfKChain
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.HalfOne
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.InvContDiffOn
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KcDual
import PositivityTheory.Representations.BoundaryCones.ArchimedeanCones.ConeOverlaps.OpenConeCriteria.OpenConeFormulation.IsOpenConeInvariant
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KchainSt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfHolds

section
noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.Kchain

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem mem_GLs_mul {a b : Mat n} (ha : a ∈ GLs n) (hb : b ∈ GLs n) : a * b ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero ha hb

theorem mem_GLs_inv {a : Mat n} (ha : a ∈ GLs n) : a⁻¹ ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq] at *
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero ha

theorem mem_GLs_conjT_inv {a : Mat n} (ha : a ∈ GLs n) : aᴴ⁻¹ ∈ GLs n := by
  apply mem_GLs_inv
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_conjTranspose] at *
  exact (star_ne_zero).mpr ha

theorem kChain_of (hS : KcSmooth) (hC : ConeGL) (h1 : HalfOne) (h2 : HalfTwo) : KChain := by
  intro n lam E Fr ε ι S Γ T h σ hσ hσ2 k hk hkK hch d hd c
  refine ⟨hS n E.V σ c Fr k Γ T d hd hσ hσ2 h.smooth hk, ?_, ?_⟩
  · rintro ⟨v, w⟩ ⟨hv, hw⟩
    have hxv := (hC n σ hσ2 v hv).1
    have hxw := (hC n σ hσ2 w hw).1
    have hw0 : (σ v)⁻¹ * d * (σ w)ᴴ⁻¹ ∈ GLs n :=
      mem_GLs_mul (mem_GLs_mul (mem_GLs_inv hxv) hd) (mem_GLs_conjT_inv hxw)
    have e1 := h.ΓFr _ hxv
    have e2 := (hch _ hw0).1
    have e4 := h.ΓFr _ (mem_GLs_inv hxw)
    have e3 := h.ΓT
    simp only [Kc, Kf]
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    have hcm : Commute Γ (Fr (σ v) * k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) * Γ * T * Fr (σ w)⁻¹) :=
      ((((show Commute Γ (Fr (σ v)) from e1).mul_right (show Commute Γ (k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹)) from e2)).mul_right
        (Commute.refl Γ)).mul_right (show Commute Γ T from e3)).mul_right (show Commute Γ (Fr (σ w)⁻¹) from e4)
    exact hcm.eq
  · rintro ⟨v, w⟩ ⟨hv, hw⟩
    rw [h1 n lam E Fr ε ι S Γ T h σ hσ hσ2 k hk hkK d hd c v hv w hw,
      h2 n lam E Fr ε ι S Γ T h σ hσ hσ2 k hk hkK d hd c v hv w hw, ← smul_add]
    have hxv := (hC n σ hσ2 v hv).1
    have hxw := (hC n σ hσ2 w hw).1
    have hw0 : (σ v)⁻¹ * d * (σ w)ᴴ⁻¹ ∈ GLs n :=
      mem_GLs_mul (mem_GLs_mul (mem_GLs_inv hxv) hd) (mem_GLs_conjT_inv hxw)
    have hc := (hch _ hw0).2
    set w0 := (σ v)⁻¹ * d * (σ w)ᴴ⁻¹
    have hz : (∑ p, ε (hb p) * (fderiv ℝ Fr 1 (hb p) * k w0 + Ld (hb p) k w0)) +
        ∑ p, (Rd (hb p) k w0 * ε (hb p) - k w0 * ε (hb p) * fderiv ℝ Fr 1 (hb p)) = 0 := by
      have e : ∑ p, ε (hb p) * (fderiv ℝ Fr 1 (hb p) * k w0 + Ld (hb p) k w0) =
          ∑ p, ε (hb p) * (Ld (hb p) k w0 + fderiv ℝ Fr 1 (hb p) * k w0) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [add_comm]
      rw [e, hc, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun p _ => ?_
      simp only [neg_mul]
      abel
    rw [← add_mul, ← add_mul, ← add_mul, ← mul_add, ← smul_add, hz, smul_zero, mul_zero, zero_mul,
      zero_mul, zero_mul, smul_zero]

end PositivityTheory.RgBcC.LfSt.Kchain
end
end

section
noncomputable section

open Matrix Finset
open scoped ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.LfSt.Kchain.KcHalf1

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem hOf_single (i : Fin n × Fin n) : hOf (Pi.single i (1 : ℝ)) = hb i := by
  simp only [hOf]
  rw [Finset.sum_eq_single i]
  · simp
  · intro p _ hp
    simp [Pi.single_apply, hp]
  · simp

theorem herm_inv_conj {x H : Mat n} (hH : H.IsHermitian) : (x⁻¹ * H * xᴴ⁻¹).IsHermitian := by
  rw [← conjTranspose_nonsing_inv]
  exact isHermitian_mul_mul_conjTranspose _ hH

def phiL {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (Fr k : Mat n → (V →L[ℂ] V)) (w : Mat n) :
    Mat n →ₗ[ℝ] (V →L[ℂ] V) where
  toFun X := fderiv ℝ Fr 1 X * k w + Ld X k w
  map_add' X Y := by
    simp only [Ld, map_add, add_mul, Matrix.add_mul, neg_add]
    abel
  map_smul' r X := by
    simp only [Ld, map_smul, smul_mul_assoc, Matrix.smul_mul, RingHom.id_apply, smul_add, smul_neg]

private theorem smul_add_smul_mul_mul_smul_add_smul_of_mul_eq_zero (hH : HbFacts) {H : Mat n} (h : H.IsHermitian) :
    ∑ p, coords H p • hb p = H := by
  conv_rhs => rw [← (hH n).2.2.1 H h]
  unfold hOf
  refine Finset.sum_congr rfl fun p _ => ?_
  ext a b
  simp [Complex.real_smul]

private theorem trace_mul_mul_mul_rotate_two (a B c D : Mat n) : trace (a * B * c * D) = trace (c * D * a * B) := by
  rw [Matrix.mul_assoc (a * B) c D, Matrix.trace_mul_comm, ← Matrix.mul_assoc]

private theorem exists_dual_basis_dlog_of_isCoord (hH : HbFacts) {W : Type*} [Ring W] [Module ℝ W] [IsScalarTower ℝ W W]
    [SMulCommClass ℝ W W] (α β : Mat n →ₗ[ℝ] W) {x : Mat n} (hx : x.det ≠ 0) :
    ∑ i, α (xᴴ * hb i * x) * β (x⁻¹ * hb i * xᴴ⁻¹) = ∑ p, α (hb p) * β (hb p) := by
  have hbh : ∀ p, (hb p).IsHermitian := (hH n).1
  have hu : IsUnit x.det := isUnit_iff_ne_zero.mpr hx
  have huH : IsUnit xᴴ.det := by
    rw [det_conjTranspose]
    exact hu.star
  have hA' : ∀ i, (x⁻¹ * hb i * xᴴ⁻¹).IsHermitian := fun i => by
    rw [← conjTranspose_nonsing_inv]
    exact isHermitian_mul_mul_conjTranspose _ (hbh i)
  have hQ : ∀ q, (xᴴ⁻¹ * hb q * x⁻¹).IsHermitian := fun q => by
    rw [← conjTranspose_nonsing_inv]
    exact isHermitian_conjTranspose_mul_mul _ (hbh q)
  have hexp : ∀ i, β (x⁻¹ * hb i * xᴴ⁻¹) = ∑ q, coords (x⁻¹ * hb i * xᴴ⁻¹) q • β (hb q) := by
    intro i
    conv_lhs => rw [← smul_add_smul_mul_mul_smul_add_smul_of_mul_eq_zero hH (hA' i)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_smul]
  have hcoef : ∀ i q, coords (x⁻¹ * hb i * xᴴ⁻¹) q = coords (xᴴ⁻¹ * hb q * x⁻¹) i := by
    intro i q
    simp only [coords]
    rw [trace_mul_mul_mul_rotate_two]
  calc ∑ i, α (xᴴ * hb i * x) * β (x⁻¹ * hb i * xᴴ⁻¹)
      = ∑ i, ∑ q, coords (xᴴ⁻¹ * hb q * x⁻¹) i • (α (xᴴ * hb i * x) * β (hb q)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hexp i, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hcoef, mul_smul_comm]
    _ = ∑ q, ∑ i, coords (xᴴ⁻¹ * hb q * x⁻¹) i • (α (xᴴ * hb i * x) * β (hb q)) := Finset.sum_comm
    _ = ∑ q, α (∑ i, coords (xᴴ⁻¹ * hb q * x⁻¹) i • (xᴴ * hb i * x)) * β (hb q) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, smul_mul_assoc]
    _ = ∑ p, α (hb p) * β (hb p) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        have hs : ∑ i, coords (xᴴ⁻¹ * hb q * x⁻¹) i • (xᴴ * hb i * x)
            = xᴴ * (∑ i, coords (xᴴ⁻¹ * hb q * x⁻¹) i • hb i) * x := by
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Matrix.mul_smul, Matrix.smul_mul]
        rw [hs, smul_add_smul_mul_mul_smul_add_smul_of_mul_eq_zero hH (hQ q)]
        simp only [Matrix.mul_assoc]
        rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, ← Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ huH, Matrix.one_mul]

set_option maxHeartbeats 800000 in
theorem halfOne_of (hH : HbFacts) (hF : FrameDer) (hO : ∀ n, IsOpen (cone n)) (h1 : DerOne) : HalfOne := by
  intro n lam E Fr ε ι S Γ T hcx σ hσ hσh k hk hkeq d hd c v hv w hw
  obtain ⟨hxG, hdetv⟩ := KcInv.coneGL n σ hσh v hv
  obtain ⟨hyG, hdetw⟩ := KcInv.coneGL n σ hσh w hw
  set F : Mat n → (E.V →L[ℂ] E.V) := fun x' => Kf Fr k Γ T d x' (σ w) with hFdef
  have hFs : ContDiffOn ℝ ∞ F (GLs n) := by
    have hinner : ContDiffOn ℝ ∞ (fun x' : Mat n => x'⁻¹ * d * (σ w)ᴴ⁻¹) (GLs n) :=
      KcInv.mul_contDiffOn (KcInv.mul_contDiffOn KcInv.inv_contDiffOn contDiffOn_const)
        contDiffOn_const
    have hmaps : Set.MapsTo (fun x' : Mat n => x'⁻¹ * d * (σ w)ᴴ⁻¹) (GLs n) (GLs n) :=
      fun x' hx' => KcInv.mul_mem (KcInv.mul_mem (KcInv.inv_mem hx') hd)
        (KcInv.inv_mem (KcInv.conjT_mem hyG))
    have h2 := hk.comp hinner hmaps
    exact (((hcx.smooth.mul h2).mul contDiffOn_const).mul contDiffOn_const).mul contDiffOn_const
  have hFinv : ∀ x' ∈ GLs n, ∀ u : unitaryGroup (Fin n) ℂ, F (x' * ↑u) = F x' := by
    intro x' hx' u
    have hu1 : ((u⁻¹ : unitaryGroup (Fin n) ℂ) : Mat n) * (u : Mat n) = 1 := by simp
    have huG : (u : Mat n) ∈ GLs n := by
      show (u : Mat n).det ≠ 0
      intro h0
      have h3 := congrArg Matrix.det hu1
      rw [det_mul, h0, mul_zero, det_one] at h3
      exact zero_ne_one h3
    have hinvu : (u : Mat n)⁻¹ = ((u⁻¹ : unitaryGroup (Fin n) ℂ) : Mat n) :=
      Matrix.inv_eq_left_inv hu1
    have hmG : x'⁻¹ * d * (σ w)ᴴ⁻¹ ∈ GLs n :=
      KcInv.mul_mem (KcInv.mul_mem (KcInv.inv_mem hx') hd) (KcInv.inv_mem (KcInv.conjT_mem hyG))
    have hk' : k (((u⁻¹ : unitaryGroup (Fin n) ℂ) : Mat n) * x'⁻¹ * d * (σ w)ᴴ⁻¹)
        = E.ρ u⁻¹ * k (x'⁻¹ * d * (σ w)ᴴ⁻¹) := by
      have h := hkeq _ hmG u⁻¹ 1
      rw [show ((1 : unitaryGroup (Fin n) ℂ) : Mat n) = 1 from rfl, Matrix.mul_one, map_one,
        mul_one] at h
      rw [← h]
      simp only [Matrix.mul_assoc]
    simp only [hFdef, Kf]
    rw [hcx.mul x' hx' _ huG, hcx.onK u, Matrix.mul_inv_rev, hinvu, hk',
      ← mul_assoc (Fr x' * E.ρ u), mul_assoc (Fr x'), ← map_mul, mul_inv_cancel, map_one, mul_one]
  have hDσ : ContDiffOn ℝ ∞ (fun w' => F (σ w')) (cone n) :=
    hFs.comp hσ (fun v' hv' => (KcInv.coneGL n σ hσh v' hv').1)
  have hDσd : DifferentiableAt ℝ (fun w' => F (σ w')) v :=
    (hDσ.contDiffAt ((hO n).mem_nhds hv)).differentiableAt (by simp)
  have hKc : ∀ e, (fderiv ℝ (Kc σ c Fr k Γ T d) (v, w)) (e, 0)
      = ((c : ℂ) * ((hOf w).det ^ n)⁻¹) • (fderiv ℝ (fun w' => F (σ w')) v) e := by
    have hKs := KcInv.kcSmooth n E.V σ c Fr k Γ T d hd hσ hσh hcx.smooth hk
    have hmem : cone n ×ˢ cone n ∈ nhds (v, w) := ((hO n).prod (hO n)).mem_nhds ⟨hv, hw⟩
    have hKd : DifferentiableAt ℝ (Kc σ c Fr k Γ T d) (v, w) :=
      (hKs.contDiffAt hmem).differentiableAt (by simp)
    have h1 := hKd.hasFDerivAt.comp v (hasFDerivAt_prodMk_left (𝕜 := ℝ) v w)
    have h2 := hDσd.hasFDerivAt.const_smul ((c : ℂ) * ((hOf w).det ^ n)⁻¹)
    have heq : (Kc σ c Fr k Γ T d) ∘ (fun e => (e, w))
        = fun v' => ((c : ℂ) * ((hOf w).det ^ n)⁻¹) • F (σ v') := by
      funext v'
      rfl
    rw [heq] at h1
    intro e
    have h3 := congrArg (fun L => L e) (h1.unique h2)
    simpa using h3
  have hfr := hF n (E.V →L[ℂ] E.V) σ F hσ hσh hFs hFinv v hv (σ v) hxG (hσh v hv)
  set x := σ v with hxdef
  set y := σ w with hydef
  set m := x⁻¹ * d * yᴴ⁻¹ with hmdef
  set C : ℂ := (c : ℂ) * ((hOf w).det ^ n)⁻¹ with hCdef
  set φ := phiL Fr k m with hφ
  have hbh := (hH n).1
  have hstep : ∀ i, (fderiv ℝ (fun w' => F (σ w')) v) (Pi.single i 1)
      = (1/2 : ℝ) • (Fr x * φ (x⁻¹ * hb i * xᴴ⁻¹) * Γ * T * Fr y⁻¹) := by
    intro i
    have hXi : (x⁻¹ * hb i * xᴴ⁻¹).IsHermitian := herm_inv_conj (hbh i)
    have hxX : x * (x⁻¹ * hb i * xᴴ⁻¹) * xᴴ = hb i := by
      have hu : IsUnit x.det := isUnit_iff_ne_zero.mpr hxG
      have huH : IsUnit xᴴ.det := by
        rw [det_conjTranspose]
        exact hu.star
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul _ huH, Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
    have hc1 : coords (hb i) = Pi.single i 1 := by
      have h6 := (hH n).2.2.2.1 (Pi.single i 1)
      rwa [hOf_single] at h6
    have hc2 : coords (hb i + hb i) = Pi.single i 1 + Pi.single i 1 := by
      rw [← hc1]
      funext p
      simp only [coords, Matrix.add_mul, Matrix.trace_add, Complex.add_re, Pi.add_apply]
    have h5 := hfr _ hXi
    rw [hxX] at h5
    first
      | rw [two_smul] at h5
      | rw [two_nsmul] at h5
    rw [hc2, map_add] at h5
    have hder : (fderiv ℝ F x) (x * (x⁻¹ * hb i * xᴴ⁻¹))
        = Fr x * φ (x⁻¹ * hb i * xᴴ⁻¹) * Γ * T * Fr y⁻¹ :=
      h1 n lam E Fr ε ι S Γ T hcx k hk d y hd hyG x hxG _
    rw [hder] at h5
    rw [← h5, ← two_smul ℝ, smul_smul]
    norm_num
  have hfe : ∀ i, ε (hb i) * Fr x = Fr x * ε (xᴴ * hb i * x) :=
    fun i => hcx.frε x hxG (hb i) (hbh i)
  have hdual := exists_dual_basis_dlog_of_isCoord hH ε φ hxG
  rw [show (∑ i, ε (hb i) * (fderiv ℝ (Kc σ c Fr k Γ T d) (v, w)) (Pi.single i 1, 0))
      = ∑ i, ε (hb i) * (C • (1/2 : ℝ) • (Fr x * φ (x⁻¹ * hb i * xᴴ⁻¹) * Γ * T * Fr y⁻¹)) from
      Finset.sum_congr rfl fun i _ => by rw [hKc, hstep]]
  calc ∑ i, ε (hb i) * (C • (1/2 : ℝ) • (Fr x * φ (x⁻¹ * hb i * xᴴ⁻¹) * Γ * T * Fr y⁻¹))
      = C • (1/2 : ℝ) • (Fr x * (∑ i, ε (xᴴ * hb i * x) * φ (x⁻¹ * hb i * xᴴ⁻¹)) * Γ * T
          * Fr y⁻¹) := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.smul_sum,
          Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_smul_comm, mul_smul_comm]
        congr 2
        simp only [← mul_assoc]
        rw [hfe i]
    _ = _ := by
        rw [hdual, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc]
        congr 1
        rw [show ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.coe_smul]
        rfl

end PositivityTheory.RgBcC.LfSt.Kchain.KcHalf1
end
end

section
noncomputable section

open Matrix Finset
open scoped ContDiff ComplexOrder

namespace PositivityTheory.RgBcC.LfSt.Kchain.KcHalf2

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem real_smul_clm {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (r : ℝ) (f : V →L[ℂ] V) :
    r • f = (r : ℂ) • f := by
  ext v
  simp [Complex.coe_smul]

theorem trace_real {H : Mat n} (hH : H.IsHermitian) : ((H.trace.re : ℝ) : ℂ) = H.trace := by
  have h : star H.trace = H.trace := by
    rw [← Matrix.trace_conjTranspose, hH.eq]
  apply Complex.ext
  · simp
  · have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    simp only [Complex.ofReal_im]
    linarith

theorem eps_sum_trace (hH : HbFacts) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V)) : ∑ p, ((hb p : Mat n).trace) • ε (hb p) = ε 1 := by
  obtain ⟨hher, -, -, -, -, -, htr, -⟩ := hH n
  have e : ∑ p, ((hb p : Mat n).trace.re) • (hb p : Mat n) = 1 := by
    rw [← htr]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← trace_real (hher p)]
    ext a b
    simp [Complex.real_smul]
  rw [← e, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, real_smul_clm, trace_real (hher p)]

theorem eps_sum_sq (hH : HbFacts) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V)) : ∑ p, ε ((hb p : Mat n) * hb p + hb p * hb p) = ((2 * n : ℕ) : ℂ) • ε 1 := by
  obtain ⟨-, -, -, -, -, hsq, -, -⟩ := hH n
  rw [← map_sum, Finset.sum_add_distrib, hsq]
  have e : (n : ℂ) • (1 : Mat n) + (n : ℂ) • 1 = ((2 * n : ℕ) : ℝ) • (1 : Mat n) := by
    ext a b
    simp [Complex.real_smul]
    ring
  rw [e, map_smul, real_smul_clm]
  norm_cast

theorem gte {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
    {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V} (h : CxData lam E Fr ε ι S Γ T) (H : Mat n) (X : E.V →L[ℂ] E.V) :
    Γ * T * (ε H * X) = -(ε H * (Γ * T * X)) := by
  rw [← mul_assoc, mul_assoc Γ, h.Tε, ← mul_assoc, h.Γε]
  simp only [neg_mul, mul_assoc]

theorem algPsi (hH : HbFacts) (hc : FrComm) {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)}
    {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)} {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}
    (h : CxData lam E Fr ε ι S Γ T) (K0 : E.V →L[ℂ] E.V) (R : Mat n → (E.V →L[ℂ] E.V)) :
    ∑ p, ((((-(2 * n : ℂ)) * (hb p : Mat n).trace) • K0 * Γ * T - R (hb p) * Γ * T -
        K0 * Γ * T * fderiv ℝ Fr 1 (hb p)) * ε (hb p)) =
      (∑ p, (R (hb p) * ε (hb p) - K0 * ε (hb p) * fderiv ℝ Fr 1 (hb p))) * Γ * T := by
  obtain ⟨hher, -⟩ := hH n
  set D0 := ∑ p, ε (hb p) * fderiv ℝ Fr 1 (hb p) with hD0
  have hTD : T * D0 = -(D0 * T) := h.TD
  have hΓdF : ∀ p, Γ * fderiv ℝ Fr 1 (hb p) = fderiv ℝ Fr 1 (hb p) * Γ := fun p =>
    (hc n lam E Fr ε ι S Γ T h (hb p) (hb p) (hher p) (hher p)).2
  have hΓD : Γ * D0 = -(D0 * Γ) := by
    rw [hD0, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← mul_assoc, h.Γε, neg_mul, mul_assoc, hΓdF p, ← mul_assoc]
  have hGTD : Γ * T * D0 = D0 * (Γ * T) := by
    rw [mul_assoc, hTD, mul_neg, ← mul_assoc, hΓD, neg_mul, neg_neg, mul_assoc]
  have hcomm : ∀ p, fderiv ℝ Fr 1 (hb p) * ε (hb p) =
      ε (hb p) * fderiv ℝ Fr 1 (hb p) - ε ((hb p : Mat n) * hb p + hb p * hb p) := fun p =>
    (hc n lam E Fr ε ι S Γ T h (hb p) (hb p) (hher p) (hher p)).1

  have hs : ∀ p, (((-(2 * n : ℂ)) * (hb p : Mat n).trace) • K0 * Γ * T - R (hb p) * Γ * T -
        K0 * Γ * T * fderiv ℝ Fr 1 (hb p)) * ε (hb p) =
      (R (hb p) * ε (hb p) - K0 * ε (hb p) * fderiv ℝ Fr 1 (hb p)) * Γ * T +
        (K0 * (ε (hb p) * fderiv ℝ Fr 1 (hb p)) * (Γ * T) - K0 * (Γ * T * (ε (hb p) * fderiv ℝ Fr 1 (hb p)))) +
        (-(K0 * ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • ε (hb p) * (Γ * T)) -
          K0 * ε ((hb p : Mat n) * hb p + hb p * hb p) * (Γ * T)) := by
    intro p
    have e1 : Γ * T * ε (hb p) = -(ε (hb p) * (Γ * T)) := by
      have := gte h (hb p) 1
      simpa using this
    have e2 : Γ * T * ε ((hb p : Mat n) * hb p + hb p * hb p) =
        -(ε ((hb p : Mat n) * hb p + hb p * hb p) * (Γ * T)) := by
      have := gte h ((hb p : Mat n) * hb p + hb p * hb p) 1
      simpa using this
    have lhs : (((-(2 * n : ℂ)) * (hb p : Mat n).trace) • K0 * Γ * T - R (hb p) * Γ * T -
        K0 * Γ * T * fderiv ℝ Fr 1 (hb p)) * ε (hb p) =
        ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • (K0 * (Γ * T * ε (hb p))) - R (hb p) * (Γ * T * ε (hb p)) -
          K0 * (Γ * T * (fderiv ℝ Fr 1 (hb p) * ε (hb p))) := by
      simp only [sub_mul, smul_mul_assoc, mul_assoc]
    rw [lhs, e1, hcomm p, mul_sub (Γ * T), e2]
    simp only [mul_neg, neg_mul, smul_neg, mul_sub, sub_mul, mul_assoc, mul_smul_comm, smul_mul_assoc]
    abel
  rw [Finset.sum_congr rfl fun p _ => hs p, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have z1 : ∑ p, (K0 * (ε (hb p) * fderiv ℝ Fr 1 (hb p)) * (Γ * T) -
      K0 * (Γ * T * (ε (hb p) * fderiv ℝ Fr 1 (hb p)))) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← hD0,
      hGTD, mul_assoc, sub_self]
  have z2 : ∑ p, (-(K0 * ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • ε (hb p) * (Γ * T)) -
      K0 * ε ((hb p : Mat n) * hb p + hb p * hb p) * (Γ * T)) = 0 := by
    have s1 : ∑ p, ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • ε (hb p) = (-(2 * n : ℂ)) • ε 1 := by
      rw [← eps_sum_trace hH ε, Finset.smul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [mul_smul]
    have s2 := eps_sum_sq hH ε
    have : ∑ p, (-(K0 * ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • ε (hb p) * (Γ * T)) -
        K0 * ε ((hb p : Mat n) * hb p + hb p * hb p) * (Γ * T)) =
        -(K0 * (∑ p, ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • ε (hb p)) * (Γ * T)) -
          K0 * (∑ p, ε ((hb p : Mat n) * hb p + hb p * hb p)) * (Γ * T) := by
      rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum,
        Finset.sum_mul]
    rw [this, s1, s2]
    push_cast
    simp only [mul_neg, neg_mul, neg_neg, mul_smul_comm, smul_mul_assoc, neg_smul, sub_self]
  rw [z1, z2, add_zero, add_zero, Finset.sum_mul, Finset.sum_mul]

theorem partial_snd {A B Z : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (f : A × B → Z) (a : A) (b : B) (hf : DifferentiableAt ℝ f (a, b)) (h : B) :
    fderiv ℝ f (a, b) (0, h) = fderiv ℝ (fun b' => f (a, b')) b h := by
  have := hf.hasFDerivAt.comp b (hasFDerivAt_prodMk_right a b)
  have e : (fun b' => f (a, b')) = f ∘ Prod.mk a := rfl
  rw [e, this.fderiv]
  simp

theorem hOf_single (i : Fin n × Fin n) : hOf (Pi.single i (1 : ℝ)) = (hb i : Mat n) := by
  unfold hOf
  rw [Finset.sum_eq_single i]
  · simp
  · intro p _ hp
    simp [Pi.single_apply, hp]
  · simp

theorem unit_of {y : Mat n} (hy : y ∈ GLs n) : IsUnit y.det := isUnit_iff_ne_zero.mpr hy

theorem isOpen_cone (hH : HbFacts) : IsOpen (cone n) := PositivityTheory.KcHalf2₂.isOpen_cone_of_hbFacts hH

section Main

variable {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
  {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}

theorem frInv (h : CxData lam E Fr ε ι S Γ T) {y : Mat n} (hy : y ∈ GLs n) :
    Fr y⁻¹ * Fr y = 1 ∧ Fr y * Fr y⁻¹ = 1 := by
  constructor
  · rw [← h.mul _ (KcInv.inv_mem hy) _ hy, Matrix.nonsing_inv_mul _ (unit_of hy), h.one]
  · rw [← h.mul _ hy _ (KcInv.inv_mem hy), Matrix.mul_nonsing_inv _ (unit_of hy), h.one]

theorem frInvEps (h : CxData lam E Fr ε ι S Γ T) {y : Mat n} (hy : y ∈ GLs n) {H : Mat n} (hH : H.IsHermitian) :
    Fr y⁻¹ * ε H = ε (yᴴ * H * y) * Fr y⁻¹ := by
  have e := h.frε y hy H hH
  calc Fr y⁻¹ * ε H = Fr y⁻¹ * ε H * (Fr y * Fr y⁻¹) := by rw [(frInv h hy).2, mul_one]
    _ = Fr y⁻¹ * (ε H * Fr y) * Fr y⁻¹ := by simp only [mul_assoc]
    _ = Fr y⁻¹ * (Fr y * ε (yᴴ * H * y)) * Fr y⁻¹ := by rw [e]
    _ = ε (yᴴ * H * y) * Fr y⁻¹ := by rw [← mul_assoc (Fr y⁻¹), (frInv h hy).1, one_mul]

def Gf (Fr k : Mat n → (E.V →L[ℂ] E.V)) (Γ T : E.V →L[ℂ] E.V) (c : ℝ) (d x : Mat n) : Mat n → (E.V →L[ℂ] E.V) :=
  fun y' => wt c y' • Kf Fr k Γ T d x y'

theorem Gf_smooth (h : CxData lam E Fr ε ι S Γ T) {k : Mat n → (E.V →L[ℂ] E.V)} (hk : ContDiffOn ℝ ∞ k (GLs n))
    (c : ℝ) {d x : Mat n} (hd : d ∈ GLs n) (hx : x ∈ GLs n) : ContDiffOn ℝ ∞ (Gf Fr k Γ T c d x) (GLs n) := by
  have hW : ContDiffOn ℝ ∞ (fun y' : Mat n => wt c y') (GLs n) := by
    unfold wt
    refine contDiffOn_const.mul (ContDiffOn.inv ?_ fun y hy => pow_ne_zero _ ?_)
    · exact (KcInv.det_contDiff.comp_contDiffOn (KcInv.mul_contDiffOn contDiffOn_id
        KcInv.star_contDiff.contDiffOn)).pow n
    · exact KcInv.mul_mem hy (KcInv.conjT_mem hy)
  have harg : ContDiffOn ℝ ∞ (fun y' : Mat n => x⁻¹ * d * y'ᴴ⁻¹) (GLs n) :=
    KcInv.mul_contDiffOn contDiffOn_const
      (KcInv.inv_contDiffOn.comp KcInv.star_contDiff.contDiffOn fun y hy => KcInv.conjT_mem hy)
  have hargm : ∀ y' ∈ GLs n, x⁻¹ * d * y'ᴴ⁻¹ ∈ GLs n := fun y' hy' =>
    KcInv.mul_mem (KcInv.mul_mem (KcInv.inv_mem hx) hd) (KcInv.inv_mem (KcInv.conjT_mem hy'))
  have hK : ContDiffOn ℝ ∞ (fun y' => Kf Fr k Γ T d x y') (GLs n) := by
    unfold Kf
    exact ContDiffOn.mul (ContDiffOn.mul (ContDiffOn.mul (ContDiffOn.mul contDiffOn_const (hk.comp harg hargm))
      contDiffOn_const) contDiffOn_const) (h.smooth.comp KcInv.inv_contDiffOn fun y hy => KcInv.inv_mem hy)
  exact hW.smul hK

theorem Gf_inv (h : CxData lam E Fr ε ι S Γ T) {k : Mat n → (E.V →L[ℂ] E.V)}
    (hkK : ∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂)
    (c : ℝ) {d x : Mat n} (hd : d ∈ GLs n) (hx : x ∈ GLs n) :
    ∀ y ∈ GLs n, ∀ u : Matrix.unitaryGroup (Fin n) ℂ, Gf Fr k Γ T c d x (y * u.1) = Gf Fr k Γ T c d x y := by
  intro y hy u
  have hu1 : u.1 * star u.1 = 1 := (Matrix.mem_unitaryGroup_iff.mp u.2)
  have hu2 : star u.1 * u.1 = 1 := (Matrix.mem_unitaryGroup_iff'.mp u.2)
  have hsu : star u.1 = u.1ᴴ := rfl
  have huG : u.1 ∈ GLs n := by
    show u.1.det ≠ 0
    intro h0
    have := congrArg Matrix.det hu2
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hsuG : star u.1 ∈ GLs n := by rw [hsu]; exact KcInv.conjT_mem huG
  have e1 : (y * u.1) * (y * u.1)ᴴ = y * yᴴ := by
    rw [Matrix.conjTranspose_mul, ← hsu, Matrix.mul_assoc, ← Matrix.mul_assoc u.1, hu1, Matrix.one_mul]
  have e2 : (y * u.1)ᴴ⁻¹ = yᴴ⁻¹ * u.1 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_inv_rev, ← hsu, Matrix.inv_eq_left_inv hu1]
  have e3 : (y * u.1)⁻¹ = star u.1 * y⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hu2]
  have hw : x⁻¹ * d * yᴴ⁻¹ ∈ GLs n :=
    KcInv.mul_mem (KcInv.mul_mem (KcInv.inv_mem hx) hd) (KcInv.inv_mem (KcInv.conjT_mem hy))
  have ek : k (x⁻¹ * d * (y * u.1)ᴴ⁻¹) = k (x⁻¹ * d * yᴴ⁻¹) * E.ρ u := by
    have := hkK _ hw 1 u
    rw [Submonoid.coe_one, Matrix.one_mul, map_one, one_mul] at this
    rw [e2, ← Matrix.mul_assoc, this]
  have ef : Fr (y * u.1)⁻¹ = E.ρ u⁻¹ * Fr y⁻¹ := by
    rw [e3, h.mul _ hsuG _ (KcInv.inv_mem hy)]
    congr 1
    rw [← h.onK]
    congr 1
  have hρΓ : E.ρ u * Γ = Γ * E.ρ u := by rw [← h.onK]; exact (h.ΓFr _ huG).symm
  have hρT : E.ρ u * T = T * E.ρ u := (h.TK u).symm
  have hρρ : E.ρ u * E.ρ u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  unfold Gf wt Kf
  rw [e1, ek, ef]
  congr 1
  calc Fr x * (k (x⁻¹ * d * yᴴ⁻¹) * E.ρ u) * Γ * T * (E.ρ u⁻¹ * Fr y⁻¹)
      = Fr x * k (x⁻¹ * d * yᴴ⁻¹) * (E.ρ u * Γ) * T * (E.ρ u⁻¹ * Fr y⁻¹) := by simp only [mul_assoc]
    _ = Fr x * k (x⁻¹ * d * yᴴ⁻¹) * Γ * (E.ρ u * T) * (E.ρ u⁻¹ * Fr y⁻¹) := by rw [hρΓ]; simp only [mul_assoc]
    _ = Fr x * k (x⁻¹ * d * yᴴ⁻¹) * Γ * T * ((E.ρ u * E.ρ u⁻¹) * Fr y⁻¹) := by rw [hρT]; simp only [mul_assoc]
    _ = Fr x * k (x⁻¹ * d * yᴴ⁻¹) * Γ * T * Fr y⁻¹ := by rw [hρρ, one_mul]

end Main

def psiL {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (K0 : V →L[ℂ] V) (Dk DF : Mat n →L[ℝ] (V →L[ℂ] V))
    (w0 : Mat n) (Γ T : V →L[ℂ] V) : Mat n →ₗ[ℝ] (V →L[ℂ] V) where
  toFun X := ((-(2 * n : ℂ)) * X.trace) • K0 * Γ * T - Dk (w0 * X) * Γ * T - K0 * Γ * T * DF X
  map_add' X Y := by
    simp only [Matrix.trace_add, mul_add, add_smul, add_mul, Matrix.mul_add, map_add]
    abel
  map_smul' r X := by
    simp only [Matrix.trace_smul, Matrix.mul_smul, map_smul, RingHom.id_apply]
    rw [real_smul_clm r (Dk (w0 * X)), real_smul_clm r (DF X), real_smul_clm r]
    have e : ((-(2 * n : ℂ)) * (r • X.trace)) = (r : ℂ) * ((-(2 * n : ℂ)) * X.trace) := by
      rw [Complex.real_smul]; ring
    rw [e, mul_smul]
    simp only [smul_mul_assoc, mul_smul_comm, smul_sub]

theorem conjT_inv_inv {y : Mat n} : (yᴴ⁻¹)ᴴ = y⁻¹ := by
  rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose]

theorem halfTwo_of (hH : HbFacts) (hF : FrameDer) (hc : FrComm) (h2 : DerTwo) (hD : DualSum) : HalfTwo := by
  intro n lam E Fr ε ι S Γ T h σ hσs hσ k hk hkK d hd c v hv w hw
  obtain ⟨hher, horth, -, hcoV, -, -, -, -⟩ := hH n
  have hgl := KcInv.coneGL n σ hσ
  have hx : σ v ∈ GLs n := (hgl v hv).1
  have hy : σ w ∈ GLs n := (hgl w hw).1
  have hyu : IsUnit (σ w).det := unit_of hy
  have hyHu : IsUnit (σ w)ᴴ.det := unit_of (KcInv.conjT_mem hy)
  have hKs := KcInv.kcSmooth n E.V σ c Fr k Γ T d hd hσs hσ h.smooth hk
  have hop : IsOpen (cone n) := isOpen_cone hH
  have hmem : (v, w) ∈ cone n ×ˢ cone n := ⟨hv, hw⟩
  have hnh : cone n ×ˢ cone n ∈ nhds (v, w) := (hop.prod hop).mem_nhds hmem
  have hca : ContDiffAt ℝ ∞ (Kc σ c Fr k Γ T d) (v, w) := hKs.contDiffAt hnh
  have hdiff : DifferentiableAt ℝ (Kc σ c Fr k Γ T d) (v, w) := hca.differentiableAt (by norm_num)
  set Ψ := psiL (k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹)) (fderiv ℝ k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹)) (fderiv ℝ Fr 1)
    ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) Γ T with hΨ
  set A : Fin n × Fin n → Mat n := fun i => (σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹ with hA
  set A' : Fin n × Fin n → Mat n := fun i => (σ w)ᴴ * hb i * σ w with hA'
  have hAh : ∀ i, (A i).IsHermitian := fun i => by
    show ((σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹)ᴴ = (σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, conjT_inv_inv, (hher i).eq,
      Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
  have hA'h : ∀ i, (A' i).IsHermitian := fun i => by
    show ((σ w)ᴴ * hb i * σ w)ᴴ = (σ w)ᴴ * hb i * σ w
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, (hher i).eq,
      Matrix.mul_assoc]
  have htr : ∀ i j, (A i * A' j).trace = if i = j then 1 else 0 := fun i j => by
    show ((σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹ * ((σ w)ᴴ * hb j * σ w)).trace = _
    have e : (σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹ * ((σ w)ᴴ * hb j * σ w) = (σ w)⁻¹ * (hb i * hb j * σ w) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((σ w)ᴴ⁻¹), Matrix.nonsing_inv_mul _ hyHu, Matrix.one_mul]
    rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hyu, Matrix.mul_one, horth]
  have hpart : ∀ i, fderiv ℝ (Kc σ c Fr k Γ T d) (v, w) (0, Pi.single i 1) =
      wt c (σ w) • (Fr (σ v) * Ψ ((1 / 2 : ℝ) • A i) * Fr (σ w)⁻¹) := by
    intro i
    rw [partial_snd _ v w hdiff]
    have heq : (fun w' => Kc σ c Fr k Γ T d (v, w')) =ᶠ[nhds w] fun w' => Gf Fr k Γ T c d (σ v) (σ w') := by
      filter_upwards [hop.mem_nhds hw] with w' hw'
      simp only [Kc, Gf, wt]
      rw [hσ w' hw']
    rw [heq.fderiv_eq]
    have hXh : ((1 / 2 : ℝ) • A i).IsHermitian := by
      show ((1 / 2 : ℝ) • A i)ᴴ = (1 / 2 : ℝ) • A i
      rw [Matrix.conjTranspose_smul, (hAh i).eq]
      simp
    have hdir : coords ((2 : ℂ) • (σ w * ((1 / 2 : ℝ) • A i) * (σ w)ᴴ)) = Pi.single i 1 := by
      have e : (2 : ℂ) • (σ w * ((1 / 2 : ℝ) • A i) * (σ w)ᴴ) = hb i := by
        show (2 : ℂ) • (σ w * ((1 / 2 : ℝ) • ((σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹)) * (σ w)ᴴ) = hb i
        rw [Matrix.mul_smul, Matrix.smul_mul]
        have e2 : σ w * ((σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹) * (σ w)ᴴ = hb i := by
          simp only [Matrix.mul_assoc]
          rw [Matrix.nonsing_inv_mul _ hyHu, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hyu,
            Matrix.one_mul]
        rw [e2]
        ext a b
        simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
        push_cast
        ring
      rw [e, ← hOf_single, hcoV]
    have hFD := hF n (E.V →L[ℂ] E.V) σ (Gf Fr k Γ T c d (σ v)) hσs hσ (Gf_smooth h hk c hd hx)
      (Gf_inv h hkK c hd hx) w hw (σ w) hy (hσ w hw) _ hXh
    rw [hdir] at hFD
    rw [hFD]
    exact h2 n lam E Fr ε ι S Γ T h k hk c d (σ v) hd hx (σ w) hy _ hXh
  have hsum : ∑ i, fderiv ℝ (Kc σ c Fr k Γ T d) (v, w) (0, Pi.single i 1) * ε (hb i) =
      wt c (σ w) • (Fr (σ v) * ((1 / 2 : ℂ) • ∑ i, Ψ (A i) * ε (A' i)) * Fr (σ w)⁻¹) := by
    rw [Finset.smul_sum, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hpart i, map_smul, real_smul_clm, smul_mul_assoc]
    congr 1
    rw [mul_assoc (Fr (σ v) * _) (Fr (σ w)⁻¹), frInvEps h hy (hher i), ← mul_assoc, mul_assoc (Fr (σ v)),
      smul_mul_assoc]
    have hc2 : (((1 / 2 : ℝ)) : ℂ) = (1 / 2 : ℂ) := by norm_num
    rw [hc2]
  rw [hsum, hD n E.V Ψ ε A A' hAh hA'h htr]
  have halg := algPsi hH hc h (k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹)) (fun X => Rd X k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹))
  have e : ∑ p, Ψ (hb p) * ε (hb p) =
      (∑ p, (Rd (hb p) k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) * ε (hb p) -
        k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) * ε (hb p) * fderiv ℝ Fr 1 (hb p))) * Γ * T := halg
  rw [e]
  have hwt : wt c (σ w) = (c : ℂ) * ((hOf w).det ^ n)⁻¹ := by simp only [wt]; rw [hσ w hw]
  rw [hwt]
  simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]

end PositivityTheory.RgBcC.LfSt.Kchain.KcHalf2
end
end

section
noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.Kchain.KbBase

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def entL (a b : Fin n) : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)

theorem contDiff_entry (a b : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y a b) := (entL a b).contDiff

theorem contDiffAt_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → Mat n} {x : E}
    (h : ∀ a b, ContDiffAt ℝ ∞ (fun z => F z a b) x) : ContDiffAt ℝ ∞ F x :=
  contDiffAt_pi' fun a => contDiffAt_pi' fun b => h a b

theorem contDiff_det_of {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → Mat n)
    (h : ∀ a b, ContDiff ℝ ∞ (fun z => F z a b)) : ContDiff ℝ ∞ (fun z => (F z).det) := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)

theorem contDiff_det : ContDiff ℝ ∞ (fun y : Mat n => y.det) := contDiff_det_of id fun a b => contDiff_entry a b

theorem contDiffAt_inv {x : Mat n} (hx : x.det ≠ 0) : ContDiffAt ℝ ∞ (fun y : Mat n => y⁻¹) x := by
  refine contDiffAt_of_entries fun a b => ?_
  have e : (fun y : Mat n => y⁻¹ a b) = fun y => (y.det)⁻¹ * (y.updateRow b (Pi.single a 1)).det := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', Matrix.adjugate_apply]
  rw [e]
  refine (contDiff_det.contDiffAt.inv hx).mul (contDiff_det_of _ fun i j => ?_).contDiffAt
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_entry _ _

end PositivityTheory.RgBcC.LfSt.Kchain.KbBase
end
end

section
noncomputable section

open Matrix Finset Filter
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.Kchain.KbCurve

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain.KbBase
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem hasDerivAt_entry {A : ℝ → Mat n} {A' : Mat n} {t : ℝ} (h : HasDerivAt A A' t) (a b : Fin n) :
    HasDerivAt (fun s => A s a b) (A' a b) t :=
  hasDerivAt_pi.1 (hasDerivAt_pi.1 h a) b

theorem hasDerivAt_of_entry {A : ℝ → Mat n} {A' : Mat n} {t : ℝ} (h : ∀ a b, HasDerivAt (fun s => A s a b) (A' a b) t) :
    HasDerivAt A A' t :=
  hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => h a b

theorem hasDerivAt_matmul {A B : ℝ → Mat n} {A' B' : Mat n} {t : ℝ} (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s => A s * B s) (A' * B t + A t * B') t := by
  apply hasDerivAt_of_entry
  intro a b
  have hsum : HasDerivAt (fun s => ∑ k, A s a k * B s k b)
      (∑ k, (A' a k * B t k b + A t a k * B' k b)) t :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_entry hA a k).mul (hasDerivAt_entry hB k b)
  simpa [Matrix.mul_apply, Finset.sum_add_distrib] using hsum

theorem hasDerivAt_line (X : Mat n) : HasDerivAt (fun t : ℝ => 1 + t • X) X 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : Mat n)
  simp only [id, one_smul] at h
  exact h

theorem det_line_ne (X : Mat n) : ∀ᶠ t : ℝ in 𝓝 0, (1 + t • X).det ≠ 0 := by
  have hc : Continuous fun t : ℝ => (1 + t • X).det :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have h0 : (1 + (0:ℝ) • X).det ≠ 0 := by simp
  exact hc.continuousAt.eventually_ne h0

theorem hasDerivAt_lineInv (X : Mat n) : HasDerivAt (fun t : ℝ => (1 + t • X)⁻¹) (-X) 0 := by
  set B : ℝ → Mat n := fun t => (1 + t • X)⁻¹ with hB
  have hB0 : B 0 = 1 := by simp [hB]
  have hcont : ContinuousAt B 0 := by
    have hline : Continuous fun t : ℝ => (1 : Mat n) + t • X :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hdet : ContinuousAt Ring.inverse ((1 : Mat n) + (0:ℝ) • X).det := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ (by simp)
    have h2 : ContinuousAt (fun t : ℝ => (1 : Mat n) + t • X) 0 := hline.continuousAt
    exact ContinuousAt.comp (g := Inv.inv) (f := fun t : ℝ => (1 : Mat n) + t • X)
      (continuousAt_matrix_inv _ hdet) h2
  have hlim : Tendsto (fun t => -(B t * X)) (𝓝[≠] (0:ℝ)) (𝓝 (-X)) := by
    have h1 : Tendsto (fun t => -(B t * X)) (𝓝 (0:ℝ)) (𝓝 (-(B 0 * X))) :=
      ((hcont.mul continuousAt_const).neg)
    rw [hB0, one_mul] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  refine hasDerivAt_iff_tendsto_slope.mpr (hlim.congr' ?_)
  have hne : ∀ᶠ t in 𝓝[≠] (0:ℝ), (1 + t • X).det ≠ 0 :=
    (det_line_ne X).filter_mono nhdsWithin_le_nhds
  filter_upwards [hne, self_mem_nhdsWithin] with t ht ht0
  have hinv : B t * (1 + t • X) = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht)
  rw [mul_add, mul_one, Matrix.mul_smul] at hinv
  have ht0' : t ≠ 0 := ht0
  rw [slope_def_module, hB0, sub_zero, ← hinv, sub_add_cancel_left, smul_neg, smul_smul,
    inv_mul_cancel₀ ht0', one_smul]

theorem hasDerivAt_detLine (X : Mat n) : HasDerivAt (fun t : ℝ => (1 + t • X).det) X.trace 0 := by
  set p : Polynomial ℂ := (1 + (Polynomial.X : Polynomial ℂ) • X.map Polynomial.C).det with hp
  have hev : ∀ t : ℝ, (1 + t • X).det = p.eval (t : ℂ) := by
    intro t
    rw [hp, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, Complex.real_smul] <;> ring
  have hd : HasDerivAt (fun y : ℝ => p.eval (y : ℂ)) (p.derivative.eval ((0:ℝ) : ℂ)) 0 :=
    (p.hasDerivAt ((0:ℝ) : ℂ)).comp_ofReal
  rw [Complex.ofReal_zero, hp, Matrix.derivative_det_one_add_X_smul] at hd
  rw [show (fun t : ℝ => (1 + t • X).det) = fun y : ℝ => p.eval (y : ℂ) from funext hev]
  exact hd

end PositivityTheory.RgBcC.LfSt.Kchain.KbCurve
end
end

section
noncomputable section

open Matrix Finset Filter
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.Kchain.KbFr

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain PositivityTheory.RgBcC.LfSt.Kchain.KbBase
  PositivityTheory.RgBcC.LfSt.Kchain.KbCurve
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem isOpen_GLs' : IsOpen (GLs n) :=
  isOpen_compl_singleton.preimage (contDiff_det (n := n)).continuous

theorem line_mem (X : Mat n) : ∀ᶠ t : ℝ in 𝓝 0, 1 + t • X ∈ GLs n := det_line_ne X

theorem hasDerivAt_fderiv_line {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {F : Mat n → Z} {x : Mat n}
    (hF : DifferentiableAt ℝ F x) (v : Mat n) : HasDerivAt (fun t : ℝ => F (x + t • v)) (fderiv ℝ F x v) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    simp only [id, one_smul] at h
    exact h
  exact hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)

theorem diffAt_of {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {F : Mat n → Z} (hF : ContDiffOn ℝ ∞ F (GLs n))
    {x : Mat n} (hx : x ∈ GLs n) : DifferentiableAt ℝ F x :=
  ((hF.contDiffAt (isOpen_GLs'.mem_nhds hx)).differentiableAt (by simp))

theorem one_mem : (1 : Mat n) ∈ GLs n := by simp [GLs]

section

variable {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
  {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}

theorem hasDerivAt_Fr_line (h : CxData lam E Fr ε ι S Γ T) (Y : Mat n) :
    HasDerivAt (fun t : ℝ => Fr (1 + t • Y)) (fderiv ℝ Fr 1 Y) 0 :=
  hasDerivAt_fderiv_line (diffAt_of h.smooth one_mem) Y

theorem conjT_line {X : Mat n} (hX : X.IsHermitian) (t : ℝ) : (1 + t • X)ᴴ = 1 + t • X := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hX.eq]
  simp

theorem frComm_at (h : CxData lam E Fr ε ι S Γ T) {X H : Mat n} (hX : X.IsHermitian) (hH : H.IsHermitian) :
    fderiv ℝ Fr 1 X * ε H = ε H * fderiv ℝ Fr 1 X - ε (X * H + H * X) ∧ Γ * fderiv ℝ Fr 1 X = fderiv ℝ Fr 1 X * Γ := by
  have hF := hasDerivAt_Fr_line h X
  constructor
  · set εc : Mat n →L[ℝ] (E.V →L[ℂ] E.V) := LinearMap.toContinuousLinearMap ε
    have hM : HasDerivAt (fun t : ℝ => (1 + t • X) * H * (1 + t • X)) (X * H + H * X) 0 := by
      have := hasDerivAt_matmul (hasDerivAt_matmul (hasDerivAt_line X) (hasDerivAt_const (0 : ℝ) H)) (hasDerivAt_line X)
      refine this.congr_deriv ?_
      simp
    have hE : HasDerivAt (fun t : ℝ => ε ((1 + t • X) * H * (1 + t • X))) (ε (X * H + H * X)) 0 :=
      εc.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hM
    have hR := hF.mul hE
    have hL := hF.const_mul (ε H)
    have e : ∀ᶠ t : ℝ in 𝓝 0, ε H * Fr (1 + t • X) = Fr (1 + t • X) * ε ((1 + t • X) * H * (1 + t • X)) := by
      filter_upwards [line_mem X] with t ht
      have := h.frε _ ht H hH
      rwa [conjT_line hX] at this
    have hL' := hL.congr_of_eventuallyEq (e.mono fun t ht => ht.symm)
    have u := hL'.unique hR
    simp only [zero_smul, add_zero, h.one, one_mul, Matrix.mul_one] at u
    rw [u]; abel
  · have hL := hF.const_mul Γ
    have hR := hF.mul_const Γ
    have e : ∀ᶠ t : ℝ in 𝓝 0, Γ * Fr (1 + t • X) = Fr (1 + t • X) * Γ := by
      filter_upwards [line_mem X] with t ht
      exact h.ΓFr _ ht
    exact (hL.congr_of_eventuallyEq (e.mono fun t ht => ht.symm)).unique hR

end

theorem frComm : FrComm := fun _ _ _ _ _ _ _ _ _ h _X _H hX hH => frComm_at h hX hH

end PositivityTheory.RgBcC.LfSt.Kchain.KbFr
end
end

section
noncomputable section

open Matrix Finset Filter
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.Kchain.KbDer

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain PositivityTheory.RgBcC.LfSt.Kchain.KbBase
  PositivityTheory.RgBcC.LfSt.Kchain.KbCurve PositivityTheory.RgBcC.LfSt.Kchain.KbFr
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiffAt_mat {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : E → Mat n} {x : E}
    (h : ContDiffAt ℝ ∞ A x) (a b : Fin n) : ContDiffAt ℝ ∞ (fun z => A z a b) x :=
  (entL a b).contDiff.contDiffAt.comp x h

theorem contDiffAt_matmul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A B : E → Mat n} {x : E}
    (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x) : ContDiffAt ℝ ∞ (fun z => A z * B z) x := by
  refine contDiffAt_of_entries fun a b => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun c _ => (contDiffAt_mat hA a c).mul (contDiffAt_mat hB c b)

theorem contDiff_conjT : ContDiff ℝ ∞ (fun y : Mat n => yᴴ) := by
  refine contDiff_iff_contDiffAt.2 fun x => contDiffAt_of_entries fun a b => ?_
  simp only [Matrix.conjTranspose_apply]
  exact (Complex.conjCLE.contDiff.comp (contDiff_entry b a)).contDiffAt

theorem inv_mem {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n := by
  show (x⁻¹).det ≠ 0
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero hx

theorem conjT_mem {x : Mat n} (hx : x ∈ GLs n) : xᴴ ∈ GLs n := by
  show (xᴴ).det ≠ 0
  rw [Matrix.det_conjTranspose]
  exact star_ne_zero.2 hx

theorem mul_mem {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  show (x * y).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero hx hy

section

variable {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
  {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}

theorem derOne_at (h : CxData lam E Fr ε ι S Γ T) {k : Mat n → (E.V →L[ℂ] E.V)} (hk : ContDiffOn ℝ ∞ k (GLs n))
    {d y : Mat n} (hd : d ∈ GLs n) (hy : y ∈ GLs n) {x : Mat n} (hx : x ∈ GLs n) (X : Mat n) :
    fderiv ℝ (fun x' => Kf Fr k Γ T d x' y) x (x * X) =
      Fr x * (fderiv ℝ Fr 1 X * k (x⁻¹ * d * yᴴ⁻¹) + Ld X k (x⁻¹ * d * yᴴ⁻¹)) * Γ * T * Fr y⁻¹ := by
  set w := x⁻¹ * d * yᴴ⁻¹ with hwdef
  have hw : w ∈ GLs n := mul_mem (mul_mem (inv_mem hx) hd) (inv_mem (conjT_mem hy))
  have hkw : DifferentiableAt ℝ k w := diffAt_of hk hw
  have hg : ContDiffAt ℝ ∞ (fun x' : Mat n => x'⁻¹ * d * yᴴ⁻¹) x :=
    contDiffAt_matmul (contDiffAt_matmul (contDiffAt_inv hx) contDiffAt_const) contDiffAt_const
  have hdiff : DifferentiableAt ℝ (fun x' => Kf Fr k Γ T d x' y) x := by
    unfold Kf
    have h1 : DifferentiableAt ℝ (fun x' : Mat n => k (x'⁻¹ * d * yᴴ⁻¹)) x :=
      hkw.comp x (hg.differentiableAt (by simp))
    exact ((((diffAt_of h.smooth hx).mul h1).mul_const Γ).mul_const T).mul_const (Fr y⁻¹)
  have h1 := hasDerivAt_fderiv_line hdiff (x * X)
  have hF : HasDerivAt (fun t : ℝ => Fr (x * (1 + t • X))) (Fr x * fderiv ℝ Fr 1 X) 0 := by
    refine ((hasDerivAt_Fr_line h X).const_mul (Fr x)).congr_of_eventuallyEq ?_
    filter_upwards [line_mem X] with t ht
    exact h.mul x hx _ ht
  have hc : HasDerivAt (fun t : ℝ => (1 + t • X)⁻¹ * w) ((-X) * w) 0 :=
    (hasDerivAt_matmul (hasDerivAt_lineInv X) (hasDerivAt_const (0 : ℝ) w)).congr_deriv (by simp)
  have hK : HasDerivAt (fun t : ℝ => k ((1 + t • X)⁻¹ * w)) (fderiv ℝ k w ((-X) * w)) 0 :=
    hkw.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  have h2 := (((hF.fun_mul hK).mul_const Γ).mul_const T).mul_const (Fr y⁻¹)
  have e : (fun t : ℝ => Kf Fr k Γ T d (x + t • (x * X)) y) =
      fun t : ℝ => Fr (x * (1 + t • X)) * k ((1 + t • X)⁻¹ * w) * Γ * T * Fr y⁻¹ := by
    funext t
    have e1 : x + t • (x * X) = x * (1 + t • X) := by rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    simp only [Kf, e1, Matrix.mul_inv_rev, hwdef, Matrix.mul_assoc]
  rw [e] at h1
  rw [h1.unique h2]
  simp only [zero_smul, add_zero, inv_one, Matrix.one_mul, Matrix.mul_one, Ld, neg_mul, map_neg]
  noncomm_ring

theorem derOne : DerOne := fun _ _ _ _ _ _ _ _ _ h _ hk _ _ hd hy _ hx X => derOne_at h hk hd hy hx X

end

end PositivityTheory.RgBcC.LfSt.Kchain.KbDer
end
end

section
noncomputable section

open Matrix Finset Filter
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.Kchain.KbDer2

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain PositivityTheory.RgBcC.LfSt.Kchain.KbBase
  PositivityTheory.RgBcC.LfSt.Kchain.KbCurve PositivityTheory.RgBcC.LfSt.Kchain.KbFr PositivityTheory.RgBcC.LfSt.Kchain.KbDer
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem det_mul_conjT_ne {y : Mat n} (hy : y ∈ GLs n) : (y * yᴴ).det ≠ 0 := mul_mem hy (conjT_mem hy)

theorem contDiffAt_wt (c : ℝ) {y : Mat n} (hy : y ∈ GLs n) : ContDiffAt ℝ ∞ (fun y' : Mat n => wt c y') y := by
  unfold wt
  have h1 : ContDiffAt ℝ ∞ (fun y' : Mat n => (y' * y'ᴴ).det) y :=
    contDiff_det.contDiffAt.comp y (contDiffAt_matmul contDiffAt_id contDiff_conjT.contDiffAt)
  exact contDiffAt_const.mul ((h1.pow n).inv (pow_ne_zero _ (det_mul_conjT_ne hy)))

theorem wt_line (c : ℝ) (y : Mat n) {X : Mat n} (hX : X.IsHermitian) (t : ℝ) :
    wt c (y * (1 + t • X)) = (c : ℂ) * ((y * yᴴ).det ^ n)⁻¹ * (((1 + t • X).det ^ (2 * n))⁻¹) := by
  unfold wt
  have e : (y * (1 + t • X)) * (y * (1 + t • X))ᴴ = y * ((1 + t • X) * (1 + t • X)) * yᴴ := by
    rw [Matrix.conjTranspose_mul, conjT_line hX, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  rw [show y.det * ((1 + t • X).det * (1 + t • X).det) * yᴴ.det = (y.det * yᴴ.det) * (1 + t • X).det ^ 2 by ring,
    mul_pow, ← pow_mul, mul_inv, mul_assoc]

section

variable {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
  {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}

theorem derTwo_at (h : CxData lam E Fr ε ι S Γ T) {k : Mat n → (E.V →L[ℂ] E.V)} (hk : ContDiffOn ℝ ∞ k (GLs n)) (c : ℝ)
    {d x : Mat n} (hd : d ∈ GLs n) (hx : x ∈ GLs n) {y : Mat n} (hy : y ∈ GLs n) {X : Mat n} (hX : X.IsHermitian) :
    fderiv ℝ (fun y' => wt c y' • Kf Fr k Γ T d x y') y (y * X) =
      wt c y • (Fr x * (((-(2 * n : ℂ)) * X.trace) • k (x⁻¹ * d * yᴴ⁻¹) * Γ * T -
        Rd X k (x⁻¹ * d * yᴴ⁻¹) * Γ * T - k (x⁻¹ * d * yᴴ⁻¹) * Γ * T * fderiv ℝ Fr 1 X) * Fr y⁻¹) := by
  set w := x⁻¹ * d * yᴴ⁻¹ with hwdef
  have hw : w ∈ GLs n := mul_mem (mul_mem (inv_mem hx) hd) (inv_mem (conjT_mem hy))
  have hkw : DifferentiableAt ℝ k w := diffAt_of hk hw
  have hg : ContDiffAt ℝ ∞ (fun y' : Mat n => x⁻¹ * d * y'ᴴ⁻¹) y :=
    contDiffAt_matmul contDiffAt_const ((contDiffAt_inv (conjT_mem hy)).comp y contDiff_conjT.contDiffAt)
  have hdiff : DifferentiableAt ℝ (fun y' => wt c y' • Kf Fr k Γ T d x y') y := by
    unfold Kf
    have h1 : DifferentiableAt ℝ (fun y' : Mat n => k (x⁻¹ * d * y'ᴴ⁻¹)) y :=
      hkw.comp y (hg.differentiableAt (by simp))
    have h2 : DifferentiableAt ℝ (fun y' : Mat n => Fr y'⁻¹) y :=
      (diffAt_of h.smooth (inv_mem hy)).comp y ((contDiffAt_inv hy).differentiableAt (by simp))
    exact ((contDiffAt_wt c hy).differentiableAt (by simp)).smul
      ((((h1.const_mul (Fr x)).mul_const Γ).mul_const T).mul h2)
  have h1 := hasDerivAt_fderiv_line hdiff (y * X)
  have hq := (hasDerivAt_detLine X).fun_pow (2 * n)
  have hq0 : ((1 + (0 : ℝ) • X).det) ^ (2 * n) ≠ 0 := by simp
  have hW := (hq.fun_inv hq0).const_mul ((c : ℂ) * ((y * yᴴ).det ^ n)⁻¹)
  have hc : HasDerivAt (fun t : ℝ => w * (1 + t • X)⁻¹) (w * (-X)) 0 :=
    (hasDerivAt_matmul (hasDerivAt_const (0 : ℝ) w) (hasDerivAt_lineInv X)).congr_deriv (by simp)
  have hK : HasDerivAt (fun t : ℝ => k (w * (1 + t • X)⁻¹)) (fderiv ℝ k w (w * (-X))) 0 :=
    hkw.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  have hP : HasDerivAt (fun t : ℝ => Fr (1 + t • X)⁻¹) (fderiv ℝ Fr 1 (-X)) 0 :=
    (diffAt_of h.smooth one_mem).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_lineInv X) (by simp)
  have hB := (((hK.const_mul (Fr x)).mul_const Γ).mul_const T).fun_mul (hP.mul_const (Fr y⁻¹))
  have h2 := hW.fun_smul hB
  have e : ∀ᶠ t : ℝ in 𝓝 0, wt c (y + t • (y * X)) • Kf Fr k Γ T d x (y + t • (y * X)) =
      ((c : ℂ) * ((y * yᴴ).det ^ n)⁻¹ * (((1 + t • X).det ^ (2 * n))⁻¹)) •
        (Fr x * k (w * (1 + t • X)⁻¹) * Γ * T * (Fr (1 + t • X)⁻¹ * Fr y⁻¹)) := by
    filter_upwards [line_mem X] with t ht
    have e1 : y + t • (y * X) = y * (1 + t • X) := by rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    rw [e1, wt_line c y hX t]
    congr 1
    unfold Kf
    rw [Matrix.conjTranspose_mul, conjT_line hX, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      h.mul _ (inv_mem ht) _ (inv_mem hy)]
    simp only [hwdef, Matrix.mul_assoc, _root_.mul_assoc]
  have h2' := h2.congr_of_eventuallyEq e
  rw [h1.unique h2']
  simp only [zero_smul, add_zero, inv_one, Matrix.mul_one, Matrix.one_mul, h.one, _root_.one_mul, Matrix.det_one,
    one_pow, inv_one, _root_.mul_one, map_neg, Matrix.mul_neg, Rd]
  have ew : (c : ℂ) * ((y * yᴴ).det ^ n)⁻¹ = wt c y := rfl
  rw [ew]
  simp only [smul_sub, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_neg, mul_neg, neg_mul, smul_add, mul_add,
    add_mul, _root_.mul_assoc, smul_smul]
  push_cast
  ring_nf
  abel_nf

theorem derTwo : DerTwo := fun _ _ _ _ _ _ _ _ _ h _ hk c _ _ hd hx _ hy _ hX => derTwo_at h hk c hd hx hy hX

end

end PositivityTheory.RgBcC.LfSt.Kchain.KbDer2
end
end

section
namespace PositivityTheory.RgBcC.LfSt.Kchain

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt

theorem kChain (hH : HbFacts) (hF : FrameDer) : KChain :=
  kChain_of KcInv.kcSmooth KcInv.coneGL
    (KcHalf1.halfOne_of hH hF (fun n => KcHalf2.isOpen_cone (n := n) hH) KbDer.derOne)
    (KcHalf2.halfTwo_of hH hF KbFr.frComm KbDer2.derTwo (KcDual.dualSum hH))

end PositivityTheory.RgBcC.LfSt.Kchain
end

section
namespace PositivityTheory.RgBcC.LfSt

theorem kChain_holds : KChain := Kchain.kChain GlobalTheory.T.height_bound_facts (GelfandReading.frameDer_of GlobalTheory.T.height_bound_facts)

end PositivityTheory.RgBcC.LfSt
end
