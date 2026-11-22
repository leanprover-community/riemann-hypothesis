module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCut

@[expose] public section

open Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVCrdGerm

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutMP

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {r : ℕ}

theorem pbOp_germ (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    pbOp l f₁ =ᶠ[𝓝 c] pbOp l f₂ := by
  filter_upwards [h.eventuallyEq_nhds] with c' hc'
  simp only [pbOp, wirtBar, hc'.fderiv_eq]

theorem cbOp_germ (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    cbOp l f₁ =ᶠ[𝓝 c] cbOp l f₂ := by
  filter_upwards [h] with c' hc'
  simp only [cbOp, hc']

theorem cbiOp_germ (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    cbiOp l f₁ =ᶠ[𝓝 c] cbiOp l f₂ := by
  filter_upwards [h] with c' hc'
  simp only [cbiOp, hc']

theorem pbN_germ (i : ℕ) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    pbN r i f₁ =ᶠ[𝓝 c] pbN r i f₂ := by
  unfold pbN
  split_ifs with hi
  · exact pbOp_germ _ h
  · exact EventuallyEq.rfl

theorem cbN_germ (i : ℕ) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    cbN r i f₁ =ᶠ[𝓝 c] cbN r i f₂ := by
  unfold cbN
  split_ifs with hi
  · exact cbOp_germ _ h
  · exact EventuallyEq.rfl

theorem cbiN_germ (i : ℕ) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    cbiN r i f₁ =ᶠ[𝓝 c] cbiN r i f₂ := by
  unfold cbiN
  split_ifs with hi
  · exact cbiOp_germ _ h
  · exact EventuallyEq.rfl

end Formalism.FourierDecayAlt.P.CutMP.TVCrdGerm
