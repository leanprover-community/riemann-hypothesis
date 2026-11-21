import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.GelFlagA

noncomputable section

open Matrix Module
open scoped ContDiff

namespace PositivityTheory.RgBcC.VC.GFB

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def lmul (a b : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => a * y * b
      map_add' := fun y z => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c y => by simp [Matrix.mul_smul, Matrix.smul_mul] }

theorem lmul_apply (a b y : Mat n) : lmul a b y = a * y * b := rfl

theorem mul_mem_GLs {a y b : Mat n} (ha : a ∈ GLs n) (hy : y ∈ GLs n) (hb : b ∈ GLs n) : a * y * b ∈ GLs n := by
  show (a * y * b).det ≠ 0
  rw [Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero ha hy) hb


theorem gel_sub (hGC : GelComm) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (s : Bool) (m : ℕ)
    {F₁ F₂ : Mat n → V} (h₁ : ContDiffOn ℝ ∞ F₁ (GLs n)) (h₂ : ContDiffOn ℝ ∞ F₂ (GLs n)) {g₀ : Mat n} (hg₀ : g₀ ∈ GLs n) :
    gel s m (fun y => F₁ y - F₂ y) g₀ = gel s m F₁ g₀ - gel s m F₂ g₀ := by
  have hP : ContDiffOn ℝ ∞ (fun y => (F₁ y, F₂ y)) (GLs n) := h₁.prodMk h₂
  have hc := (hGC n (V × V) V s m _ hP).2 g₀ hg₀
  have c1 := hc.2.2 (ContinuousLinearMap.fst ℂ V V - ContinuousLinearMap.snd ℂ V V)
  have c2 := hc.2.2 (ContinuousLinearMap.fst ℂ V V)
  have c3 := hc.2.2 (ContinuousLinearMap.snd ℂ V V)
  have e1 : (fun y => (ContinuousLinearMap.fst ℂ V V - ContinuousLinearMap.snd ℂ V V) (F₁ y, F₂ y)) =
      fun y => F₁ y - F₂ y := by funext y; simp
  have e2 : (fun y => (ContinuousLinearMap.fst ℂ V V) (F₁ y, F₂ y)) = F₁ := by funext y; simp
  have e3 : (fun y => (ContinuousLinearMap.snd ℂ V V) (F₁ y, F₂ y)) = F₂ := by funext y; simp
  rw [e1] at c1; rw [e2] at c2; rw [e3] at c3
  rw [c1, c2, c3]; simp



end PositivityTheory.RgBcC.VC.GFB
