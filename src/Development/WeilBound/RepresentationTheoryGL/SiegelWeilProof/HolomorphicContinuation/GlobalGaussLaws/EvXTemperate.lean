module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.EvXTemperate
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.SchwartzPolyGauss

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

theorem evX_temperate {m n : ℕ} (P : PX m n) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => evX P u) := by
  have hcoord : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => u a i) := by
    intro a i
    exact ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj a : (Fin m → Fin n → ℂ) →L[ℝ] (Fin n → ℂ))).hasTemperateGrowth
  have hconj : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => star (u a i)) := by
    intro a i
    have h := (Complex.conjCLE.toContinuousLinearMap.comp
      ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℝ] ℂ).comp
        (ContinuousLinearMap.proj a : (Fin m → Fin n → ℂ) →L[ℝ] (Fin n → ℂ)))).hasTemperateGrowth
    convert h using 1
    funext u
    simp
  refine MvPolynomial.induction_on
    (motive := fun Q : PX m n =>
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => evX Q u)) P ?_ ?_ ?_
  · intro a
    convert Function.HasTemperateGrowth.const (E := Fin m → Fin n → ℂ) a using 1
    funext u
    simp [evX]
  · intro p q hp hq
    convert hp.add hq using 1
    funext u
    simp [evX]
  · intro p k hp
    obtain ⟨a, i, b⟩ := k
    cases b
    · have e : (fun u : Fin m → Fin n → ℂ => evX (p * X (a, i, false)) u) =
          (fun u => evX p u) * (fun u => u a i) := by
        funext u
        simp [evX]
      rw [e]
      exact hp.mul (hcoord a i)
    · have e : (fun u : Fin m → Fin n → ℂ => evX (p * X (a, i, true)) u) =
          (fun u => evX p u) * (fun u => star (u a i)) := by
        funext u
        simp [evX]
      rw [e]
      exact hp.mul (hconj a i)

theorem gs_sch {m n : ℕ} (c : ℝ) (hc : 0 < c) :
    ∃ S : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u, S u = gs c u := by
  apply _root_.PositivityTheory.SiegelWeilFormula.KFock.gsSch <;> assumption

theorem schFP : SchFP := by
  intro m n c hc P
  obtain ⟨S, hS⟩ := gs_sch (m := m) (n := n) c hc
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u => evX P u) S, ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply (evX_temperate P)]
  funext u
  simp [fP, hS, smul_eq_mul]

end PositivityTheory.Rg.Sw.Glob
