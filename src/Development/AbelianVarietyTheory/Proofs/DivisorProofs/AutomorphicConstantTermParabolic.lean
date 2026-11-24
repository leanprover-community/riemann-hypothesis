module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeApproximationUpwardIdele
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.AutomorphicL2Unitary (LeftInv)
open GlobalTheory.Cusp (Cocompact constTermOn)
open scoped TensorProduct

namespace GlobalTheory.UAut.ConstAut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem leftInv_foldr {Γ : Subgroup (GAd σ J)} {φ : GAd σ J → ℂ} (h : LeftInv Γ φ) :
    ∀ l : List (ℝ → GAd σ J), LeftInv Γ (l.foldr lineDer φ) := by
  intro l
  induction l with
  | nil => exact h
  | cons γ l ih =>
    intro x hx g
    simp only [List.foldr_cons, lineDer, mul_assoc, ih x hx]

theorem realLine_zero (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) : γ 0 = 1 := by
  have e := isRealLine_add F E σ h n J γ hγ 0 0
  rw [add_zero] at e
  exact mul_left_cancel (e.symm.trans (mul_one _).symm)

theorem hasDerivAt_foldr (h : IsCMExt F E σ) {φ : GAd σ J → ℂ} (hs : IsSm σ J φ) {l : List (ℝ → GAd σ J)}
    (hl : ∀ γ ∈ l, IsRealLine σ J γ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (g : GAd σ J) (t : ℝ) :
    HasDerivAt (fun s => l.foldr lineDer φ (g * γ s)) ((γ :: l).foldr lineDer φ (g * γ t)) t := by
  have hd := (GlobalTheory.ThK.RealLineGrowthDerivative.differentiableAt_foldr_lineDer hs l hl hγ (g * γ t)).hasDerivAt
  have e : ∀ s, g * γ t * γ (s - t) = g * γ s := fun s => by
    rw [mul_assoc, ← isRealLine_add F E σ h n J γ hγ, add_sub_cancel]
  have h2 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hd)
  simp only [e] at h2
  exact h2

end GlobalTheory.UAut.ConstAut

end
