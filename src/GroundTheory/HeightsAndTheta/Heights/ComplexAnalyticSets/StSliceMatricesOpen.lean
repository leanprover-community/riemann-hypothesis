module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def SliceMatricesOpen.Statement : Prop :=
  ∀ (n k m : ℕ) (γ : Fin m → (Fin (k + 1) → ℂ) → Fin n → ℂ) (s : Fin m → Fin (k + 1) → ℂ),
    (∀ b, DifferentiableAt ℂ (γ b) (s b)) →
    (∀ b (v : Fin (k + 1) → ℂ), v 0 = 0 → fderiv ℂ (γ b) (s b) v = 0 → v = 0) →
      IsOpen {L : Matrix (Fin k) (Fin n) ℂ |
          ∀ b, Function.Bijective (fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ b t)) (s b))} ∧
        {L : Matrix (Fin k) (Fin n) ℂ |
          ∀ b, Function.Bijective (fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ b t)) (s b))}.Nonempty

end

end GroundTheory.Heights₂.Heights
