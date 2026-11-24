module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermWeierstrassPreparation
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

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def WeierstrassPolynomialDivision.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (d : ℕ) (c : Fin d → (σ → ℂ) → ℂ) (g : (Option σ → ℂ) → ℂ),
    (∀ j, AnalyticAt ℂ (c j) 0) → (∀ j, c j 0 = 0) → AnalyticAt ℂ g 0 →
    ∃ (q : (Option σ → ℂ) → ℂ) (a : Fin d → (σ → ℂ) → ℂ),
      AnalyticAt ℂ q 0 ∧ (∀ j, AnalyticAt ℂ (a j) 0) ∧
      ∀ᶠ x in 𝓝 (0 : Option σ → ℂ),
        g x = q x * weierstrassPolynomial c x + ∑ j : Fin d, a j (fun i => x (some i)) * x none ^ (j : ℕ)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
