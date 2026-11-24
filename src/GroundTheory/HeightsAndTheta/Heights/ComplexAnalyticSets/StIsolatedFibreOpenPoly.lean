module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
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

open MvPolynomial Topology ComplexSets

noncomputable section

def IsolatedFibreOpenPoly.Statement : Prop :=
  ∀ (n d : ℕ) (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ),
    P.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = (d : ℕ) → x ∈ zeroSet P →
    (∃ W ∈ 𝓝 x, ∀ x' ∈ zeroSet P ∩ W, (∀ i, eval x' (p i) = eval x (p i)) → x' = x) →
    ∀ W' ∈ 𝓝 x, (fun x' : Fin n → ℂ => fun i => eval x' (p i)) '' (zeroSet P ∩ W') ∈
      𝓝 (fun i => eval x (p i))

end

end GroundTheory.Heights₂.Heights
