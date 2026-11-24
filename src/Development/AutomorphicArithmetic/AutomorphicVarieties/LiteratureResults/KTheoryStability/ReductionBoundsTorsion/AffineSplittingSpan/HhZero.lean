module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.CoreDefs
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

open PrismSpan

variable {P Q : Type} [Group P] [Group Q]

theorem ru_eq (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g) (u : Q) (hu : ∀ g, g * u = u * g)
    {a b : ℕ} {F : Bi P Q a b} (hF : PInv pr F) : Ru u F = Tc (s u) (Rt (s u)⁻¹ F) := by
  funext x y
  unfold PInv at hF
  have h := hF (s u)⁻¹ (fun i => x i * u) y
  simp only [map_inv, hs] at h
  show F (fun i => x i * u) y = F x (fun j => (s u)⁻¹ * y j * s u * (s u)⁻¹)
  rw [← h]
  congr 1
  · funext i
    rw [hu (x i), inv_mul_cancel_left]
  · funext j
    group

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
