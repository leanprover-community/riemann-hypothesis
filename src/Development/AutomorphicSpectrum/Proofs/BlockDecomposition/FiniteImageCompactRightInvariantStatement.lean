module

public import Mathlib.Topology.Algebra.Group.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteImageCompactRightInvariant
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


theorem _root_.GlobalTheory.T.finite_image_compact_right_invariant : ∀ {Γ X : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (K : Set Γ), IsCompact K → ∀ Gf : Γ → X, {s : Γ | ∀ x, Gf (x * s) = Gf x} ∈ nhds (1 : Γ) → (Gf '' K).Finite := by
  first | exact @GlobalTheory.CompanionTheory.TopGroup.finite_image_of_right_invariant_near_one | exact GlobalTheory.CompanionTheory.TopGroup.finite_image_of_right_invariant_near_one | (intros; apply GlobalTheory.CompanionTheory.TopGroup.finite_image_of_right_invariant_near_one <;> assumption)
