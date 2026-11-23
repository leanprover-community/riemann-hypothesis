module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedLevelPatternOfFramePlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.iteratedLevelPattern_of_framePlaces : ∀ (F : Type) [Zero F] [One F] (κ ρ s τ j : ℕ) (R : ℕ → ℕ → F), ((∀ p', p' < κ + s + 1 → R p' p' = 1 ∧ ∀ p, p < κ + s + 1 + j * τ → p ≠ p' →
        (κ + s + 1 ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → R p p' = 0) ∧
      (∀ p p', κ + s + 1 ≤ p' → p' < κ + s + 1 + j * τ → p < κ + s + 1 + j * τ →
        (p' - (κ + s + 1)) / τ < (p - (κ + s + 1)) / τ → R p p' = 0)) → (∀ (a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j), ¬ FreeIx ρ a b → R (zPos a) (zPos b) = if a = b then 1 else 0) := by
  first | exact @GlobalTheory.patOfPlaces | exact GlobalTheory.patOfPlaces | (intros; apply GlobalTheory.patOfPlaces <;> assumption)
