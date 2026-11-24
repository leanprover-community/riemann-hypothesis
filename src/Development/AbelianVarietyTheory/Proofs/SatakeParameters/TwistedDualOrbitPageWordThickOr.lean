module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxSizeAtNonThickPlaceLeAndBoundStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickIffThickEmbeddingStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_thickOr : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG),
    Roomy L C → (pageWord L j ε τ φ).ThickOr := by
  intro D L C j ε τ φ hR i
  by_cases h : Thick D.host (letter τ φ i)
  · exact Or.inl ((GlobalTheory.T.twistedDualOrbitPageWord_thick_iff_thickEmbedding L C j ε τ φ hR i).2 h)
  · right
    have h1 := (GlobalTheory.T.maxSizeAtNonThickPlace_le_and_bound L C hR).2 _ j h
    show szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) ≤ ((wHat D : ℕ) : ℤ)
    unfold szT wHat
    push_cast
    split_ifs <;> omega

end GlobalTheory.HTW
