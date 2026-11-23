module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Convex.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GermSectionsHalfPlaneGlobalSection
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

open Filter Topology

theorem _root_.GlobalTheory.T.germSections_halfPlane_global_section : ∀ (Y : Type) (G : ℂ → (ℂ → Y) → Prop) (T : ℝ), (∀ w s s', s =ᶠ[𝓝 w] s' → G w s → G w s') → (∀ w : ℂ, T < w.im → ∃ s, ∀ᶠ z in 𝓝 w, G z s) → (∀ (U : Set ℂ) (s s' : ℂ → Y), IsOpen U → Convex ℝ U → (∀ z ∈ U, T < z.im) → (∀ z ∈ U, G z s) → (∀ z ∈ U, G z s') → ∀ w ∈ U, s w = s' w → Set.EqOn s s' U) → (∀ (U : Set ℂ) (s s' : ℂ → Y), IsOpen U → Convex ℝ U → (∀ z ∈ U, T < z.im) → (∀ z ∈ U, G z s) → ∀ w ∈ U, G w s' → ∃ s'' : ℂ → Y, (∀ z ∈ U, G z s'') ∧ s'' w = s' w) → ∃ s : ℂ → Y, ∀ w : ℂ, T < w.im → G w s := by
  exact @GlobalTheory.germSections_halfPlane_global
