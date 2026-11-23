module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSpanProjectionBound
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

@[expose] public section

open GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lattice_span_projection_bound : ∀ (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (i : Ω₀ →+* Ω) (Li Li₀ : Type) [AddCommGroup Li] [Module Ω Li] [AddCommGroup Li₀] [Module Ω₀ Li₀] (ι : Li₀ →+ Li), IsExtOver i ι → Submodule.span Ω (Set.range ι) = ⊤ → ∀ (W : Subring Ω) (L₀ : Set Li₀) (L : Set Li) (r : ℕ) (b : Fin r → Li) (b₀ : Fin r → Li₀) (π₀ : Fin r → Module.Dual Ω₀ Li₀) (T : Module.End Ω Li) (Dn κ : Ω) (m : Ω₀), Submodule.span W L = Submodule.span W (ι '' L₀) → (∀ e ∈ L, T e ∈ Submodule.span W (Set.range b)) → (∀ j, T (ι (b₀ j)) = Dn • ι (b₀ j)) → (∀ j, m • b₀ j ∈ L₀) → (∀ a j, π₀ a (b₀ j) = if a = j then 1 else 0) → (∀ a, ∀ e ∈ L₀, i (m * π₀ a e) ∈ W) → (∀ j, κ • b j ∈ L) → (∀ j, b j ∈ Submodule.span Ω (Set.range fun a => ι (b₀ a))) → (∀ j, (Dn * i m) • ι (b₀ j) ∈ Submodule.span W (Set.range b)) ∧ ∀ j, (i m * κ) • b j ∈ Submodule.span W (Set.range fun a => ι (b₀ a)) := by
  exact @GlobalTheory.CompanionTheory.Ar.Frames.two_frames
