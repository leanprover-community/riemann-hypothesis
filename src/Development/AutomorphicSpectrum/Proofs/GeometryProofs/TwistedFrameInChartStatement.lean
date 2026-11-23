module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdUpdateDiv
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedFrameInChart
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

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem _root_.GlobalTheory.T.twisted_frame_in_chart : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (r : ℕ) (V : Submodule Ω E) (L : Lat ξ E) (m n : ℕ) (φ : Fin n → Module.Dual Ω E) (b : Fin r → E) (c : κ) (p : Cpt ξ), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → L.IsVB r V → IsTwistGen ξ x L m φ → (LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = V) → InChart ξ x c p → ∃ g ∈ chartSub x c, unitAt ξ p g ∧ ∃ (T : Matrix (Fin r) (Fin r) Ω) (M : Matrix (Fin n) (Fin r) Ω) (N : Matrix (Fin r) (Fin n) Ω), T.det ≠ 0 ∧ (∀ j l, M j l ∈ locSub (chartSub x c) g) ∧ (∀ l j, N l j ∈ locSub (chartSub x c) g) ∧ N * M = 1 ∧ ∀ j l, φ j (b l) = x c ^ m * (M * T) j l := by
  exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_chart_frame
