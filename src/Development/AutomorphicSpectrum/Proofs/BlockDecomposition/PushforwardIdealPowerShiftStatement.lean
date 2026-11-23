module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalIdeal
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardIdealPowerShift
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

theorem _root_.GlobalTheory.T.pushforward_ideal_power_shift : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X), IsProper φ → φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {G : Z.Modules}, IsCoherent G → ∀ (V : X.Opens), IsAffineOpen V → ∃ c : ℕ, ∀ (n : ℕ) (s : Γ(G, φ ⁻¹ᵁ V)), s ∈ Set.range ((idealPowι I G (n + c)).app (φ ⁻¹ᵁ V)) → (show Γ((Scheme.Modules.pushforward φ).obj G, V) from s) ∈ (Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ((Scheme.Modules.pushforward φ).obj G, V)) := by
  exact @GlobalTheory.CompanionTheory.GE.FormalShift.formal_shift
