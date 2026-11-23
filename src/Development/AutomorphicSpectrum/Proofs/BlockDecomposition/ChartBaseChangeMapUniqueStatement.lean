module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartBaseChangeMapUnique
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

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem _root_.GlobalTheory.T.chart_base_change_map_unique : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) {S T : Finset (Fin d)} (θ₁ θ₂ : R0 K n d S →ₐ[K] C.R T), (∀ b, θ₁ (poly n K S b) = toR C T (phi C b)) → (∀ b, θ₂ (poly n K S b) = toR C T (phi C b)) → ∀ (θ' : R0 K n d T →ₐ[K] C.R T) (hθ' : ∀ b, θ' (poly n K T b) = toR C T (phi C b)), IsBaseChange (Aa C) (thetaLin C θ' hθ') → θ₁ = θ₂ := by
  exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique.theta_unique
