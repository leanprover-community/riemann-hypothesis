module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantAnnihilatingVectorZero
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
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD

@[expose] public section

open Finset Matrix PositivityTheory.RgHe.Frame

theorem _root_.GlobalTheory.T.commutant_annihilating_vector_zero : ∀ {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (d : Fin m → ℂ) (v : Fin m → ℂ), IsUnit g.det → Function.Injective d → (∀ i, (g⁻¹ *ᵥ v) i ≠ 0) → ∀ A : Matrix (Fin m) (Fin m) ℂ, A * (g * diagonal d * g⁻¹) = (g * diagonal d * g⁻¹) * A → A *ᵥ v = 0 → A = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.commutant_cyclic_eq_zero | exact GlobalTheory.CompanionTheory.RgHeFrame.commutant_cyclic_eq_zero | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.commutant_cyclic_eq_zero <;> assumption)
