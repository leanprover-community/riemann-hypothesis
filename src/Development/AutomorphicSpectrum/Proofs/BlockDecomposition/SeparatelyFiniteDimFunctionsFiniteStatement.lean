module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparatelyFiniteDimFunctionsFinite
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
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace

@[expose] public section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

theorem _root_.GlobalTheory.T.separately_finite_dim_functions_finite : ∀ (X Y : Type) (V₁ : Submodule ℂ (X → ℂ)) (V₂ : Submodule ℂ (Y → ℂ)), FiniteDimensional ℂ V₁ → FiniteDimensional ℂ V₂ → ∃ 𝓥 : Submodule ℂ (X × Y → ℂ), FiniteDimensional ℂ 𝓥 ∧ ∀ f : X × Y → ℂ, (∀ y, (fun x => f (x, y)) ∈ V₁) → (∀ x, (fun y => f (x, y)) ∈ V₂) → f ∈ 𝓥 := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.ProdTrick.exists_finiteDimensional_of_slices | exact GlobalTheory.CompanionTheory.CTFin.ProdTrick.exists_finiteDimensional_of_slices | (intros; apply GlobalTheory.CompanionTheory.CTFin.ProdTrick.exists_finiteDimensional_of_slices <;> assumption)
