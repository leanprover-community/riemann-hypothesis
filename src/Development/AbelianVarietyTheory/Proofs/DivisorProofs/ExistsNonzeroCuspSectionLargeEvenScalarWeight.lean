module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
public import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.WeightEqZeroOfOneIsSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspNe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD

theorem GlobalTheory.ScalarPoin.exists_cusp_ne_some : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → (∀ n : ℕ, Even n → ∀ γ ∈ X.Γ, X.χ (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) γ = 1) → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Even n ∧ ∃ P ∈ X.SS (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)), ∃ y ∈ X.dom, P y ≠ 0 := by
  intro E _ _ _ r X hp0 hpr hχ N
  obtain ⟨y, hy⟩ := GlobalTheory.FlagSecProbe.dom_nonempty X
  obtain ⟨n, hN, -, hev, P, hP, hPy⟩ := GlobalTheory.ScalarPoin.exists_cusp_ne E r X hp0 hpr hχ y hy N
  exact ⟨n, hN, hev, P, hP, y, hy, hPy⟩
