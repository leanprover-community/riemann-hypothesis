module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DiscriminantValuationDifferent
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

@[expose] public section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

theorem _root_.GlobalTheory.T.discriminant_valuation_different : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 E)), P.IsPrime → (p : 𝓞 E) ∈ P → ((padicValInt p (discr E) : ℕ)) * (normalizedFactors (Ideal.span {(p : 𝓞 E)})).count P = (normalizedFactors (differentIdeal ℤ (𝓞 E))).count P * Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.Different.padicValInt_discr_mul_count_eq | exact GlobalTheory.CompanionTheory.Different.padicValInt_discr_mul_count_eq | (intros; apply GlobalTheory.CompanionTheory.Different.padicValInt_discr_mul_count_eq <;> assumption)
