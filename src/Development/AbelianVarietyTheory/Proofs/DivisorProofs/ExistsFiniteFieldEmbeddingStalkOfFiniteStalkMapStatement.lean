module

public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFieldEmbeddingStalkOfFiniteStalkMap
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

@[expose] public section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_finite_fieldEmbedding_stalk_of_finite_stalkMap : ∀ (Ω : Type) [Field Ω] (X : Scheme.{0}) (p : Sp Ω ⟶ X), (p.stalkMap (genericPoint (Sp Ω))).hom.Finite → ∃ φ : X.presheaf.stalk (p.base (genericPoint (Sp Ω))) →+* Ω, φ.Finite ∧ ∀ (K : Type) [Field K] (τ₁ τ₂ : Ω →+* K), spMap τ₁ ≫ p = spMap τ₂ ≫ p → τ₁.comp φ = τ₂.comp φ := by
  first | exact @GlobalTheory.StalkField.exists_stalk_field_hom | exact GlobalTheory.StalkField.exists_stalk_field_hom | (intros; apply GlobalTheory.StalkField.exists_stalk_field_hom <;> assumption)
