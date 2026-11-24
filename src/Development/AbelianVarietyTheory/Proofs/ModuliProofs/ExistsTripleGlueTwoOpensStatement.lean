module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTripleGlueTwoOpens
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.exists_triple_glue_two_opens : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (U V : X.Opens) (t₁ : SAB H U.toScheme) (t₂ : SAB H V.toScheme) (t₀ : SAB H (U ⊓ V).toScheme) (m₁ : SABMap t₀ t₁ (X.homOfLE inf_le_left)) (m₂ : SABMap t₀ t₂ (X.homOfLE inf_le_right)), U ⊔ V = ⊤ → (IsReduced U.toScheme ∧ genericPoints U.toScheme ⊆ abLocus t₁.G) → (IsReduced V.toScheme ∧ genericPoints V.toScheme ⊆ abLocus t₂.G) → ∃ (t : SAB H X) (n₁ : SABMap t₁ t U.ι) (n₂ : SABMap t₂ t V.ι), m₁.φ ≫ n₁.φ = m₂.φ ≫ n₂.φ := by
  first | exact @GlobalTheory.TripleGlue.exists_sab_glue | exact GlobalTheory.TripleGlue.exists_sab_glue | (intros; apply GlobalTheory.TripleGlue.exists_sab_glue <;> assumption)
