module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorOfOriginDerivation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

theorem _root_.GlobalTheory.T.exists_tangentVector_of_originDerivation : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (D : G.left.presheaf.stalk (origin G) → R), (∀ x y, D (x + y) = D x + D y) → (∀ x y, D (x * y) = evO G x * D y + evO G y * D x) → (∀ r, D (constO G r) = 0) → ∃ v : TanM (𝟙 (Sp R)) G, ∀ f, tanDer G v f = D f := by
  first | exact @GlobalTheory.CoordsOrigin.exists_tan_of_derivation | exact GlobalTheory.CoordsOrigin.exists_tan_of_derivation | (intros; apply GlobalTheory.CoordsOrigin.exists_tan_of_derivation <;> assumption)
