module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.VeryAmpleByDescendsCountableSubring
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
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.veryAmpleBy_descends_to_countable_subring : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) [Flat f] (H : LB X) (m : ℕ) (s : Fin (m + 1) → H.Sec) (S : Set R), H.IsLB → VeryAmpleBy f H s → S.Countable → ∃ (R₀ : Subring R) (_ : IsLocalRing R₀) (_ : IsPrincipalIdealRing R₀) (X₀ : Scheme.{0}) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) (H₀ : LB X₀) (s₀ : Fin (m + 1) → H₀.Sec), Countable R₀ ∧ S ⊆ R₀ ∧ IsLocalHom R₀.subtype ∧ Module.FaithfullyFlat R₀ R ∧ IsPullback π f f₀ (spMap R₀.subtype) ∧ Flat f₀ ∧ H₀.IsLB ∧ VeryAmpleBy f₀ H₀ s₀ ∧ LBIso H (H₀.pull π) := by
  first | exact @GlobalTheory.veryAmpleBy_descends_countable_subring | exact GlobalTheory.veryAmpleBy_descends_countable_subring | (intros; apply GlobalTheory.veryAmpleBy_descends_countable_subring <;> assumption)
