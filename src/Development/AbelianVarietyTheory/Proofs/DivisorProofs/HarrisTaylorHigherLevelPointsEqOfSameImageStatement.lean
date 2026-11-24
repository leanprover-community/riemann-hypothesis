module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorHigherLevelPointsEqOfSameImage
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.harrisTaylor_higherLevel_points_eq_of_same_image : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (M' : Model b N') (π : M'.X ⟶ S), π ≫ s = M'.s → ∀ (om : ObjMap (M'.univ.forget N hd hc) o π) (T : Scheme.{0}) (g₁ g₂ : T ⟶ M'.X), g₁ ≫ π = g₂ ≫ π → (∀ a, g₁ ≫ (M'.univ.eta a).left ≫ om.φ = g₂ ≫ (M'.univ.eta a).left ≫ om.φ) → g₁ = g₂ := by
  first | exact @GlobalTheory.UPel.HT.LiftUniq.eq_of_same_image | exact GlobalTheory.UPel.HT.LiftUniq.eq_of_same_image | (intros; apply GlobalTheory.UPel.HT.LiftUniq.eq_of_same_image <;> assumption)
