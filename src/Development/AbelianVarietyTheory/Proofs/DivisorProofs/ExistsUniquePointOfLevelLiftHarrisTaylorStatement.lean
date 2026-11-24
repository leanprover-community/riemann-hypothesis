module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePointOfLevelLiftHarrisTaylor
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

theorem _root_.GlobalTheory.T.exists_unique_point_of_level_lift_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ), 3 ≤ N → ∀ (hd : N ∣ N') (hc : N'.Coprime p) (M : Model b N) (M' : Model b N') (π : M'.X ⟶ M.X), π ≫ M.s = M'.s → ∀ (om : ObjMap (M'.univ.forget N hd hc) M.univ π) (T : Over M.X) (lv : D.La → (T ⟶ M.univ.A)), IsLift M.univ N' T lv → ∃ g : T.left ⟶ M'.X, g ≫ π = T.hom ∧ ∀ a, (lv a).left = g ≫ (M'.univ.eta a).left ≫ om.φ := by
  first | exact @GlobalTheory.UPel.HT.OfLift.ofLift | exact GlobalTheory.UPel.HT.OfLift.ofLift | (intros; apply GlobalTheory.UPel.HT.OfLift.ofLift <;> assumption)
