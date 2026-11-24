module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleLevelLiftScheme
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

theorem _root_.GlobalTheory.T.exists_finite_etale_level_lift_scheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ), N'.Coprime p → N ∣ N' → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Over S) (ηu : D.La → (Y ⟶ o.A)), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (T : Over S) (lv : D.La → (T ⟶ o.A)), (IsLift o N' T lv → ∃! f : T ⟶ Y, ∀ a, f ≫ ηu a = lv a) ∧ ((∃ f : T ⟶ Y, ∀ a, f ≫ ηu a = lv a) → IsLift o N' T lv) := by
  first | exact @GlobalTheory.UPel.HT.exists_liftScheme | exact GlobalTheory.UPel.HT.exists_liftScheme | (intros; apply GlobalTheory.UPel.HT.exists_liftScheme <;> assumption)
