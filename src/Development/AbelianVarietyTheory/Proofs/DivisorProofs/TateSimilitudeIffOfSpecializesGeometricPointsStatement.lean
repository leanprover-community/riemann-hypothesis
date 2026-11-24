module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudeIffOfSpecializesGeometricPoints
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

theorem _root_.GlobalTheory.T.tateSimilitude_iff_of_specializes_geometric_points : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ), N'.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (T : Over S) [IsLocallyNoetherian T.left] (lv : D.La → (T ⟶ o.A)), (∀ x y, lv (x + y) = lv x * lv y) → (∀ x, lv (N' • x) = 1) → (∀ (c : D.O) x, lv (c • x) = lv x ≫ o.act.act c) → ∀ {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] (x : Sp k ⟶ T.left) (x' : Sp k' ⟶ T.left) (u : Sp k) (u' : Sp k'), x'.base u' ⤳ x.base u → ((∃ I : TateIsoO D k (Over.mk (x ≫ T.hom) ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv y = I.ev N' y) ↔ (∃ I : TateIsoO D k' (Over.mk (x' ≫ T.hom) ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ y, (Over.homMk x' rfl : Over.mk (x' ≫ T.hom) ⟶ T) ≫ lv y = I.ev N' y)) := by
  first | exact @GlobalTheory.HTSpecTate.tateIsoO_iff_of_specializes | exact GlobalTheory.HTSpecTate.tateIsoO_iff_of_specializes | (intros; apply GlobalTheory.HTSpecTate.tateIsoO_iff_of_specializes; all_goals assumption)
