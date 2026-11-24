module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingConditionLocusIsClopen
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

theorem _root_.GlobalTheory.T.weilPairing_condition_locus_isClopen : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (Z : Over S) (t₁ : Z.left ⟶ Sp (cycAway M)) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ (β : cycAway M →+* k) (z : kˣ), x ≫ t₁ = spMap β → (z : k) = β (zetaAway M) → ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e c) (unitOn (z ^ (2 * omegaStd a c)))) := by
  first | (exact @GlobalTheory.HTWeilLocus.weil_locus_clopen) | (exact GlobalTheory.HTWeilLocus.weil_locus_clopen) | (intros; apply GlobalTheory.HTWeilLocus.weil_locus_clopen  <;> assumption)
