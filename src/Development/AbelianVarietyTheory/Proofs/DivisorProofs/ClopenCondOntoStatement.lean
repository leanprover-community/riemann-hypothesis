module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenCondOnto
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.clopenCond_onto_alt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom → Etale K.hom → (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x) → ∀ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom → Etale Z.hom → (∀ x y, et (x + y) = et x * et y) → (∀ (c : D.O) x, et (c • x) = et x ≫ o.act.act c) → (∀ x ∈ wSub D w0 r, et x = 1) → GlobalTheory.LevCover.ClopenCond Z fun T' h => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T'.left), ∀ g : Over.mk (x ≫ T'.hom) ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃ y, (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ h ≫ et y = g := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.clopenCond_onto) | (exact GlobalTheory.UPel.HT.EtLev.clopenCond_onto) | (intros; apply GlobalTheory.UPel.HT.EtLev.clopenCond_onto <;> assumption)
