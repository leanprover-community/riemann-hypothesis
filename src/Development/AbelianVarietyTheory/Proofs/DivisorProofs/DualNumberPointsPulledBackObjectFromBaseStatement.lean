module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberPointsPulledBackObjectFromBase
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.dualNumber_points_pulledBack_object_from_base : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (k : Type) [Field k] (f : L.W →+* DualNumber k) (o' : LowObj D' c (f.comp L.b)) (m₁ : ObjMap o' L.o (spMap f)) (m₂ : ObjMap o' L.o (spMap (GlobalTheory.RigChart.constHom f))) (n : ℕ), (n : k) ≠ 0 → (∀ (Z : Scheme.{0}) (x : Z ⟶ o'.t.G.left) (y : Z ⟶ Sp k), x ≫ o'.t.G.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ m₁.toSABMap.φ = x ≫ m₂.toSABMap.φ) → ∀ u : L.D.X → (Sp (DualNumber k) ⟶ o'.t.G.left), (∀ y, u y ≫ o'.t.G.hom = 𝟙 _) → (∀ y, u y ≫ m₁.toSABMap.φ ≫ L.φB = spMap f ≫ (L.D.c (n • y)).left) → (∀ y, u y ≫ m₂.toSABMap.φ ≫ L.φB = spMap (GlobalTheory.RigChart.constHom f) ≫ (L.D.c (n • y)).left) → ∃ x : L.D.X → (Sp (DualNumber k) ⟶ o'.t.G.left), (∀ y, x y ≫ m₁.toSABMap.φ ≫ L.φB = spMap f ≫ (L.D.c y).left) ∧ (∀ y, x y ≫ m₂.toSABMap.φ ≫ L.φB = spMap (GlobalTheory.RigChart.constHom f) ≫ (L.D.c y).left) ∧ (∀ y, x y ≫ o'.t.G.hom = 𝟙 _) := by
  first | exact @GlobalTheory.UCanon.pts_eps_of_mul | exact GlobalTheory.UCanon.pts_eps_of_mul | (intros; apply GlobalTheory.UCanon.pts_eps_of_mul <;> assumption)
