module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaObjectComparisonMapsCocycle
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.thetaObject_comparison_maps_cocycle : (∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s), f ≫ s = s' → ∃ t' : TObj g k J b s', TMap t' t f) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (β : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (I : Type) (U : I → S.Opens) (t : ∀ i, TObj g k J β ((U i).ι ≫ s)) (u : ∀ i j, TObj g k J β ((U i ⊓ U j).ι ≫ s)) (a : ∀ i j, (u i j).A.left ⟶ (t i).A.left) (b : ∀ i j, (u i j).A.left ⟶ (t j).A.left), (∀ i j, IsGrpPullback (u i j).A (t i).A (S.homOfLE inf_le_left) (a i j) ∧ LBIso (u i j).L ((t i).L.pull (a i j)) ∧ ∀ l, ((u i j).pt l).left ≫ a i j = S.homOfLE inf_le_left ≫ ((t i).pt l).left) → (∀ i j, IsGrpPullback (u i j).A (t j).A (S.homOfLE inf_le_right) (b i j) ∧ LBIso (u i j).L ((t j).L.pull (b i j)) ∧ ∀ l, ((u i j).pt l).left ≫ b i j = S.homOfLE inf_le_right ≫ ((t j).pt l).left) → (∀ (T : Scheme.{0}) (i : I) (f : T ⟶ (U i).toScheme) (u : TObj g k J β (f ≫ (U i).ι ≫ s)) (φ φ' : u.A.left ⟶ (t i).A.left), IsOpenImmersion f → IsGrpPullback u.A (t i).A f φ → IsGrpPullback u.A (t i).A f φ' → LBIso u.L ((t i).L.pull φ) → LBIso u.L ((t i).L.pull φ') → (∀ a, (u.pt a).left ≫ φ = (u.pt a).left ≫ φ') → φ = φ') → ∀ i j k (T : Scheme.{0}) (x : T ⟶ (u i j).A.left) (y : T ⟶ (u j k).A.left) (z : T ⟶ (u i k).A.left), x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k := by
  first | exact @GlobalTheory.ThetaCocycle.cocycle | exact GlobalTheory.ThetaCocycle.cocycle | (intros; apply GlobalTheory.ThetaCocycle.cocycle <;> assumption)
