module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleTrace.Tr

def Splits {Y X W : Scheme.{0}} (a : Y ⟶ X) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)) : Prop :=
  ∃ hs : ∀ j, s j ≫ a = x, IsIso (Sigma.desc (fun j => pullback.lift (s j) (𝟙 W) (by rw [hs j, Category.id_comp])) :
      ∐ (fun _ : Fin m => W) ⟶ pullback a x)

section
variable (R : Type) [CommRing R]

abbrev fr (X : Scheme.{0}) : Shv R := (free R).obj (yoneda.obj X)

abbrev gen {U X : Scheme.{0}} (x : U ⟶ X) : Sec (fr R X) U := freeGen R (yoneda.obj X) U x

def IsTr {Y X : Scheme.{0}} (a : Y ⟶ X) (τ : fr R X ⟶ fr R Y) : Prop :=
  ∀ (W : Scheme.{0}) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)), Splits a x m s →
    Sec.map τ (gen R x) = ∑ j, gen R (s j)

variable {R}

end

def LSpl : Prop := ∀ {Y X W : Scheme.{0}} (a : Y ⟶ X) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)), Splits a x m s →
  (∀ (U : Scheme.{0}) (w : U ⟶ W), Splits a (w ≫ x) m (fun j => w ≫ s j)) ∧
  (∀ y : W ⟶ Y, y ≫ a = x → ∀ t : W, ∃ (O : W.Opens) (j : Fin m), t ∈ O ∧ O.ι ≫ y = O.ι ≫ s j) ∧
  (Nonempty W → Function.Injective s)

def LLoc : Prop := ∀ {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a → ∀ (W : Scheme.{0}) (x : W ⟶ X) (t : W),
  ∃ (U : Scheme.{0}) (g : U ⟶ W) (m : ℕ) (s : Fin m → (U ⟶ Y)), Etale g ∧ t ∈ Set.range g ∧ Splits a (g ≫ x) m s

def LTau : Prop := ∀ (R : Type) [CommRing R] {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a →
  ∃ τ : fr R X ⟶ fr R Y, IsTr R a τ

section Glue
variable (l : ℕ) [Fact l.Prime]

end Glue

end LateralTheory.EtaleTrace.Tr

end
