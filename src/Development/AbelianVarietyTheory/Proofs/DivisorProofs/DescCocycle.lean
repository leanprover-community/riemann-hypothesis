module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LBDescent

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

abbrev Triple : Scheme.{0} := pullback (pullback.snd f f) (pullback.fst f f)

def pr13 : Triple f ⟶ pullback f f :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst f f) (pullback.snd _ _ ≫ pullback.snd f f) (by
    calc (pullback.fst _ _ ≫ pullback.fst f f) ≫ f = pullback.fst (pullback.snd f f) (pullback.fst f f) ≫
          pullback.snd f f ≫ f := by rw [Category.assoc, pullback.condition]
      _ = pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f ≫ f := pullback.condition_assoc _
      _ = (pullback.snd _ _ ≫ pullback.snd f f) ≫ f := by rw [pullback.condition, Category.assoc])

def chart (L : LB X) (i j : L.ι) : (pullback f f).Opens :=
  pullback.fst f f ⁻¹ᵁ L.U i ⊓ pullback.snd f f ⁻¹ᵁ L.U j

def DescCompat (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) : Prop :=
  ∀ (z : ↥(pullback f f)) (i i' j j' : L.ι), pullback.fst f f z ∈ L.U i → pullback.fst f f z ∈ L.U i' →
    pullback.snd f f z ∈ L.U j → pullback.snd f f z ∈ L.U j' →
    gm (𝟙 _) z _ (φ i' j') =
      gm (pullback.fst f f) z _ (L.g i i') * gm (𝟙 _) z _ (φ i j) * gm (pullback.snd f f) z _ (L.g j' j)

def DescCocycle (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) : Prop :=
  ∀ (w : ↥(Triple f)) (i j k : L.ι), pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w) ∈ L.U i →
    pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w) ∈ L.U j → pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) w) ∈ L.U k →
    gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ (φ i j) *
      gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ (φ j k) = gm (pr13 f) w _ (φ i k)

end GlobalTheory.LBDescent
