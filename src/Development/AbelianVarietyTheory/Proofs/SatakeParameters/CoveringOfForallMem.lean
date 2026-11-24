module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsZeroFreeSchOfIsEmpty
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC.Tr

def SplitBy {Z X V : Scheme.{0}} (f : Z ⟶ X) (y : V ⟶ X) {m : ℕ} (s : Fin m → (V ⟶ Z)) : Prop :=
  ∃ hs : ∀ j, s j ≫ f = y, IsIso (Sigma.desc (fun j => pullback.lift (s j) (𝟙 V) (by rw [hs j, Category.id_comp])) :
    ∐ (fun _ : Fin m => V) ⟶ pullback f y)

def Splits {Z X V : Scheme.{0}} (f : Z ⟶ X) (y : V ⟶ X) : Prop :=
  ∃ (m : ℕ) (s : Fin m → (V ⟶ Z)), SplitBy f y s

def splitSieve {Z X S : Scheme.{0}} (f : Z ⟶ X) (x : S ⟶ X) : Sieve S :=
  Sieve.generate (fun V (v : V ⟶ S) => Splits f (v ≫ x))

theorem IsTransfer.apply_of_splitBy (R : Type) [CommRing R] {Z X V : Scheme.{0}} {f : Z ⟶ X} {t : freeSch R X ⟶ freeSch R Z}
    (ht : IsTransfer R f t) {y : V ⟶ X} {m : ℕ} {s : Fin m → (V ⟶ Z)} (hs : SplitBy f y s) :
    (free R).map (yoneda.map y) ≫ t = ∑ j, (free R).map (yoneda.map (s j)) :=
  ht V y m s hs.1 hs.2

end GlobalTheory.EtC.Tr
