module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
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
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.AlgebraicGeometry.Group.Affine

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.SpecialConn

variable {O : Type} [CommRing O] [IsLocalRing O] {Y : Scheme.{0}} (f : Y ⟶ Spec (.of O))

abbrev thickQ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    O →+* O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1) :=
  Ideal.Quotient.mk _

def thickR (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1 + 1) →+* O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

theorem thickR_comp (n : ℕ) : (thickR O n).comp (thickQ O (n + 1)) = thickQ O n := rfl

def thickFib (n : ℕ) : Scheme.{0} :=
  pullback f (Spec.map (CommRingCat.ofHom (thickQ O n)))

def thickι (n : ℕ) : thickFib f n ⟶ Y := pullback.fst _ _

def thickTr (n : ℕ) : thickFib f n ⟶ thickFib f (n + 1) :=
  pullback.map _ _ _ _ (𝟙 Y) (Spec.map (CommRingCat.ofHom (thickR O n))) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, thickR_comp])

theorem thickTr_ι (n : ℕ) : thickTr f n ≫ thickι f (n + 1) = thickι f n :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

end GlobalTheory.SpecialConn
