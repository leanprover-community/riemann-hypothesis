module

public import Development.EtaleCohomology.EtaleSheaves.LeafTwistPf
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
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafLocPf

def overIso {R : Type} [CommRing R] (X : Scheme.{0}) (F G : Shv R)
    (e : ∀ U : Scheme.{0}, (U ⟶ X) → (Sec F U ≃ₗ[ULift.{1} R] Sec G U))
    (he : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), e V (g ≫ x) (Sec.res g s) = Sec.res g (e U x s)) :
    F.over X ≅ G.over X :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun Y => (e Y.unop.left Y.unop.hom).toModuleIso) (by
    intro Y Y' f
    ext s
    have h := he f.unop.left Y.unop.hom s
    rw [Over.w f.unop] at h
    exact h))

def LocOver : Prop := Hyps → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F G : Shv R),
  Nonempty (F.over X ≅ G.over X) → ∀ n : ℤ, Nonempty (H R (sch.obj X) F n ≃+ H R (sch.obj X) G n)

theorem LeafLoc_of (hO : LocOver) : LateralTheory.E.LeafTwistPf.LeafLoc := by
  intro hy R _ X F G e he n
  exact hO hy R X F G ⟨overIso X F G e he⟩ n

abbrev secCx {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0}) : CochainComplex (ModuleCat.{1} (ULift.{1} R)) ℤ :=
  ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op X)).mapHomologicalComplex _).obj (res R F)

def LocSec : Prop := Hyps → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F : Shv R) (n : ℤ),
  Nonempty (H R (sch.obj X) F n ≃+ (secCx F X).homology n)

def LocSlice : Prop := Hyps → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F G : Shv R),
  Nonempty (F.over X ≅ G.over X) → ∀ n : ℤ, Nonempty ((secCx F X).homology n ≃+ (secCx G X).homology n)

theorem LocOver_of (hS : LocSec) (hL : LocSlice) : LocOver := by
  intro hy R _ X F G hi n
  obtain ⟨a⟩ := hS hy R X F n
  obtain ⟨b⟩ := hS hy R X G n
  obtain ⟨c⟩ := hL hy R X F G hi n
  exact ⟨(a.trans c).trans b.symm⟩

theorem LeafLoc_of' (hS : LocSec) (hL : LocSlice) : LateralTheory.E.LeafTwistPf.LeafLoc :=
  LeafLoc_of (LocOver_of hS hL)

end LateralTheory.E.LeafLocPf
