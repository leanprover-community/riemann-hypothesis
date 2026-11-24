module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

universe w v u

namespace CrystallineSemistableComparison.Pb

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

abbrev cechCx (F : C ⥤ ModuleCat.{w} R) {ι : Type} (U : ι → ObjectProperty C) (p : ℕ) : Cx.{max u v w} R where
  X q := ∀ i : Fin (p + 1) → ι, CH.Cn ((capT U i).ι ⋙ F) q
  d q := LinearMap.pi fun i => (CH.d _ q).comp (LinearMap.proj i)
  dd q x := funext fun i => CH.d_d _ q (x i)

abbrev cechCC (F : C ⥤ ModuleCat.{w} R) {ι : Type} (U : ι → ObjectProperty C) : CosCx.{max u v w} R where
  K p := cechCx F U p
  δ n k :=
    { f := fun q => LinearMap.pi fun i =>
        ((resU F (U := capT U (i ∘ k.succAbove)) (V := capT U i) fun _ h _ => h _).pullC q).comp
          (LinearMap.proj (i ∘ k.succAbove))
      comm := fun q x => by
        funext i
        exact CH.Mor.d_pullC (resU F (U := capT U (i ∘ k.succAbove)) (V := capT U i) fun _ h _ => h _) q (x (i ∘ k.succAbove)) }
  rel n j i q x := by
    funext t
    have e : (t ∘ (j.succAbove i).succAbove) ∘ (i.predAbove j).succAbove = (t ∘ j.succAbove) ∘ i.succAbove :=
      funext fun k => congrArg t (Fin.succAbove_succAbove_succAbove_predAbove j i k)
    have key : ∀ (a a' : Fin (n + 2) → ι) (b b' : Fin (n + 1) → ι) (hb : b = b') h1 h2 h3 h4,
        (resU F (U := capT U a) (V := capT U t) h1).pullC q ((resU F (U := capT U b) (V := capT U a) h2).pullC q (x b)) =
        (resU F (U := capT U a') (V := capT U t) h3).pullC q ((resU F (U := capT U b') (V := capT U a') h4).pullC q (x b')) := by
      intro a a' b b' hb h1 h2 h3 h4
      subst hb
      rfl
    exact key _ _ _ _ e _ _ _ _

def cechAugRowU (F : C ⥤ ModuleCat.{w} R) {ι : Type} (U : ι → ObjectProperty C) :
    DCx.AugRow (CH.cx F) (cechCC F U).dcx where
  ε q := LinearMap.pi fun i : Fin (0 + 1) → ι => (CH.Mor.restrict F (capT U i).ι).pullC q
  hε q x := by
    have e : ((cechCC F U).cos q).δ 0 0 (LinearMap.pi (fun i : Fin (0 + 1) → ι => (CH.Mor.restrict F (capT U i).ι).pullC q) x) =
        ((cechCC F U).cos q).δ 0 1 (LinearMap.pi (fun i : Fin (0 + 1) → ι => (CH.Mor.restrict F (capT U i).ι).pullC q) x) := by
      funext t s; rfl
    refine (Cos.d_apply ((cechCC F U).cos q) 0 _).trans ?_
    rw [Fin.sum_univ_two, e]
    simp
  comm q x := by
    funext i
    exact CH.Mor.d_pullC (CH.Mor.restrict F (capT U i).ι) q x

end CrystallineSemistableComparison.Pb
