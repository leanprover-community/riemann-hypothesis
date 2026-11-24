module

public import Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun
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
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.MVPf

def MVSpc : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g →
  ∀ n : ℤ, (∀ c : H R (pullback f g) F n, ∃ a b, c = pull R (pullback.fst f g) F n a - pull R (pullback.snd f g) F n b) →
  ∀ x : H R E F (n + 1), pull R f F _ x = 0 → pull R g F _ x = 0 → x = 0

def StdCover : Prop := ∀ (R : Type) [CommRing R] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  Cover2 R (spMap (algebraMap S (Localization.Away f))) (spMap (algebraMap S (Localization.Away g)))

def StdPB : Prop := ∀ (S : Type) [CommRing S] (f g : S),
  ∃ e : sp (Localization.Away (f * g)) ⟶
      pullback (spMap (algebraMap S (Localization.Away f))) (spMap (algebraMap S (Localization.Away g))),
    IsIso e ∧ e ≫ pullback.fst _ _ = spMap (LateralTheory.E.t_E1Cut.rL f g) ∧ e ≫ pullback.snd _ _ = spMap (LateralTheory.E.t_E1Cut.rR f g)

theorem pull_inj_of_iso (R : Type) [CommRing R] {E E' : Spc} (e : E ⟶ E') [IsIso e] (F : Shv R) (n : ℤ) :
    Function.Injective (pull R e F n) := by
  intro x y h
  have hx : pull R (inv e) F n (pull R e F n x) = x := by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  have hy : pull R (inv e) F n (pull R e F n y) = y := by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  rw [← hx, ← hy, h]

end LateralTheory.E.MVPf

open LateralTheory.E.MVPf in
theorem LateralTheory.E.t_E1Cut.MV_of (h1 : MVSpc) (h2 : StdCover) (h3 : StdPB) : LateralTheory.E.t_E1Cut.MV := by
  intro hA1 R _ F S _ f g hfg n hc x hxf hxg
  refine h1 hA1 R F _ _ (h2 R S f g hfg) n ?_ x hxf hxg
  intro c
  obtain ⟨e, he, hfst, hsnd⟩ := h3 S f g
  obtain ⟨a, b, hab⟩ := hc (pull R e F n c)
  refine ⟨a, b, pull_inj_of_iso R e F n ?_⟩
  rw [hab, map_sub, ← pull_comp, ← pull_comp, hfst, hsnd]
