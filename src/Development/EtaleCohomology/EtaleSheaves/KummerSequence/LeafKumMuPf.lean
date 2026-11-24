module

public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumSeqPf
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

namespace LateralTheory.E.H2CurveOrder.LeafKumMuPf

variable {R : Type} [CommRing R]

abbrev evU (U : Scheme.{0}) : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)

theorem kerSec_inj {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) :
    Function.Injective (Sec.map (kernel.ι φ) (U := U)) := by
  have hm : Mono ((evU U).map (kernel.ι φ)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 hm

theorem secMap_comp {F G K : Shv R} (f : F ⟶ G) (g : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem secMap_zero {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := rfl

def LeafKumMuUnits : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  ∃ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, κ ≫ LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q = 0 ∧
    ∀ U : Scheme.{0}, Nonempty (Sx (sp B) 0 U) → Function.Injective (Sec.map κ (U := U)) ∧
      ∀ s : Sec Gm U, Sec.map (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q) s = 0 → ∃ t, Sec.map κ t = s

def LeafKumMuSec : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  ∃ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ kernel (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q),
    ∀ U : Scheme.{0}, Nonempty (Sx (sp B) 0 U) → Function.Bijective (Sec.map κ (U := U))

theorem LeafKumMuSec_of (hU : LeafKumMuUnits) : LeafKumMuSec := by
  intro q _ B _ hq
  obtain ⟨κ, h0, hκ⟩ := hU q B hq
  refine ⟨kernel.lift _ κ h0, fun U hUB => ?_⟩
  obtain ⟨hi, hs⟩ := hκ U hUB
  have hc : ∀ t : Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U, Sec.map (kernel.ι _) (Sec.map (kernel.lift _ κ h0) t) = Sec.map κ t := by
    intro t; rw [← secMap_comp, kernel.lift_ι]
  refine ⟨fun a b hab => hi ?_, fun y => ?_⟩
  · rw [← hc, ← hc, hab]
  · obtain ⟨t, ht⟩ := hs (Sec.map (kernel.ι _) y) (by rw [← secMap_comp, kernel.condition, secMap_zero])
    exact ⟨t, kerSec_inj _ U (by rw [hc, ht])⟩

theorem LeafKumMu_of (h8 : A8) (h10 : A10) (hU : LeafKumMuUnits) : LateralTheory.E.H2CurveOrder.LeafKumSeqPf.LeafKumMu := by
  intro _ q _ B _ hq
  obtain ⟨κ, hκ⟩ := LeafKumMuSec_of hU q B hq
  have b1 := h8 ℤ (ZMod q) (Int.castRingHom (ZMod q)) (sp B) (tw q 1) 1
  have b2 := h10 ℤ (sp B) κ hκ 1
  exact ⟨((AddEquiv.ofBijective _ b1).trans (AddEquiv.ofBijective _ b2)).symm⟩

end LateralTheory.E.H2CurveOrder.LeafKumMuPf
