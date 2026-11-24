module

public import Development.EtaleCohomology.KummerTheory.TwSecPf
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
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

namespace LateralTheory.KummerTheory.SecSHPf

theorem bij_of_top (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (hU : ∀ S ∈ Scheme.etaleTopology U, S (𝟙 U)) : Function.Bijective (ofRings.sec (R := R) M U) := by
  constructor
  · intro x y hxy
    have h := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M))
      (X := op U) x y hxy
    have := hU _ h
    simp [Presheaf.equalizerSieve] at this
    exact this
  · intro s
    have h := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (U := op U) s
    obtain ⟨t, ht⟩ := hU _ h
    refine ⟨t, ?_⟩
    simp at ht
    exact ht

def ShSect : Prop := ∀ (A : Type) [CommRing A], SH A → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of A)),
  Etale f → Surjective f → ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _

theorem top_of_sect (hs : ShSect) (A : Type) [CommRing A] (hA : SH A) :
    ∀ S ∈ Scheme.etaleTopology (Spec (CommRingCat.of A)), S (𝟙 _) := by
  intro S hS
  obtain ⟨hH, hsc⟩ := hA
  obtain ⟨𝒰, hle⟩ := Scheme.mem_grothendieckTopology_iff.1 hS
  obtain ⟨i, y, hy⟩ := ((Scheme.presieve₀_mem_precoverage_iff 𝒰.toPreZeroHypercover).1 𝒰.mem₀).1
    (IsLocalRing.closedPoint A : Spec (CommRingCat.of A))
  have he : Etale (𝒰.f i) := 𝒰.map_prop i
  have hsurj : Surjective (𝒰.f i) := by
    refine ⟨fun p => ?_⟩
    have hsp : p ⤳ (𝒰.f i) y := by
      rw [hy]; exact IsLocalRing.specializes_closedPoint (R := A) p
    obtain ⟨y', -, hy'⟩ := Flat.generalizingMap (𝒰.f i) hsp
    exact ⟨y', hy'⟩
  obtain ⟨s, hs'⟩ := hs A ⟨hH, hsc⟩ _ (𝒰.f i) he hsurj
  have := S.downward_closed (hle (𝒰.X i) (𝒰.f i) (Presieve.ofArrows.mk i)) s
  rwa [hs'] at this

end LateralTheory.KummerTheory.SecSHPf

namespace LateralTheory.KummerTheory

theorem SecSH_of (h : SecSHPf.ShSect) : SecSH := by
  intro A _ hA R _ M
  exact SecSHPf.bij_of_top R M _ (SecSHPf.top_of_sect h A hA)

end LateralTheory.KummerTheory
