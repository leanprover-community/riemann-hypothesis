module

public import Development.EtaleCohomology.EtaleSheaves.LeafGlueProperPf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section
open AlgebraicGeometry.StructureSheaf CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.LeafGlueGenericPf

def eta (A : Type) [CommRing A] [IsDomain A] : Sp A := ⟨⊥, Ideal.isPrime_bot⟩

theorem eta_generic (A : Type) [CommRing A] [IsDomain A] : IsGenericPoint (eta A) (⊤ : Set (Sp A)) := by
  rw [isGenericPoint_iff_specializes]
  intro y
  simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
  exact (PrimeSpectrum.le_iff_specializes (eta A) y).1 bot_le

def etaT (A : Type) [CommRing A] [IsDomain A] : PrimeSpectrum.Top A := ⟨⊥, Ideal.isPrime_bot⟩

def psi0 {A L : Type} [CommRing A] [IsDomain A] [Field L] [Algebra A L] [IsFractionRing A L] :
    L →+* (structurePresheafInCommRingCat A).stalk (etaT A) := by
  have : (etaT A).asIdeal.IsPrime := Ideal.isPrime_bot
  exact IsLocalization.lift (M := nonZeroDivisors A) (S := L)
    (g := algebraMap A ((structurePresheafInCommRingCat A).stalk (etaT A))) (by
      intro y
      have hy : (y : A) ∈ (etaT A).asIdeal.primeCompl := by
        intro h0; exact nonZeroDivisors.ne_zero y.2 h0
      exact IsLocalization.map_units ((structurePresheafInCommRingCat A).stalk (etaT A))
        (⟨y, hy⟩ : (etaT A).asIdeal.primeCompl))

theorem fractionFieldToGenericStalk_algebraMap_eq {A L : Type} [CommRing A] [IsDomain A] [Field L] [Algebra A L] [IsFractionRing A L] (a : A) :
    psi0 (L := L) (algebraMap A L a) = StructureSheaf.toStalk A (etaT A) a := by
  unfold psi0; simp only [IsLocalization.lift_eq]; rfl

theorem glued_curve_generic_point_maps_to_function_field : LeafGlueGeneric := by
  intro Ω L _ _ _ A B u h G
  have := G.hiA
  have : IsFractionRing A L := h.2.2.2.2.2.2.2.2.2.1
  have : IsIntegral G.C0 := glued_affine_curve_is_integral_scheme Ω L A B u h G
  let s := G.iA.stalkMap (eta A)
  refine ⟨G.iA.base (eta A), Spec.map (inv s) ≫ Spec.map (CommRingCat.ofHom (psi0 (L := L))), ?_, ?_⟩
  · have hg := (eta_generic A).image G.iA.base.hom.continuous
    rw [Set.top_eq_univ, Set.image_univ,
      (G.iA.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)).closure_eq] at hg
    exact hg
  · have key := Scheme.SpecMap_stalkMap_fromSpecStalk G.iA (x := eta A)
    have hinv : G.C0.fromSpecStalk (G.iA.base (eta A)) =
        Spec.map (inv s) ≫ (Sp A).fromSpecStalk (eta A) ≫ G.iA := by
      rw [← key, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
    rw [Category.assoc, hinv, Category.assoc, Category.assoc, G.hcA]
    congr 1
    rw [Spec.fromSpecStalk_eq']
    erw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    have ha : algebraMap Ω L a = algebraMap A L (algebraMap Ω A a) := rfl
    change psi0 (L := L) (algebraMap Ω L a) = StructureSheaf.toStalk A (etaT A) (algebraMap Ω A a)
    rw [ha, fractionFieldToGenericStalk_algebraMap_eq]

end LateralTheory.E.LeafGlueGenericPf
