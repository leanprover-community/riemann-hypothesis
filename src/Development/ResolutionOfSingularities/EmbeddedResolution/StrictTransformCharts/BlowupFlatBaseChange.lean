module

public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
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
import Mathlib.Tactic.Linter.Style
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

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace FunctorialResolution.EmbeddedResolution

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.comap_of_flat {X Y : Scheme.{u}} {D : X.IdealSheafData}
    (hD : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor D) (f : Y ⟶ X) [AlgebraicGeometry.Flat f] :
    FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor (D.comap f) := by
  unfold FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor at hD ⊢
  intro y
  obtain ⟨U, s, hxU, hs, hUs⟩ := hD (f.base y)
  obtain ⟨V, hV2, hyV, hVle⟩ :=
    exists_isAffineOpen_mem_and_subset (x := y) (U := f ⁻¹ᵁ (U : X.Opens)) hxU
  let V' : Y.affineOpens := ⟨V, hV2⟩
  have hflat : (Scheme.Hom.appLE f (U : X.Opens) (V' : Y.Opens) hVle).hom.Flat :=
    Scheme.Hom.flat_appLE f U.2 hV2 hVle
  refine ⟨V', (Scheme.Hom.appLE f (U : X.Opens) (V' : Y.Opens) hVle).hom s, hyV, ?_, ?_⟩
  · let _ := (Scheme.Hom.appLE f (U : X.Opens) (V' : Y.Opens) hVle).hom.toAlgebra
    have : Module.Flat Γ(X, U.1) Γ(Y, V'.1) := hflat
    have hreg : IsSMulRegular Γ(Y, V'.1) s := Module.Flat.isSMulRegular_of_nonZeroDivisors hs
    refine mem_nonZeroDivisors_iff.mpr ⟨fun t ht => ?_, fun t ht => ?_⟩
    · exact hreg (show s • t = s • 0 by rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, ht, smul_zero])
    · exact hreg (show s • t = s • 0 by rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm, ht, smul_zero])
  · rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE D f U V' hVle, hUs, Ideal.map_span,
      Set.image_singleton]

theorem _root_.FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.pullback_snd_of_flat {X Y B : Scheme.{u}} {π : B ⟶ X}
    {J : X.IdealSheafData} (h : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf π J) (g : Y ⟶ X) [AlgebraicGeometry.Flat g] :
    FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf (pullback.snd π g) (J.comap g) := by
  have e1 : (J.comap g).comap (pullback.snd π g)
      = (J.comap π).comap (pullback.fst π g) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      pullback.condition]
  refine ⟨?_, ?_⟩
  · rw [e1]
    exact h.1.comap_of_flat (pullback.fst π g)
  · intro W m hm
    have hm' : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor (J.comap (m ≫ g)) := by
      rw [Scheme.IdealSheafData.comap_comp]
      exact hm
    obtain ⟨b, hb, hbuniq⟩ := h.2 W (m ≫ g) hm'
    refine ⟨pullback.lift b m hb, ?_, ?_⟩
    · exact pullback.lift_snd b m hb
    · intro a ha
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst]
        refine hbuniq _ ?_
        show (a ≫ pullback.fst π g) ≫ π = m ≫ g
        rw [Category.assoc, pullback.condition, ← Category.assoc, ha]
      · rw [pullback.lift_snd, ha]

theorem _root_.FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.of_isPullback_of_flat {X Y B P : Scheme.{u}} {π : B ⟶ X}
    {J : X.IdealSheafData} (h : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf π J) (g : Y ⟶ X) [AlgebraicGeometry.Flat g]
    {p : P ⟶ B} {q : P ⟶ Y} (hsq : IsPullback p q π g) :
    FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf q (J.comap g) := by
  have h3 : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf (pullback.snd π g) (J.comap g) := h.pullback_snd_of_flat g
  have h4 := h3.iso_hom_comp hsq.isoPullback
  rwa [hsq.isoPullback_hom_snd] at h4

theorem _root_.FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.exists_isPullback_of_flat {X Y B B' : Scheme.{u}} {π : B ⟶ X}
    {J : X.IdealSheafData} (h : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf π J) (g : Y ⟶ X) [AlgebraicGeometry.Flat g]
    {π' : B' ⟶ Y} (h' : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf π' (J.comap g)) :
    ∃ q : B' ⟶ B, q ≫ π = π' ≫ g ∧ IsPullback q π' π g := by
  obtain ⟨e, he⟩ := h'.exists_iso (h.pullback_snd_of_flat g)
  have hc : (e.hom ≫ pullback.fst π g) ≫ π = π' ≫ g := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  exact ⟨e.hom ≫ pullback.fst π g, hc, IsPullback.of_iso_pullback ⟨hc⟩ e rfl he⟩

end FunctorialResolution.EmbeddedResolution
