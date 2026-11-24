module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.SmoothLift

theorem isIso_spMap_mk_bot (R : Type) [CommRing R] : IsIso (spMap (Ideal.Quotient.mk (⊥ : Ideal R))) := by
  let e : R ≃+* R ⧸ (⊥ : Ideal R) := RingEquiv.ofBijective (Ideal.Quotient.mk ⊥)
    ⟨fun a b h ↦ by simpa [sub_eq_zero] using Ideal.Quotient.eq.1 h, Ideal.Quotient.mk_surjective⟩
  have : IsIso (spMap e.toRingHom) := inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  exact this

def ofSmooth (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (hs : Smooth s) (hsep : IsSeparated s)
    (hqc : QuasiCompact s) : Data where
  R := R
  I := ⊥
  κ := dp0 R
  nil := isDPNilpotent_bot R
  X := X
  X₀ := X
  s := s
  t := s
  i := 𝟙 X
  smooth := hs
  sep := hsep
  qc := hqc
  red := by
    haveI := isIso_spMap_mk_bot R
    refine ⟨s ≫ inv (spMap (Ideal.Quotient.mk (⊥ : Ideal R))), ?_, by simp⟩
    exact IsPullback.of_horiz_isIso ⟨by simp⟩

end GlobalTheory.SmoothLift

namespace GlobalTheory.CechDR

open GlobalTheory.SmoothLift

theorem cechDeRham_comparison_bijective_cup_smooth (hP : GlobalTheory.Published.CrystallineSmoothLift) : ∀ (R : Type) [CommRing R] (X : Scheme.{0})
    (s : X ⟶ Sp R), Smooth s → IsSeparated s → QuasiCompact s → Function.Bijective (cmp1 s) ∧
    ∃ e : SecondDeRham s ≃ₗ[R] HH2 s, ∀ a b : FirstDeRham s, e (cup _ a b) = cupHH s (cmp1 s a) (cmp1 s b) := by
  intro R _ X s hs hsep hqc
  obtain ⟨e₁, e₂, hcup, hcmp, -⟩ := hP
  let D := ofSmooth R X s hs hsep hqc
  have key : ∀ c : FirstDeRham s, e₁ D c = cmp1 s c := fun c ↦ by
    have h1 := hcmp D (IsMor.id (dp0 R) s) c
    have h2 : (IsMor.id (dp0 R) s).pull1 c = c := IsMor.pullCohomologyOne_id _ c
    exact (congrArg (e₁ D) h2).symm.trans h1
  refine ⟨?_, e₂ D, fun a b ↦ ?_⟩
  · have hf : (cmp1 s : FirstDeRham s → HH1 s) = e₁ D := funext fun c ↦ (key c).symm
    rw [hf]; exact (e₁ D).bijective
  · rw [← key, ← key]; exact hcup D a b

end GlobalTheory.CechDR
