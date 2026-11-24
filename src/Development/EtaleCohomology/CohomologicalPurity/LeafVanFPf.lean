module

public import Development.EtaleCohomology.CohomologicalPurity.LeafClCut
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.Cl

theorem range_frame_ι {d : ℕ} {P : SP d} (F : Frame P) :
    ((off F.B F.I : (Spec (CommRingCat.of F.B)).Opens) : Set (Spec (CommRingCat.of F.B))) =
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I))))ᶜ := by
  have h := range_comap_of_surjective (f := Ideal.Quotient.mk F.I) (hf :=
    Ideal.Quotient.mk_surjective)
  rw [Ideal.mk_ker] at h
  change (PrimeSpectrum.zeroLocus (F.I : Set F.B))ᶜ = _
  rw [← h]
  rfl

def Frame.sp {d : ℕ} {P : SP d} (F : Frame P) (hw : Etale F.w) : SP d where
  X := Spec (CommRingCat.of F.B)
  Z := Spec (CommRingCat.of (F.B ⧸ F.I))
  S := P.S
  p := F.w ≫ P.p
  ι := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I))
  e := P.e
  U := off F.B F.I
  cl := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  smX := by
    have := P.smX
    have : SmoothOfRelativeDimension 0 F.w := inferInstance
    simpa using (inferInstance : SmoothOfRelativeDimension (0 + (P.e + d)) (F.w ≫ P.p))
  smZ := by
    have hz : Etale F.z := MorphismProperty.of_isPullback F.cart hw
    have := P.smZ
    have : SmoothOfRelativeDimension 0 F.z := inferInstance
    have e : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I)) ≫ F.w ≫ P.p = F.z ≫ P.ι ≫ P.p := by
      rw [← Category.assoc, F.cart.w, Category.assoc]
    rw [e]
    simpa using (inferInstance : SmoothOfRelativeDimension (0 + P.e) (F.z ≫ P.ι ≫ P.p))
  hU := range_frame_ι F

theorem LeafVanF_of (hV : LeafVan) : LeafVanF := by
  intro hH d q _ P hq F hw i
  refine hV hH d q (F.sp hw) ?_ i
  have h := hq.map F.w.appTop.hom
  rw [map_natCast] at h
  exact h

end LateralTheory.CohomologicalPurity.Cl
