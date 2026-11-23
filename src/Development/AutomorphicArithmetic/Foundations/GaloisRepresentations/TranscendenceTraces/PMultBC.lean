module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private lemma length_self_eq {R R' : Type} [CommRing R] [CommRing R'] (e : R ≃+* R') :
    Module.length R R = Module.length R' R' := by
  have h : ((Module.length R R : ℕ∞) : WithBot ℕ∞) = (Module.length R' R' : ℕ∞) := by
    rw [Module.coe_length, Module.coe_length]
    exact Order.krullDim_eq_of_orderIso e.idealComapOrderIso.symm
  exact_mod_cast h

private lemma length_stalk_eq {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (x : X) (y : Y) (hy : f x = y) :
    Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y) =
      Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) := by
  subst hy
  exact length_self_eq (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv

theorem UpperTheory.Gal.TranscendenceTraces.multBC_of :
    MultBC := by
  intro Z' S' Z S v p' p g h
  funext Ω _ _ z
  have hw : (z ≫ p') ≫ g = (z ≫ v) ≫ p := by
    simp only [Category.assoc, h.w]
  have hP : IsPullback (pullback.fst p' (z ≫ p') ≫ v) (pullback.snd p' (z ≫ p')) p ((z ≫ v) ≫ p) := by
    rw [← hw]
    exact (IsPullback.of_hasPullback p' (z ≫ p')).paste_horiz h
  have hl : (pullback.lift z (𝟙 _) (Category.id_comp _).symm : gp Ω ⟶ pullback p' (z ≫ p')) ≫ hP.isoPullback.hom =
      pullback.lift (z ≫ v) (𝟙 _) (Category.id_comp _).symm := by
    apply pullback.hom_ext
    · rw [Category.assoc, hP.isoPullback_hom_fst, pullback.lift_fst_assoc, pullback.lift_fst]
    · rw [Category.assoc, hP.isoPullback_hom_snd, pullback.lift_snd, pullback.lift_snd]
  have hpt : hP.isoPullback.hom (pt (pullback.lift z (𝟙 _) (Category.id_comp _).symm : gp Ω ⟶ pullback p' (z ≫ p'))) =
      pt (pullback.lift (z ≫ v) (𝟙 _) (Category.id_comp _).symm : gp Ω ⟶ pullback p ((z ≫ v) ≫ p)) := by
    rw [← pt_comp, hl]
  simp only [Wt.comap, mult]
  rw [length_stalk_eq hP.isoPullback.hom _ _ hpt]
