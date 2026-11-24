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
import Mathlib.Tactic.Linter.HaveILetI
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtAgree_of :
    NwtOpen → WtUnique → GenBasic → MultBC → NwtAgree := by
  intro hOpen hUniq hGen _ Z S p _ A B _ _ w w' hw hw' Ω _ _ z z' hz
  have hc : pullback.fst A.u B.u ≫ A.u = pullback.snd A.u B.u ≫ B.u := pullback.condition
  have hP : IsPullback (pullback.fst p (pullback.fst A.u B.u ≫ A.u))
      (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) p (pullback.fst A.u B.u ≫ A.u) :=
    IsPullback.of_hasPullback _ _
  have hP' : IsPullback (pullback.fst p (pullback.fst A.u B.u ≫ A.u))
      (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) p (pullback.snd A.u B.u ≫ B.u) := by
    rw [← hc]
    exact hP
  have eA : pullback.fst p (pullback.fst A.u B.u ≫ A.u) ≫ p =
      (pullback.snd p (pullback.fst A.u B.u ≫ A.u) ≫ pullback.fst A.u B.u) ≫ A.u := by
    rw [Category.assoc]
    exact hP.w
  have eB : pullback.fst p (pullback.fst A.u B.u ≫ A.u) ≫ p =
      (pullback.snd p (pullback.fst A.u B.u ≫ A.u) ≫ pullback.snd A.u B.u) ≫ B.u := by
    rw [Category.assoc]
    exact hP'.w
  let C : Sq A.r := ⟨pullback A.u B.u, pullback p (pullback.fst A.u B.u ≫ A.u), pullback.fst A.u B.u,
    A.pb.lift _ _ eA, pullback.snd p (pullback.fst A.u B.u ≫ A.u),
    IsPullback.of_right (by rw [A.pb.lift_fst]; exact hP) (A.pb.lift_snd _ _ _) A.pb⟩
  let C' : Sq B.r := ⟨pullback A.u B.u, pullback p (pullback.fst A.u B.u ≫ A.u), pullback.snd A.u B.u,
    B.pb.lift _ _ eB, pullback.snd p (pullback.fst A.u B.u ≫ A.u),
    IsPullback.of_right (by rw [B.pb.lift_fst]; exact hP') (B.pb.lift_snd _ _ _) B.pb⟩
  haveI : IsOpenImmersion C.u := inferInstanceAs (IsOpenImmersion (pullback.fst A.u B.u))
  haveI : IsOpenImmersion C'.u := inferInstanceAs (IsOpenImmersion (pullback.snd A.u B.u))
  have h1 : IsNwt (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) (w.comap C.v) := hOpen A.r w C hw
  have h2 : IsNwt (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) (w'.comap C'.v) := hOpen B.r w' C' hw'
  haveI : IsFinite (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) := MorphismProperty.of_isPullback hP ‹_›
  have hE : w.comap C.v = w'.comap C'.v :=
    hUniq _ _ _ h1.1 h2.1 {s | GenPt s} (hGen.1 _) fun Ω _ _ y hy => by
      rw [h1.2 Ω y hy, h2.2 Ω y hy]
  have e1 : (z ≫ A.r) ≫ A.u = (z' ≫ B.r) ≫ B.u := by
    rw [Category.assoc, Category.assoc, ← A.pb.w, ← B.pb.w, ← Category.assoc, ← Category.assoc, hz]
  have e2 : (z ≫ A.v) ≫ p = pullback.lift (z ≫ A.r) (z' ≫ B.r) e1 ≫ pullback.fst A.u B.u ≫ A.u := by
    rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, A.pb.w]
  let z0 : gp Ω ⟶ pullback p (pullback.fst A.u B.u ≫ A.u) :=
    pullback.lift (z ≫ A.v) (pullback.lift (z ≫ A.r) (z' ≫ B.r) e1) e2
  have hz0 : z0 ≫ C.v = z := by
    apply A.pb.hom_ext
    · change (z0 ≫ A.pb.lift _ _ eA) ≫ A.v = _
      rw [Category.assoc, A.pb.lift_fst]
      exact pullback.lift_fst _ _ _
    · change (z0 ≫ A.pb.lift _ _ eA) ≫ A.r = _
      rw [Category.assoc, A.pb.lift_snd, pullback.lift_snd_assoc, pullback.lift_fst]
  have hz0' : z0 ≫ C'.v = z' := by
    apply B.pb.hom_ext
    · change (z0 ≫ B.pb.lift _ _ eB) ≫ B.v = _
      rw [Category.assoc, B.pb.lift_fst, ← hz]
      exact pullback.lift_fst _ _ _
    · change (z0 ≫ B.pb.lift _ _ eB) ≫ B.r = _
      rw [Category.assoc, B.pb.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd]
  have := congrFun (congrFun (congrFun (congrFun hE Ω) ‹_›) ‹_›) z0
  simpa only [Wt.comap, hz0, hz0'] using this
