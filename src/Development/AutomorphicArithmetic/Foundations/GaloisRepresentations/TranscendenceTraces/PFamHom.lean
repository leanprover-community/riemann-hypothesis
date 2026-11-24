module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiExact
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private noncomputable def postFam {Z S : Scheme.{0}} {p : Z ⟶ S} {R : Type} [CommRing R] {G K J : Shv R}
    (t : Fam0 p G K) (m : K ⟶ J) : Fam0 p G J where
  app A := ((m.hom.app (op A.U)).hom.toAddMonoidHom).comp (t.app A)
  nat {A B} s a := by
    change Sec.res s.g (Sec.map m (t.app B a)) = Sec.map m (t.app A (Sec.res s.k a))
    rw [← t.nat s a, map_res]

theorem UpperTheory.Gal.TranscendenceTraces.famHom_of :
    FamHom := by
  intro Q Z S p Φ _ e hrep I J
  constructor
  · intro m
    refine ⟨⟨fun n => postFam (e (I.X n)) (m.f n), fun A s t a => ?_⟩, fun n A a => rfl⟩
    have hc := congrArg (fun φ => Sec.map φ ((e (I.X s)).app A a)) (m.comm s t)
    exact hc.trans (congrArg (Sec.map (m.f t)) (hrep.nat (I.d s t) A a))
  · intro τ
    choose mm hmm _ using fun n => hrep.univ (I.X n) (J.X n) (τ.deg n)
    refine ⟨⟨mm, fun i j _ => ?_⟩, fun n A a => (hmm n A a).symm⟩
    apply (hrep.univ (I.X i) (J.X j) (postFam (τ.deg i) (J.d i j))).unique
    · intro A a
      exact congrArg (Sec.map (J.d i j)) (hmm i A a)
    · intro A a
      exact ((congrArg (Sec.map (mm j)) (hrep.nat (I.d i j) A a)).trans (hmm j A _)).trans
        (τ.comm A i j a).symm
