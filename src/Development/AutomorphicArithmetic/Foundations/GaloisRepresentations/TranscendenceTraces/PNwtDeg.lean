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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtDeg_of :
    WtNormal → WtDegConst → MultSum → MultBC → GenBasic → NwtDeg := by
  intro hN hD hMS hBC hG Z' Z S K _ v p' p g _ _ hpb hLoc hg
  obtain ⟨hW, hgen⟩ := hN p hLoc
  obtain ⟨d, hd⟩ := hD p (nwt p) hW
  rw [hd]
  haveI : IsFinite p' := MorphismProperty.of_isPullback (P := @IsFinite) hpb inferInstance
  let Ω := AlgebraicClosure K
  let y : gp Ω ⟶ gp K := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  have hval := congrArg (fun w : Wt S => w Ω (y ≫ g)) hd
  simp only [Wt.const] at hval
  have h1 : Wt.push p (nwt p) Ω (y ≫ g) = Wt.push p (mult p) Ω (y ≫ g) := by
    simp only [Wt.push]
    apply finsum_congr
    intro z
    apply finsum_congr
    intro hz
    apply hgen
    have hz' : z ≫ p = y ≫ g := hz
    rw [hz', pt_comp, Subsingleton.elim (pt y) (IsLocalRing.closedPoint K)]
    exact (hG.2.2 S _).mpr hg
  have h2 : Wt.push p (mult p) Ω (y ≫ g) = Wt.push p' (mult p') Ω y := by
    simp only [Wt.push]
    symm
    rw [finsum_mem_eq_of_bijOn (fun z => z ≫ v) (fib_bijOn hpb y)
      (g := fun z => mult p Ω z)]
    intro z _
    rw [hBC v p' p g hpb]
    rfl
  have h3 := hMS p' Ω y
  have h4 : pt y = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  rw [h1, h2, h3, h4] at hval
  rw [hval]
