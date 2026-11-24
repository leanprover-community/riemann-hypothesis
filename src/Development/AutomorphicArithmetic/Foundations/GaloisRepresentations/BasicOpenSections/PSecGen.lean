module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.ResClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

theorem UpperTheory.Gal.Mod.secGen :
    SecGen := by
  intro Z Y g _ V _ _ _ y
  have hP : IsProper g := inferInstance
  have hV : ValuativeCriterion g := by
    rw [IsProper.eq_valuativeCriterion] at hP
    exact hP.1.1.1
  let e : Spec (CommRingCat.of (FractionRing V)) ⟶ Spec (CommRingCat.of V) :=
    Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    show (e ≫ z) ≫ g = e ≫ y
    rw [Category.assoc, show z ≫ g = y from hz]
  · intro z₁ hz₁ z₂ hz₂ h
    have h₁ : z₁ ≫ g = y := hz₁
    have h₂ : z₂ ≫ g = y := hz₂
    have h' : e ≫ z₁ = e ≫ z₂ := h
    let S : ValuativeCommSq g :=
      ⟨V, FractionRing V, e ≫ z₁, y, ⟨by rw [Category.assoc, h₁]⟩⟩
    have hu := ValuativeCriterion.uniqueness hV S
    have := @Subsingleton.elim _ hu
      ⟨z₁, rfl, h₁⟩ ⟨z₂, h'.symm, h₂⟩
    exact congrArg CommSq.LiftStruct.l this
  · intro x hx
    have hx' : x ≫ g = e ≫ y := hx
    let S : ValuativeCommSq g := ⟨V, FractionRing V, x, y, ⟨hx'⟩⟩
    obtain ⟨⟨l⟩⟩ := ValuativeCriterion.existence hV S
    exact ⟨l.l, l.fac_right, l.fac_left⟩
