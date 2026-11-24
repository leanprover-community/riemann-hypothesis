module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterSecond
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Base

private theorem tf (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

attribute [local instance] tf

private theorem algClo (L Ω : Type) [Field L] [CharZero L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra L Ω] :
    IsAlgClosure L Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩

private theorem cyc_cont (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  _root_.UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cyc_cont F Ω l

private theorem cyc_conj {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    {c c' : G F Ω} (h : UpperTheory.V.Af.IsConjEl c) (h' : UpperTheory.V.Af.IsConjEl c') : cycBar F Ω l c = cycBar F Ω l c' := by
  have h1 : cycZ F Ω l c = -1 := UpperTheory.V.IsConjOm.cyc (E := F) (σ := c.toRingEquiv) h
  have h2 : cycZ F Ω l c' = -1 := UpperTheory.V.IsConjOm.cyc (E := F) (σ := c'.toRingEquiv) h'
  simp only [cycBar, MonoidHom.comp_apply, h1, h2]
