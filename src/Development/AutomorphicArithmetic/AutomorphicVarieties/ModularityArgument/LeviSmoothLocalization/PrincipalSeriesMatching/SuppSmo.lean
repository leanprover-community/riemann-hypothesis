module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Strong
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

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.suppSmo :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.SuppSmo := by
  intro K _ _ _ n _ π π' h t v hw
  have e : π = π' := GlobalTheory.CuspRep.CuspSub.ext (UpperTheory.V.Af.strongMultOneC K n π π'
    (h.mono fun w ⟨B, h₁, h₂⟩ =>
      ⟨B, (GlobalTheory.CuspRep.CG.hasSat_mk π w B).1 h₁, (GlobalTheory.CuspRep.CG.hasSat_mk π' w B).1 h₂⟩))
  exact e ▸ hw
