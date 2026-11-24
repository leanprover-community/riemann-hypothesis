module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
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

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

namespace GlobalTheory.CoefDuty.MemberO

variable {D : D7}


theorem live_iff (L : LocAll (lay0 D)) (i : L.X.nd.Loc) : Live (withLoc L).nd i ↔ Live L.lay.fixZ.nd i := Iff.rfl


theorem zdecomp_iff (L : LocAll (lay0 D)) (i : L.X.nd.Loc) : ZDecomp (withLoc L).nd i ↔ ZDecomp L.lay.fixZ.nd i := Iff.rfl


theorem chosen_iff (L : LocAll (lay0 D)) (i : L.X.nd.Loc) (S : Set ℂ) :
    Chosen (withLoc L).nd (withLoc L).naut i S ↔ Chosen L.lay.fixZ.nd L.lay.fixZ.naut i S := Iff.rfl


theorem goodR_iff (L : LocAll (lay0 D)) (i : L.X.nd.Loc) :
    (∃ r, GoodR (withLoc L).nd i r) ↔ ∃ r, GoodR L.lay.fixZ.nd i r := Iff.rfl


theorem taken_iff (L : LocAll (lay0 D)) (i : L.X.nd.Loc) :
    (∃ r ρ, GoodR (withLoc L).nd i r ∧ TakenWild (withLoc L).nd i r ρ) ↔
      ∃ r ρ, GoodR L.lay.fixZ.nd i r ∧ TakenWild L.lay.fixZ.nd i r ρ := Iff.rfl

end GlobalTheory.CoefDuty.MemberO

namespace GlobalTheory.CoefDuty.MemberO



end GlobalTheory.CoefDuty.MemberO

end
