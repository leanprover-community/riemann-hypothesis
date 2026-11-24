module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaPair
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
import GroundTheory.AutomorphicForms.LocallyProfinite

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HenQ
open GlobalTheory.CuspRep (GA Af finGL)

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.HenQ

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem finGL_apply (k : GL (Fin n) (Af K)) (a b : Fin n) :
    ((finGL K n k : GA K n) : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) a b =
      (1 : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) a b
        - GlobalTheory.CuspRep.sFin K ((1 : Matrix (Fin n) (Fin n) (Af K)) a b)
        + GlobalTheory.CuspRep.sFin K ((k : Matrix (Fin n) (Fin n) (Af K)) a b) := rfl

theorem sFin_fst (x : Af K) : (GlobalTheory.CuspRep.sFin K x).1 = 0 := rfl

end GlobalTheory.HenQ

namespace GlobalTheory.HenQ

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

end GlobalTheory.HenQ
