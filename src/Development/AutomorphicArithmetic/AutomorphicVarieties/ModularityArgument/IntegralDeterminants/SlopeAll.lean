module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.SlopeAllOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.SlopeCsd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.SlopeGood
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

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

namespace UpperTheory.V.Z.Int

theorem slopeAll (hL : GlobalTheory.GalCut.QuadLift) (hD : GlobalTheory.Cong.DescOffT) : SlopeAll := slopeAllOf hL (slopeGood (slopeCsd hD))

theorem intP (hL : GlobalTheory.GalCut.QuadLift) (hD : GlobalTheory.Cong.DescOffT) : UpperTheory.V.Br.IntP :=
  fun K _ _ _ n hn m hm _ _ π hπ _ w _ _ _ _ B hB => slopeAll hL hD K n (by omega) m hm π hπ.1 hπ.2.1 w B hB

theorem intK (hL : GlobalTheory.GalCut.QuadLift) (hD : GlobalTheory.Cong.DescOffT) : IntK :=
  fun K _ _ _ n hn m hm _ _ π hπ _ w _ _ _ _ B hB => slopeAll hL hD K n (by omega) m hm π hπ.1
    ⟨quadChar K ^ n, fun v => by rw [locInf_pow, quadChar_locInf], by
      rw [map_pow, compNorm_quadChar, one_pow]
      exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hπ.2.1⟩ w B hB

end UpperTheory.V.Z.Int
