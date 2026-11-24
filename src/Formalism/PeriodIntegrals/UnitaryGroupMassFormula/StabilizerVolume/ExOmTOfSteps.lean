module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocExOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibInf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

theorem latSB_holds : LatSB := by
  intro F E _ _ _ _ d M n b v
  have : Module.Finite F E := Module.Finite.of_basis b
  exact PositiveNearLattice.isSB_latV b v n M

theorem exOmT_of_steps' (hI : FibInfEx) (hV : FibVEx) (hU : SdUniq) (hDI : DensFibInf)
    (hDV : DensFibV) (hR : RestrProd) : ExOmT :=
  exOmT_of_steps hI hV latSB_holds hU hDI hDV hR

theorem exOmT_of_open (hI : FibInfEx) (hV : FibVEx) (hU : SdUniq) (hR : RestrProd) : ExOmT :=
  exOmT_of_steps' hI hV hU densFibInf_holds densFibV_holds hR

end PI.VolStabS
