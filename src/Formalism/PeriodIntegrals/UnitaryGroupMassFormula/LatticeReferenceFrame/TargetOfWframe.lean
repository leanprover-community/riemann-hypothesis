module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.PPAssemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.GWGlue
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.GlueHoldsVar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.IdemMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.LocGlob
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.LocalAssemblyPrincipal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.ThetaSeriesExistence
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

namespace PI.ScRefExists.Top

open PI.ScRefExists.Sk

theorem target_of_wframe (h : WFrame) : PI.ScRefExists.Target :=
  target_of_steps PI.ScRefExists.GlueC.glue_holds_var PI.ScRefExists.TH.theta_series_existence
    PI.ScRefExists.Id.idemLift PI.ScRefExists.LG.local_global_principle_alt
    (PI.ScRefExists.GWG.globW_of (gwpp_of h PI.ScRefExists.PPA.local_assembly_principal)
      PI.ScRefExists.GWG.chinese_remainder_gluing)

end PI.ScRefExists.Top
