module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobalLUnit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobVol
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

noncomputable section
open scoped NumberField

namespace PI.UnitaryGroupMassFormula.UnitDetRoot

open PI

theorem globalLUnit : GlobalLUnit :=
  globalLUnit_of
    (fun F _ _ _ _ _ c h => vol_smul_le F c h)
    (fun F _ _ _ δ Λ => vol_img F δ Λ)
    (fun _ _ _ _ _ _ _ _ _ _ _ hok => vol_std_le hok)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => vol_std_ne_bot)

end PI.UnitaryGroupMassFormula.UnitDetRoot
