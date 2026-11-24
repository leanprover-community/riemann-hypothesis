module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemSpanAaF
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrFacInvMul
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
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.IsLoUniConjTranspose

@[expose] public section

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section LocU

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem locU_mul (A B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    locU Z p A * locU Z p B = locU Z p (A * B) := by
  ext i j

  simp only [Matrix.mul_apply, locU_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc _ = Ring.inverse (frFac Z.δ p i) * (D.s.atP p).ιE (A i k) *
        (frFac Z.δ p k * Ring.inverse (frFac Z.δ p k)) * (D.s.atP p).ιE (B k j) * frFac Z.δ p j := by ring
    _ = _ := by rw [frFac_mul_inv, mul_one]; ring

theorem locU_sub_one (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    locU Z p A - 1 = locU Z p (A - 1) := by
  ext i j
  simp only [Matrix.sub_apply, locU_apply, map_sub, Matrix.one_apply]
  split_ifs with h
  · subst h
    rw [map_one, mul_sub, sub_mul, mul_one, frFac_inv_mul]
  · simp only [map_zero, sub_zero]

end LocU

end Formalism.L2.SG.Pf.FibQ
