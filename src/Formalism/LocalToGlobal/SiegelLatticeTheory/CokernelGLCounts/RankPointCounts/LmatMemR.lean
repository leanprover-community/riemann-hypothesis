module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemROf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.PairValDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.IsLoUniConjTranspose

@[expose] public section

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ModeG

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

theorem det_upper {X : Formalism.L2.SG.LsDatumB.MatP D p} (h1 : ∀ a b, b < a → X a b = 0) (h2 : ∀ a, X a a = 1) :
    X.det = 1 := by
  have hb : X.BlockTriangular id := fun i j hij => h1 i j hij
  rw [Matrix.det_of_upperTriangular hb]
  simp [h2]

theorem det_lower {X : Formalism.L2.SG.LsDatumB.MatP D p} (h1 : ∀ a b, a < b → X a b = 0) (h2 : ∀ a, X a a = 1) :
    X.det = 1 := by
  have hb : X.BlockTriangular OrderDual.toDual := fun i j hij => h1 i j hij
  rw [Matrix.det_of_lowerTriangular X hb]
  simp [h2]

theorem lmat_mem_R (hs : (Z.M p).split = some g) {x y : (D.s.atP p).Ep} (hx : x ∈ (Z.M p).L.O)
    (hy : y ∈ (Z.M p).L.O)
    (hc : ∃ o ∈ (Z.M p).L.O, x - (Z.M p).L.cj y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * o) :
    g.e.symm ((g.e x).1, (g.e y).2) ∈ (Z.M p).R := by
  obtain ⟨o, ho, he⟩ := hc
  refine mem_R_of Z p g hs (by rw [AlgEquiv.apply_symm_apply]; exact (comp_mem Z p g hx).1)
    (by rw [AlgEquiv.apply_symm_apply]; exact (comp_mem Z p g hy).2) ⟨(g.e o).1, (comp_mem Z p g ho).1, ?_⟩
  rw [AlgEquiv.apply_symm_apply]
  have h := congrArg (fun t => (g.e t).1) he
  simp only [map_sub, map_mul, AlgEquiv.commutes, g.e_cj, Prod.fst_sub, Prod.fst_mul,
    Prod.fst_swap, Prod.algebraMap_apply] at h
  rw [h]
  rfl

end ModeG

end Formalism.L2.SG.Pf.FibQ
