module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountPositivity.LeadingMinorFullEqProd
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.CntLocal

@[expose] public section

noncomputable section

namespace PI.CntNotPosW

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem totPos_of_flags (D : Formalism.BasicNotions.D7) {T T' : ℕ} (F : FlagG (VS D) D.R.rS (T : D.host.E))
    (F' : FlagG (VS D) D.R.rS (T' : D.host.E)) (hG : Gflag F F' ≠ 0) : TotPos (Gflag F F') := by
  unfold TotPos
  intro τ
  haveI := D.host.isCMField_hostE
  refine gflag_pos (p' := ((VS D).sig (embS D τ)).1) (q' := ((VS D).sig (embS D τ)).2) F F' (embS D τ)
    (fun a => NumberField.IsCMField.complexEmbedding_complexConj _ (embS D τ) a) (D.sp.Y_sig 0 (embS D τ)) ?_ hG
  rw [D.sp.baseSpace_signature_eq]
  rfl

end PI.CntNotPosW
