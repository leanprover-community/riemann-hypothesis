module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FvecMemAsp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PairCorankPositivity.FinrankOrthAddLe
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UUE_eq_Asp {D : D7} {T T' : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hΛ : Submodule.IsFullLattice D.host.E Λ) (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (hL : IsLift Λ F) (hL' : IsLift Λ F') : UUE Λ F F' = Asp F.fl F'.fl := by
  refine le_antisymm ?_ ?_
  · have hX' : F'.fl.X ≤ Asp F.fl F'.fl := by rw [← Asp_symm]; exact X_le_Asp F'.fl F.fl
    have hz' : F'.fl.z ∈ Asp F.fl F'.fl := by rw [← Asp_symm]; exact z_mem_Asp F'.fl F.fl
    have key : UU Λ F F' ≤ (Asp F.fl F'.fl).restrictScalars (𝓞 D.host.E) := by
      unfold UU
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · intro y hy
        exact X_le_Asp F.fl F'.fl (Submodule.mem_inf.1 hy).2
      · rw [Submodule.span_le, Set.singleton_subset_iff, hL.2]
        exact z_mem_Asp F.fl F'.fl
      · intro y hy
        exact hX' (Submodule.mem_inf.1 hy).2
      · rw [Submodule.span_le, Set.singleton_subset_iff, hL'.2]
        exact hz'
    unfold UUE spanE
    rw [Submodule.span_le]
    intro x hx
    exact key hx
  · rw [Asp, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact PI.PairCorankPos.W.frame_mem_UUE Λ hΛ F F' hL hL' i

end Formalism.L2.SG.NGCut.NormalVectorPairings
