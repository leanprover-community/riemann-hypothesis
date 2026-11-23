module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumACut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlobalCountOfModule
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ModSideUL
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

namespace Formalism.L2.SG.LsDatumA

def ModSide0G : Prop := Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSide0 M r n true)

def ModSideUG : Prop := Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSideU M r n true)

theorem modSide0_mode (h0G : ModSide0G) :
    Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSide0 M r n M.split.isSome) := by
  intro F _ _ _ E _ _ _ _ M hM r n
  cases h : M.split.isSome
  · exact modSide0L F E M hM r n
  · exact h0G F E M hM r n

theorem modSideU_mode (hUG : ModSideUG) :
    Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSideU M r n M.split.isSome) := by
  intro F _ _ _ E _ _ _ _ M hM r n
  cases h : M.split.isSome
  · exact modSideUL F E M hM r n
  · exact hUG F E M hM r n

theorem globalCount_of_split_mode (D : Formalism.BasicNotions.D7) (h0G : ModSide0G) (hUG : ModSideUG) : Formalism.MainNotions.ThinScalesBound.T2 D :=
  globalCount_of_module D (fun F _ _ _ E _ _ _ _ M hM => modSide0_mode h0G F E M hM _ _)
    (fun F _ _ _ E _ _ _ _ M hM => modSideU_mode hUG F E M hM _ _)

end Formalism.L2.SG.LsDatumA
