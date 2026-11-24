module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagAtScale
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Rk

theorem hsNormSq_add_le_three_halves {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A B : Wq →L[ℂ] Wp) :
    hsNormSq (A + B) ≤ 3 / 2 * hsNormSq A + 3 * hsNormSq B := by
  rw [hsNormSq_eq, hsNormSq_eq, hsNormSq_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := norm_add_le (A (stdOrthonormalBasis ℂ Wq i)) (B (stdOrthonormalBasis ℂ Wq i))
  have h0 := norm_nonneg (A (stdOrthonormalBasis ℂ Wq i) + B (stdOrthonormalBasis ℂ Wq i))
  rw [ContinuousLinearMap.add_apply]
  nlinarith [sq_nonneg (‖A (stdOrthonormalBasis ℂ Wq i)‖ - 2 * ‖B (stdOrthonormalBasis ℂ Wq i)‖)]

theorem hsDev_le_split_three_halves : ∀ (D : D7) (u : D.what₂.Word), GlobalTheory.Core.Rk.hsDev D u ≤
    3 / 2 * hsNormSq (Kmat D.s u u - AdmissibleBoundsFromSource.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) + 3 * hsNormSq (AdmissibleBoundsFromSource.Kpp D u u) := by
  intro D u
  have e : Kmat D.s u u - ContinuousLinearMap.id ℂ (D.s.Cu u) =
      (Kmat D.s u u - AdmissibleBoundsFromSource.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) + AdmissibleBoundsFromSource.Kpp D u u := by abel
  unfold GlobalTheory.Core.Rk.hsDev
  rw [e]
  exact hsNormSq_add_le_three_halves _ _

end GlobalTheory.Core.Rk
