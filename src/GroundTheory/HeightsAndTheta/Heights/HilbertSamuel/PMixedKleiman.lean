module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedKleiman
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedKleimanTop
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

theorem MixedKleiman.atDim_of_steps (hL : MixedKleimanLow.Statement) (hT : MixedKleimanTop.Statement) :
    ∀ d, MixedKleiman.AtDim d := by
  intro d
  induction d with
  | zero => exact MixedKleiman.atDim_zero
  | succ n ih =>
    have ih' : MixedKleiman.AtDim (n + 1 - 1) := by simpa using ih
    have hLow : MixedKleiman.LowAt (n + 1) := hL (n + 1) ih'
    intro K _ ι _ P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj
    rcases lt_or_eq_of_le hj with hj | rfl
    · exact hLow K ι P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj
    · have hlist : (fun i : Fin (n + 1) => if (i : ℕ) < n + 1 then M else A) = fun _ => M :=
        funext fun i => if_pos i.isLt
      rw [hlist]
      rcases Nat.lt_or_ge n 1 with hn | hn
      · obtain rfl : n = 0 := by omega
        have hW := hhM P hP le_rfl
        have e : (fun _ : Fin 1 => M) = ![M] := by
          funext i
          fin_cases i
          rfl
        simpa [e] using hW
      · exact hT (n + 1) (by omega) ih' hLow K ι P P0 M II hII h1 hP h0 hsM hnM hcM hhM

theorem MixedKleiman.proof (hL : MixedKleimanLow.Statement) (hT : MixedKleimanTop.Statement) :
    MixedKleiman.Statement := by
  intro K _ ι _ P P0 d M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj
  exact MixedKleiman.atDim_of_steps hL hT d K ι P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj

end GroundTheory.Heights₂.Heights.HilbertSamuel
