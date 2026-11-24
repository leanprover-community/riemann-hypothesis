module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionZeroOneProperties
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.closedDiscGaugeCompletion_zero_one_properties : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ x y : Disc l (0 : Wq l bk.a) 1, ‖x * y‖ = ‖x‖ * ‖y‖) ∧ (∀ x : Disc l (0 : Wq l bk.a) 1, ‖x‖ ≤ 1 → ∃ w, x = toDisc l (0 : Wq l bk.a) 1 w) ∧ Function.Injective (toDisc l (0 : Wq l bk.a) 1) ∧ ∀ w : Wq l bk.a, IsUnit w → ‖toDisc l (0 : Wq l bk.a) 1 w‖ = 1 := by
  first | exact @GlobalTheory.BSP.disc_zero_one | exact GlobalTheory.BSP.disc_zero_one | (intros; apply GlobalTheory.BSP.disc_zero_one <;> assumption)
