module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimit
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
open Matrix

theorem _root_.GlobalTheory.T.ainf_closed_membership_limit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (mem : (Fin d → Ainf l) → Prop), mem 0 → (∀ y z, mem y → mem z → mem (y + z)) → (∀ (c : bk.S) y, mem y → mem (fun a => bk.ev c * y a)) → (∀ y, mem (fun a => (l : Ainf l) * y a) → mem y) → (∀ y : ℕ → Fin d → Ainf l, (∀ n, mem (y n)) → (∀ n a, (l : Ainf l) ^ n ∣ y (n + 1) a - y n a) → ∀ z : Fin d → Ainf l, (∀ n a, (l : Ainf l) ^ n ∣ z a - y n a) → mem z) → ∀ (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Y' : Matrix (Fin d) (Fin d) (WCb l)), (Y1.map (inclW l)).det ≠ 0 → IsUnit Y' → (∀ c : Fin d → bk.S, mem (Y1 *ᵥ fun a => bk.ev (c a))) → (∀ y, mem y → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun a => inclW l (y a)) = Y' *ᵥ w) → ∃ Y : Matrix (Fin d) (Fin d) (Ainf l), IsUnit (Y.map (inclW l)) ∧ ∀ y, mem y ↔ ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a) := by
  first | exact @GlobalTheory.BSP.saturated_module_free | exact GlobalTheory.BSP.saturated_module_free | (intros; apply GlobalTheory.BSP.saturated_module_free <;> assumption)
