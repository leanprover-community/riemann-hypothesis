module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBaseEqOfClosedDiscExtendsNormLeOne
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

theorem _root_.GlobalTheory.T.exists_base_eq_of_closedDisc_extends_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, 0 < ρ → ρ < 1 → ∀ y : Disc l (s X) ρ, (∀ ρ₁ : ℝ≥0, ρ₁ < 1 → ∃ (ρ' : ℝ≥0) (R : Disc l (s X) ρ' →+* Disc l (s X) ρ) (y' : Disc l (s X) ρ'), ρ₁ ≤ ρ' ∧ ρ ≤ ρ' ∧ ρ' < 1 ∧ IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R ∧ R y' = y ∧ ‖y'‖ ≤ 1) → ∃ a, toDisc l (s X) ρ a = y := by
  first | exact @GlobalTheory.BSP.exists_toDisc_eq_of_extends_norm_le_one | exact GlobalTheory.BSP.exists_toDisc_eq_of_extends_norm_le_one | (intros; apply GlobalTheory.BSP.exists_toDisc_eq_of_extends_norm_le_one <;> assumption)
