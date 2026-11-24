module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1BallCocycleLogCyclotomic
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

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.cocycle_eq_log_cyclotomic_smul_add_coboundary : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ s : ℕ, Lev l s → (∀ c : GQ l → PadicComplex l, CocOn (Gj K s) (fun g y => act g y) {y | ‖y‖ ≤ 1} c → ∃ α ∈ inC (Ks K s), ‖α‖ ≤ (l : ℝ) ^ (1 + s) ∧ ∃ b : PadicComplex l, ∀ σ ∈ Gj K s, c σ = algebraMap ℚ_[l] (PadicComplex l) (logZl l (χ σ : ℚ_[l])) * α + (act σ b - b)) ∧ ∀ α ∈ inC (Ks K s), ∀ b : PadicComplex l, (∀ σ ∈ Gj K s, algebraMap ℚ_[l] (PadicComplex l) (logZl l (χ σ : ℚ_[l])) * α = act σ b - b) → α = 0 := by
  first | exact @GlobalTheory.Cyc.LogClass.image_H1_logChi | exact GlobalTheory.Cyc.LogClass.image_H1_logChi | (intros; apply GlobalTheory.Cyc.LogClass.image_H1_logChi <;> assumption)
