module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanCyclotomicTwoCocyclesFiniteExtension
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.span_cyclotomic_twoCocycles_finite_extension : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → (∃ z0 : ↥(GK K) × ↥(GK K) → ℚ_[l], (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → ℚ_[l], Continuous z → (∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : ℚ_[l], CobL (P.PD K) (z - x • z0)) → ∃ z0 : ↥(GK K) × ↥(GK K) → LL, (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → LL, Continuous z → (∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : LL, CobL (P.PD K) (z - x • z0) := by
  first | exact @GlobalTheory.span_cocycles_cyc_ext | exact GlobalTheory.span_cocycles_cyc_ext | (intros; apply GlobalTheory.span_cocycles_cyc_ext <;> assumption)
