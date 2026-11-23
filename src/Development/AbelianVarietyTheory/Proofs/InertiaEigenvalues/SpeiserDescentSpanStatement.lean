module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpeiserDescentSpan
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


theorem _root_.GlobalTheory.T.mem_span_fixed_of_semilinear_action : ∀ {G L Ω M : Type} [Group G] [Field L] [Field Ω] [Algebra L Ω] [AddCommGroup M] [Module Ω M] [Module L M] [IsScalarTower L Ω M] (b : G → Ω → Ω) (a : G → L →+* Ω) (σ : G → M →+ M) (W : Submodule L M), (∀ g h c, a (g * h) c = b g (a h c)) → (∀ c, a 1 c = algebraMap L Ω c) → (∀ m, σ 1 m = m) → (∀ g h m, σ (g * h) m = σ g (σ h m)) → (∀ g (c : L) m, σ g (c • m) = a g c • σ g m) → (Set.range a).Finite → (∀ g, ∀ m ∈ W, σ g m ∈ W) → (∀ g, (∀ c, a g c = algebraMap L Ω c) → ∀ m ∈ W, σ g m = m) → ∀ m ∈ W, m ∈ Submodule.span Ω {m | m ∈ W ∧ ∀ g, σ g m = m} := by
  first | exact @GlobalTheory.speiser_descent_span | exact GlobalTheory.speiser_descent_span | (intros; apply GlobalTheory.speiser_descent_span <;> assumption)
