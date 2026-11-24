module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDivLocalEmbeddingCloseToOne
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.norm_div_localEmbedding_close_to_one : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (σ : E' →+* w.adicCompletion E), (∀ x : E, σ (algebraMap E E' x) = algebraMap E _ x) → (∀ x : E', Valued.v (σ x) = w'.valuation E' x) → ∀ M : ℕ, ∃ M' : ℕ, ∀ z : E', z ≠ 0 → (∀ w'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'), w''.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal → w'' ≠ w' → w''.valuation E' (z - 1) ≤ WithZero.exp (-(M' : ℤ))) → Valued.v (algebraMap E (w.adicCompletion E) (Algebra.norm E z) / σ z - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  first | exact @GlobalTheory.NormCompat.RatioClose.norm_div_close_to_one | exact GlobalTheory.NormCompat.RatioClose.norm_div_close_to_one | (intros; apply GlobalTheory.NormCompat.RatioClose.norm_div_close_to_one <;> assumption)
