module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IndepSpanRankTransferLargeFieldComplex
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

theorem _root_.GlobalTheory.T.indep_span_rank_transfer_largeField_complex : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (R : Rdg X) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (t : Idx D j N → ℂ), R.Generic t → ∀ (u : WeightFamilies.Wt D j) (ι : Type) [Fintype ι] (p : ι → MvPolynomial (Idx D j N) X.Forms), (∀ i, OfWt X u (p i)) → (LinearIndependent (Kp X la N) (fun i => toRp X la N (p i)) ↔ LinearIndependent ℂ (fun i => R.toFn t (p i))) ∧ (∀ q, OfWt X u q → (toRp X la N q ∈ Submodule.span (Kp X la N) (Set.range fun i => toRp X la N (p i)) ↔ R.toFn t q ∈ Submodule.span ℂ (Set.range fun i => R.toFn t (p i)))) ∧ Module.finrank (Kp X la N) (Submodule.span (Kp X la N) (Set.range fun i => toRp X la N (p i))) = Module.finrank ℂ (Submodule.span ℂ (Set.range fun i => R.toFn t (p i))) := by
  first | exact @GlobalTheory.reading_transfer | exact GlobalTheory.reading_transfer | (intros; apply GlobalTheory.reading_transfer <;> assumption)
