module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GenericSectionsPolynomialDictionary
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

theorem _root_.GlobalTheory.T.genericSections_polynomial_dictionary : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (R : Rdg X) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ), (∀ i, toRp X la N (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k))) = sec X la w i ∧ R.toFn t (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k))) = R.s w t i ∧ OfWt X wL (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k)) : MvPolynomial (Idx D j N) X.Forms)) ∧ (∀ F, toRp X la N (MvPolynomial.C F) = emb X la N F ∧ R.toFn t (MvPolynomial.C F) = R.ev F) ∧ (∀ u (F : B.Cusp j u), OfWt X u (MvPolynomial.C (X.inc u F) : MvPolynomial (Idx D j N) X.Forms)) ∧ (∀ u u' (p q : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → OfWt X u' q → OfWt X (wadd u u') (p * q)) ∧ (∀ u (p : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → toRp X la N p ∈ Vw X la N u ∧ R.toFn t p ∈ R.sp u Set.univ) ∧ (∀ u u', ∀ f ∈ R.sp u Set.univ, ∀ g ∈ R.sp u' Set.univ, f * g ∈ R.sp (wadd u u') Set.univ) ∧ (∀ u (s : Set (B.Cusp j u)), R.sp u (Submodule.span B.KO s) = R.sp u s) ∧ (∀ u (M : Submodule B.KO (B.Cusp j u)), FiniteDimensional ℂ (R.sp u M) ∧ Module.finrank ℂ (R.sp u M) = Module.finrank B.KO M) := by
  first | exact @GlobalTheory.Shares.polyDictionary | exact GlobalTheory.Shares.polyDictionary | (intros; apply GlobalTheory.Shares.polyDictionary <;> assumption)
