module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerEqProdLocalDiagonal
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

theorem _root_.GlobalTheory.T.adelicDiagonalUniformizer_eq_prod_localDiagonal : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (l' : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℕ)),
    (∀ w i, ((l' w i : ℕ) : ℤ) = l w i) → GlobalTheory.CellDec.tl n ϖ l = GlobalTheory.JSW.tl ϖ l' := by
  first | exact @GlobalTheory.CellDecNat.tl_eq_jsw_tl | exact GlobalTheory.CellDecNat.tl_eq_jsw_tl | (intros; apply GlobalTheory.CellDecNat.tl_eq_jsw_tl <;> assumption)
