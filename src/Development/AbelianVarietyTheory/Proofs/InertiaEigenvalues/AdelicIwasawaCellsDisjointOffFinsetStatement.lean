module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaCellsDisjointOffFinset
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

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

theorem _root_.GlobalTheory.T.adelic_iwasawa_cells_disjoint_off_finset : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) →
    ∀ (l l' : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n), (∀ v ∈ S, l v = 0) → (∀ v ∈ S, l' v = 0) →
      (GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S → (GlobalTheory.CellDec.tl n ϖ l')⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S → l = l' := by
  first | exact @GlobalTheory.CellDec.eq_of_tl_inv_mul_mem_C0_of_tl_inv_mul_mem_C0 | exact GlobalTheory.CellDec.eq_of_tl_inv_mul_mem_C0_of_tl_inv_mul_mem_C0 | (intros; apply GlobalTheory.CellDec.eq_of_tl_inv_mul_mem_C0_of_tl_inv_mul_mem_C0 <;> assumption)
