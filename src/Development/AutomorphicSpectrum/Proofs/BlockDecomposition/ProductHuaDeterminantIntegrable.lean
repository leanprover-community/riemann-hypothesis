module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HuaDeterminantIntegrableOfLtStatement
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
public import Mathlib.MeasureTheory.Integral.Pi
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

open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem integrable_prod_detW_rpow : ∀ (W : Type) [Fintype W] (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s →
    ∀ ν : Measure (W → hermC n), ν.IsAddHaarMeasure →
    Integrable (fun b : W → hermC n => ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  intro W _ n s hs ν hν
  let μ₀ : Measure (hermC n) := Measure.addHaar
  have hf : ∀ _w : W, Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) μ₀ :=
    fun _ => GlobalTheory.T.hua_determinant_integrable_of_lt n s hs μ₀ inferInstance
  have hpi := Integrable.fintype_prod (μ := fun _ : W => μ₀)
    (f := fun _ : W => fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) hf
  rw [Measure.isAddLeftInvariant_eq_smul ν (Measure.pi fun _ : W => μ₀)]
  exact hpi.smul_measure_nnreal

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
