module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableHaarVolOfLintegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralDetPowIntegerMatricesFiniteStatement
import Formalism.DoubleCosetMeasures.Statement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section
namespace GlobalTheory.GJTransfer

theorem integrable_indicator_intM_mul_nabs_rpow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (σ : ℝ), (n : ℝ) - 1 < σ →
    Integrable (fun g : GL (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val * nabs k (gdet g) ^ σ) (haarVol (KO k (Fin n))) := by
  intro k _ _ _ _ _ _ n σ hσ
  have hint : ∀ (μ : Measure k) [μ.IsAddHaarMeasure] (s : ℝ), -1 < s →
      ∫⁻ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal
        (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) X ∂(volM μ (Fin n) (Fin n)) < ⊤ := by
    intro μ _ s hs
    exact GlobalTheory.T.lintegral_det_pow_integer_matrices_finite k μ n s hs
  exact integrable_haarVol_of_lintegral n σ (min (σ - n) 0) (min_le_left _ _)
    (hint _ _ (lt_min (by linarith) (by norm_num)))

end GlobalTheory.GJTransfer
