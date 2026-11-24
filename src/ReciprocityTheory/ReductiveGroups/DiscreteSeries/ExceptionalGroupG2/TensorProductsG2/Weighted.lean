module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.WeightedA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ArbitraryB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FormulaF
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.WeightedB
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IntegrableComplexContinuousBoundedSupport
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ClassTwoEntries
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumIrr
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.NormSubOneLeOfHsdA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.WeightedB, ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Weighted

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.WeightedB =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.WeightedB", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.WeightedB\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.WeightedA\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero\nimport Formalism.RealPlaceAnalysis.RealPlaceTaylor.IntegrableComplexContinuousBoundedSupport\nimport Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ArbitraryB\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ClassTwoEntries\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumIrr\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfChar\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.NormSubOneLeOfHsdA\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FormulaF\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {ε : Fin n → Bool}

variable {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
  {v₀ : T.V}

theorem wd_datum_datum (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hΨw : ∀ μ : Measure (S7.UJ ε), μ.IsHaarMeasure →
      Integrable (fun g : S7.UJ ε => ‖Ψ (S7.toM g)‖ ^ 2 * S7.hs (S7.toM g) ^ ((2 : ℝ) / 2)) μ)
    (x' : smD ε (rreg ε)) (hx' : x' ∈ datumV ε Ψ v₀) (x : smD ε (rreg ε)) (hx : x ∈ datumV ε Ψ v₀) :
    MemLp (wdF ε (wdCoef ε (x' : L2 ε) x)) 2 (Formalism.REAL.muG ε) := by
  obtain ⟨u', hu'⟩ := (mem_datumV_iff hP v₀ x').1 hx'
  obtain ⟨u, hu⟩ := (mem_datumV_iff hP v₀ x).1 hx
  have hG := wd_psi_memLp hP hΨw
  have hm : AEStronglyMeasurable (wdF ε (wdCoef ε (x' : L2 ε) x)) (Formalism.REAL.muG ε) := by
    unfold wdF
    exact ((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (wd_hs_cont.comp (continuous_umatA ε)))).mul (wdCoef_cont _ _)).aestronglyMeasurable
  refine hG.of_le_mul (c := ‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖u'‖ * ‖u‖) hm (Filter.Eventually.of_forall fun g => ?_)
  simp only [wdF, wdCoef_apply, hu', hu]
  have h3 : 0 ≤ ‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 := by positivity
  rw [formulaF hgap hP hv₀ g.2 u u']
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg h3]
  have h1 : ‖inner ℂ u' (Ψ (Formalism.MainNotions.S.umat g) u)‖ ≤ ‖u'‖ * (‖Ψ (Formalism.MainNotions.S.umat g)‖ * ‖u‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ((Ψ _).le_opNorm u) (norm_nonneg _))
  have h2 : 0 ≤ Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) := Real.sqrt_nonneg _
  calc Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) * (‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖inner ℂ u' (Ψ (Formalism.MainNotions.S.umat g) u)‖)
      ≤ Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) * (‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * (‖u'‖ * (‖Ψ (Formalism.MainNotions.S.umat g)‖ * ‖u‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h3) h2
    _ = _ := by ring

theorem wd_gen_datum (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hΨw : ∀ μ : Measure (S7.UJ ε), μ.IsHaarMeasure →
      Integrable (fun g : S7.UJ ε => ‖Ψ (S7.toM g)‖ ^ 2 * S7.hs (S7.toM g) ^ ((2 : ℝ) / 2)) μ)
    (i : Fin n) (w : smD ε (rreg ε)) (hw : w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))
    (x : smD ε (rreg ε)) (hx : x ∈ datumV ε Ψ v₀) :
    MemLp (wdF ε (wdCoef ε (w : L2 ε) x)) 2 (Formalism.REAL.muG ε) := by
  have h := wd_key hP hv₀ i (x : L2 ε) (fun y hy => wd_datum_datum hgap hP hv₀ hΨw x hx y hy) w hw
  have hinv := (h.comp_measurePreserving (Measure.measurePreserving_inv (Formalism.REAL.muG ε))).star
  have e : star (wdF ε (wdCoef ε (x : L2 ε) w) ∘ Inv.inv) = wdF ε (wdCoef ε (w : L2 ε) x) := by
    funext g
    simp only [Pi.star_apply, Function.comp_apply, wdF, wdCoef_apply, star_mul', RCLike.star_def,
      Complex.conj_ofReal]
    rw [wd_hs_inv, inner_conj_symm, wd_rreg_adj, inv_inv]
  rw [e] at hinv
  exact hinv

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.WeightedB =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Weighted =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Weighted", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.WeightedB\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

open MeasureTheory

theorem weighted_datum {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V} (hgap : StdGap ε lam)
    (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hΨw : ∀ μ : Measure (S7.UJ ε), μ.IsHaarMeasure →
      Integrable (fun g : S7.UJ ε => ‖Ψ (S7.toM g)‖ ^ 2 * S7.hs (S7.toM g) ^ ((2 : ℝ) / 2)) μ) :
    ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε =>
        ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε)))
        2 (Formalism.REAL.muG ε) := by
  intro v hv w hw
  show MemLp (wdF ε (wdCoef ε ((w : smD ε (rreg ε)) : L2 ε) v)) 2 (Formalism.REAL.muG ε)
  rcases isEmpty_or_nonempty (Fin n) with hn | hne
  · have e : wdF ε (wdCoef ε ((w : smD ε (rreg ε)) : L2 ε) v) = 0 := by
      funext g
      simp [wdF, S7.hs]
    rw [e]
    exact MemLp.zero
  · obtain ⟨i⟩ := hne
    exact wd_key hP hv₀ i (w : L2 ε) (fun x hx => wd_gen_datum hgap hP hv₀ hΨw i w hw x hx) v hv

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Weighted =====
