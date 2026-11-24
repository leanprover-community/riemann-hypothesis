module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.WeightedB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.WeightedA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ArbitraryB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ClassTwoEntries
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumIrr
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.NormSubOneLeOfHsdA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FormulaF

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {ε : Fin n → Bool}

theorem wd_rreg_adj (g : Formalism.REAL.UJ ε) (a b : L2 ε) :
    inner ℂ (rreg ε (Formalism.MainNotions.S.umat g) a) b = inner ℂ a (rreg ε (Formalism.MainNotions.S.umat g⁻¹) b) := by
  apply ReciprocityTheory.ChartRestriction.DS.wd_rreg_adj <;> assumption

theorem wd_hs_inv (g : Formalism.REAL.UJ ε) : S7.hs (Formalism.MainNotions.S.umat g⁻¹) = S7.hs (Formalism.MainNotions.S.umat g) := by
  apply ReciprocityTheory.ChartRestriction.DS.wd_hs_inv <;> assumption

theorem wdF_add (f f' : Matrix (Fin n) (Fin n) ℂ → ℂ) : wdF ε (f + f') = wdF ε f + wdF ε f' := by
  funext g; simp [wdF, mul_add]

theorem wdF_smul (c : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : wdF ε (c • f) = c • wdF ε f := by
  funext g; simp only [wdF, Pi.smul_apply, smul_eq_mul]; ring

theorem wdF_zero : wdF ε (0 : Matrix (Fin n) (Fin n) ℂ → ℂ) = 0 := by
  funext g; simp [wdF]

variable {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
  {v₀ : T.V}

theorem wd_key (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (i : Fin n) (w : L2 ε)
    (hw : ∀ x ∈ datumV ε Ψ v₀, MemLp (wdF ε (wdCoef ε w x)) 2 (Formalism.REAL.muG ε)) :
    ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), MemLp (wdF ε (wdCoef ε w v)) 2 (Formalism.REAL.muG ε) := by
  apply ReciprocityTheory.ChartRestriction.DS.wd_key <;> assumption

theorem wd_psi_memLp (hP : IsPsiFor ε lam T Ψ)
    (hΨw : ∀ μ : Measure (S7.UJ ε), μ.IsHaarMeasure →
      Integrable (fun g : S7.UJ ε => ‖Ψ (S7.toM g)‖ ^ 2 * S7.hs (S7.toM g) ^ ((2 : ℝ) / 2)) μ) :
    MemLp (wdF ε (fun g => ((‖Ψ g‖ : ℝ) : ℂ))) 2 (Formalism.REAL.muG ε) := by
  apply ReciprocityTheory.ChartRestriction.DS.wd_psi_memLp <;> assumption

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
