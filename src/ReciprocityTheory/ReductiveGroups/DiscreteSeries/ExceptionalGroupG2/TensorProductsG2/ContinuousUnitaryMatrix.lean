module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ContinuousUnitaryMatrix
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.HasDerivAtInvExpCurveEntry
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UpqRep

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS.G2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}

theorem smoothOnG_inner_rep (w : H) {v : H} (hv : IsSmoothVecU ε σ v) :
    Formalism.REAL.SmoothOnG ε (fun g => inner ℂ w (σ g v)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg, hF, he⟩ := hv g₀ hg₀
  exact ⟨U, fun g => inner ℂ w (F g), hU, hg, contDiffOn_const.inner ℂ hF,
    fun g hgU hgJ => congrArg (inner ℂ w) (he g hgU hgJ)⟩

private theorem smoothOnG_mul' {F G : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : Formalism.REAL.SmoothOnG ε F)
    (hG : Formalism.REAL.SmoothOnG ε G) : Formalism.REAL.SmoothOnG ε (fun x => F x * G x) := by
  intro g₀ hg₀
  obtain ⟨U1, F1, hU1, hg1, hF1, he1⟩ := hF g₀ hg₀
  obtain ⟨U2, F2, hU2, hg2, hF2, he2⟩ := hG g₀ hg₀
  refine ⟨U1 ∩ U2, fun x => F1 x * F2 x, hU1.inter hU2, ⟨hg1, hg2⟩,
    (hF1.mono Set.inter_subset_left).mul (hF2.mono Set.inter_subset_right), fun g hg hgJ => ?_⟩
  show F g * G g = F1 g * F2 g
  rw [he1 g hg.1 hgJ, he2 g hg.2 hgJ]

theorem continuous_umat' : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) := by
  exact Units.continuous_val.comp continuous_subtype_val

theorem continuous_rep_orbit (hσ : IsURepOn (UJset ε) σ) (v : H) :
    Continuous (fun g : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat g) v) := by
  exact (hσ.2.2 v).comp_continuous continuous_umat' fun g => Formalism.MainNotions.BridgeCSchur.umat_mem g

theorem tensor_term_memLp (hσ : IsURepOn (UJset ε) σ) {S : Submodule ℂ D}
    (hW : ∀ v ∈ S, ∀ w ∈ S, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (dual : Bool) {w v : D} (hw : w ∈ S) (hv : v ∈ S) (c d : Fin n) :
    MemLp (fun g : Formalism.REAL.UJ ε =>
      oa1Phi dual (Formalism.MainNotions.S.umat g) c d * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε) := by
  have hU : ∀ g : Formalism.REAL.UJ ε, inUJ ε (Formalism.MainNotions.S.umat g) := fun g => Formalism.MainNotions.BridgeCSchur.umat_mem g
  refine (hW v hv w hw).of_le ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact ((continuous_tensor_phi dual c d).mul (continuous_const.inner (continuous_rep_orbit hσ _))).aestronglyMeasurable
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right (norm_tensor_phi_le_sqrt_hs (hU g) dual c d) (norm_nonneg _)

end ReciprocityTheory.ChartRestriction.DS.G2
