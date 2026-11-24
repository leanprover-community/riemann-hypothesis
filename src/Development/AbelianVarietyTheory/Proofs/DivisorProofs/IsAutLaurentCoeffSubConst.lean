module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
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
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.LaurentAut

open scoped ContDiff

theorem hasDerivAt_integral_cpt {𝕜 : Type} [RCLike 𝕜] [NormedSpace 𝕜 ℂ] [ProperSpace 𝕜] {H : Type} [TopologicalSpace H] [T2Space H]
    [MeasurableSpace H] [OpensMeasurableSpace H] (μ : Measure H) [IsFiniteMeasureOnCompacts μ] {Φ Φ' : 𝕜 → H → ℂ} {x₀ : 𝕜}
    {C : Set H} (hC : IsCompact C) (hc : ∀ t, Continuous (Φ t)) (hc' : Continuous fun p : 𝕜 × H => Φ' p.1 p.2)
    (h0 : ∀ t ∈ Metric.closedBall x₀ 1, ∀ y ∉ C, Φ t y = 0 ∧ Φ' t y = 0)
    (hd : ∀ t y, HasDerivAt (Φ · y) (Φ' t y) t) :
    HasDerivAt (fun t => ∫ y, Φ t y ∂μ) (∫ y, Φ' x₀ y ∂μ) x₀ := by
  obtain ⟨B, hB⟩ := ((isCompact_closedBall x₀ 1).prod hC).exists_bound_of_continuousOn hc'.continuousOn
  have hx : x₀ ∈ Metric.closedBall x₀ 1 := Metric.mem_closedBall_self zero_le_one
  have hc0 : Continuous (Φ' x₀) := hc'.comp (continuous_const.prodMk continuous_id)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := C.indicator fun _ => B)
    (Metric.closedBall_mem_nhds x₀ one_pos) ?_
    ((hc x₀).integrable_of_hasCompactSupport (.intro hC fun y hy => (h0 x₀ hx y hy).1))
    (hc0.integrable_of_hasCompactSupport (.intro hC fun y hy => (h0 x₀ hx y hy).2)).aestronglyMeasurable
    (.of_forall fun y t ht => ?_) ?_ (.of_forall fun y t _ => hd t y)).2
  · filter_upwards [Metric.closedBall_mem_nhds x₀ one_pos] with t ht
    exact ((hc t).integrable_of_hasCompactSupport (.intro hC fun y hy => (h0 t ht y hy).1)).aestronglyMeasurable
  · by_cases hy : y ∈ C
    · rw [Set.indicator_of_mem hy]; exact hB (t, y) ⟨ht, hy⟩
    · rw [Set.indicator_of_notMem hy, (h0 t ht y hy).2, norm_zero]
  · exact (integrable_indicator_iff hC.measurableSet).2 (integrableOn_const hC.measure_lt_top.ne)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Abstract

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] {N : ℕ}
  {j : H →* G} {ι : H →* Matrix (Fin N) (Fin N) ℂ}

variable [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  (hι : IsEmbedding ι) (h1 : ∀ y, ‖(ι y).det‖ = 1)
include hι h1

variable [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure]


end Abstract

section Unitary

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {N : ℕ} {ι : GInf σ J →* Matrix (Fin N) (Fin N) ℂ}
  (hι : IsEmbedding ι) (h1 : ∀ y, ‖(ι y).det‖ = 1) {f : Matrix (Fin N) (Fin N) ℂ → ℝ}
include hι h1

variable {x : Matrix (Fin n) (Fin 1) E} {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)}
  {h : GAd σ J → ℝ}

end Unitary



end GlobalTheory.LaurentAut
end
