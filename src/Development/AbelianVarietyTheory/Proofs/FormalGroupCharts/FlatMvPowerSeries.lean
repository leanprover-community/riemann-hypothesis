module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.EquationalCriterion

@[expose] public section

open MvPowerSeries IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.PowerSeriesFlat

theorem flat_pi (T : Type*) [CommRing T] [IsNoetherianRing T] (ι : Type*) :
    Module.Flat T (ι → T) := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro l f x h
  let φ : (Fin l → T) →ₗ[T] T := Fintype.linearCombination T f
  have hφ : ∀ v : Fin l → T, φ v = ∑ i, f i * v i := by
    intro v
    simp [φ, Fintype.linearCombination_apply, mul_comm]
  have hfg : (LinearMap.ker φ).FG := IsNoetherian.noetherian _
  obtain ⟨k, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hx : ∀ t : ι, ∃ c : Fin k → T, ∑ j, c j • s j = fun i => x i t := by
    intro t
    have hm : (fun i => x i t) ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker, hφ]
      have := congrFun h t
      simpa [Finset.sum_apply] using this
    rw [← hs] at hm
    exact (Submodule.mem_span_range_iff_exists_fun T).1 hm
  choose c hc using hx
  refine ⟨k, fun i j => s j i, fun j t => c t j, ?_, ?_⟩
  · intro i
    funext t
    have := congrFun (hc t) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · intro j
    have hm : s j ∈ LinearMap.ker φ := by
      rw [← hs]
      exact Submodule.subset_span ⟨j, rfl⟩
    rwa [LinearMap.mem_ker, hφ] at hm

theorem flat_mvPowerSeries :
    ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (σ : Type),
      Module.Flat T (MvPowerSeries σ T) :=
  fun T _ _ σ => flat_pi T (σ →₀ ℕ)

end GlobalTheory.PowerSeriesFlat
