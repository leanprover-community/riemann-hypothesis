module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CvAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LocInt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestOps
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneParam
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem hasDerivAt_conv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (f ψ ψ' : G → ℂ) (hf : LocallyIntegrable f μ)
    (h' : Continuous ψ') (hs' : HasCompactSupport ψ')
    (hi : ∀ x, Integrable (fun y => f y * ψ (y⁻¹ * x)) μ) (hi' : ∀ x, Integrable (fun y => f y * ψ' (y⁻¹ * x)) μ)
    (c : ℝ → G) (hc : Continuous c) (c0 : c 0 = 1) (cadd : ∀ s t, c (s + t) = c s * c t)
    (hd : ∀ g, HasDerivAt (fun t => ψ (g * c t)) (ψ' g) 0) (x : G) :
    HasDerivAt (fun t => ∫ y, f y * ψ (y⁻¹ * (x * c t)) ∂μ) (∫ y, f y * ψ' (y⁻¹ * x) ∂μ) 0 := by
  obtain ⟨M, hM⟩ := h'.bounded_above_of_compact_support hs'
  let K : Set G := (fun p : ℝ × G => x * c p.1 * p.2⁻¹) '' (Set.Icc (-1 : ℝ) 1 ×ˢ tsupport ψ')
  have hK : IsCompact K := (isCompact_Icc.prod hs').image (by fun_prop)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hb : Integrable (K.indicator fun y => ‖f y‖ * M) μ :=
    (integrable_indicator_iff hKm).2 ((hf.integrableOn_isCompact hK).norm.mul_const M)
  have hdt : ∀ g t, HasDerivAt (fun s => ψ (g * c s)) (ψ' (g * c t)) t := fun g t => by
    have h1 : HasDerivAt (fun s => ψ (g * c t * c s)) (ψ' (g * c t)) (t - t) := by
      rw [sub_self]; exact hd _
    have h2 := h1.comp_sub_const t t
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only [mul_assoc, ← cadd, add_sub_cancel]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ)
    (F := fun t y => f y * ψ (y⁻¹ * (x * c t))) (F' := fun t y => f y * ψ' (y⁻¹ * (x * c t)))
    (x₀ := (0 : ℝ)) (s := Set.Icc (-1 : ℝ) 1) (bound := K.indicator fun y => ‖f y‖ * M)
    (Icc_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun t => (hi _).aestronglyMeasurable) (hi _) (hi' _).aestronglyMeasurable
    (Eventually.of_forall fun y t ht => by
      by_cases hy : y ∈ K
      · rw [Set.indicator_of_mem hy, norm_mul]
        exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      · rw [Set.indicator_of_notMem hy]
        have : ψ' (y⁻¹ * (x * c t)) = 0 := by
          by_contra hne
          exact hy ⟨(t, y⁻¹ * (x * c t)), ⟨ht, subset_tsupport _ hne⟩, by simp [mul_assoc]⟩
        simp [this]) hb
    (Eventually.of_forall fun y t _ => by
      simpa only [mul_assoc] using (hdt (y⁻¹ * x) t).const_mul (f y))
  simpa only [c0, mul_one] using key.2

theorem UpperTheory.V.Cj.H.cvLie :
    UpperTheory.V.Cj.H.CvLie := by
  intro E _ _ _ a μ _ _ ψ φ hψ F hφ X
  obtain ⟨c, c0, cadd, ccont, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  have t1 := UpperTheory.V.Cj.H.testOps E a ψ
  have hψ' : IsTest (lie E a X ψ) := (t1.2 hψ).1 X
  have k1 : Continuous ψ.1 := (t1.1 hψ.2).1
  have k2 : Continuous (lie E a X ψ).1 := ((UpperTheory.V.Cj.H.testOps E a _).1 hψ'.2).1
  funext x
  have d := hasDerivAt_conv μ (GlobalTheory.AutomorphicL2Unitary.lift (latticeGL E a) F) ψ.1 (lie E a X ψ).1
    ((UpperTheory.V.Cj.H.locInt (GA E a) (latticeGL E a) μ).1 F) k2 hψ'.1
    ((UpperTheory.V.Cj.H.cvAlg (GA E a) (latticeGL E a) μ ψ.1 k1 hψ.1).1 F)
    ((UpperTheory.V.Cj.H.cvAlg (GA E a) (latticeGL E a) μ _ k2 hψ'.1).1 F)
    (fun s => infGL E a (c s)) ccont (by rw [c0, map_one]) (fun s t => by rw [cadd, map_mul])
    (fun g => hasDerivAt_curve ψ g c X c0 cder) x
  have d' := hasDerivAt_curve φ x c X c0 cder
  exact d'.unique (d.congr_of_eventuallyEq (Eventually.of_forall fun t => congrFun hφ _))
