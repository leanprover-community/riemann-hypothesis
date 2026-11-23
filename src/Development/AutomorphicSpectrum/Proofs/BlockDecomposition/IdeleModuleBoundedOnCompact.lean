module

public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
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
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MatrixTransvectionDiagonalDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import Formalism.UnipotentAdelicQuotients.SWXSDefs

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.IdeleModBdd

theorem ideleModule_bounded_on_compact : ∀ (K : Type) [Field K] [NumberField K] (C : Set (AdeleRing (𝓞 K) K)), IsCompact C → ∃ R : ℝ, ∀ a : IdeleGroup K, (a : AdeleRing (𝓞 K) K) ∈ C → (IdeleGroup.ideleModule K a : ℝ) ≤ R := by
  intro K _ _ C hC
  let U : Finset (HeightOneSpectrum (𝓞 K)) → Set (AdeleRing (𝓞 K) K) := fun S =>
    {x | ∀ v, v ∉ S → x.2 v ∈ v.adicCompletionIntegers K}
  have hUo : ∀ S, IsOpen (U S) := fun S =>
    (RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _)
      (p := fun v : HeightOneSpectrum (𝓞 K) => v ∉ S)).preimage continuous_snd
  have hcov : C ⊆ ⋃ S, U S := by
    intro x _
    have hfin : {v : HeightOneSpectrum (𝓞 K) | ¬ x.2 v ∈ v.adicCompletionIntegers K}.Finite :=
      Filter.eventually_cofinite.1 x.2.2
    exact Set.mem_iUnion.2 ⟨hfin.toFinset, fun v hv => by
      by_contra h
      exact hv (hfin.mem_toFinset.2 h)⟩
  have hdir : Directed (· ⊆ ·) U := fun S T =>
    ⟨S ∪ T, fun x hx v hv => hx v fun h => hv (Finset.mem_union_left _ h),
      fun x hx v hv => hx v fun h => hv (Finset.mem_union_right _ h)⟩
  obtain ⟨S, hS⟩ := hC.elim_directed_cover U hUo hcov hdir
  have hfinB : ∀ v : HeightOneSpectrum (𝓞 K), ∃ B : ℝ, ∀ x ∈ C, ‖x.2 v‖ ≤ B := fun v => by
    have hc : Continuous fun x : AdeleRing (𝓞 K) K => ‖x.2 v‖ :=
      continuous_norm.comp ((RestrictedProduct.continuous_eval v).comp continuous_snd)
    obtain ⟨B, hB⟩ := (hC.image hc).bddAbove
    exact ⟨B, fun x hx => hB ⟨x, hx, rfl⟩⟩
  have hinfB : ∀ w : InfinitePlace K, ∃ B : ℝ, ∀ x ∈ C, ‖x.1 w‖ ≤ B := fun w => by
    have hc : Continuous fun x : AdeleRing (𝓞 K) K => ‖x.1 w‖ :=
      continuous_norm.comp ((continuous_apply w).comp continuous_fst)
    obtain ⟨B, hB⟩ := (hC.image hc).bddAbove
    exact ⟨B, fun x hx => hB ⟨x, hx, rfl⟩⟩
  choose Bf hBf using hfinB
  choose Bi hBi using hinfB
  refine ⟨(∏ w : InfinitePlace K, max (Bi w) 0 ^ w.mult) * ∏ v ∈ S, max (Bf v) 1, ?_⟩
  intro a ha
  rw [IdeleGroup.ideleModule_eq]
  have h1 : ∏ w : InfinitePlace K, ‖(a : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult ≤
      ∏ w : InfinitePlace K, max (Bi w) 0 ^ w.mult :=
    Finset.prod_le_prod₀ (fun _ _ => by positivity) fun w _ =>
      pow_le_pow_left₀ (norm_nonneg _) ((hBi w _ ha).trans (le_max_left _ _)) _
  have h2 : ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(a : AdeleRing (𝓞 K) K).2 v‖ ≤
      ∏ v ∈ S, max (Bf v) 1 := by
    have hfs := IdeleGroup.finite_mulSupport_norm a
    have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) =>
        ‖(a : AdeleRing (𝓞 K) K).2 v‖) ⊆ ((hfs.toFinset ∪ S : Finset _) : Set _) := fun v hv => by
      simp only [Finset.coe_union, Set.Finite.coe_toFinset]
      exact Or.inl hv
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
    calc ∏ v ∈ hfs.toFinset ∪ S, ‖(a : AdeleRing (𝓞 K) K).2 v‖
        ≤ ∏ v ∈ hfs.toFinset ∪ S, (if v ∈ S then max (Bf v) 1 else 1) := by
          refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun v _ => ?_
          split_ifs with hv
          · exact (hBf v _ ha).trans (le_max_left _ _)
          · exact (Valued.toNormedField.norm_le_one_iff).2
              ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).1 (hS ha v hv))
      _ = ∏ v ∈ S, (if v ∈ S then max (Bf v) 1 else 1) :=
          (Finset.prod_subset Finset.subset_union_right fun v _ hv => if_neg hv).symm
      _ = ∏ v ∈ S, max (Bf v) 1 := Finset.prod_congr rfl fun v hv => if_pos hv
  exact mul_le_mul h1 h2 (IdeleGroup.finiteModule_pos a).le
    (Finset.prod_nonneg fun _ _ => by positivity)

end GlobalTheory.CompanionTheory.IdeleModBdd

end
