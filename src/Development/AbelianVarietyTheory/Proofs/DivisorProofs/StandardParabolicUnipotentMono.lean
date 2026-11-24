module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.StdPar

section DimensionMonotonicity
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X : Matrix (Fin n) (Fin r) E}

theorem unip_maps_colSpan {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) {I : Set (Fin r)}
    (hI : ∀ i ∈ I, ∀ l, l < i → l ∈ I) {y : Fin n → AF F ⊗[F] E} (hy : y ∈ colSpan F X I) :
    (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X I := by
  have key : colSpan F X I ≤ (colSpan F X I).comap (matHom _ σ J g).1.mulVecLin := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have h1 := (Subgroup.mem_iInf.1 hg.1 i).2 _ (Submodule.subset_span ⟨i, rfl, rfl⟩)
    have h2 : colSpan F X {l | ∃ k ∈ T, l ≤ k ∧ k < i} ≤ colSpan F X I := by
      refine Submodule.span_mono (Set.image_mono ?_)
      rintro l ⟨k, -, hlk, hki⟩
      exact hI i hi l (lt_of_le_of_lt hlk hki)
    have h3 : (fun i => (adMat F X)ᵀ i) i ∈ colSpan F X I := Submodule.subset_span ⟨i, hi, rfl⟩
    show (matHom _ σ J g).1 *ᵥ _ ∈ colSpan F X I
    have := add_mem (h2 h1) h3
    rwa [sub_add_cancel] at this
  exact key hy

theorem unip_iff_colSpan {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) {I : Set (Fin r)}
    (hI : ∀ i ∈ I, ∀ l, l < i → l ∈ I) (y : Fin n → AF F ⊗[F] E) :
    y ∈ colSpan F X I ↔ (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X I := by
  refine ⟨unip_maps_colSpan hg hI, fun h => ?_⟩
  have := unip_maps_colSpan (inv_mem hg) hI h
  rwa [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec] at this

end DimensionMonotonicity

theorem unip_mono_of_subset : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S T : Finset (Fin r)), T ⊆ S → GlobalTheory.StdPar.unip σ J X T ≤ GlobalTheory.StdPar.unip σ J X S := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y _ S T hTS g hg
  refine ⟨Subgroup.mem_iInf.2 fun j => ⟨unip_iff_colSpan hg ?_, fun y hy => ?_⟩,
    ⟨unip_iff_colSpan hg ?_, fun y hy => ?_⟩⟩
  · rintro i ⟨k, hk, hik, hkj⟩ l hl
    exact ⟨k, hk, (le_of_lt (lt_of_lt_of_le hl hik)), hkj⟩
  · refine Submodule.span_mono (Set.image_mono ?_) ((Subgroup.mem_iInf.1 hg.1 j).2 y hy)
    rintro l ⟨k, hk, h1, h2⟩
    exact ⟨k, hTS hk, h1, h2⟩
  · rintro i ⟨k, hk, hik⟩ l hl
    exact ⟨k, hk, le_of_lt (lt_of_lt_of_le hl hik)⟩
  · have hy' : y ∈ colPerp σ J X {i | ∃ k ∈ T, i ≤ k} := by
      simp only [colPerp, Submodule.mem_iInf] at hy ⊢
      rintro i ⟨k, hk, hik⟩
      exact hy i ⟨k, hTS hk, hik⟩
    refine Submodule.span_mono (Set.image_mono ?_) (hg.2.2 y hy')
    rintro l ⟨k, hk, h1⟩
    exact ⟨k, hTS hk, h1⟩

end GlobalTheory.StdPar
