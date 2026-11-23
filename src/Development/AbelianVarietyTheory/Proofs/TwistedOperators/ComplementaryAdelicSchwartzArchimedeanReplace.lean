module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TwistRest

open scoped Classical in
theorem restTr : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (r : (κ → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r → f ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r := by
  intro F _ _ κ _ f f₁ r hr hf
  obtain ⟨hinv, hsch⟩ := hr

  set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := fun y => r (fun i => ((0 : InfiniteAdeleRing F), y i)) with hgdef
  have hrg : ∀ x : κ → AF F, r x = g (fun i => (x i).2) := by
    intro x
    let z : κ → AF F := fun i => ((x i).1, (0 : FiniteAdeleRing (𝓞 F) F))
    have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z := by
      intro u hu
      have hu1 : u.1 = 0 :=
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
      funext i
      change (u * z i : AF F) = 0
      refine Prod.ext ?_ ?_
      · change u.1 * (x i).1 = 0
        rw [hu1, zero_mul]
      · change u.2 * 0 = 0
        exact mul_zero _
    let x' : κ → AF F := fun i => ((0 : InfiniteAdeleRing F), (x i).2)
    have := hinv x' z hz
    have hx : x = x' + z := by
      funext i
      refine Prod.ext ?_ ?_
      · change (x i).1 = (0 : InfiniteAdeleRing F) + (x i).1
        rw [zero_add]
      · change (x i).2 = (x i).2 + (0 : FiniteAdeleRing (𝓞 F) F)
        rw [add_zero]
    exact (congrArg r hx).trans this
  have htens : ∀ f' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (⇑f') r = GlobalTheory.WeilM.pureA F (⇑f') g := by
    intro f'
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.WeilM.pureA, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI]
    rw [hrg x]

  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  let a : κ → InfiniteAdeleRing F := fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x₀ i)
  let Λ : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :=
    { toFun := fun Φ y => Φ (fun i => (a i, y i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΛ : ∀ (f' : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g' : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      Λ (GlobalTheory.WeilM.pureA F f' g') = f' x₀ • g' := by
    intro f' g'
    funext y
    change f' (fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F) (a i)) * g' y = f' x₀ * g' y
    congr 1
    apply congrArg f'
    funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x₀ i)
  have hle : GlobalTheory.WeilM.schA F κ ≤ (GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)).comap Λ := by
    refine Submodule.span_le.2 ?_
    rintro Φ ⟨f', g', hg', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, hΛ]
    exact Submodule.smul_mem _ _ hg'
  have hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    have h1 := hle (htens f ▸ hsch)
    rw [Submodule.mem_comap, hΛ] at h1
    have := Submodule.smul_mem _ (f x₀)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hx₀, one_smul] at this
  refine ⟨hinv, ?_⟩
  rw [htens f₁]
  exact Submodule.subset_span ⟨f₁, g, hg, rfl⟩

end GlobalTheory.TwistRest
