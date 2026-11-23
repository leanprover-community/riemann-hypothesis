module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrArchPairAdeleJoin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormSmulLeftLinearPhaseLe
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilL2Words

theorem schr_archPair_mem_schA : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F h) φ ∈ GlobalTheory.WeilM.schA F κ := by
  intro F _ _ _ κ _ ψ hψ h φ hφ
  obtain ⟨ℓ, -, hℓ⟩ := hψ
  obtain ⟨n, f, g, hg, rfl⟩ := schA_exists_sum F hφ
  let M : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] mixedEmbedding.mixedSpace F :=
    ∑ k, (LinearMap.mulRight ℝ (h.2 k)).comp (LinearMap.proj k)
  let L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (ℓ.comp M)
  have hL : ∀ X, L X = ℓ (∑ k, X k * h.2 k) := by
    intro X
    simp [L, M]
  set c : ℝ := ℓ (∑ k, h.1 k * h.2 k) / 2 with hc
  have hgr := GlobalTheory.LinPhaseSeminorm.hasTemperateGrowth_phase L (-c) (-1)
  rw [← GlobalTheory.LinPhaseSeminorm.phase_eq] at hgr
  rw [schr_sum']
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span
    ⟨SchwartzMap.smulLeftCLM ℂ
      (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((-1 * L x + (-1) ^ 2 * -c : ℝ) : ℂ)))
      (SchwartzMap.compSubConstCLM ℂ (-h.1) (f i)), g i, hg i, ?_⟩
  funext a
  rw [← adeleJoin_archPart F a, schr_archPair_adeleJoin F ψ ℓ hℓ, GlobalTheory.WeilCont.pureA_adeleJoin,
    GlobalTheory.WeilCont.pureA_adeleJoin, SchwartzMap.smulLeftCLM_apply_apply hgr, SchwartzMap.compSubConstCLM_apply,
    sub_neg_eq_add, smul_eq_mul, hL, ← mul_assoc]
  congr 2
  rw [hc]
  push_cast
  ring_nf

end GlobalTheory.WeilL2Words

end
