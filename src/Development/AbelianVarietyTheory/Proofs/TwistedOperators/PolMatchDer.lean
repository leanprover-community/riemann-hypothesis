module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Basic.Complex.Basic
public import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.LieEq

theorem exists_op {S S' Pi : Type} [AddCommGroup S] [Module ℂ S] [AddCommGroup S'] [Module ℂ S'] [AddCommGroup Pi] [Module ℂ Pi]
    (N : Submodule ℂ S) (N' : Submodule ℂ S') (p : S →ₗ[ℂ] Pi) (p' : S' →ₗ[ℂ] Pi) (δ : S →ₗ[ℂ] S) (δ' : S' →ₗ[ℂ] S')
    (h : ∀ f ∈ N, ∀ f' ∈ N', p f = p' f' → p (δ f) = p' (δ' f')) :
    ∃ A : Pi →ₗ[ℂ] Pi, (∀ f ∈ N, A (p f) = p (δ f)) ∧ ∀ f' ∈ N', A (p' f') = p' (δ' f') := by
  let L : (N × N') →ₗ[ℂ] Pi := p ∘ₗ N.subtype ∘ₗ LinearMap.fst ℂ N N' + p' ∘ₗ N'.subtype ∘ₗ LinearMap.snd ℂ N N'
  let L₁ : (N × N') →ₗ[ℂ] Pi := p ∘ₗ δ ∘ₗ N.subtype ∘ₗ LinearMap.fst ℂ N N' + p' ∘ₗ δ' ∘ₗ N'.subtype ∘ₗ LinearMap.snd ℂ N N'
  have hk : LinearMap.ker L ≤ LinearMap.ker L₁ := by
    intro x hx
    simp only [LinearMap.mem_ker, L, L₁, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, Submodule.coe_subtype] at hx ⊢
    have e : p (x.1 : S) = p' (-(x.2 : S')) := by rw [map_neg]; exact eq_neg_of_add_eq_zero_left hx
    have := h _ x.1.2 _ (N'.neg_mem x.2.2) e
    rw [this, map_neg, map_neg, neg_add_cancel]
  let A₀ : LinearMap.range L →ₗ[ℂ] Pi := (LinearMap.ker L).liftQ L₁ hk ∘ₗ L.quotKerEquivRange.symm.toLinearMap
  have hA₀ : ∀ x, A₀ ⟨L x, LinearMap.mem_range_self L x⟩ = L₁ x := by
    intro x
    simp only [A₀, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  obtain ⟨A, hA⟩ := LinearMap.exists_extend A₀
  have hA' : ∀ x, A (L x) = L₁ x := fun x => by
    rw [← hA₀ x, ← hA]; rfl
  refine ⟨A, fun f hf => ?_, fun f' hf' => ?_⟩
  · have := hA' (⟨f, hf⟩, 0)
    simpa [L, L₁] using this
  · have := hA' (0, ⟨f', hf'⟩)
    simpa [L, L₁] using this

end GlobalTheory.SquareAgree.LieEq

end
