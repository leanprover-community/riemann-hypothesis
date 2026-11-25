module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.SliceAn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSmulSemi, Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelAction

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSmulSemi =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSmulSemi", "h": "module\n\nimport Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.SliceAn\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\npublic import Mathlib.Analysis.Normed.Module.DoubleDual\npublic import Mathlib.Analysis.Normed.Operator.BanachSteinhaus\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic

noncomputable section

namespace GlobalTheory.DiffDecay

section Weak

variable {E : Type} [AddCommGroup E] [Module ℂ E]

def WithSemi (_p : Seminorm ℂ E) : Type := E

instance (p : Seminorm ℂ E) : AddCommGroup (WithSemi p) := inferInstanceAs (AddCommGroup E)
instance (p : Seminorm ℂ E) : Module ℂ (WithSemi p) := inferInstanceAs (Module ℂ E)
instance (p : Seminorm ℂ E) : SeminormedAddCommGroup (WithSemi p) :=
  AddGroupSeminorm.toSeminormedAddCommGroup (E := WithSemi p) p.toAddGroupSeminorm
instance (p : Seminorm ℂ E) : NormedSpace ℂ (WithSemi p) where
  norm_smul_le a x := (map_smul_eq_mul p a x).le

end Weak

section Tame

variable {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] {W : Type} [SeminormedAddCommGroup W]

def Tame (R : W → E →ₗ[ℂ] E) : Prop :=
  ∀ p : Seminorm ℂ E, Continuous p → ∃ (q : Seminorm ℂ E) (M : ℕ), Continuous q ∧
    ∀ w f, p (R w f - f) ≤ ‖w‖ * (1 + ‖w‖) ^ M * q f

end Tame

section Heis

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : Type} [SeminormedAddCommGroup W]

end Heis

end GlobalTheory.DiffDecay

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSmulSemi =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelAction =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelAction", "h": "module\n\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSmulSemi\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Module.DoubleDual\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM Filter Topology
open scoped SchwartzMap GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical

noncomputable section

namespace GlobalTheory.ArchJointCont

theorem continuous_of_weak {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (A : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ)) (h : ∀ T : 𝓢(V, ℂ) →L[ℂ] ℂ, Continuous fun f => T (A f)) : Continuous A := by
  haveI : BarrelledSpace ℂ 𝓢(V, ℂ) := GlobalTheory.schwartzMap_barrelledSpace V
  refine (schwartz_withSeminorms ℂ V ℂ).continuous_of_continuous_comp A fun i => ?_
  set p : Seminorm ℂ 𝓢(V, ℂ) := schwartzSeminormFamily ℂ V ℂ i
  have hp : Continuous p := (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i
  let j₀ : 𝓢(V, ℂ) →ₗ[ℂ] GlobalTheory.DiffDecay.WithSemi p := LinearMap.id
  have hj : Continuous j₀ := by
    refine continuous_of_continuousAt_zero j₀ ?_
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    have := hp.tendsto 0
    rw [map_zero] at this
    exact this
  let j : 𝓢(V, ℂ) →L[ℂ] GlobalTheory.DiffDecay.WithSemi p := ⟨j₀, hj⟩
  have hnorm : ∀ x, ‖j x‖ = p x := fun x => rfl
  refine Seminorm.continuous_of_lowerSemicontinuous _ fun f₀ y hy => ?_
  change y < p (A f₀) at hy
  rcases lt_or_ge y 0 with hy0 | hy0
  · exact Eventually.of_forall fun f => lt_of_lt_of_le hy0 (apply_nonneg _ _)
  have hex : ∃ L : StrongDual ℂ (GlobalTheory.DiffDecay.WithSemi p), y * ‖L‖ < ‖L (j (A f₀))‖ := by
    by_contra hne
    push_neg at hne
    have h1 : ‖NormedSpace.inclusionInDoubleDual ℂ (GlobalTheory.DiffDecay.WithSemi p) (j (A f₀))‖ ≤ y :=
      ContinuousLinearMap.opNorm_le_bound _ hy0 fun L => by
        rw [NormedSpace.dual_def]; exact hne L
    rw [show NormedSpace.inclusionInDoubleDual ℂ (GlobalTheory.DiffDecay.WithSemi p) (j (A f₀)) =
      NormedSpace.inclusionInDoubleDualLi ℂ (j (A f₀)) from rfl, LinearIsometry.norm_map, hnorm] at h1
    exact absurd hy (not_lt.2 h1)
  obtain ⟨L, hL⟩ := hex
  have hc : Continuous fun f => ‖L (j (A f))‖ := (h (L.comp j)).norm
  filter_upwards [(hc.tendsto f₀).eventually_const_lt hL] with f hf
  change y < p (A f)
  have h2 : ‖L (j (A f))‖ ≤ ‖L‖ * p (A f) := by rw [← hnorm]; exact L.le_opNorm _
  have h4 : y * ‖L‖ < ‖L‖ * p (A f) := lt_of_lt_of_le hf h2
  by_contra hcon
  push_neg at hcon
  nlinarith [norm_nonneg L]

theorem exists_adm (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (T : SInf F κ →L[ℂ] ℂ) :
    ∃ l ∈ (adeleClass F).adm κ, ∀ (f : SInf F κ) (g : (κ → IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) → ℂ),
      l (pureA F ⇑f g) = g 0 * T f := by
  let lift : (κ → mixedEmbedding.mixedSpace F) → (κ → AF F) := fun y i =>
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0)
  let sl : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) := LinearMap.funLeft ℂ ℂ lift
  let co : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) :=
    { toFun := fun f => ⇑f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hco : Function.Injective co := DFunLike.coe_injective
  let e := LinearEquiv.ofInjective co hco
  obtain ⟨T₂, hT₂⟩ := LinearMap.exists_extend (T.toLinearMap ∘ₗ e.symm.toLinearMap)
  have hT₂f : ∀ f : SInf F κ, T₂ ⇑f = T f := fun f => by
    have := congrArg (fun m => m (e f)) hT₂
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      ContinuousLinearMap.coe_coe] at this
    rw [LinearEquiv.ofInjective_apply] at this
    exact this
  have hsl : ∀ (f : SInf F κ) g, sl (pureA F ⇑f g) = g 0 • ⇑f := fun f g => by
    funext y
    show pureA F ⇑f g (lift y) = g 0 * f y
    simp only [pureA, lift, RingEquiv.apply_symm_apply]
    rw [mul_comm]
    rfl
  refine ⟨T₂ ∘ₗ sl, fun g _ => ⟨g 0 • T, fun f => ?_⟩, fun f g => ?_⟩
  · simp [hsl, hT₂f]
  · simp [hsl, hT₂f]

end GlobalTheory.ArchJointCont
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelAction =====
