module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpanRangeEqTopOfIsIrreducible
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory.OuterTensor

theorem nontrivial_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
  exact hne (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem isIrreducible_outer_tprod :
    ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W), ρ.IsIrreducible → σ.IsIrreducible → (Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H)) : Representation ℂ (G × H) (V ⊗[ℂ] W)).IsIrreducible := by
  intro G H V W _ _ _ _ _ _ _ _ ρ σ hρ hσ
  have hV := nontrivial_of_isIrreducible ρ hρ
  have hW := nontrivial_of_isIrreducible σ hσ
  have sρ := GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible G V ρ hρ
  have sσ := GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible H W σ hσ
  have hVW : Nontrivial (V ⊗[ℂ] W) := by
    apply Module.nontrivial_of_finrank_pos (R := ℂ)
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h : (⊥ : Submodule ℂ (V ⊗[ℂ] W)) = ⊤)
  have h1 : ∀ (g : G) (B : W →ₗ[ℂ] W), ∀ x ∈ S.toSubmodule,
      TensorProduct.map (ρ g) B x ∈ S.toSubmodule := by
    intro g B
    have hB : B ∈ Submodule.span ℂ (Set.range σ) := sσ ▸ Submodule.mem_top
    induction hB using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨h, rfl⟩ := hB
      intro x hx
      exact S.apply_mem_toSubmodule (g, h) hx
    | zero => intro x _; simp
    | add B C _ _ hB hC =>
      intro x hx
      rw [TensorProduct.map_add_right, LinearMap.add_apply]
      exact add_mem (hB x hx) (hC x hx)
    | smul c B _ hB =>
      intro x hx
      rw [TensorProduct.map_smul_right, LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ (hB x hx)
  have h2 : ∀ (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W), ∀ x ∈ S.toSubmodule,
      TensorProduct.map A B x ∈ S.toSubmodule := by
    intro A B
    have hA : A ∈ Submodule.span ℂ (Set.range ρ) := sρ ▸ Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem A hA =>
      obtain ⟨g, rfl⟩ := hA
      exact h1 g B
    | zero => intro x _; simp
    | add A C _ _ hA hC =>
      intro x hx
      rw [TensorProduct.map_add_left, LinearMap.add_apply]
      exact add_mem (hA x hx) (hC x hx)
    | smul c A _ hA =>
      intro x hx
      rw [TensorProduct.map_smul_left, LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ (hA x hx)
  have h3 : ∀ (F : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W), ∀ x ∈ S.toSubmodule, F x ∈ S.toSubmodule := by
    intro F
    obtain ⟨t, rfl⟩ := (homTensorHomEquiv ℂ V W V W).surjective F
    induction t using TensorProduct.induction_on with
    | zero => intro x _; simp
    | tmul A B =>
      intro x hx
      rw [homTensorHomEquiv_apply, TensorProduct.homTensorHomMap_apply]
      exact h2 A B x hx
    | add s t hs ht =>
      intro x hx
      rw [map_add (f := _), LinearMap.add_apply]
      exact add_mem (hs x hx) (ht x hx)
  by_cases hS : S.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hS)
  · right
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊤
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hx0
    have := h3 (f.smulRight y) x hx
    simpa [hf] using this

end GlobalTheory.OuterTensor
