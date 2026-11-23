module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRightInvRightTwisted
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

@[expose] public section

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

variable {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]

def twInv (Γ : Subgroup G) (g : G) (A : E →ₗ[ℂ] E) : Submodule ℂ (G → E) :=
  GlobalTheory.TwistedInverseSubgroups.leftInvRightTwisted Γ g A

def cocyc (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) : Submodule ℂ (Γ → E) where
  carrier := {z | ∀ γ δ : Γ, z (γ * δ) = ρ (δ : G) (z γ) + z δ}
  add_mem' := by
    intro z z' h h' γ δ
    simp only [Pi.add_apply, h γ δ, h' γ δ, map_add (f := _)]
    abel
  zero_mem' := fun _ _ => by simp
  smul_mem' := by
    intro c z h γ δ
    simp only [Pi.smul_apply, h γ δ, map_smul, smul_add]

def extn (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G) : Submodule ℂ (G → E) where
  carrier := {u | (∀ γ ∈ Γ, ∀ x, u (γ * x) - u x = ρ x (u γ - u 1)) ∧ ∀ x, u (x * s) = ρ s (u x)}
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun γ hγ x => ?_, fun x => by simp [h2, h2']⟩
    simp only [Pi.add_apply]
    rw [add_sub_add_comm, h1 γ hγ, h1' γ hγ, add_sub_add_comm, map_add (f := _)]
  zero_mem' := ⟨fun _ _ _ => by simp, fun _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    refine ⟨fun γ hγ x => ?_, fun x => by simp [h2]⟩
    simp only [Pi.smul_apply]
    rw [← smul_sub, h1 γ hγ, ← smul_sub, map_smul]

def relThree (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (t : G) : Submodule ℂ (G → E) where
  carrier := {Φ | Φ ∈ twInv Γ (t ^ 3) (ρ (t ^ 3)) ∧
    ∀ x, ρ (t ^ 2) (Φ x) + ρ t (Φ (x * t)) + Φ (x * t ^ 2) = 0}
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨Submodule.add_mem _ h1 h1', fun x => ?_⟩
    simp only [Pi.add_apply, map_add (f := _)]
    rw [← add_zero (0 : E)]
    nth_rewrite 1 [← h2 x]
    rw [← h2' x]
    abel
  zero_mem' := ⟨Submodule.zero_mem _, fun _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    refine ⟨Submodule.smul_mem _ c h1, fun x => ?_⟩
    simp only [Pi.smul_apply, map_smul]
    rw [← smul_add, ← smul_add, h2, smul_zero]

end GlobalTheory.HeckeFamilyMatrices.CocBound
