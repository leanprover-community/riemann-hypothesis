module

public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.AdditiveDefs
public import Mathlib.Algebra.Field.ZMod
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.AdditiveInvariants
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Representation
open scoped TensorProduct

universe u v

section Fun

variable {k Γ N : Type*} [CommSemiring k] [Group Γ] [AddCommMonoid N] [Module k N]

def funRep (Y : Type*) [MulAction Γ Y] (σ : Representation k Γ N) : Representation k Γ (Y → N) where
  toFun γ := LinearMap.pi fun y => σ γ ∘ₗ LinearMap.proj (γ⁻¹ • y)
  map_one' := by
    ext F y
    simp
  map_mul' γ δ := by
    ext F y
    simp [mul_smul]

end Fun

section Pi

variable {k Γ : Type*} [CommSemiring k] [Monoid Γ]

def piFamilyRep {ι : Type*} (V : ι → Type*) [∀ i, AddCommMonoid (V i)] [∀ i, Module k (V i)]
    (ρ : ∀ i, Representation k Γ (V i)) : Representation k Γ (∀ i, V i) where
  toFun γ := LinearMap.pi fun i => ρ i γ ∘ₗ LinearMap.proj i
  map_one' := by
    ext
    simp
  map_mul' γ δ := by
    ext
    simp

end Pi

theorem finite_tensorProduct_zmod (l : ℕ) [NeZero l] (W N : Type*) [AddCommGroup W]
    [Module (ZMod l) W] [Finite W] [AddCommGroup N] [Module (ZMod l) N] [Finite N] :
    Finite (W ⊗[ZMod l] N) := by
  have := Module.Finite.of_finite (R := ZMod l) (M := W)
  have := Module.Finite.of_finite (R := ZMod l) (M := N)
  exact Module.finite_of_finite (ZMod l)

namespace AdditiveFunction

variable {l : ℕ} {Γ : Type v} [Group Γ]

noncomputable def tensorRep [Fact l.Prime] (d : AdditiveFunction.{u} l Γ) {N : Type u}
    [AddCommGroup N] [Module (ZMod l) N] [Finite N] (σ : Representation (ZMod l) Γ N) :
    AdditiveFunction.{u} l Γ where
  toFun W _ _ _ ρ :=
    haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
    haveI := finite_tensorProduct_zmod l W N
    d.toFun (W ⊗[ZMod l] N) (ρ.tprod σ)
  additive := by
    intro X₁ X₂ X₃ _ _ _ _ _ _ _ _ _ ρ₁ ρ₂ ρ₃ f g hf hg hinj hfg hs
    have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
    have := finite_tensorProduct_zmod l X₁ N
    have := finite_tensorProduct_zmod l X₂ N
    have := finite_tensorProduct_zmod l X₃ N
    exact d.additive _ _ _ (f.rTensor N) (g.rTensor N)
      (isIntertwiningMap_rTensor σ hf) (isIntertwiningMap_rTensor σ hg)
      (Module.Flat.rTensor_preserves_injective_linearMap f hinj) (rTensor_exact N hfg hs)
      (LinearMap.rTensor_surjective N hs)

theorem tensorRep_apply [Fact l.Prime] (d : AdditiveFunction.{u} l Γ) {N : Type u}
    [AddCommGroup N] [Module (ZMod l) N] [Finite N] (σ : Representation (ZMod l) Γ N)
    (W : Type u) [AddCommGroup W] [Module (ZMod l) W] [Finite W]
    (ρ : Representation (ZMod l) Γ W) [Finite (W ⊗[ZMod l] N)] :
    (d.tensorRep σ).toFun W ρ = d.toFun (W ⊗[ZMod l] N) (ρ.tprod σ) := by
  rfl

end AdditiveFunction

end GroundTheory.ProfCoh
