module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

open Module

namespace GlobalTheory.HyodoDef.PairLin

variable {k M M' : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
  [FiniteDimensional k M] [FiniteDimensional k M']

theorem finrank_annihilator_add (β : M →ₗ[k] M' →ₗ[k] k) (S : Submodule k M')
    (hS : LinearMap.ker β.flip ≤ S) :
    finrank k (LinearMap.ker (S.subtype.dualMap ∘ₗ β)) + finrank k S
      = finrank k M + finrank k (LinearMap.ker β.flip) := by
  set φ : M →ₗ[k] Dual k S := S.subtype.dualMap ∘ₗ β with hφ
  set ψ : S →ₗ[k] Dual k M := β.flip ∘ₗ S.subtype with hψ
  have hφψ : φ = ψ.dualMap ∘ₗ (Module.evalEquiv k M).toLinearMap := by
    ext a s; rfl
  have hrange : LinearMap.range φ = LinearMap.range ψ.dualMap := by
    rw [hφψ, LinearEquiv.range_comp]
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 := LinearMap.finrank_range_add_finrank_ker ψ
  have h3 : finrank k (LinearMap.range φ) = finrank k (LinearMap.range ψ) := by
    rw [hrange, LinearMap.finrank_range_dualMap_eq_finrank_range]
  have h4 : finrank k (LinearMap.ker ψ) = finrank k (LinearMap.ker β.flip) := by
    have : LinearMap.ker ψ = (LinearMap.ker β.flip).comap S.subtype := by
      rw [hψ, LinearMap.ker_comp]
    rw [this]
    exact (Submodule.comapSubtypeEquivOfLe hS).finrank_eq
  omega

theorem finrank_add_le (β : M →ₗ[k] M' →ₗ[k] k) (Ag Af : Submodule k M) (Ae Af' : Submodule k M')
    (hN : ∀ b : M', (∀ a : M, β a b = 0) → b ∈ Ae ⊓ Af')
    (hg : ∀ a ∈ Ag, ∀ b ∈ Ae, β a b = 0)
    (hf : ∀ a : M, a ∈ Af ↔ ∀ b ∈ Af', β a b = 0) :
    finrank k Ag + finrank k Ae ≤ finrank k Af + finrank k Af' := by
  have hker : ∀ b : M', b ∈ LinearMap.ker β.flip → b ∈ Ae ⊓ Af' := by
    intro b hb
    apply hN b
    intro a
    have := LinearMap.congr_fun (LinearMap.mem_ker.mp hb) a
    simpa using this
  have hNe : LinearMap.ker β.flip ≤ Ae := fun b hb => (hker b hb).1
  have hNf : LinearMap.ker β.flip ≤ Af' := fun b hb => (hker b hb).2
  have he := finrank_annihilator_add β Ae hNe
  have hf' := finrank_annihilator_add β Af' hNf
  have hgle : Ag ≤ LinearMap.ker (Ae.subtype.dualMap ∘ₗ β) := by
    intro a ha
    rw [LinearMap.mem_ker]
    ext ⟨b, hb⟩
    simpa using hg a ha b hb
  have hfeq : Af = LinearMap.ker (Af'.subtype.dualMap ∘ₗ β) := by
    ext a
    rw [hf a, LinearMap.mem_ker]
    constructor
    · intro h
      ext ⟨b, hb⟩
      simpa using h b hb
    · intro h b hb
      have := LinearMap.congr_fun h ⟨b, hb⟩
      simpa using this
  have hAg := Submodule.finrank_mono hgle
  rw [hfeq]
  omega

end GlobalTheory.HyodoDef.PairLin
