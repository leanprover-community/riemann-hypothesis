module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

namespace GlobalTheory

theorem functional_fixed_by_idempotent_represented
    {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hL : ∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) (_hR : ∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0)
    (P P' : Module.End ℂ V) (_hP : P ∘ₗ P = P) (hfin : FiniteDimensional ℂ (LinearMap.range P))
    (hadj : ∀ φ ψ, B (P φ) ψ = B φ (P' ψ)) (f : V →ₗ[ℂ] ℂ) (hf : f ∘ₗ P = f) :
    ∃ ψ, ∀ φ, B φ ψ = f φ := by
  set U := LinearMap.range P

  let T : V →ₗ[ℂ] Module.Dual ℂ U := (B.domRestrict U).flip
  have hT : ∀ ψ (u : U), T ψ u = B u ψ := fun _ _ => rfl
  have hcoann : (LinearMap.range T).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Submodule.mem_dualCoannihilator] at hu
    have : (u : V) = 0 := hL u (fun ψ => by
      have := hu (T ψ) ⟨ψ, rfl⟩
      simpa [hT] using this)
    simpa using Subtype.ext this
  have hsurj : LinearMap.range T = ⊤ := by
    have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range T)
    rw [hcoann] at h
    rw [← h]
    exact Submodule.dualAnnihilator_bot
  have : f.domRestrict U ∈ LinearMap.range T := by rw [hsurj]; trivial
  obtain ⟨ψ, hψ⟩ := this
  refine ⟨P' ψ, fun φ => ?_⟩
  rw [← hadj]
  have h1 : T ψ ⟨P φ, φ, rfl⟩ = f (P φ) := by rw [hψ]; rfl
  rw [hT] at h1
  rw [h1]
  exact congrArg (fun g : V →ₗ[ℂ] ℂ => g φ) hf

end GlobalTheory
