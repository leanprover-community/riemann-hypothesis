module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntVZero
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem pow_indep_tensor : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.C), (minpoly G.F γ).natDegree = G.n →
    ∀ (v : AwayP p) (c : Fin G.n → Qv v ⊗[ℚ] G.F),
      ∑ i, iotaF G v (c i) * (1 : Qv v) ⊗ₜ[ℚ] γ ^ (i : ℕ) = 0 → c = 0 := by
  intro p _ G γ hn v c hc

  let ψ : (Fin G.n → G.F) →ₗ[ℚ] G.C :=
    { toFun := fun f => ∑ i, f i • γ ^ (i : ℕ)
      map_add' := fun f g => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun q f => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_assoc] }
  have li : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ)) := by
    have := linearIndependent_pow (K := G.F) γ
    rw [hn] at this
    exact this
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    exact funext ((Fintype.linearIndependent_iff.mp li) f hf)
  have hinj : Function.Injective (ψ.lTensor (Qv v)) :=
    Module.Flat.lTensor_preserves_injective_linearMap ψ hψ
  let e := TensorProduct.piRight ℚ ℚ (Qv v) (fun _ : Fin G.n => G.F)
  have key : ∀ t : Qv v ⊗[ℚ] (Fin G.n → G.F),
      ∑ i, iotaF G v (e t i) * (1 : Qv v) ⊗ₜ[ℚ] γ ^ (i : ℕ) = ψ.lTensor (Qv v) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), ← hx, ← hy, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.add_apply, map_add (f := _), add_mul]
    | tmul q f =>
      rw [LinearMap.lTensor_tmul]
      have : ∀ i, e (q ⊗ₜ[ℚ] f) i = q ⊗ₜ[ℚ] f i := fun i => rfl
      simp only [this, iotaF_tmul, Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.tmul_sum, Algebra.smul_def]

  have h0 : ψ.lTensor (Qv v) (e.symm c) = 0 := by
    rw [← key, LinearEquiv.apply_symm_apply]; exact hc
  have : e.symm c = 0 := hinj (by rw [h0, map_zero])
  rw [← e.apply_symm_apply c, this, map_zero]

end GlobalTheory.OrbFinAf
