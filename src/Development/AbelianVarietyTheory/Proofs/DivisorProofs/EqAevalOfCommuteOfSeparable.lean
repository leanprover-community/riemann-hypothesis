module

import Formalism.PadicSubsetSums.StableGradedCounts.ExistsNeZeroAevalEqZero
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative

@[expose] public section

open Polynomial
open scoped TensorProduct

namespace GlobalTheory.SepCentralizer

theorem exists_ne_zero_aeval_eq_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (p : K[X]) (hp : Irreducible p)
    (hdvd : p ∣ g.charpoly) : ∃ w : V, w ≠ 0 ∧ aeval g p w = 0 := by
  apply Formalism.IrreducibleCountingLemmas.Z.exists_ne_zero_aeval_eq_zero <;> assumption

theorem exists_annihilator_eq {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (hs : g.charpoly.Separable) (d : K[X]) :
    d ∣ g.charpoly → ∃ e : V, aeval g d e = 0 ∧ ∀ q : K[X], aeval g q e = 0 → d ∣ q := by
  apply Formalism.IrreducibleCountingLemmas.Z.exists_annihilator_eq <;> assumption

theorem exists_cyclic {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (hs : g.charpoly.Separable) :
    ∃ e : V, ∀ v : V, ∃ q : K[X], aeval g q e = v := by
  obtain ⟨e, -, he⟩ := exists_annihilator_eq g hs g.charpoly dvd_rfl
  refine ⟨e, ?_⟩
  let φ : K[X] →ₗ[K] V := (LinearMap.applyₗ e) ∘ₗ (aeval g).toLinearMap
  have hφ : ∀ p, φ p = aeval g p e := fun p => rfl
  let ψ : degreeLT K (Module.finrank K V) →ₗ[K] V := φ ∘ₗ (degreeLT K (Module.finrank K V)).subtype
  have hinj : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro q hq
    have h1 : g.charpoly ∣ (q : K[X]) := he _ hq
    have h2 : (q : K[X]).degree < g.charpoly.degree := by
      rw [degree_eq_natDegree g.charpoly_monic.ne_zero, LinearMap.charpoly_natDegree]
      exact mem_degreeLT.1 q.2
    exact Subtype.ext (eq_zero_of_dvd_of_degree_lt h1 h2)
  have hfin : Module.finrank K (degreeLT K (Module.finrank K V)) = Module.finrank K V := by
    rw [(degreeLTEquiv K (Module.finrank K V)).finrank_eq, Module.finrank_fin_fun]
  have : FiniteDimensional K (degreeLT K (Module.finrank K V)) :=
    (degreeLTEquiv K (Module.finrank K V)).symm.finiteDimensional
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 hinj
  intro v
  obtain ⟨q, hq⟩ := hsurj v
  exact ⟨q, hq⟩

theorem exists_eq_aeval_of_commute {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g c : Module.End K V) (hs : g.charpoly.Separable)
    (hc : c * g = g * c) : ∃ p : K[X], c = aeval g p := by
  obtain ⟨e, he⟩ := exists_cyclic g hs
  obtain ⟨p, hp⟩ := he (c e)
  refine ⟨p, LinearMap.ext fun v => ?_⟩
  obtain ⟨q, rfl⟩ := he v
  have hcq : Commute (aeval g q) c :=
    (Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton K g) hc).symm
  rw [← Module.End.mul_apply, ← hcq.eq, Module.End.mul_apply, ← hp, ← Module.End.mul_apply,
    ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

theorem eq_aeval_of_commute_of_separable : ∀ (k : Type) [Field k] (n : ℕ)
    (Γ C : Matrix (Fin n) (Fin n) k) (u r : k[X]),
    u * Γ.charpoly + r * derivative Γ.charpoly = 1 → C * Γ = Γ * C →
    ∃ g : k[X], C = aeval Γ g := by
  intro k _ n Γ C u r h hC
  let e := (Matrix.toLinAlgEquiv' (R := k) (n := Fin n))
  have hs : (e Γ).charpoly.Separable := by
    rw [show e Γ = Matrix.toLin' Γ from rfl, Matrix.charpoly_toLin']
    exact ⟨u, r, h⟩
  have hc : e C * e Γ = e Γ * e C := by
    rw [← map_mul, ← map_mul, hC]
  obtain ⟨p, hp⟩ := exists_eq_aeval_of_commute _ _ hs hc
  refine ⟨p, e.injective ?_⟩
  rw [hp]
  exact aeval_algHom_apply e.toAlgHom Γ p

end GlobalTheory.SepCentralizer
