module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipMir
public import GroundTheory.LocalFields.LocalFourierChar
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirFourier

theorem exists_box_subset_of_mem_nhds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) {U : Set (Fin n → k)} (hU : U ∈ 𝓝 (0 : Fin n → k)) :
    ∃ N : ℤ, ∀ x ∈ box k n N, Multiplicative.toAdd x ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  have hball : ∀ i, ∃ N : ℤ, (valBall k N : Set k) ⊆ t i := fun i => by
    obtain ⟨N, -, hN⟩ := (hasBasis_nhds_zero_valBall (K := k)).mem_iff.mp (ht i)
    exact ⟨N, hN⟩
  choose Nf hNf using hball
  refine ⟨((Finset.univ.sup fun i => (Nf i).toNat : ℕ) : ℤ), fun x hx => hsub fun i _ => ?_⟩
  have hle : Nf i ≤ ((Finset.univ.sup fun i => (Nf i).toNat : ℕ) : ℤ) :=
    (Int.self_le_toNat (Nf i)).trans (by exact_mod_cast Finset.le_sup (f := fun i => (Nf i).toNat) (Finset.mem_univ i))
  exact hNf i (valBall_antitone hle ((mem_box k).mp hx i))

theorem exists_box_fixed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V), IsSmooth ρ →
    ∀ v : V, ∃ N : ℤ, ∀ x ∈ box k n N, ρ x v = v := by
  intro k _ _ _ _ n V _ _ ρ hρ v
  have hopen : IsOpen {y : Fin n → k | ρ (Multiplicative.ofAdd y) v = v} := hρ v
  have hU : {y : Fin n → k | ρ (Multiplicative.ofAdd y) v = v} ∈ 𝓝 (0 : Fin n → k) :=
    hopen.mem_nhds (by simp)
  obtain ⟨N, hN⟩ := exists_box_subset_of_mem_nhds k n hU
  exact ⟨N, fun x hx => by simpa using hN x hx⟩

end GlobalTheory.CompanionTheory.MirFourier
