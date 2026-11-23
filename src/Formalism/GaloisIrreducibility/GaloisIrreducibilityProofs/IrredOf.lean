module

public import Formalism.GaloisIrreducibility.NoSolvableOf
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace Formalism.GaloisIrreducibility

open Finset

lemma isSubSum_of_subset {ι : Type} (f : ι → ℕ) (I J : Finset ι) (hJ : J ⊆ I) :
    IsSubSum (I.val.map f) (∑ i ∈ J, f i) := by
  unfold IsSubSum
  exact ⟨J.val.map f, Multiset.map_le_map (Finset.val_le_iff.2 hJ), rfl⟩

theorem irreducible_of_galois_conditions : IrredOf := by
  intro hA K V P ι _ _ _ _ _ τ F q O I hFτ hO hroots hsub W hWτ hWF
  classical
  have hs1 : ∀ v, IsSubSum ((I v).val.map fun i => (O v i).card) (Module.finrank K W) := by
    intro v
    obtain ⟨J, hJ, hJeq⟩ := hA K V ι (τ v) (F v) (q v) (O v) (I v) (hFτ v) (hO v) (hroots v) ⊥ W
      bot_le (by simp) (by simp) (hWτ v) (hWF v)
    rw [finrank_bot, Nat.sub_zero] at hJeq
    rw [hJeq]
    exact isSubSum_of_subset _ _ _ hJ
  have hs2 : ∀ v, IsSubSum ((I v).val.map fun i => (O v i).card)
      (Module.finrank K V - Module.finrank K W) := by
    intro v
    obtain ⟨J, hJ, hJeq⟩ := hA K V ι (τ v) (F v) (q v) (O v) (I v) (hFτ v) (hO v) (hroots v) W ⊤
      le_top (hWτ v) (hWF v) (by simp) (by simp)
    rw [finrank_top] at hJeq
    rw [hJeq]
    exact isSubSum_of_subset _ _ _ hJ
  by_contra hne
  push_neg at hne
  obtain ⟨h0, h1⟩ := hne
  have hd0 : 0 < Module.finrank K W :=
    Nat.pos_of_ne_zero fun h => h0 (Submodule.finrank_eq_zero.mp h)
  have hdN : Module.finrank K W < Module.finrank K V :=
    Submodule.finrank_lt h1
  obtain ⟨v, hv⟩ := hsub (min (Module.finrank K W) (Module.finrank K V - Module.finrank K W))
    (by omega) (by omega)
  apply hv
  rcases min_choice (Module.finrank K W) (Module.finrank K V - Module.finrank K W) with h | h
  · rw [h]
    exact hs1 v
  · rw [h]
    exact hs2 v

end Formalism.GaloisIrreducibility
