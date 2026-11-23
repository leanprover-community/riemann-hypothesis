module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.LogRootDiscChar
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ConductorLocalPartDvdIff
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
public import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.MulChar.Duality
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace KStar.Ram

open DirichletCharacter

private theorem prime_dvd_finset_lcm {ι : Type*} {p : ℕ} (hp : p.Prime) (s : Finset ι)
    (c : ι → ℕ) : p ∣ s.lcm c ↔ ∃ i ∈ s, p ∣ c i := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [hp.ne_one]
  · intro a t ha ih
    rw [Finset.lcm_insert]
    change p ∣ Nat.lcm (c a) (t.lcm c) ↔ _
    rw [hp.dvd_lcm, ih]
    simp

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

theorem ramIdx_eq_one_iff (X : Subgroup (DirichletCharacter ℂ N)) :
    (ramIdx l X = 1 ↔ ∀ ψ ∈ X, ¬ l ∣ ψ.conductor) ∧ (ramIdx l X = 1 ↔ ¬ l ∣ fieldCond X) ∧
      1 ≤ ramIdx l X := by
  have key : ramIdx l X = 1 ↔ ∀ ψ ∈ X, localPart N l ψ = 1 := by
    unfold ramIdx
    rw [Subgroup.card_eq_one, Subgroup.map_eq_bot_iff]
    exact ⟨fun h ψ hψ => h hψ, fun h ψ hψ => h ψ hψ⟩
  have e1 : ramIdx l X = 1 ↔ ∀ ψ ∈ X, ¬ l ∣ ψ.conductor := by
    rw [key]
    exact forall₂_congr fun ψ _ => (localPart_eq_one_iff l ψ).2
  refine ⟨e1, ?_, ?_⟩
  · rw [e1]
    unfold fieldCond
    rw [prime_dvd_finset_lcm (Fact.out)]
    simp
  · unfold ramIdx
    exact Nat.card_pos

end KStar.Ram
