module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import GroundTheory.LocalFields.Interface
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem character_kernel_generator (G : Type) [Group G] (p r : ℕ) (a : G → ℤ) (hp : p.Prime)
    (hadd : ∀ σ τ, (p : ℤ) ^ r ∣ a (σ * τ) - a σ - a τ) (hne : ∃ σ, ¬ (p : ℤ) ^ r ∣ a σ) :
    ∃ (J : Subgroup G) (_ : J.Normal) (σ₁ : G) (c : ℤ), (∀ σ, σ ∈ J ↔ (p : ℤ) ^ r ∣ a σ) ∧
      c * (p : ℤ) ^ r = (J.index : ℤ) * a σ₁ ∧ ¬ (p : ℤ) ∣ c := by
  classical
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcast : ∀ x : ℤ, ((x : ZMod (p ^ r)) = 0 ↔ (p : ℤ) ^ r ∣ x) := by
    intro x
    exact_mod_cast ZMod.intCast_zmod_eq_zero_iff_dvd x (p ^ r)
  have hmul : ∀ σ τ, ((a (σ * τ) : ZMod (p ^ r))) = (a σ : ZMod (p ^ r)) + (a τ : ZMod (p ^ r)) := by
    intro σ τ
    have := (hcast _).2 (hadd σ τ)
    push_cast at this
    linear_combination this
  have hone : ((a 1 : ℤ) : ZMod (p ^ r)) = 0 := by
    have := hmul 1 1
    simp only [mul_one] at this
    linear_combination -this
  let f : G →* Multiplicative (ZMod (p ^ r)) :=
    { toFun := fun σ => Multiplicative.ofAdd (a σ : ZMod (p ^ r))
      map_one' := by simp only [hone, ofAdd_zero]
      map_mul' := fun σ τ => by simp only [hmul, ofAdd_add] }
  have hfx : ∀ σ, f σ = Multiplicative.ofAdd (a σ : ZMod (p ^ r)) := fun _ => rfl
  have hker : ∀ σ, σ ∈ f.ker ↔ (p : ℤ) ^ r ∣ a σ := by
    intro σ
    rw [MonoidHom.mem_ker, hfx, ofAdd_eq_one, hcast]
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := f.range)
  obtain ⟨σ₁, hσ₁⟩ := g.2
  set x : ZMod (p ^ r) := (a σ₁ : ZMod (p ^ r)) with hxdef
  have hidx : f.ker.index = addOrderOf x := by
    have h1 : f.ker.index = Nat.card f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    rw [h1, ← hg, ← Subgroup.orderOf_coe, ← hσ₁, hfx, orderOf_ofAdd_eq_addOrderOf]
  have hsm : ∀ k : ℕ, k • x = 0 ↔ (p : ℤ) ^ r ∣ (k : ℤ) * a σ₁ := by
    intro k
    rw [← hcast]
    push_cast
    rw [nsmul_eq_mul]
  have hdvd : addOrderOf x ∣ p ^ r :=
    (addOrderOf_dvd_natCard x).trans (by rw [Nat.card_zmod])
  obtain ⟨s, hsr, hs⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hs0 : s ≠ 0 := by
    rintro rfl
    obtain ⟨τ, hτ⟩ := hne
    have : f.ker = ⊤ := Subgroup.index_eq_one.1 (by rw [hidx, hs, pow_zero])
    exact hτ ((hker τ).1 (this ▸ Subgroup.mem_top τ))
  obtain ⟨c, hc⟩ := (hsm (addOrderOf x)).1 (addOrderOf_nsmul_eq_zero x)
  refine ⟨f.ker, inferInstance, σ₁, c, hker, ?_, ?_⟩
  · rw [hidx, hc]; ring
  · rintro ⟨d, rfl⟩
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have key : (p : ℤ) ^ r ∣ ((p ^ (s - 1) : ℕ) : ℤ) * a σ₁ := by
      refine ⟨d, ?_⟩
      apply mul_left_cancel₀ hp0
      have hs' : (p : ℤ) ^ s = p * p ^ (s - 1) := by
        rw [← pow_succ']; congr 1; omega
      have := hc
      rw [hs] at this
      push_cast at this ⊢
      rw [hs'] at this
      linear_combination this
    have h2 : addOrderOf x ∣ p ^ (s - 1) :=
      addOrderOf_dvd_of_nsmul_eq_zero ((hsm _).2 key)
    rw [hs, Nat.pow_dvd_pow_iff_le_right hp.one_lt] at h2
    omega

end GlobalTheory.PMon.Ram
