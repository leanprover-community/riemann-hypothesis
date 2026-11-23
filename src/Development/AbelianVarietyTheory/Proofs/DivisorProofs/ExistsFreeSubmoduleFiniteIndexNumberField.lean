module

public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan

namespace GlobalTheory

theorem latt_free_sub_full_rank {E : Type} [Field E] [NumberField E] (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    ∃ (f : (Fin (Module.finrank (𝓞 E) X) → 𝓞 E) →ₗ[𝓞 E] X) (m : ℕ), 0 < m ∧
      Function.Injective f ∧ ∀ x : X, m • x ∈ LinearMap.range f := by
  classical
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  set r := Module.finrank (𝓞 E) X
  obtain ⟨e, he⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := X) (le_refl r)
  let f : (Fin r → 𝓞 E) →ₗ[𝓞 E] X := Fintype.linearCombination (𝓞 E) e
  have hfv' : ∀ c : Fin r → 𝓞 E, f c = ∑ i, c i • e i := fun c => by
    simp [f, Fintype.linearCombination_apply]
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    rw [hfv'] at hc
    exact funext ((Fintype.linearIndependent_iff.mp he) c hc)

  have key : ∀ x : X, ∃ n : ℕ, 0 < n ∧ n • x ∈ LinearMap.range f := by
    intro x
    have hdep : ¬ LinearIndependent (𝓞 E) (Fin.cons x e : Fin (r + 1) → X) := by
      intro h
      have := h.fintype_card_le_finrank
      simp [r] at this
    rw [Fintype.not_linearIndependent_iff] at hdep
    obtain ⟨g, hg, i, hi⟩ := hdep
    rw [Fin.sum_univ_succ] at hg
    simp only [Fin.cons_zero, Fin.cons_succ] at hg
    have ha : g 0 ≠ 0 := by
      intro h0
      rw [h0, zero_smul, zero_add] at hg
      have hz := (Fintype.linearIndependent_iff.mp he) (fun j => g j.succ) hg
      refine hi ?_
      refine Fin.cases h0 (fun j => hz j) i
    have hax : g 0 • x ∈ LinearMap.range f := by
      refine ⟨fun j => - g j.succ, ?_⟩
      rw [hfv']
      simp only [neg_smul, Finset.sum_neg_distrib]
      exact (neg_eq_of_add_eq_zero_left hg)
    have hI : Ideal.span {g 0} ≠ ⊥ := by simpa using ha
    have hN : Ideal.absNorm (Ideal.span {g 0}) ≠ 0 := by
      rwa [Ne, Ideal.absNorm_eq_zero_iff]
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {g 0}))
    refine ⟨Ideal.absNorm (Ideal.span {g 0}), Nat.pos_of_ne_zero hN, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hb, mul_smul]
    exact Submodule.smul_mem _ _ hax
  choose N hNpos hNmem using key
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := X)
  refine ⟨f, ∏ s ∈ S, N s, Finset.prod_pos (fun s _ => hNpos s), hf, ?_⟩
  have hgen : ∀ s ∈ S, (∏ t ∈ S, N t) • s ∈ LinearMap.range f := by
    intro s hs
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem N hs
    rw [hk, mul_comm, mul_smul]
    exact AddSubmonoid.nsmul_mem (LinearMap.range f).toAddSubmonoid (hNmem s) k
  intro x
  have hx : x ∈ Submodule.span ℤ (S : Set X) := by rw [hS]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [smul_comm]
    exact zsmul_mem hy a

end GlobalTheory
