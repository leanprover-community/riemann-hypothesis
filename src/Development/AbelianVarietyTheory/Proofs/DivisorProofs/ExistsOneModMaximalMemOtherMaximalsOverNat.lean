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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

theorem GlobalTheory.sep_one_mod_maximal_mem_others : ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal),
    ∃ e : 𝓞 E, e - 1 ∈ 𝔭 ∧ ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮 := by
  intro E _ _ n hn 𝔭 h𝔭
  have hn0 : (n : 𝓞 E) ≠ 0 := by exact_mod_cast hn.ne'
  have hI0 : Ideal.span {(n : 𝓞 E)} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  set S := (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(n : 𝓞 E)})).toFinset.erase 𝔭
    with hS
  have htop : 𝔭 ⊔ ∏ 𝔮 ∈ S, 𝔮 = ⊤ := by
    refine Ideal.sup_prod_eq_top fun 𝔮 h𝔮 => ?_
    rw [hS, Finset.mem_erase, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hI0] at h𝔮
    obtain ⟨hne, hpr, hle⟩ := h𝔮
    have hbot : 𝔮 ≠ ⊥ := by
      rintro rfl
      rw [Ideal.span_le, Set.singleton_subset_iff] at hle
      exact hn0 hle
    have hmax : 𝔮.IsMaximal := hpr.isMaximal hbot
    by_contra hc
    have e1 : 𝔭 = 𝔭 ⊔ 𝔮 := h𝔭.eq_of_le hc le_sup_left
    have h2 : 𝔮 ≤ 𝔭 := e1 ▸ le_sup_right
    exact hne (hmax.eq_of_le h𝔭.ne_top h2)
  have h1 : (1 : 𝓞 E) ∈ 𝔭 ⊔ ∏ 𝔮 ∈ S, 𝔮 := htop ▸ Submodule.mem_top
  obtain ⟨p, hp, e, he, hpe⟩ := Submodule.mem_sup.mp h1
  refine ⟨e, ?_, fun 𝔮 hmax hn𝔮 hne => ?_⟩
  · have : e - 1 = -p := by rw [← hpe]; ring
    rw [this]; exact 𝔭.neg_mem hp
  · have hmem : 𝔮 ∈ S := by
      rw [hS, Finset.mem_erase, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hI0]
      exact ⟨hne, hmax.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hn𝔮⟩
    exact Ideal.prod_le_inf.trans (Finset.inf_le hmem) he
