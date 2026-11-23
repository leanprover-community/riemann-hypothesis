module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem oldIdx_injective {K : Type} {ι : K → Type} :
    Function.Injective (oldIdx (ι := ι)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  change (⟨some a, b⟩ : (o : Option K) × Tb ι o) = ⟨some c, d⟩ at h
  cases h
  rfl

theorem isMultiHomog_inc {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {f : MRing ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) :
    IsMultiHomog (inc f : MRing (Tb ι)) (fun o => o.elim 0 a) := by
  classical
  intro m hm o
  have hinj : Function.Injective (oldIdx (ι := ι)) := oldIdx_injective
  change m ∈ (MvPolynomial.rename oldIdx f).support at hm
  rw [MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨m', hm', rfl⟩ := hm
  cases o with
  | none =>
    simp only [Option.elim_none]
    apply Finset.sum_eq_zero
    intro i _
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨q, hq⟩
    have h0 := congrArg (fun z : (o : Option K) × Tb ι o => z.1) hq
    simp [oldIdx] at h0
  | some k =>
    simp only [Option.elim_some]
    refine (Fintype.sum_equiv (show Tb ι (some k) ≃ ι k from Equiv.refl _) _
      (fun i => m' ⟨k, i⟩) (fun i => ?_)).trans (hf m' hm' k)
    exact Finsupp.mapDomain_apply_of_injective hinj m' ⟨k, i⟩

theorem sum_single_none {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] (j : Fin 2) (o : Option K) :
    ∑ i, (Finsupp.single (⟨none, j⟩ : Σ o, Tb ι o) 2) ⟨o, i⟩ = o.elim 2 (fun _ => 0) := by
  classical
  cases o with
  | none =>
    simp only [Option.elim_none]
    refine (Fintype.sum_equiv (show Tb ι none ≃ Fin 2 from Equiv.refl _) _
      (fun i : Fin 2 => (Finsupp.single (⟨none, j⟩ : Σ o, Tb ι o) 2) ⟨none, i⟩) (fun _ => rfl)).trans ?_
    rw [Fin.sum_univ_two]
    fin_cases j <;> simp [Finsupp.single_apply] <;>
      (intro h
       have h2 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
       have h3 := congrArg (fun t : Fin 2 => (t : ℕ)) h2
       exact absurd h3 (by decide))
  | some k =>
    simp only [Option.elim_some]
    apply Finset.sum_eq_zero
    intro i _
    rw [Finsupp.single_apply, if_neg]
    intro h
    have h0 := congrArg (fun z : (o : Option K) × Tb ι o => z.1) h
    simp at h0

theorem isMultiHomog_quad {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] (p : ℕ) :
    IsMultiHomog (quad p : MRing (Tb ι)) (fun o => o.elim 2 (fun _ => 0)) := by
  classical
  intro m hm o
  have h1 : (xN ^ 2 : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (0 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (1 : ℤ) := by
    simp only [xN, MvPolynomial.X_pow_eq_monomial]
  have h2 : (MvPolynomial.C (p : ℤ) * yN ^ 2 : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (1 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (p : ℤ) := by
    simp only [yN, MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, mul_one]
  have hq : (quad p : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (0 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (1 : ℤ) +
      MvPolynomial.monomial (Finsupp.single (⟨none, (1 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (p : ℤ) := by
    unfold quad
    rw [h1, h2]
  rw [hq] at hm
  have hm2 := Finset.mem_union.mp (MvPolynomial.support_add hm)
  rcases hm2 with h | h
  · have h' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset h)
    subst h'
    exact sum_single_none (ι := ι) 0 o
  · have h' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset h)
    subst h'
    exact sum_single_none (ι := ι) 1 o

theorem isMultiHomogIdeal_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (W : Ideal (MRing ι)) (hW : IsMultiHomogIdeal W) : IsMultiHomogIdeal (twist p W) := by
  obtain ⟨S, hS, rfl⟩ := hW
  refine ⟨(inc '' S) ∪ {quad p}, ?_, ?_⟩
  · rintro f (⟨g, hg, rfl⟩ | hf)
    · obtain ⟨a, ha⟩ := hS g hg
      exact ⟨_, isMultiHomog_inc ha⟩
    · rw [Set.mem_singleton_iff] at hf
      subst hf
      exact ⟨_, isMultiHomog_quad p⟩
  · rw [twist, Ideal.map_span, Ideal.span_union]

end GlobalTheory.CompanionTheory.Ar.Tw
