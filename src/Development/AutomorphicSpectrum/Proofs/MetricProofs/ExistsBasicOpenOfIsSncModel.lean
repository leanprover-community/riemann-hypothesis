module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
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
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem exists_basicOpen_of_isSncModel : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)), IsSncModel y e J → ∀ p : (k : K) → ι k, (∀ k, y ⟨k, p k⟩ ≠ 0) → ∀ t : (Σ k, ι k) → ℂ, (∀ G : MvPolynomial (Σ k, ι k) ℚ, aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) G = 0 → eval t (map (algebraMap ℚ ℂ) G) = 0) → ∃ (F : MvPolynomial (Σ k, ι k) ℚ) (S : Subalgebra ℚ Ω) (z : Fin e → S) (n : ℕ), aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) F ≠ 0 ∧ eval t (map (algebraMap ℚ ℂ) F) ≠ 0 ∧ S = Algebra.adjoin ℚ (insert (aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) F)⁻¹ (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩))) ∧ Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧ ∀ q : Ideal S, q.IsPrime → ((∀ g ∈ J, ∀ s : S, (s : Ω) = aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) g → s ∈ q) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q) := by
  intro K _ ι _ Ω _ _ y e J h p hp t ht
  obtain ⟨m, f, a, hf, ha, hsum, hcl⟩ := h p hp
  rw [Algebra.adjoin_range_eq_range_aeval] at hf ha
  choose F hF using fun l => AlgHom.mem_range _ |>.1 (hf l)
  choose A hA using fun l => AlgHom.mem_range _ |>.1 (ha l)
  obtain rfl : f = fun l => aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) (F l) :=
    funext fun l => (hF l).symm
  have hker : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) (∑ l, A l * F l - 1) = 0 := by

    simp only [map_sub, map_sum, map_mul, map_one, hA]
    exact sub_eq_zero.2 hsum
  have h1 := ht _ hker

  simp only [map_sub, map_sum, map_mul, map_one] at h1
  obtain ⟨l, hl⟩ : ∃ l, eval t (map (algebraMap ℚ ℂ) (F l)) ≠ 0 := by
    by_contra hc
    push_neg at hc
    simp [hc] at h1
  have hfl : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) (F l) ≠ 0 := fun h0 => hl (ht _ h0)
  obtain ⟨-, z, n, -, -, hspan, hq⟩ := hcl l hfl _ rfl
  exact ⟨F l, _, z, n, hfl, hl, rfl, hspan, hq⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
