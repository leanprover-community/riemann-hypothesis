module

public import Formalism.PadicSubsetSums.CentralIdempotents.SchurOrthogonalityCompact
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
public import Mathlib.RingTheory.RamificationInertia.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped NumberField

namespace Formalism.IrreducibleCountingLemmas.Z

theorem degree_one_split : DegreeOneSplit := by
  intro F E _ _ _ _ _ h2 P _ hP hf he
  classical
  set p : Ideal (𝓞 F) := P.under (𝓞 F) with hp
  have hfin : (p.primesOver (𝓞 E)).Finite := Algebra.QuasiFinite.finite_primesOver p
  let _ : Fintype (p.primesOver (𝓞 E)) := hfin.fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  have hrank : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← h2]
    exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm
  rw [hrank] at hsum
  have hf1 : P.inertiaDeg (𝓞 F) = 1 := by
    have := Ideal.inertiaDeg_tower (R := ℤ) p P
    rw [hf] at this
    exact Nat.eq_one_of_mul_eq_one_left this.symm
  have hPmem : P ∈ p.primesOver (𝓞 E) := ⟨inferInstance, ⟨rfl⟩⟩
  have hpos : ∀ q : p.primesOver (𝓞 E), 1 ≤ q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) := by
    intro q
    have : q.1.IsPrime := q.2.1
    exact Nat.mul_pos (Ideal.ramificationIdx_pos (R := 𝓞 F) q.1) (Ideal.inertiaDeg_pos q.1 (𝓞 F))
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨P, hPmem⟩ : p.primesOver (𝓞 E)))] at hsum
  simp only [he, hf1, mul_one] at hsum
  have hrest : ∑ q ∈ Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E)),
      q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) = 1 := by omega
  have hle : (Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E))).card ≤ 1 := by
    calc _ = ∑ q ∈ Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E)), 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun q _ => hpos q
      _ = 1 := hrest
  have hge : (Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E))).card ≠ 0 := by
    intro h0
    rw [Finset.card_eq_zero] at h0
    rw [h0] at hrest
    simp at hrest
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at hle hge
  have key : Fintype.card { x // x ∈ p.primesOver (𝓞 E) } = 2 := by omega
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact key

end Formalism.IrreducibleCountingLemmas.Z
