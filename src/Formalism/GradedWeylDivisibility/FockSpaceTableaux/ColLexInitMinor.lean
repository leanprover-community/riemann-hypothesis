module

public import Formalism.GradedWeylDivisibility.StatementC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

theorem lcminor_initMinor_eq (R : Type) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    initMinor R I hs = ∑ σ : Equiv.Perm (Fin s),
      monomial (∑ q : Fin s, Finsupp.single (I (σ q), Fin.castLE hs q) 1)
        (((Equiv.Perm.sign σ : ℤ) : R)) := by
  rw [initMinor, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.of_apply]
  rw [← mul_one (((Equiv.Perm.sign σ : ℤ) : R)), ← C_mul_monomial, monomial_sum_one,
    Units.smul_def, zsmul_eq_mul]
  congr 1

theorem colLexInitMinor_of (h : MinorExpLt) : ColLexInitMinor := by
  intro R _ _ r n s I hs hI
  rw [lcminor_initMinor_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin s)))]
  simp only [Equiv.Perm.one_apply, Equiv.Perm.sign_one, Units.val_one, Int.cast_one]
  set g := ∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin s)),
    monomial (∑ q : Fin s, Finsupp.single (I (σ q), Fin.castLE hs q) 1)
      (((Equiv.Perm.sign σ : ℤ) : R)) with hg_def
  set e := ∑ q : Fin s, Finsupp.single (I q, Fin.castLE hs q) 1 with he
  have hdf : (colLex r n).degree (monomial e (1 : R)) = e := by
    classical
    rw [MonomialOrder.degree_monomial]
    simp
  by_cases hg : g = 0
  · rw [hg, add_zero, hdf, MonomialOrder.leadingCoeff_monomial]
    exact ⟨rfl, rfl⟩
  · have hne : (Finset.univ.erase (1 : Equiv.Perm (Fin s))).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      apply hg
      rw [hg_def, h0, Finset.sum_empty]
    have hlt : (colLex r n).toSyn ((colLex r n).degree g) <
        (colLex r n).toSyn ((colLex r n).degree (monomial e (1 : R))) := by
      rw [hdf]
      refine lt_of_le_of_lt MonomialOrder.degree_sum_le ?_
      obtain ⟨σ0, hσ0⟩ := hne
      rw [Finset.sup_lt_iff (lt_of_le_of_lt bot_le (h r n s I hs hI σ0 (Finset.ne_of_mem_erase hσ0)))]
      intro σ hσ
      exact lt_of_le_of_lt (MonomialOrder.degree_monomial_le _) (h r n s I hs hI σ (Finset.ne_of_mem_erase hσ))
    rw [MonomialOrder.degree_add_of_lt hlt, MonomialOrder.leadingCoeff_add_of_lt hlt, hdf,
      MonomialOrder.leadingCoeff_monomial]
    exact ⟨rfl, rfl⟩

end Formalism.GradedWeylDivisibility
