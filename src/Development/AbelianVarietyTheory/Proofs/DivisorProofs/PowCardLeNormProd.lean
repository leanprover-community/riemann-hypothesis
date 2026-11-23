module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

namespace GlobalTheory.RootNormLowerBound

theorem pow_card_le_norm_prod {ε : ℝ} (hε : 0 < ε) (s : Multiset ℂ)
    (h : ∀ t ∈ s, ε ≤ ‖t‖) : ε ^ Multiset.card s ≤ ‖(s.map (fun a => -a)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := h a (Multiset.mem_cons_self a s)
    have ih' := ih fun t ht => h t (Multiset.mem_cons_of_mem ht)
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul, norm_neg, pow_succ,
      mul_comm (ε ^ Multiset.card s)]
    exact mul_le_mul ha ih' (by positivity) (norm_nonneg _)

theorem exists_root_norm_lt {F : Polynomial ℂ} (hF : Polynomial.Monic F) {ε : ℝ}
    (hε : (0 : ℝ) < ε) (h0 : ‖F.coeff (0 : ℕ)‖ < ε ^ Polynomial.natDegree F) :
    ∃ (t : ℂ), Polynomial.IsRoot F t ∧ ‖t‖ < ε := by
  by_contra hcon
  have hall : ∀ t ∈ F.roots, ε ≤ ‖t‖ := fun t ht =>
    le_of_not_gt fun hlt => hcon ⟨t, (Polynomial.mem_roots hF.ne_zero).1 ht, hlt⟩
  have h1 := pow_card_le_norm_prod hε F.roots hall
  have hc : F.coeff 0 = (F.roots.map fun a => -a).prod := by
    rw [(IsAlgClosed.splits F).coeff_zero_eq_prod_roots_of_monic hF, Multiset.prod_map_neg,
      IsAlgClosed.card_roots_eq_natDegree]
  rw [IsAlgClosed.card_roots_eq_natDegree, ← hc] at h1
  linarith

end GlobalTheory.RootNormLowerBound
