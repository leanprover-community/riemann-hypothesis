module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem multiset_prod_mem_cuspForms {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) (la : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ)
    (hw : ∀ i, w i ∈ X.SS la) (s : Multiset (Fin N)) (hs : s ≠ 0) :
    (s.map w).prod ∈ X.SS (s.card • la) := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl hs
  | cons a s ih =>
    by_cases h0 : s = 0
    · subst h0
      simpa using hw a
    · have h := (siegelSpaceAlgebra_holds (E := E) r X (s.card • la) la 0).2.1 _ (ih h0) _ (hw a).1
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, succ_nsmul, mul_comm]
      exact h

theorem eval_isHomogeneous_mem_cuspForms :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
      ∀ (la : Wt X.Ψ r) (N d : ℕ) (w : Fin N → Frame X.Ψ r → ℂ) (p : MvPolynomial (Fin N) ℂ),
        (∀ i, w i ∈ X.SS la) → 0 < d → p.IsHomogeneous d →
        (fun x => MvPolynomial.eval (fun i => w i x) p) ∈ X.SS (d • la) := by
  intro E _ _ _ r X la N d w p hw hd hp
  obtain ⟨⟨h0, hadd, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds (E := E) r X (d • la) (d • la) 0
  have hmon : ∀ m ∈ p.support, (m.toMultiset.map w).prod ∈ X.SS (d • la) := by
    intro m hm
    have hc : m.toMultiset.card = d := by
      rw [Finsupp.card_toMultiset]
      have := hp (MvPolynomial.mem_support_iff.1 hm)
      simpa [Finsupp.weight_apply, Finsupp.sum] using this
    have := multiset_prod_mem_cuspForms X la w hw m.toMultiset (by
      intro h; rw [h] at hc; simp at hc; omega)
    rwa [hc] at this
  have heq : (fun x => MvPolynomial.eval (fun i => w i x) p) =
      ∑ m ∈ p.support, p.coeff m • (m.toMultiset.map w).prod := by
    funext x
    rw [MvPolynomial.eval_eq, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
      Finsupp.prod_mapDomain_index (by simp) (by intros; rw [pow_add])]
    simp [Finsupp.prod, Finset.prod_apply]
  rw [heq]
  exact Finset.sum_induction _ (fun P => P ∈ X.SS (d • la)) (fun a b ha hb => hadd a ha b hb) h0
    (fun m hm => hsmul _ _ (hmon m hm))

end GlobalTheory
