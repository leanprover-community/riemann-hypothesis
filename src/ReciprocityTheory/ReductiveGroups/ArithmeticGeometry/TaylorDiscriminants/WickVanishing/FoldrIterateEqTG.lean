module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ETGMulQ
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.EvalZeroReplicateAppend
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.FoldrIterateDerivationEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SumSplitsEvalTwoWord

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB.G2.Gen

open ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {S : Type} [CommRing S] {ι : Type}
  (D : ι → S → S) (κ : k →+* S)

def PolG [Fintype ι] (P : MvPolynomial ι k) (A : S) : S :=
  ∑ n ∈ P.support, κ (P.coeff n) * (Finset.univ : Finset ι).toList.foldr (fun l g => (D l)^[n l] g) A

theorem TG_replicate (n : ℕ) (l : ι) (A : S) : TG D (List.replicate n l) A = (D l)^[n] A := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, Function.iterate_succ_apply', ← ih]
    rfl

theorem foldr_iterate_eq_TG (Ls : List ι) (m : ι →₀ ℕ) (A : S) :
    Ls.foldr (fun l g => (D l)^[m l] g) A = TG D (word Ls m) A := by
  induction Ls with
  | nil => rfl
  | cons l Ls ih =>
    rw [List.foldr_cons, ih]
    have e : word (l :: Ls) m = List.replicate (m l) l ++ word Ls m := by simp [word]
    rw [e, TG_append, TG_replicate]

theorem e_PolG [Fintype ι] (e : S →+* k) (he : ∀ a, e (κ a) = a) (P : MvPolynomial ι k) (A : S) :
    e (PolG D κ P A) = (AddMonoidAlgebra.coeff P).sum
      (fun n a => a * e (TG D (word (Finset.univ : Finset ι).toList n) A)) := by

  simp only [PolG, map_sum, map_mul, he, foldr_iterate_eq_TG]
  rfl

theorem half_gen [Algebra ℚ k] [Fintype ι]
    (hadd : ∀ l f g, D l (f + g) = D l f + D l g) (hC : ∀ l a, D l (κ a) = 0)
    (hmul : ∀ l f g, D l (f * g) = D l f * g + f * D l g)
    (e : S →+* k) (he : ∀ a, e (κ a) = a) (c : ι → ι → k) (q : S) (hc : ∀ l l', c l l' = c l' l)
    (hq0 : e q = 0) (hq1 : ∀ l, e (D l q) = 0) (hq2 : ∀ l l', D l (D l' q) = κ (c l l'))
    (P : MvPolynomial ι k) (A : S) :
    e (PolG D κ P (A * q)) = algebraMap ℚ k (1 / 2) * e (PolG D κ (secondOrder k c P) A) := by
  classical
  set ψ : List ι → k := fun w => e (TG D w A) with hψ
  rw [e_PolG D κ e he, e_PolG D κ e he]
  have h2 : (AddMonoidAlgebra.coeff (secondOrder k c P)).sum
      (fun n a => a * e (TG D (word (Finset.univ : Finset ι).toList n) A)) = lamW ψ (secondOrder k c P) := rfl
  rw [h2, lamW_secondOrder, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun n _ => ?_
  rw [e_TG_mul_q D κ hadd hC hmul e c q hq0 hq1 hq2 he]
  have h3 := sum_splits_evalTwo_word c hc (Finset.univ : Finset ι).toList (Finset.nodup_toList _) n ψ
  have h4 : (algebraMap ℚ k (1 / 2)) * 2 = 1 := by
    rw [← map_ofNat (algebraMap ℚ k) 2, ← map_mul]; norm_num
  calc (AddMonoidAlgebra.coeff P) n * ((splits (word (Finset.univ : Finset ι).toList n)).map
        (fun p => e (TG D p.1 A) * ev2 c p.2)).sum
      = (AddMonoidAlgebra.coeff P) n * ((algebraMap ℚ k (1 / 2) * 2) *
          ((splits (word (Finset.univ : Finset ι).toList n)).map (fun p => ψ p.1 * ev2 c p.2)).sum) := by
        rw [h4, one_mul]
    _ = algebraMap ℚ k (1 / 2) * ((AddMonoidAlgebra.coeff P) n * rW ψ c n) := by
        rw [mul_assoc (algebraMap ℚ k (1 / 2)), h3]
        simp only [rW]
        ring

theorem kill_gen [Algebra ℚ k] [Fintype ι]
    (hadd : ∀ l f g, D l (f + g) = D l f + D l g) (hC : ∀ l a, D l (κ a) = 0)
    (hmul : ∀ l f g, D l (f * g) = D l f * g + f * D l g)
    (e : S →+* k) (he : ∀ a, e (κ a) = a) (c : ι → ι → k) (q : S) (hc : ∀ l l', c l l' = c l' l)
    (hq0 : e q = 0) (hq1 : ∀ l, e (D l q) = 0) (hq2 : ∀ l l', D l (D l' q) = κ (c l l'))
    (P : MvPolynomial ι k) (hP : secondOrder k c P = 0) (G Y : S) :
    e (PolG D κ P (G * (1 + q * Y))) = e (PolG D κ P G) := by
  have hsplit : G * (1 + q * Y) = G + G * Y * q := by ring
  have hlin : ∀ A B, PolG D κ P (A + B) = PolG D κ P A + PolG D κ P B := by
    intro A B
    simp only [PolG, foldr_iterate_eq_TG]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [TG_add, mul_add]
    exact hadd
  rw [hsplit, hlin, map_add (f := _), half_gen D κ hadd hC hmul e he c q hc hq0 hq1 hq2 P (G * Y), hP]
  simp [PolG]

end ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
