module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallMemFilt

@[expose] public section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory.FormalOrigin.Extend

theorem list_foldr_iterate_single_of_nodup {A : Type} {n : ℕ} (d : Fin n → A → A) (j : Fin n) (f : A) :
    ∀ l : List (Fin n), l.Nodup →
      l.foldr (fun i g => (d i)^[(Finsupp.single j 1 : Fin n →₀ ℕ) i] g) f = if j ∈ l then d j f else f := by
  intro l hl
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    rw [List.foldr_cons, ih hl.2]
    by_cases hij : i = j
    · subst hij
      simp [hl.1]
    · have hji : j ≠ i := fun h => hij h.symm
      simp [Finsupp.single_apply, hij, hji]

theorem taylor_coeff_single (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B)
    (ds : Fin n → Derivation ℤ A A) (j : Fin n) (f : A) :
    MvPowerSeries.coeff (Finsupp.single j 1) (taylor ev (fun i => ⇑(ds i)) f) = ev (ds j f) := by
  have hit : iterOp (fun i => ⇑(ds i)) (Finsupp.single j 1) f = ds j f := by
    unfold iterOp
    rw [list_foldr_iterate_single_of_nodup _ j f _ (List.nodup_finRange n)]
    simp [List.mem_finRange]
  have hprod : (∏ i, (((Finsupp.single j 1 : Fin n →₀ ℕ) i).factorial : ℚ)) = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    by_cases h : j = i
    · subst h; simp
    · simp [Finsupp.single_apply, h]
  show (∏ i, (((Finsupp.single j 1 : Fin n →₀ ℕ) i).factorial : ℚ))⁻¹ • ev (iterOp (fun i => ⇑(ds i)) (Finsupp.single j 1) f) = _
  rw [hit, hprod, inv_one, one_smul]

end GlobalTheory.FormalOrigin.Extend
