module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.MapUgCToUg
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.RootsC

variable {l : ℕ} [hl : Fact l.Prime]

theorem seq_add_pow (m d : ℕ) : rootSeq l (m + d) ^ l ^ d = rootSeq l m := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc, pow_succ', pow_mul, GroundTheory.PAdicHodge.rootSeq_succ_pow, ih]

theorem seq_primitive (n : ℕ) : IsPrimitiveRoot (rootSeq l n) (l ^ n) := by
  cases n with
  | zero =>
    rw [pow_zero, IsPrimitiveRoot.one_right_iff]
    simpa using (GroundTheory.PAdicHodge.rootSeq_pow (p := l) 0)
  | succ k =>
    have h1 : ¬ rootSeq l (k + 1) ^ l ^ k = 1 := by
      rw [Nat.add_comm, seq_add_pow]
      exact GroundTheory.PAdicHodge.rootSeq_one_ne_one
    have h2 := orderOf_eq_prime_pow h1 (GroundTheory.PAdicHodge.rootSeq_pow (p := l) (k + 1))
    rw [← h2]
    exact IsPrimitiveRoot.orderOf _

theorem exists_primitive_cl (n : ℕ) : ∃ η : PadicAlgCl l, IsPrimitiveRoot η (l ^ n) := by
  have hq : (l ^ n : ℕ) ≠ 0 := pow_ne_zero n hl.out.ne_zero
  haveI : NeZero ((l ^ n : ℕ) : PadicAlgCl l) := ⟨by exact_mod_cast hq⟩
  have hdeg : (Polynomial.cyclotomic (l ^ n) (PadicAlgCl l)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    have ht : 0 < Nat.totient (l ^ n) := Nat.totient_pos.2 (Nat.pos_of_ne_zero hq)
    exact_mod_cast ht.ne'
  obtain ⟨η, hη⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨η, Polynomial.isRoot_cyclotomic_iff.1 hη⟩

theorem exists_lift (n : ℕ) :
    ∃ ρ : PadicAlgCl l, IsPrimitiveRoot ρ (l ^ n) ∧ clToC l ρ = rootSeq l n := by
  obtain ⟨η, hη⟩ := exists_primitive_cl (l := l) n
  have hinj : Function.Injective (clToC l) := (clToC l).injective
  have hη' : IsPrimitiveRoot (clToC l η) (l ^ n) :=
    (IsPrimitiveRoot.map_iff_of_injective hinj).2 hη
  obtain ⟨i, -, hi⟩ := hη'.eq_pow_of_pow_eq_one (GroundTheory.PAdicHodge.rootSeq_pow (p := l) n)
  refine ⟨η ^ i, ?_, by rw [map_pow, hi]⟩
  rw [← IsPrimitiveRoot.map_iff_of_injective hinj, map_pow, hi]
  exact seq_primitive n

theorem prim_of_primitive {q : ℕ} (hq : q ≠ 0) {F : Type} [Field F] [CharZero F] {ρ : F}
    (h : IsPrimitiveRoot ρ q) :
    IsUnit ((q : ℕ) : F) ∧ Polynomial.aeval ρ (Polynomial.cyclotomic q ℤ) = 0 := by
  refine ⟨isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hq), ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact h.isRoot_cyclotomic (Nat.pos_of_ne_zero hq)

theorem rootsEx : CrystallineSemistableComparison.E.RootsEx := by
  intro l _
  choose ρ hρ using fun n => exists_lift (l := l) n
  exact ⟨⟨fun n => Subtype.mk (ρ n)
      (prim_of_primitive (pow_ne_zero n (Fact.out : l.Prime).ne_zero) (hρ n).1),
    fun n => (hρ n).2⟩⟩

end GlobalTheory.CompanionTheory.RootsC
