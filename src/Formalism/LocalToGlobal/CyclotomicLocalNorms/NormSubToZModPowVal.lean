module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

noncomputable section

namespace Formalism.L2.LocGap.Gal

open Formalism.BasicNotions Formalism.BasicNotions.Loc

variable (l : ℕ) [Fact l.Prime]

instance enoughRoots (i : ℕ) : HasEnoughRootsOfUnity (Om l) (l ^ i) := by
  have : NeZero (l ^ i) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  infer_instance

def χZ : GQ l →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (Om l) l).comp (MulSemiringAction.toRingAut (GQ l) (Om l))

def χQ : GQ l →* ℚ_[l]ˣ := (Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp (χZ l)

variable {l}

theorem χQ_coe (g : GQ l) : ((χQ l g : ℚ_[l]ˣ) : ℚ_[l]) = (((χZ l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := rfl

theorem χZ_spec (g : GQ l) (m : ℕ) (ζ : Om l) (h : ζ ^ (l ^ m) = 1) :
    g ζ = ζ ^ (((χZ l g : ℤ_[l]ˣ) : ℤ_[l]).toZModPow m).val :=
  cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ l) (Om l) g) ζ h

variable (l)

theorem exists_root_ne_one : ∃ z : Om l, z ^ l = 1 ∧ z ≠ 1 := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ 1)
  rw [pow_one] at hζ
  exact ⟨ζ, hζ.pow_eq_one, hζ.ne_one (Fact.out : l.Prime).one_lt⟩

theorem exists_root (x : Om l) : ∃ z : Om l, z ^ l = x :=
  IsAlgClosed.exists_pow_nat_eq x (Fact.out : l.Prime).pos

def ζQ : ℕ → Om l
  | 0 => 1
  | 1 => (exists_root_ne_one l).choose
  | (m + 2) => (exists_root l (ζQ (m + 1))).choose

theorem ζQ_zero : ζQ l 0 = 1 := rfl

theorem ζQ_one : ζQ l 1 ≠ 1 := (exists_root_ne_one l).choose_spec.2

theorem ζQ_succ (m : ℕ) : ζQ l (m + 1) ^ l = ζQ l m := by
  cases m with
  | zero => exact (exists_root_ne_one l).choose_spec.1
  | succ m => exact (exists_root l (ζQ l (m + 1))).choose_spec

theorem ζQ_pow (m k : ℕ) : ζQ l (m + k) ^ (l ^ k) = ζQ l m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, pow_succ, pow_mul', ζQ_succ, ih]

theorem ζQ_pow_eq_one (m : ℕ) : ζQ l m ^ (l ^ m) = 1 := by
  have h := ζQ_pow l 0 m
  rw [zero_add, ζQ_zero] at h
  exact h

theorem ζQ_primitive (m : ℕ) : IsPrimitiveRoot (ζQ l m) (l ^ m) := by
  cases m with
  | zero =>
    rw [ζQ_zero, pow_zero]
    exact IsPrimitiveRoot.one
  | succ n =>
    rw [IsPrimitiveRoot.iff_orderOf]
    refine orderOf_eq_prime_pow ?_ (ζQ_pow_eq_one l (n + 1))
    have h := ζQ_pow l 1 n
    rw [add_comm 1 n] at h
    rw [h]
    exact ζQ_one l

end Formalism.L2.LocGap.Gal
