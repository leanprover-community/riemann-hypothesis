module

public import Mathlib.Algebra.DualNumber
public import ReciprocityTheory.DualLattices.SqZeroOfSpan
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.LocalRing.Basic

@[expose] public section

noncomputable section

open TensorProduct ReciprocityTheory.PGsh

namespace GlobalTheory.IndefiniteRowSideFullHecke.EtaDualPairing

universe u

variable {R₀ : Type u} [CommRing R₀]

theorem isLocalRing_dualNumber (A : Type u) [CommRing A] [IsLocalRing A] :
    IsLocalRing (DualNumber A) := by
  haveI : Nontrivial (DualNumber A) := inferInstanceAs (Nontrivial (A × A))
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst

def dual (R : LAlg R₀) : LAlg R₀ :=
  @LAlg.mk R₀ _ (DualNumber R) _ _ (isLocalRing_dualNumber R)

def eta (R : LAlg R₀) : dual R := (DualNumber.eps : DualNumber R)

def red (R : LAlg R₀) : LHom (dual R) R :=
  ⟨TrivSqZeroExt.fstHom R₀ R R,
    ⟨fun _ h => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 h⟩⟩

def incl (R : LAlg R₀) : LHom R (dual R) :=
  ⟨TrivSqZeroExt.inlAlgHom R₀ R R,
    ⟨fun _ h => TrivSqZeroExt.isUnit_inl_iff.1 h⟩⟩

theorem red_comp_incl (R : LAlg R₀) : (red R).comp (incl R) = LHom.id R :=
  Subtype.ext (AlgHom.ext fun _ => rfl)

theorem eta_mul_eta (R : LAlg R₀) : eta R * eta R = 0 := DualNumber.eps_mul_eps

theorem red_sqZero (R : LAlg R₀) : (red R).SqZero := by
  refine LHom.sqZero_of_span _ (eta R) (fun a => ⟨(incl R).1 a, rfl⟩) ?_ (eta_mul_eta R)
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton']
  constructor
  · intro hx
    have key : ∀ b : DualNumber R, TrivSqZeroExt.fst b = 0 →
        (TrivSqZeroExt.inl (TrivSqZeroExt.snd b) : DualNumber R) * DualNumber.eps = b :=
      fun b hb => by ext <;> simp [hb]
    exact ⟨_, key x hx⟩
  · rintro ⟨a, rfl⟩
    have key : ∀ b : DualNumber R, TrivSqZeroExt.fst (b * DualNumber.eps) = 0 := fun b => by simp
    exact key a

def onePlusEta (R : LAlg R₀) (a : R) : (dual R)ˣ where
  val := 1 + eta R * (incl R).1 a
  inv := 1 - eta R * (incl R).1 a
  val_inv := by linear_combination (-((incl R).1 a) ^ 2) * eta_mul_eta R
  inv_val := by linear_combination (-((incl R).1 a) ^ 2) * eta_mul_eta R

variable (B : BX R₀)

end GlobalTheory.IndefiniteRowSideFullHecke.EtaDualPairing
