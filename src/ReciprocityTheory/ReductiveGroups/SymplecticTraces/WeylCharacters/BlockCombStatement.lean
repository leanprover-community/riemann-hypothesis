module

public import Mathlib.Tactic.Continuity
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.AltBranchStatement
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

def numK {K : Type*} [Field K] {n : ℕ} (ε : Fin n → Bool) (a : Fin n → ℤ) (t : Fin n → K) : K :=
  ∑ σ ∈ (univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => ∀ i, ε (σ i) = ε i),
    ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, t (σ i) ^ a i

def wdenK {K : Type*} [Field K] {n : ℕ} (ε : Fin n → Bool) (t : Fin n → K) : K :=
  ∏ i : Fin n, ∏ j : Fin n, if i < j ∧ ε i = ε j then t i - t j else 1

def rhoK {n : ℕ} (ε : Fin n → Bool) : Fin n → ℤ :=
  fun i => ((univ.filter fun j : Fin n => i < j ∧ ε j = ε i).card : ℤ)

def cnt {n : ℕ} (ε : Fin n → Bool) (b : Bool) : ℕ := (univ.filter fun i : Fin n => ε i = b).card

def blk {n : ℕ} (ε : Fin n → Bool) (b : Bool) : Fin (cnt ε b) → Fin n :=
  fun r => (univ.filter fun i : Fin n => ε i = b).orderEmbOfFin rfl r

def BlockCombStatement : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (ε : Fin n → Bool) (a : Fin n → ℤ) (t : Fin n → K),
    wdenK ε t = wden (cnt ε true) (t ∘ blk ε true) * wden (cnt ε false) (t ∘ blk ε false) ∧
    numK ε a t = alt (cnt ε true) (a ∘ blk ε true) (t ∘ blk ε true) *
      alt (cnt ε false) (a ∘ blk ε false) (t ∘ blk ε false) ∧
    ∀ b : Bool, rhoK ε ∘ blk ε b = delta (cnt ε b)

theorem blk_mem {n : ℕ} (ε : Fin n → Bool) (b : Bool) (r : Fin (cnt ε b)) : ε (blk ε b r) = b := by
  have h := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = b) rfl r
  exact (Finset.mem_filter.mp h).2

theorem blk_strictMono {n : ℕ} (ε : Fin n → Bool) (b : Bool) : StrictMono (blk ε b) :=
  fun _ _ h => (Finset.orderEmbOfFin (univ.filter fun i : Fin n => ε i = b) rfl).strictMono h

end ReciprocityTheory.ChartRestriction.TR.Weyl
