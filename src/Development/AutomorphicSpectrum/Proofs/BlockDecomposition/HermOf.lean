module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix TensorProduct

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def hermE (σ : E →ₐ[F] E) (n : ℕ) : Submodule F (Matrix (Fin n) (Fin n) E) where
  carrier := {c | ∀ a b, σ (c b a) = c a b}
  add_mem' := by
    intro c d hc hd a b
    simp [map_add (f := _), hc a b, hd a b]
  zero_mem' := by
    intro a b
    simp
  smul_mem' := by
    intro t c hc a b
    simp [hc a b]

def hermIn (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (n : ℕ) :
    hermE σ n →+ HermR R σ n where
  toFun c := hermOf R σ c.1 c.2
  map_zero' := by
    apply Subtype.ext
    ext a b
    simp [hermOf]
  map_add' := by
    intro c d
    apply Subtype.ext
    ext a b
    simp [hermOf]

variable [NumberField E]

def hermO (σ : E →ₐ[F] E) (n : ℕ) : AddSubgroup (hermE σ n) where
  carrier := {c | ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = c.1 a b}
  add_mem' := by
    intro c d hc hd a b
    obtain ⟨o, ho⟩ := hc a b
    obtain ⟨p, hp⟩ := hd a b
    exact ⟨o + p, by simp [ho, hp]⟩
  zero_mem' := fun a b => ⟨0, by simp⟩
  neg_mem' := by
    intro c hc a b
    obtain ⟨o, ho⟩ := hc a b
    exact ⟨-o, by simp [ho]⟩

def Kc {n : ℕ} (c : Matrix (Fin n) (Fin n) E) : AddSubgroup (Fin n → 𝓞 E) where
  carrier := {y | ∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = (c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) i}
  add_mem' := by
    intro y z hy hz i
    obtain ⟨o, ho⟩ := hy i
    obtain ⟨p, hp⟩ := hz i
    refine ⟨o + p, ?_⟩
    have : (fun j => algebraMap (𝓞 E) E ((y + z) j)) =
        (fun j => algebraMap (𝓞 E) E (y j)) + fun j => algebraMap (𝓞 E) E (z j) := by
      funext j
      simp
    rw [this, Matrix.mulVec_add, Pi.add_apply, ← ho, ← hp, map_add (f := _)]
  zero_mem' := fun i => ⟨0, by
    have h0 : (fun _ : Fin n => (0 : E)) = 0 := rfl
    simp [h0, Matrix.mulVec_zero]⟩
  neg_mem' := by
    intro y hy i
    obtain ⟨o, ho⟩ := hy i
    refine ⟨-o, ?_⟩
    have : (fun j => algebraMap (𝓞 E) E ((-y) j)) = -fun j => algebraMap (𝓞 E) E (y j) := by
      funext j
      simp
    rw [this, Matrix.mulVec_neg, Pi.neg_apply, ← ho, map_neg]

def delta {n : ℕ} (c : Matrix (Fin n) (Fin n) E) : ℕ := (Kc c).index

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
