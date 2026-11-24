module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LinMulti

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace

namespace GlobalTheory.SepReal

variable {n : ℕ}

abbrev Mat (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

def embH (e : Option (Fin n) ≃ Fin (n + 1)) (h : Mat n) : Mat (n + 1) :=
  fun a b => match e.symm a, e.symm b with
    | some i, some j => h i j
    | none, none => 1
    | _, _ => 0

def embL (e : Option (Fin n) ≃ Fin (n + 1)) (X : Mat n) : Mat (n + 1) :=
  fun a b => match e.symm a, e.symm b with
    | some i, some j => X i j
    | _, _ => 0

def Signs (e : Option (Fin n) ≃ Fin (n + 1)) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) : Prop :=
  ε (e none) = true ∧ ∀ i, ε (e (some i)) = ε' i

def hsn {m : ℕ} (g : Mat m) : ℝ := Real.sqrt (∑ a, ∑ b, ‖g a b‖ ^ 2)

def colLen (e : Option (Fin n) ≃ Fin (n + 1)) (g : Mat (n + 1)) : ℝ := Real.sqrt (∑ a, ‖g a (e none)‖ ^ 2)

def Interlaced (ε : Fin (n + 1) → Bool) (lam : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (mu : Fin n → ℝ) : Prop :=
  ∀ x y : Fin (n + 1) ⊕ Fin n, Sum.elim lam mu y < Sum.elim lam mu x →
    (∀ z, ¬ (Sum.elim lam mu y < Sum.elim lam mu z ∧ Sum.elim lam mu z < Sum.elim lam mu x)) →
      (Sum.elim ε ε' x = Sum.elim ε ε' y ↔ x.isLeft ≠ y.isLeft)

section Reps

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']

def IsHMap (e : Option (Fin n) ≃ Fin (n + 1)) (ε' : Fin n → Bool) (π : Mat (n + 1) → (H →L[ℂ] H)) (σ : Mat n → (H' →L[ℂ] H'))
    (j : H' →L[ℂ] H) : Prop := ∀ h ∈ UJset ε', ∀ w, j (σ h w) = π (embH e h) (j w)

def IsProj (e : Option (Fin n) ≃ Fin (n + 1)) (ε' : Fin n → Bool) (π : Mat (n + 1) → (H →L[ℂ] H)) (σ : Mat n → (H' →L[ℂ] H'))
    (j : H' →L[ℂ] H) (P : H →L[ℂ] H') : Prop :=
  IsHMap e ε' π σ j ∧ (∀ w, ‖j w‖ = ‖w‖) ∧ (∀ v w, ⟪j w, v⟫_ℂ = ⟪w, P v⟫_ℂ) ∧ ∀ j', IsHMap e ε' π σ j' → ∃ c : ℂ, j' = c • j

end Reps

structure Par (e : Option (Fin n) ≃ Fin (n + 1)) (ε : Fin (n + 1) → Bool) (lam : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (mu : Fin n → ℝ)
    (B : ℝ) : Prop where

  signs : Signs e ε ε'

  three_le : 3 ≤ n

  hlam : IsHCParam lam

  hmu : IsHCParam mu

  word : Interlaced ε lam ε' mu

  word' : ∀ s, Interlaced ε (lam - Pi.single s 1) ε' mu

  wide : ∀ a c, a < c → 2 ≤ lam a - lam c

  wide' : ∀ a c, a < c → 2 ≤ mu a - mu c

  gap : GapAtLeast ε lam (1000 * ((n : ℝ) + 1) ^ 3)

  gap' : GapAtLeast ε' mu (1000 * ((n : ℝ) + 1) ^ 3)

  neg : ∃ i, ε' i = false

  pos : (univ.filter fun i => ε' i = false).card ≤ (univ.filter fun i => ε' i = true).card

  bound : (∀ a, |lam a| ≤ B) ∧ ∀ i, |mu i| ≤ B

def ForPair (Q : ∀ (n : ℕ) (_ : Option (Fin n) ≃ Fin (n + 1)) (_ : Fin (n + 1) → Bool) (_ : Fin (n + 1) → ℝ) (_ : Fin n → Bool)
    (_ : Fin n → ℝ) (_ : ℝ) (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'],
    (Mat (n + 1) → (H →L[ℂ] H)) → (Mat n → (H' →L[ℂ] H')) → Prop) : Prop :=
  ∀ (n : ℕ) (e : Option (Fin n) ≃ Fin (n + 1)) (ε : Fin (n + 1) → Bool) (lam : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (mu : Fin n → ℝ)
    (B : ℝ), Par e ε lam ε' mu B → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
      [InnerProductSpace ℂ H'] (π : Mat (n + 1) → (H →L[ℂ] H)) (σ : Mat n → (H' →L[ℂ] H')), IsDS ε lam π → IsDS ε' mu σ →
      Q n e ε lam ε' mu B H H' π σ

def big (C : ℝ) (n : ℕ) (B : ℝ) : ℝ := Real.exp (C * ((n : ℝ) + 1) ^ 4 * Real.log (8 * ((n : ℝ) + 1) * B))

def nbh {m : ℕ} (ε : Fin m → Bool) (δ : ℝ) : Set (UJ ε) := {g | hsn (umat g - 1) ≤ δ}

theorem embH_one (e : Option (Fin n) ≃ Fin (n + 1)) : embH e 1 = 1 := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a <;> cases b <;> simp [embH, Matrix.one_apply]

theorem embH_mul (e : Option (Fin n) ≃ Fin (n + 1)) (h h' : Mat n) : embH e (h * h') = embH e h * embH e h' := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_option]
  cases a <;> cases b <;> simp [embH, Matrix.mul_apply]

end GlobalTheory.SepReal

end
