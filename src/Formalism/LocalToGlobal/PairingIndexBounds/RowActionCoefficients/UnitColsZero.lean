module

public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.ColHLe
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FockR

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.L2.G.Pend

def UnitCols : Prop :=
  ∀ (n l : ℕ), l ≤ n → ∀ I : Fin (n - l) → Fin n, Function.Injective I →
    ∃ (J : Fin l → Fin n) (ε : ℤ), Function.Injective J ∧ (∀ i q, J i ≠ I q) ∧ (ε = 1 ∨ ε = -1) ∧
      ∀ (A : Type) [CommRing A] (z : Fin n → ℕ → A),
        (catM l (unitM A I) z).det = (ε : A) * (Matrix.of fun i i' : Fin l => z (J i') i.val).det

def MinorZero : Prop :=
  ∀ (A : Type) [CommRing A] (r n s : ℕ) (hs : s ≤ n) (I : Fin s → Fin r), ¬ Function.Injective I → initMinor A I hs = 0

def HvFull : Prop :=
  ∀ (A : Type) [CommRing A] (n : ℕ) (μ : Fin n → ℕ), Antitone μ → ∀ c e : ℕ, (∀ t, μ t ≤ c) → (∀ t, e ≤ μ t) →
    (∀ t : Fin n, t.val + 1 = n → μ t = e) → 0 < n →
    ∀ (x : Fin n → ℕ → A) (y : Matrix (Fin n) (Fin n) A),
      hvE x y c (fun k => colH μ k.val) (fun k => colH_le μ k.val) =
        ((Matrix.of fun a i : Fin n => x a i.val).det * y.det) ^ e *
          hvE x y c (fun k => colH (fun t => μ t - e) k.val) (fun k => colH_le _ k.val)

def HvMemE : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ c : ℕ, (∀ t, ν t ≤ c) → ∀ x : Fin n → ℕ → K,
    hvE (fun a i => C (x a i)) (yV K n) c (fun k => colH ν k.val) (fun k => colH_le ν k.val) ∈ dualWeyl K n n ν

def HvMemO : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (μ : Fin n → ℕ), Antitone μ → ∀ c : ℕ, (∀ t, μ t ≤ c) → ∀ x : Fin n → ℕ → K,
    hvO (fun a i => C (x a i)) (yV K n) c (fun k => colH μ k.val) ∈ dualWeyl K n n fun t => c - μ t.rev

end Formalism.L2.PairingIndexBounds.Ent
