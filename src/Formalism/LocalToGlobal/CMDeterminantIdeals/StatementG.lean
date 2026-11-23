module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.SemistableReduction.LatSemiSt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.LamCM

open IsLocalRing
open scoped ComplexOrder

abbrev FrVar {B : Type} (m : B → ℕ) : Type := Σ b : B, Fin (m b) × Fin (m b)

variable {B : Type} {m : B → ℕ}

def evalFr {R : Type} [CommRing R] (P : MvPolynomial (FrVar m) R) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) : R :=
  MvPolynomial.eval (fun v : FrVar m => X v.1 v.2.2 v.2.1) P

def substFr {R : Type} [CommRing R] (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) (P : MvPolynomial (FrVar m) R) :
    MvPolynomial (FrVar m) R :=
  MvPolynomial.bind₁ (fun v : FrVar m => ∑ j, MvPolynomial.C (U v.1 j v.2.2) * MvPolynomial.X (⟨v.1, (v.2.1, j)⟩ : FrVar m)) P

def LemmaGCore : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (B : Type) [Fintype B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K),
    (Infinite (ResidueField R) ∨ P.totalDegree + ∑ b, m b < Nat.card (ResidueField R)) →
    (∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R, (∀ b, IsUnit (X b).det) →
      evalFr P (fun b => (X b).map (algebraMap R K)) ∈ Set.range (algebraMap R K)) →
    ∀ μ, AddMonoidAlgebra.coeff P μ ∈ Set.range (algebraMap R K)

def BigResExt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V →
    Finite (ResidueField V) → ∀ N : ℕ,
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra V W),
      IsAdicComplete (maximalIdeal W) W ∧ Finite (ResidueField W) ∧ N < Nat.card (ResidueField W) ∧
      Function.Injective (algebraMap V W) ∧ IsLocalHom (algebraMap V W)

def LemmaG : Prop :=
  ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (B : Type) [Fintype B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K),
    IsAdicComplete (maximalIdeal V) V → Finite (ResidueField V) →
    (∀ (W KW : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field KW] [Algebra W KW] [IsFractionRing W KW]
      [Algebra V W] (f : K →+* KW), IsAdicComplete (maximalIdeal W) W → Finite (ResidueField W) →
      IsLocalHom (algebraMap V W) → (∀ a : V, f (algebraMap V K a) = algebraMap W KW (algebraMap V W a)) →
      ∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) W, (∀ b, IsUnit (X b).det) →
        evalFr (MvPolynomial.map f P) (fun b => (X b).map (algebraMap W KW)) ∈ Set.range (algebraMap W KW)) →
    ∀ μ, AddMonoidAlgebra.coeff P μ ∈ Set.range (algebraMap V K)

def SubstGauss : Prop :=
  ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (B : Type) [Fintype B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K)
    (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (c : ∀ b, Fin (m b) → K),
    (∀ μ, AddMonoidAlgebra.coeff P μ ∈ Set.range (algebraMap R K)) →
    (∀ b j k, c b j * U b j k ∈ Set.range (algebraMap R K)) →
    ∀ μ : FrVar m →₀ ℕ, AddMonoidAlgebra.coeff (substFr U P) μ * ∏ v : FrVar m, c v.1 v.2.2 ^ μ v ∈ Set.range (algebraMap R K)

def IsEquiv [DecidableEq B] (a : ∀ b, Fin (m b) → ℕ) (P : MvPolynomial (FrVar m) ℂ) : Prop :=
  ∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) ℂ),
    (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id →
    evalFr P (Function.update X b (X b * t)) = ReciprocityTheory.MultiplicativeHeights.triChar (a b) t * evalFr P X

def ArchTie : Prop :=
  ∀ (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (a : ∀ b, Fin (m b) → ℕ) (P : MvPolynomial (FrVar m) ℂ)
    (Hm U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ) (nn : ∀ b, Fin (m b) → ℝ) (C La : ℝ) (r : ℕ),
    (∀ b, (Hm b).PosDef) → IsEquiv a P →
    (∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ, (∀ b, (X b).conjTranspose * Hm b * X b = 1) → ‖evalFr P X‖ ≤ C) →
    (∀ b j, 0 < nn b j) → 0 ≤ La → (∀ b, m b ≤ r) →
    (∀ b j, ReciprocityTheory.MultiplicativeHeights.hq (Hm b) (U b j) ≤ (La * nn b j) ^ 2) →
    ∀ z : FrVar m → ℂ, (∀ v : FrVar m, ‖z v‖ * nn v.1 v.2.2 ≤ 1) →
      ‖MvPolynomial.eval z (substFr U P)‖ ≤ C * ((r : ℝ) * La) ^ (∑ b, ∑ i, a b i)

def SubstHomog : Prop :=
  ∀ (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (a : ∀ b, Fin (m b) → ℕ) (P : MvPolynomial (FrVar m) ℂ)
    (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ), IsEquiv a P →
    ∀ μ : FrVar m →₀ ℕ, AddMonoidAlgebra.coeff (substFr U P) μ ≠ 0 → ∑ v : FrVar m, μ v = ∑ b, ∑ i, a b i

end Formalism.L2.LamCM
