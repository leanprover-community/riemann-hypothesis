module

public import Formalism.GradedWeylDivisibility.StatementA
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open MvPolynomial

namespace Formalism.CohomologicalDescent.LD

open Formalism.GradedWeylDivisibility

def boxesOfContent {q : ℕ} (lam2 tau : Fin q → ℕ) (c : ℤ) : ℕ :=
  (Finset.univ.filter fun a : Fin q => (lam2 a : ℤ) ≤ c + (a.val : ℤ) ∧ c + (a.val : ℤ) < (tau a : ℤ)).card

def colLen {q : ℕ} (lam2 tau : Fin q → ℕ) (j : ℕ) : ℕ :=
  (Finset.univ.filter fun a : Fin q => lam2 a ≤ j ∧ j < tau a).card

def shapes (p w i : ℕ) {q : ℕ} (lam2 : Fin q → ℕ) : Finset (Fin q → ℕ) :=
  (Fintype.piFinset fun a : Fin q => Finset.Icc (lam2 a) (lam2 a + i)).filter fun tau =>
    (∀ a b : Fin q, a ≤ b → tau b ≤ tau a) ∧ ∑ a, tau a = ∑ a, lam2 a + i ∧
      (∀ b : Fin q, ∀ j < tau b, colLen lam2 tau j ≤ p) ∧ boxesOfContent lam2 tau (w : ℤ) = 0

def mu (p w i : ℕ) {q : ℕ} (lam2 : Fin q → ℕ) (c : ℤ) : ℕ :=
  (shapes p w i lam2).sup fun tau => boxesOfContent lam2 tau c

def Dn (p w i : ℕ) {q : ℕ} (lam2 : Fin q → ℕ) : ℤ :=
  ∏ k ∈ Finset.range (q + w + i), ((w : ℤ) - ((k : ℤ) - (q : ℤ))) ^ mu p w i lam2 ((k : ℤ) - (q : ℤ))

noncomputable def nablaWt (r : ℕ) (ν μ : Fin r → ℕ) : Submodule ℤ (MvPolynomial (Fin r × Fin r) ℤ) :=
  dualWeyl ℤ r r ν ⊓ weightedHomogeneousSubmodule ℤ (rowW r r) μ

def KilledAt (l r : ℕ) (ν μ : Fin r → ℕ) (c : ℤ) : Prop :=
  ∀ x ∈ nablaWt r ν μ, ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ (m * c) • x ∈ weyl ℤ r r le_rfl ν

def ExpLe (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ) : Prop := KilledAt l r ν μ ((l : ℤ) ^ e)

def blockWt (p q w : ℕ) (κ : Fin q → ℕ) : Fin (p + q) → ℕ := Fin.append (fun _ : Fin p => w) κ

def blockWtLast (p q w : ℕ) (κ : Fin q → ℕ) : Fin (q + p) → ℕ := Fin.append κ (fun _ : Fin p => w)

def IsDepth (p q w : ℕ) (μ : Fin (p + q) → ℕ) (i : ℕ) : Prop :=
  ∑ a : Fin p, μ (Fin.castAdd q a) + i = p * w

def IsDepthLast (p q w : ℕ) (μ : Fin (q + p) → ℕ) (i : ℕ) : Prop :=
  ∑ a : Fin p, μ (Fin.natAdd q a) = p * w + i

def depth2 {r : ℕ} (ξ : Fin r → ℤ) (lam μ : Fin r → ℕ) : ℤ := ∑ a, ξ a * ((lam a : ℤ) - (μ a : ℤ))

def LemmaDGradedAt (l p q w : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (p + q) → ℤ) : Prop :=
  ∀ (i' : ℤ) (eL : ℕ),
    (∀ μ2 : Fin q → ℕ, depth2 ξ (blockWt p q w lam2) (blockWt p q w μ2) ≤ i' → ExpLe l q lam2 μ2 eL) →
    ∀ (i : ℕ) (μ : Fin (p + q) → ℕ), IsDepth p q w μ i → depth2 ξ (blockWt p q w lam2) μ ≤ i' →
      ExpLe l (p + q) (blockWt p q w lam2) μ (eL + padicValInt l (Dn p w i lam2))

def LemmaDGraded : Prop :=
  ∀ (l p q w : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (p + q) → ℤ), l.Prime → Antitone lam2 → (∀ b, lam2 b ≤ w) →
    Antitone ξ → LemmaDGradedAt l p q w lam2 ξ

def LemmaDLast : Prop :=
  ∀ (l p q w M : ℕ) (lam2 : Fin q → ℕ), l.Prime → Antitone lam2 → (∀ b, w ≤ lam2 b ∧ lam2 b ≤ M) →
    ∀ eL : ℕ, (∀ μ2 : Fin q → ℕ, ExpLe l q lam2 μ2 eL) →
      ∀ (i : ℕ) (μ : Fin (q + p) → ℕ), IsDepthLast p q w μ i →
        ExpLe l (q + p) (blockWtLast p q w lam2) μ
          (eL + padicValInt l (Dn p (M - w) i fun b : Fin q => M - lam2 (Fin.rev b)))

def DnNeZero : Prop :=
  ∀ (p w i q : ℕ) (lam2 : Fin q → ℕ), Dn p w i lam2 ≠ 0

def MuSupport : Prop :=
  ∀ (p w i q : ℕ) (lam2 : Fin q → ℕ) (c : ℤ), (∀ b, lam2 b ≤ w) → mu p w i lam2 c ≠ 0 →
    -(q : ℤ) ≤ c ∧ c < (w : ℤ) + (i : ℤ)

def ExpLeMono : Prop :=
  ∀ (l r : ℕ) (ν μ : Fin r → ℕ) (e e' : ℕ), e ≤ e' → ExpLe l r ν μ e → ExpLe l r ν μ e'

def MuLe : Prop :=
  ∀ (p w i q : ℕ) (lam2 : Fin q → ℕ) (c : ℤ), mu p w i lam2 c ≤ p

def MuRange : Prop :=
  ∀ (p w i q m : ℕ) (lam2 : Fin q → ℕ) (c : ℤ), (∀ b, m ≤ lam2 b ∧ lam2 b ≤ w) → mu p w i lam2 c ≠ 0 →
    (m : ℤ) - (q : ℤ) < c ∧ c < (w : ℤ)

def DnDvd : Prop :=
  ∀ (p w i q m : ℕ) (lam2 : Fin q → ℕ), (∀ b, m ≤ lam2 b ∧ lam2 b ≤ w) →
    Dn p w i lam2 ∣ (((w + q - m - 1).factorial ^ p : ℕ) : ℤ)

def DnVal : Prop :=
  ∀ (l p w i q m : ℕ) (lam2 : Fin q → ℕ), l.Prime → (∀ b, m ≤ lam2 b ∧ lam2 b ≤ w) →
    (l - 1) * padicValInt l (Dn p w i lam2) ≤ p * (w + q - m - 1)

end Formalism.CohomologicalDescent.LD
