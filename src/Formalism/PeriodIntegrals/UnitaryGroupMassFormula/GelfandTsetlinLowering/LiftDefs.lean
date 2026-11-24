module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
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
import Formalism.LocalRingCardinality.Params

@[expose] public section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

def eRow {n N : ℕ} (h : n + 1 = N) (a : Fin n) : Fin N := ⟨a.1, by omega⟩

def lastW (N : ℕ) : Fin N × Fin N → ℕ := fun v => if v.1.1 + 1 = N then 1 else 0

def dLast {n N : ℕ} (lam : DomWeight N) (mu : DomWeight n) : ℕ := (degZ lam mu - lam.detShift).toNat

def liftWt {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) (ω : Fin n → ℕ) : Fin N → ℕ :=
  fun a => if ha : a.1 < n then ω ⟨a.1, ha⟩ + (mu.detShift - lam.detShift).toNat else dLast lam mu

def liftWord {n N : ℕ} (h : n + 1 = N) (w : List (Fin n × Fin n × ℕ)) : List (Fin N × Fin N × ℕ) :=
  w.map fun x => (eRow h x.1, eRow h x.2.1, x.2.2)

def OffDiag {r : ℕ} (w : List (Fin r × Fin r × ℕ)) : Prop := ∀ x ∈ w, x.1 ≠ x.2.1

def tupCnt {n K : ℕ} {sz : Fin K → ℕ} (I : ∀ k, Fin (sz k) → Fin n) (a : Fin n) : ℕ :=
  ∑ k, (Finset.univ.filter fun p : Fin (sz k) => I k p = a).card

def EqvDiv : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (mu : DomWeight n) (lam : DomWeight N)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
    ∀ (a b : Fin n), a ≠ b → ∀ (k : ℕ), ∀ s ∈ nablaSq ℂ n mu,
      φ (rowDiv ℂ a b k s) = rowDiv ℂ (eRow h a) (eRow h b) k (φ s)

def EqvRowWt : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n), Interlace h lam mu →
    ∀ (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
    ∀ (ω : Fin n → ℕ), ∀ s ∈ nablaSq ℂ n mu, IsWeightedHomogeneous (rowW n n) s ω →
      IsWeightedHomogeneous (rowW N N) (φ s) (liftWt h lam mu ω)

def EqvLast : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n), Interlace h lam mu →
    ∀ (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
    ∀ s ∈ nablaSq ℂ n mu, IsWeightedHomogeneous (lastW N) (φ s) (dLast lam mu)

def Decomp : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ (io0 : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ),
      IsEqv h sg lam io0 → io0 (extremal ℂ n sg) ≠ 0 →
      ∀ f ∈ nablaSq ℂ N lam, IsWeightedHomogeneous (lastW N) f (dLast lam sg) →
        ∃ u ∈ nablaSq ℂ n sg, f - io0 u ∈ OtherPart h lam sg

def ZComm : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N)
    (Z : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ),
    (∀ (mu : DomWeight n), Interlace h lam mu →
      ∀ (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
        ∃ z : ℂ, ∀ s ∈ nablaSq ℂ n mu, Z (φ s) = z • φ s) →
    (∀ f ∈ nablaSq ℂ N lam, Z f ∈ nablaSq ℂ N lam) ∧
    (∀ (a b : Fin n), a ≠ b → ∀ (k : ℕ), ∀ f ∈ nablaSq ℂ N lam,
      Z (rowDiv ℂ (eRow h a) (eRow h b) k f) = rowDiv ℂ (eRow h a) (eRow h b) k (Z f)) ∧
    (∀ (ω : Fin N → ℕ), ∀ f ∈ nablaSq ℂ N lam, IsWeightedHomogeneous (rowW N N) f ω →
      IsWeightedHomogeneous (rowW N N) (Z f) ω)

def FockDetect : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ (io0 : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ),
      IsEqv h sg lam io0 → io0 (extremal ℂ n sg) = xi ℂ h lam sg →
      ∀ u ∈ nablaSq ℂ n sg,
        (∀ w : List (Fin n × Fin n × ℕ), OffDiag w →
          Formalism.REAL.fockF (applyWord ℂ (liftWord h w) (io0 u)) (xi ℂ h lam sg) = 0) →
        io0 u = 0

def TupleCore : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n), shapeDeg sz = sg.natW →
    ∃ M : (∀ k, Fin (sz k) → Fin n) → MvPolynomial (Fin N × Fin N) ℤ,
      (∀ I, M I ∈ nablaSq ℤ N lam ∧
        IsWeightedHomogeneous (rowW N N) (M I) (liftWt h lam sg (tupCnt I)) ∧
        IsWeightedHomogeneous (rowW n n) (bideterminant ℤ sz hsz I) (tupCnt I)) ∧
      (∀ I, ∀ w : List (Fin n × Fin n × ℕ), OffDiag w →
        ∃ d : (∀ k, Fin (sz k) → Fin n) →₀ ℤ,
          applyWord ℤ w (bideterminant ℤ sz hsz I) = d.sum (fun J c => c • bideterminant ℤ sz hsz J) ∧
          applyWord ℤ (liftWord h w) (M I) = d.sum (fun J c => c • M J)) ∧
      (∀ J, tupCnt J = sg.natW →
        ∃ ε : ℤ, bideterminant ℤ sz hsz J = ε • extremal ℤ n sg ∧ M J = ε • xi ℤ h lam sg) ∧
      (∃ J0, tupCnt J0 = sg.natW ∧ bideterminant ℤ sz hsz J0 = extremal ℤ n sg ∧ M J0 = xi ℤ h lam sg)

end PI.WGL
