module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftDefs
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

namespace PI.WGL.LTM

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

def liftRows {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) : Fin (m + 1) → Fin N :=
  fun p => if hp : p.1 < m then eRow h (ρ ⟨p.1, hp⟩) else ⟨N - 1, by omega⟩

def unl {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m ≤ N) :
    MvPolynomial (Fin N × Fin N) ℤ :=
  initMinor ℤ (eRow h ∘ ρ) hm

def lif {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m + 1 ≤ N) :
    MvPolynomial (Fin N × Fin N) ℤ :=
  initMinor ℤ (liftRows h ρ) hm

def C0 {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : MvPolynomial (Fin N × Fin N) ℤ :=
  ∏ i : Fin n, (if i.1 + 1 = n then (lpMinor ℤ (r := N) (n := N) (i.1 + 1) (by omega) (by omega)) ^ (aa h lam sg i).toNat
      else 1) *
    (if i.1 = 0 then (initMinor ℤ (n := N) (rowsZ h i) (by omega)) ^ (bb h lam sg i).toNat else 1)

def Mlift {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K)) (I : ∀ k, Fin (sz k) → Fin n) : MvPolynomial (Fin N × Fin N) ℤ :=
  C0 h lam sg * ∏ k : Fin K,
    if k ∈ L then lif h (I k) (by have := hsz k; omega) else unl h (I k) (by have := hsz k; omega)

def GoodL {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (L : Finset (Fin K)) : Prop :=
  (∀ k ∈ L, 0 < sz k) ∧
  ∀ i : Fin n, (Finset.univ.filter fun k => k ∈ L ∧ sz k = i.1).card = if i.1 = 0 then 0 else (bb h lam sg i).toNat

def stdT {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) : ∀ k, Fin (sz k) → Fin n :=
  fun k p => ⟨p.1, lt_of_lt_of_le p.2 (hsz k)⟩

def TopPart : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n), shapeDeg sz = sg.natW →
    ∀ L : Finset (Fin K), GoodL h lam sg sz L →
      (∀ J, tupCnt J = sg.natW →
        ∃ ε : ℤ, bideterminant ℤ sz hsz J = ε • extremal ℤ n sg ∧ Mlift h lam sg sz hsz L J = ε • xi ℤ h lam sg) ∧
      tupCnt (stdT sz hsz) = sg.natW ∧ bideterminant ℤ sz hsz (stdT sz hsz) = extremal ℤ n sg ∧
        Mlift h lam sg sz hsz L (stdT sz hsz) = xi ℤ h lam sg

end PI.WGL.LTM
