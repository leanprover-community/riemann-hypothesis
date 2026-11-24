module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MapNatActR
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open MvPolynomial Matrix Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags

open Formalism.L2.G.Cmp

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ} {LL : Type} [Field LL]

def IntSpanG (embLL : LL →+* ℂ) (R0 : Subring LL) (lam : Tau → DomWeight n) :
    AddSubgroup (MvPolynomial (Tau × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {q | ∃ (r : LL) (f : Tau → MvPolynomial (Fin n × Fin n) ℤ), r ∈ R0 ∧ (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    q = embLL r • ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

def nAt (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (N : Tau → GL (Fin n) LL)
    (v : Fin P.nV) (s : Fin (P.n' v)) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL :=
  if Even s.val then (N (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) LL).submatrix (finCongr h) (finCongr h)
  else (((N (pos ⟨v, s⟩))⁻¹ : GL (Fin n) LL) : Matrix (Fin n) (Fin n) LL)ᵀ.submatrix (finCongr h) (finCongr h)

def CoreAt (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G : Tau → Matrix (Fin n) (Fin n) ℂ)
    (embLL : LL →+* ℂ) (e : LL →+* Kf) (R0 : Subring LL) (lam : Tau → DomWeight n) (M N : Tau → GL (Fin n) LL)
    (L : P.Tup) (Q : XR P LL) : Prop :=
  MvPolynomial.map e Q ∈ P.HtupW L ↔ ∃ Pp ∈ IntSpanG embLL R0 lam, ∀ z : Frames G,
    evC P h pos G (fun τ => (M τ : Matrix (Fin n) (Fin n) LL).map embLL) (MvPolynomial.map embLL Q) z =
      fnOf G (shiftOf lam) (fun τ => (((N τ)⁻¹ * M τ : GL (Fin n) LL) : Matrix (Fin n) (Fin n) LL).map embLL) Pp z

end Gen

def WeylLatticeDescent : Prop :=
  ∀ {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ} {LL : Type} [Field LL] (h : P.m + 1 = n)
    (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G : Tau → Matrix (Fin n) (Fin n) ℂ)
    (embLL : LL →+* ℂ) (e : LL →+* Kf) (R0 : Subring LL), IsFractionRing O Kf →
    (∀ x, x ∈ R0 ↔ e x ∈ Set.range (algebraMap O Kf)) → ∀ lam : Tau → DomWeight n, WtTie P h pos lam →
    ∀ (M N : Tau → GL (Fin n) LL) (L : P.Tup),
    (∀ v (s : Fin (P.n' v)), extO O (P.ι v) (P.σ v) s.val (L v) = colSpan O ((nAt P h pos N v s).map e)) →
    ∀ Q : XR P LL, CoreAt P h pos G embLL e R0 lam M N L Q

def DescVal : Prop :=
  ∀ {LL Kf O ι : Type} [Field LL] [Field Kf] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Kf]
    [IsFractionRing O Kf] (e : LL →+* Kf) (R0 : Subring LL), (∀ x, x ∈ R0 ↔ e x ∈ Set.range (algebraMap O Kf)) →
    ∀ (S : Set (MvPolynomial ι LL)) (Q : MvPolynomial ι LL),
    MvPolynomial.map e Q ∈ Submodule.span O ((fun q => MvPolynomial.map e q) '' S) → Q ∈ Submodule.span R0 S

end Formalism.L2.G.RelativeIndexFlags
