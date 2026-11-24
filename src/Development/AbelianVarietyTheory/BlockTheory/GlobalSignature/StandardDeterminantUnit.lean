module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
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

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit

open Formalism.L2.Col

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def StdAtAll (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : Prop :=
  ∀ P ∈ ST, d.1.at P = stdAt E n P

def DetUnitAt (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (Q : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ g : Sp E n ≃ₗ[E] Sp E n, (∀ x : Sp E n, g x ∈ d.1.at Q ↔ x ∈ stdAt E n Q) →
    Q.valuation E (LinearMap.det (g : Sp E n →ₗ[E] Sp E n)) = 1

def SplitNonConj (ST : Finset (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ P ∈ ST, ∀ Q ∈ ST, Q ≠ conjPrime₂ P


variable (E n ST SG) in
def HasStdReps : Prop :=
  ∀ d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG), ∃ ga : UF E n, StdAtAll (((ga, 1) : UF E n × GLG (E := E) (n := n) (SG := SG)) • d)


end Generic

def Representatives : Prop :=
  ∀ (X : Fields), X.Ok → ∀ (Pr : Primes X), Pr.Ok → ∀ (u : Pr.Word) (n : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E)))
    (d : DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := SG)), ∃ ga : UF X.E n, ∀ P ∈ Pr.vT u,
      ((((ga, 1) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • d).1.at P = stdAt X.E n P)

def RepresentativesSplit : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E))),
    SplitNonConj ST → HasStdReps E n ST SG

theorem splitNonConj_vT {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) : SplitNonConj (Pr.vT u) := by
  intro P hP Q hQ h
  apply conj_piT_notMem hPr u ⟨Q, hQ⟩
  change cO X.E (Pr.piT u) ∈ Q.asIdeal
  rw [h, mem_conjP, cO_cO]
  exact decoFin_mem_of_mem_divs hP

theorem representatives_of_split (h : RepresentativesSplit) : Representatives :=
  fun X _ _ hPr u n SG d => h X.E n _ SG (splitNonConj_vT hPr u) d

end GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit
