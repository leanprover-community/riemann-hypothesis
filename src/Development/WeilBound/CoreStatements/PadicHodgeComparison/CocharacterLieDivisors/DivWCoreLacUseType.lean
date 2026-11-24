module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.CocharacterLieDivisors.MeetsOpenCosets
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Topology.Instances.Matrix
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial

namespace PositivityTheory.AutomorphicGaloisHodgeTate.Div

def WGen {K : Type} [Field K] (n : ℕ) (P : K[X]) : Prop :=
  P.Separable ∧
  (∀ x ∈ P.roots, ∀ y ∈ P.roots, x ≠ y → ∀ c : ℕ, 0 < c → c ≤ n → (x / y) ^ c ≠ 1) ∧
  (∀ x ∈ P.roots, ∀ y ∈ P.roots, ∀ z ∈ P.roots, x ≠ y → z ≠ y → x ≠ z → x * z ≠ y ^ 2) ∧
  (∀ M : Multiset K, (∀ x ∈ M, x ∈ P.roots) → Multiset.card M = n → M ≠ P.roots →
    M.prod ≠ P.roots.prod)

def ProdGen {K : Type} [Field K] (n : ℕ) (P : K[X]) : Prop :=
  P.Separable ∧ ∀ M : Multiset K, (∀ x ∈ M, x ∈ P.roots) → Multiset.card M = n → M ≠ P.roots →
    M.prod ≠ P.roots.prod

def IsLac {K : Type} [Field K] {n : ℕ} (e : Fin n → K) : Prop :=
  ∀ A B : Finset (Fin n), A.Nonempty → B.Nonempty → Disjoint A B →
    (B.card : K) * (∑ i ∈ A, e i) ≠ (A.card : K) * (∑ i ∈ B, e i)

def DivWCoreLac : Prop :=
  ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (K K' : Type) [Field K] [IsAlgClosed K] [CharZero K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] [Field K'] [IsAlgClosed K'] [Algebra K K']
    (N n : ℕ) (ρ : Γ →* GL (Fin N) K),
      Continuous (fun g : Γ => (ρ g : Matrix (Fin N) (Fin N) K)) → IsSSMat ρ →
    ∀ (S : Set Γ), Dense S →
    ∀ (P : Γ → K[X]), (∀ s ∈ S, (P s).Monic ∧ (P s).natDegree = n) →
      (∀ s ∈ S, aeval (ρ s : Matrix (Fin N) (Fin N) K) (P s) = 0) →
    ∀ (X : Matrix (Fin N) (Fin N) K'), InLieZar ρ X →
      (∃ e : Fin n → K', Function.Injective e ∧ IsLac e ∧ ∀ i, X.charpoly.IsRoot (e i)) →
    ∀ (ψ : Γ →* Kˣ), Continuous (fun g : Γ => ((ψ g : Kˣ) : K)) →
      (∀ s ∈ S, ((ψ s : Kˣ) : K) = (-1) ^ n * (P s).coeff 0) →
    ∃ r : Γ →* GL (Fin n) K,
      Continuous (fun g : Γ => (r g : Matrix (Fin n) (Fin n) K)) ∧ IsSSMat r ∧
      (∃ A : Matrix (Fin N) (Fin n) K, A.rank = n ∧
        ∀ g : Γ, (ρ g : Matrix (Fin N) (Fin N) K) * A = A * (r g : Matrix (Fin n) (Fin n) K)) ∧
      (∃ (k : ℕ) (B : Matrix (Fin n × Fin k) (Fin N) K), B.rank = N ∧
        ∀ g : Γ, Matrix.kronecker (r g : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin k) (Fin k) K) * B =
          B * (ρ g : Matrix (Fin N) (Fin N) K)) ∧
      (∀ g : Γ, aeval (ρ g : Matrix (Fin N) (Fin N) K) (r g : Matrix (Fin n) (Fin n) K).charpoly = 0) ∧
      (∀ s ∈ S, aeval (r s : Matrix (Fin n) (Fin n) K) (P s) = 0) ∧
      (∀ g : Γ, ((r g : Matrix (Fin n) (Fin n) K).det) = ((ψ g : Kˣ) : K)) ∧
      IsOpen {g : Γ | (r g : Matrix (Fin n) (Fin n) K).charpoly.Separable} ∧
      Dense {g : Γ | (r g : Matrix (Fin n) (Fin n) K).charpoly.Separable} ∧
      (∀ s ∈ S, (r s : Matrix (Fin n) (Fin n) K).charpoly.Separable →
        (r s : Matrix (Fin n) (Fin n) K).charpoly = P s) ∧
      (∀ s ∈ S, ProdGen n (P s) → (r s : Matrix (Fin n) (Fin n) K).charpoly = P s)

end PositivityTheory.AutomorphicGaloisHodgeTate.Div
