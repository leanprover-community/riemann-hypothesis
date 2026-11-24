module

public import ReciprocityTheory.DualLattices.FormalChartAtZero
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def nsmulF {S : Type} [CommRing S] [Algebra R₀ S] (F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀)
    (a : Fin g → S) : ℕ → Fin g → S
  | 0 => 0
  | n + 1 => fAdd F (nsmulF F a n) a

def PSerFrobStatement (p : ℕ) [Fact p.Prime] (K : LAlg R₀) (ch : FormalChartAtZero B K g) : Prop :=
  ∀ N : ℕ, ∃ G : Fin g → MvPolynomial (Fin g) R₀,
    (∀ k m, (∃ i, ¬ p ∣ m i) → ∃ r : R₀, AddMonoidAlgebra.coeff (G k) m = p * r) ∧
    ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, a i ^ N = 0) →
      nsmulF ch.F a p = fun k => MvPolynomial.aeval a (G k)

end ReciprocityTheory.PGsh.Be2
