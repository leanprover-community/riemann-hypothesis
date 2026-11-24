module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.FinalD
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
import Mathlib.RingTheory.SimpleRing.Principal
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

open MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

theorem fk_map_initMinor {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n s : ℕ} (I : Fin s → Fin r)
    (hs : s ≤ n) : map φ (Formalism.GradedWeylDivisibility.initMinor R I hs) = Formalism.GradedWeylDivisibility.initMinor S I hs := by
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det]
  exact congrArg Matrix.det (by ext p q; simp)

theorem fk_map_bidet {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n k : ℕ} (sz : Fin k → ℕ)
    (hsz : ∀ i, sz i ≤ n) (I : ∀ i, Fin (sz i) → Fin r) :
    map φ (Formalism.GradedWeylDivisibility.bideterminant R sz hsz I) = Formalism.GradedWeylDivisibility.bideterminant S sz hsz I := by
  simp only [Formalism.GradedWeylDivisibility.bideterminant, map_prod]
  exact Finset.prod_congr rfl fun i _ => fk_map_initMinor φ _ _

theorem ssB_int (K : Type) [Field K] {n : ℕ} (ν : Fin n → ℕ) (m : Formalism.GradedWeylDivisibility.ssIdx n n ν) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℤ, ssB K ν m = map (Int.castRingHom K) P := by
  obtain ⟨k, sz, hsz, I, -, -, h⟩ := ((Formalism.GradedWeylDivisibility.sSBasis K n n ν).choose_spec.2 m).2.2
  exact ⟨Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I, by rw [fk_map_bidet]; exact h⟩

theorem fk_map_blockEmb {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {ι : Type} {k n : ℕ} (τ : ι)
    (f : MvPolynomial (Fin k × Fin n) R) :
    map φ (Formalism.GradedWeylDivisibility.blockEmb R τ f) = Formalism.GradedWeylDivisibility.blockEmb S τ (map φ f) := by
  simp only [Formalism.GradedWeylDivisibility.blockEmb]
  exact map_rename φ _ f

theorem bVVfun_int (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (i : VVIdx lam) :
    ∃ P : MvPolynomial (ι × Fin n × Fin n) ℤ, bVVfun K lam i = MvPolynomial.map (Int.castRingHom K) P := by
  choose Q hQ using fun τ => ssB_int K (lam τ).natW (i τ)
  refine ⟨∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℤ τ (Q τ), ?_⟩
  rw [map_prod]
  unfold bVVfun ten
  exact Finset.prod_congr rfl fun τ _ => by rw [fk_map_blockEmb]; exact congrArg _ (hQ τ)

end Formalism.L2.DIV
