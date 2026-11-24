module

public import Development.EtaleCohomology.EtaleSheaves.StandardChartsLineZero
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.StdChartsProof

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

def Restr (B : Subalgebra A K) (t : K) (Q : PrimeSpectrum (AdjoinInv B t)) (S : Subalgebra A K) (x : PrimeSpectrum S) :
    Prop := ∀ s : S, s ∈ x.asIdeal ↔ ∃ d ∈ Q.asIdeal, (d : K) = (s : K)

structure Cover {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K) : Prop where
  ex : ∃ (jU : Spec (CommRingCat.of B) ⟶ Z) (jV : Spec (CommRingCat.of C) ⟶ Z),
    IsOpenImmersion jU ∧ IsOpenImmersion jV ∧ Set.range jU.base ∪ Set.range jV.base = Set.univ ∧
    jU ≫ p = Spec.map (CommRingCat.ofHom (algebraMap A B)) ∧ jV ≫ p = Spec.map (CommRingCat.ofHom (algebraMap A C)) ∧
    ∀ (x : PrimeSpectrum B) (y : PrimeSpectrum C), jU.base x = jV.base y ↔
      ∃ Q : PrimeSpectrum (AdjoinInv B t), Restr B t Q B x ∧ Restr B t Q C y

def ChartsGeom : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → AICSch Z →
  ∃ (K : Type) (_ : Field K) (_ : Algebra A K) (B C : Subalgebra A K) (t : K), Charts B C t ∧
    (∀ x ∈ B, x ∈ C → IsIntegral A x) ∧ Cover p B C t

def FibreIdem : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K] [Algebra A K] {Z : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K), Charts B C t → Cover p B C t →
    ∀ W : Set ↑(pullback p (cpt A)), IsClopen W → ∃ e f : K, IdemPair B C t e f ∧
      ((e ∈ mS B ∧ f ∈ mS C) → W = ∅) ∧ ((e - 1 ∈ mS B ∧ f - 1 ∈ mS C) → W = Set.univ)

theorem StdCharts_of (hG : ChartsGeom) (hF : FibreIdem) : LateralTheory.E.StandardEtaleChartsIdempotentGluing.StdCharts := by
  intro A _ _ Z p hIL hZ
  obtain ⟨K, hK, hA, B, C, t, hc, hint, hcov⟩ := hG A p hIL hZ
  exact ⟨K, hK, hA, B, C, t, hc, hint, fun W hW => hF A K p B C t hc hcov W hW⟩

end LateralTheory.E.StdChartsProof
