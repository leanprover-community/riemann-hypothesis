module

public import Development.EtaleCohomology.EtaleSheaves.LineHigh
public import Development.EtaleCohomology.EtaleSheaves.LineZeroCut
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
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.StandardEtaleChartsIdempotentGluing

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

def mS (S : Subalgebra A K) : Submodule A K := IsLocalRing.maximalIdeal A • Subalgebra.toSubmodule S

def AdjoinInv (B : Subalgebra A K) (t : K) : Subalgebra A K := Algebra.adjoin A ((B : Set K) ∪ {t⁻¹})

structure Charts (B C : Subalgebra A K) (t : K) : Prop where
  ne : t ≠ 0
  tB : t ∈ B
  tC : t⁻¹ ∈ C
  intB : ∀ b ∈ B, IsIntegral (Algebra.adjoin A {t}) b
  intC : ∀ c ∈ C, IsIntegral (Algebra.adjoin A {t⁻¹}) c
  glue : AdjoinInv B t = Algebra.adjoin A ((C : Set K) ∪ {t})

def IdemPair (B C : Subalgebra A K) (t e f : K) : Prop :=
  e ∈ B ∧ f ∈ C ∧ e * e - e ∈ mS B ∧ f * f - f ∈ mS C ∧ e - f ∈ mS (AdjoinInv B t)

def StdCharts : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → AICSch Z →
  ∃ (K : Type) (_ : Field K) (_ : Algebra A K) (B C : Subalgebra A K) (t : K), Charts B C t ∧
    (∀ x ∈ B, x ∈ C → IsIntegral A x) ∧
    ∀ W : Set ↑(pullback p (cpt A)), IsClopen W → ∃ e f : K, IdemPair B C t e f ∧
      ((e ∈ mS B ∧ f ∈ mS C) → W = ∅) ∧ ((e - 1 ∈ mS B ∧ f - 1 ∈ mS C) → W = Set.univ)

def IdemLift : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] (K : Type) [Field K] [Algebra A K]
  (B C : Subalgebra A K) (t : K), Charts B C t → ∀ e f : K, IdemPair B C t e f →
  ∃ g ∈ B, g ∈ C ∧ g - e ∈ mS B ∧ g - f ∈ mS C

def AlgGlue : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] (K : Type) [Field K] [Algebra A K]
  (B C : Subalgebra A K) (t : K), Charts B C t → (∀ x ∈ B, x ∈ C → IsIntegral A x) → ∀ e f : K, IdemPair B C t e f →
  (e ∈ mS B ∧ f ∈ mS C) ∨ (e - 1 ∈ mS B ∧ f - 1 ∈ mS C)

theorem goal_of (hS : StdCharts) (hG : AlgGlue) : LateralTheory.E.t_E2Cut.LineZero := by
  intro A _ _ hSH Z p hIL hZ
  obtain ⟨hH, -⟩ := hSH
  have hne : Nonempty ↑(pullback p (cpt A)) := by
    obtain ⟨L, u, l, hu, hl, rfl⟩ := hIL
    have := hl.1
    have := hZ.1
    exact LateralTheory.E.LineZeroCut.lzNonempty A (u ≫ l) inferInstance inferInstance
  obtain ⟨K, _, _, B, C, t, hc, hint, hW⟩ := hS A p hIL hZ
  have hpre : PreconnectedSpace ↑(pullback p (cpt A)) := by
    rw [preconnectedSpace_iff_clopen]
    intro W hW'
    obtain ⟨e, f, hef, h0, h1⟩ := hW W hW'
    rcases hG A K B C t hc hint e f hef with h | h
    · exact Or.inl (h0 h)
    · exact Or.inr (h1 h)
  exact { toPreconnectedSpace := hpre, toNonempty := hne }

end LateralTheory.E.StandardEtaleChartsIdempotentGluing
