module

public import Development.EtaleCohomology.EtaleTrace.LCoverCut
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
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

def GenEtale : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X P : Scheme.{0}} [IsIntegral X] [IsIntegral P] (p : X ⟶ S k)
  (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p → LocallyOfFiniteType r → IsFinite π → Surjective π →
  (π.stalkMap (genericPoint X)).hom.FormallyUnramified → ∃ V : P.Opens, (V : Set P).Nonempty ∧ Etale (π ∣_ V)

def RatPtIn : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {P : Scheme.{0}} (r : P ⟶ S k), LocallyOfFiniteType r →
  ∀ V : P.Opens, (V : Set P).Nonempty → ∃ t : Pt r, ∀ x, t.1.base x ∈ V

def FibreOfEtale : Prop := ∀ (k : Type) [Field k] {X P : Scheme.{0}} (p : X ⟶ S k) (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p →
  ∀ V : P.Opens, Etale (π ∣_ V) → ∀ t : Pt r, (∀ x, t.1.base x ∈ V) → Etale (equalizer.ι π (p ≫ t.1) ≫ p)

theorem Fibre_of (h1 : GenEtale) (h2 : RatPtIn) (h3 : FibreOfEtale) : Fibre := by
  intro k _ _ X P _ _ p r π hπ hr hfin hsurj hun
  obtain ⟨V, hV, hE⟩ := h1 k p r π hπ hr hfin hsurj hun
  obtain ⟨t, ht⟩ := h2 k r hr V hV
  exact ⟨t, h3 k p r π hπ V hE t ht⟩

end LateralTheory.EtaleTrace.Cov
