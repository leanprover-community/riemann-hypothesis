module

public import Development.EtaleCohomology.EtaleSheaves.LChartPf
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
import Mathlib.RingTheory.Unramified.LocalStructure
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

namespace LateralTheory.E.LSurjChartPf

theorem zmt_etale_at (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
    (q : Ideal A') [q.IsPrime] :
    ∃ S' : Subalgebra A A', S'.toSubmodule.FG ∧ ∃ r : S',
      r.1 ∉ q ∧ Function.Bijective (Localization.awayMap S'.val.toRingHom r) :=
  (Algebra.ZariskisMainProperty.of_finiteType q).exists_fg_and_exists_notMem_and_awayMap_bijective _

def GraphPatch : Prop :=
  ∀ (A : Type) [CommRing A] (I : Ideal A) (A' : Type) [CommRing A'] [Algebra A A']
    (φ : A' →ₐ[A] A ⧸ I),
    (∀ q : Ideal A', q.IsPrime → RingHom.ker φ ≤ q → ∃ S' : Subalgebra A A', S'.toSubmodule.FG ∧
      ∃ r : S', r.1 ∉ q ∧ Function.Bijective (Localization.awayMap S'.val.toRingHom r)) →
    ∃ (S : Subalgebra A A') (_ : S.toSubmodule.FG) (r : S),
      IsUnit (φ r.1) ∧ Function.Bijective (Localization.awayMap S.val.toRingHom r)

def FiniteGraphChart : Prop :=
  ∀ (A : Type) [CommRing A] (I : Ideal A) (A' : Type) [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
    (φ : A' →ₐ[A] A ⧸ I), ∃ (S : Subalgebra A A') (_ : S.toSubmodule.FG) (r : S),
      IsUnit (φ r.1) ∧ Function.Bijective (Localization.awayMap S.val.toRingHom r)

def FiniteChartSurj : Prop :=
  ∀ (A : Type) [CommRing A] (I : Ideal A), I ≤ Ideal.jacobson ⊥ → LateralTheory.E.LChartPf.IdemLiftInt A I →
  ∀ (A' : Type) [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (φ : A' →ₐ[A] A ⧸ I)
    (S : Subalgebra A A') (_ : S.toSubmodule.FG) (r : S),
    IsUnit (φ r.1) → Function.Bijective (Localization.awayMap S.val.toRingHom r) →
    ∃ g : A', IsUnit (φ g) ∧ Function.Surjective (algebraMap A (Localization.Away g))

theorem FiniteGraphChart_of (hP : GraphPatch) : FiniteGraphChart := by
  intro A _ I A' _ _ _ φ
  exact hP A I A' φ (fun q hq _ => zmt_etale_at A A' q)

theorem LSurjChart_of' (hA : FiniteGraphChart) (hB : FiniteChartSurj) :
    LateralTheory.E.LChartPf.LSurjChart := by
  intro A _ I hI hid A' _ _ _ φ
  obtain ⟨S, hS, r, hr, hb⟩ := hA A I A' φ
  exact hB A I hI hid A' φ S hS r hr hb

theorem LSurjChart_of (hP : GraphPatch) (hB : FiniteChartSurj) : LateralTheory.E.LChartPf.LSurjChart :=
  LSurjChart_of' (FiniteGraphChart_of hP) hB

end LateralTheory.E.LSurjChartPf
