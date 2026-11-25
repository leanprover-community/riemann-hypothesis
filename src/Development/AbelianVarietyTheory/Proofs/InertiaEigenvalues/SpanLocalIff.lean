module

public import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.Localization.Finiteness

@[expose] public section

open IsDedekindDomain NumberField

namespace GlobalTheory.LocalSpanCriterion

theorem span_local_iff {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module (RingOfIntegers K) V] (w : HeightOneSpectrum (RingOfIntegers K))
    [Module (Formalism.L2.Col.Ow w) V] [IsScalarTower (RingOfIntegers K) (Formalism.L2.Col.Ow w) V]
    (T : Set V) (x : V) :
    x ∈ Submodule.span (Formalism.L2.Col.Ow w) T ↔
      x ∈ Formalism.HermitianLatticesTheory.localization₂ (HeightOneSpectrum.asIdeal w)
        (Submodule.span (RingOfIntegers K) T) := by
  have hmem : ∀ y : V, y ∈ Formalism.HermitianLatticesTheory.localization₂ (HeightOneSpectrum.asIdeal w)
        (Submodule.span (RingOfIntegers K) T) ↔
      ∃ s ∈ w.asIdeal.primeCompl, s • y ∈ Submodule.span (RingOfIntegers K) T := fun y => Iff.rfl
  rw [hmem]
  constructor
  · intro hx
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span w.asIdeal.primeCompl
      (Formalism.L2.Col.Ow w) T x hx
    exact ⟨t, t.2, ht⟩
  · rintro ⟨s, hs, hsx⟩
    have hu : IsUnit (algebraMap (RingOfIntegers K) (Formalism.L2.Col.Ow w) s) :=
      IsLocalization.map_units (Formalism.L2.Col.Ow w) (⟨s, hs⟩ : w.asIdeal.primeCompl)
    have h1 : s • x ∈ Submodule.span (Formalism.L2.Col.Ow w) T := by
      have := Submodule.span_le_restrictScalars (RingOfIntegers K) (Formalism.L2.Col.Ow w) T hsx
      exact this
    rw [← algebraMap_smul (Formalism.L2.Col.Ow w) s x] at h1
    obtain ⟨u, hu'⟩ := hu
    have h2 := Submodule.smul_mem _ (↑u⁻¹ : Formalism.L2.Col.Ow w) h1
    rwa [← hu', smul_smul, Units.inv_mul, one_smul] at h2

end GlobalTheory.LocalSpanCriterion
