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
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, w.asIdeal.primeCompl.one_mem, by simpa using Submodule.subset_span hy⟩
    | zero => exact ⟨1, w.asIdeal.primeCompl.one_mem, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, hs, hsy⟩ := hy
      obtain ⟨t, ht, htz⟩ := hz
      refine ⟨s * t, w.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
      have e : (s * t) • (y + z) = t • (s • y) + s • (t • z) := by
        rw [smul_add, mul_smul, smul_comm s t y, mul_smul]
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ t hsy) (Submodule.smul_mem _ s htz)
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := hy
      obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.mk'_surjective w.asIdeal.primeCompl a
      refine ⟨s * t, w.asIdeal.primeCompl.mul_mem hs t.2, ?_⟩
      have hspec : (IsLocalization.mk' (Formalism.L2.Col.Ow w) r t) *
          algebraMap (RingOfIntegers K) (Formalism.L2.Col.Ow w) (t : RingOfIntegers K) =
          algebraMap (RingOfIntegers K) (Formalism.L2.Col.Ow w) r := IsLocalization.mk'_spec _ r t
      simp only at hrt
      rw [hrt] at hspec
      have e : (s * (t : RingOfIntegers K)) • (a • y) = r • (s • y) := by
        have ht : (t : RingOfIntegers K) • (a • y) = r • y := by
          rw [← algebraMap_smul (Formalism.L2.Col.Ow w) (t : RingOfIntegers K) (a • y), smul_smul,
            mul_comm, hspec, algebraMap_smul]
        rw [mul_comm, mul_smul, smul_comm (t : RingOfIntegers K) s, ht, smul_comm s r]
      rw [e]
      exact Submodule.smul_mem _ r hsy
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
