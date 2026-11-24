module

public import Formalism.GaloisCohomology.Statement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.QzBasic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe

@[expose] public section

open UpperTheory.V UpperTheory.V.PropA Formalism.GaloisCohomology

theorem UpperTheory.V.PropA.qzInj :
    ∀ (l : ℕ) [Fact l.Prime], Module.Injective ℤ_[l] (QZ l) := by
  intro l _
  refine Module.Baer.injective ?_
  intro I g
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal I).principal
  have hmem : ∀ x ∈ I, ∃ c : ℤ_[l], c • a = x := fun x hx =>
    Submodule.mem_span_singleton.1 (ha ▸ hx)
  have haI : a ∈ I := ha ▸ Submodule.mem_span_singleton_self a
  have hy : ∃ y : QZ l, a • y = g ⟨a, haI⟩ := by
    by_cases h0 : a = 0
    · refine ⟨0, ?_⟩
      have : (⟨a, haI⟩ : I) = 0 := Subtype.ext h0
      rw [this, map_zero, smul_zero]
    · exact (UpperTheory.V.Kum.qzBasic l).1 a h0 _
  obtain ⟨y, hy⟩ := hy
  refine ⟨LinearMap.toSpanSingleton ℤ_[l] (QZ l) y, fun x hx => ?_⟩
  obtain ⟨c, rfl⟩ := hmem x hx
  have : (⟨c • a, hx⟩ : I) = c • (⟨a, haI⟩ : I) := rfl
  rw [this, map_smul g, ← hy, LinearMap.toSpanSingleton_apply, smul_eq_mul, mul_smul]
