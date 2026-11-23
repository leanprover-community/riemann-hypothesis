module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteIsAlgClosedCExt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace GlobalTheory.Ex

theorem exists_complete_isAlgClosed_centred_at_prime :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [Algebra.IsAlgebraic R K] (P : Ideal R), P.IsPrime → P ≠ ⊥ → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (gam : K →+* C), (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) ∧ ∀ r ∈ P, ‖gam (algebraMap R K r)‖ < 1 := by
  intro R K _ _ _ _ _ _ _ P hP hP0
  obtain ⟨O, _, _, _, _, φ, hker, hcom⟩ :=
    GlobalTheory.exists_complete_discreteValuationRing_of_prime_lt (⊥ : Ideal R) P (bot_lt_iff_ne_bot.2 hP0)
  have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 hker
  obtain ⟨C, i1, i2, i3, i4, i5, -, -, h1, h2⟩ :=
    GlobalTheory.Ex.exists_complete_isAlgClosed_cExt O (FractionRing O)
  let ψ : R →+* C := (algebraMap (FractionRing O) C).comp ((algebraMap O (FractionRing O)).comp φ)
  have hψ : Function.Injective ψ :=
    (algebraMap (FractionRing O) C).injective.comp
      ((IsFractionRing.injective O (FractionRing O)).comp hφ)
  letI : Algebra R C := ψ.toAlgebra
  haveI : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).2 hψ
  let g : K →ₐ[R] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hg : ∀ r, g.toRingHom (algebraMap R K r) = ψ r := fun r => g.commutes r
  refine ⟨C, i1, i2, i3, i4, g.toRingHom, fun r => ?_, fun r hr => ?_⟩
  · rw [hg]
    exact h1 (φ r)
  · rw [hg]
    exact h2 (φ r) (by rw [← hcom] at hr; exact hr)

end GlobalTheory.Ex
