module

public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableIffOfLeOfLe
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthLocalizedModuleEqZeroOfNotAnnihilatorLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.KrullDimension.PID
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

namespace GlobalTheory

open Formalism.MainNotions.IntegralHeckeForms

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W]


variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W] in
theorem _root_.GlobalTheory.relLength_ne_top_of_isLatIn {V A B : Submodule O W} (hA : _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn A V)
    (hB : _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn B V) : _root_.GlobalTheory.relLength A B ≠ ⊤ := by
  rw [_root_.GlobalTheory.relLength_ne_top_iff]
  obtain ⟨hAfg, hAV, -⟩ := hA
  obtain ⟨-, -, hBV⟩ := hB
  have : Module.Finite O A := Module.Finite.iff_fg.mpr hAfg
  apply _root_.GlobalTheory.isFiniteLength_of_isTorsion
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    obtain ⟨c, hc, hcB⟩ := hBV a (hAV a.2)
    refine ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hcB


variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W] in
theorem _root_.GlobalTheory.lengthCommensurable_of_isLatIn {V A B : Submodule O W} (hA : _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn A V)
    (hB : _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn B V) : _root_.GlobalTheory.LengthCommensurable A B :=
  ⟨_root_.GlobalTheory.relLength_ne_top_of_isLatIn hA hB,
    _root_.GlobalTheory.relLength_ne_top_of_isLatIn hB hA⟩


variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W] in
theorem _root_.GlobalTheory.sIdx_eq_signedLength_div (l : ℕ) (A B : Submodule O W) :
    _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l A B = (_root_.GlobalTheory.signedLength A B : ℝ) /
      ((IsDiscreteValuationRing.addVal O (l : O)).toNat : ℝ) := by
  unfold _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx _root_.Formalism.MainNotions.IntegralHeckeForms.lenR _root_.GlobalTheory.signedLength
  rw [← _root_.GlobalTheory.relLength_eq_length_quotient_comap,
    ← _root_.GlobalTheory.relLength_eq_length_quotient_comap]
  push_cast
  rw [sub_div]


variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W] in
theorem _root_.GlobalTheory.sIdx_add_and_mono :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (W : Type)
      [AddCommGroup W] [Module O W] (l : ℕ) (V L₁ L₂ L₃ : Submodule O W),
      _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₁ V → _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₂ V → _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₃ V →
      _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₃ = _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ + _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₂ L₃ ∧
        (L₃ ≤ L₂ → _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ ≤ _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₃) := by
  intro O _ _ _ W _ _ l V L₁ L₂ L₃ h₁ h₂ h₃
  have hadd : _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₃ = _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ + _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₂ L₃ := by
    simp only [_root_.GlobalTheory.sIdx_eq_signedLength_div]
    rw [(_root_.GlobalTheory.lengthCommensurable_of_isLatIn h₁ h₂).signedLength_eq_add
      (_root_.GlobalTheory.lengthCommensurable_of_isLatIn h₂ h₃)]
    push_cast
    rw [add_div]
  refine ⟨hadd, fun hle => ?_⟩
  rw [hadd, le_add_iff_nonneg_right, _root_.GlobalTheory.sIdx_eq_signedLength_div]
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact_mod_cast (_root_.GlobalTheory.lengthCommensurable_of_isLatIn h₂ h₃).signedLength_nonneg hle

end GlobalTheory
