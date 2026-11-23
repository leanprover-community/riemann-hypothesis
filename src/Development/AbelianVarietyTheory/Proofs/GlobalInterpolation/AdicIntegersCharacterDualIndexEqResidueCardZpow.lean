module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.DualExponentDensity
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDensityEuler
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacter
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.DualIndexPow

theorem nIdx_eq_zpow : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (c : ℤ), (∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp c) → LocalAdditiveCharacterDual.nIdx F ψ v = (PlaceSplittingTypes.resCard F v : ℝ) ^ c := by
  intro F _ _ ψ v c h
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective F v
    (WithZero.exp (-c))
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact WithZero.exp_ne_zero ha.symm
  have hu : ∀ hx : WithZero.exp (-c) ≠ 0, Multiplicative.toAdd (WithZero.unzero hx) = -c :=
    fun _ => rfl

  have hd : GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.psiDual F ψ v = GlobalTheory.LocalDensityProduct.colonV v a := by
    ext t
    rw [GlobalTheory.LocalDensityProduct.mem_colonV]
    change (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1) ↔ _
    rw [h t, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, ha,
      WithZero.exp_neg, mul_inv_le_iff₀ (by simp), one_mul]
  have hi : GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.intV F v = GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.intV F v := rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.nIdx
  rw [hd, hi, (GlobalTheory.LocalDensityProduct.index_colonV v a ha0).2,
    NumberField.FinitePlace.norm_def, ha,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.resCard]
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, WithZero.log_exp]
  simp [_root_.zpow_neg]

end GlobalTheory.DualIndexPow
