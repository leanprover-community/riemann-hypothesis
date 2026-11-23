module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexNeZeroOfReps
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory

theorem matrix_intertwiner_descends : ∀ (K : Type) [Field K] (e : K →+* ℂ) (Γ m p : Type) [Fintype m] [Fintype p] (A : Γ → Matrix m m K) (B : Γ → Matrix p p K), (∃ X : Matrix p m ℂ, X ≠ 0 ∧ ∀ γ, X * (A γ).map e = (B γ).map e * X) → ∃ X : Matrix p m K, X ≠ 0 ∧ ∀ γ, X * A γ = B γ * X := by
  intro K _ e Γ m p _ _ A B ⟨X, hX, hXc⟩
  letI := e.toAlgebra
  obtain ⟨a, b, hab⟩ : ∃ a b, X a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hX (Matrix.ext h)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual K ℂ, ℓ (X a b) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hab ((Module.forall_dual_apply_eq_zero_iff K (X a b)).1 h)
  have h1 : ∀ (x : ℂ) (c : K), ℓ (x * e c) = ℓ x * c := by
    intro x c
    have : x * e c = c • x := by rw [Algebra.smul_def, mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have h2 : ∀ (x : ℂ) (c : K), ℓ (e c * x) = c * ℓ x := by
    intro x c
    have : e c * x = c • x := by rw [Algebra.smul_def]; rfl
    rw [this, map_smul, smul_eq_mul]
  refine ⟨X.map ℓ, ?_, fun γ => ?_⟩
  · intro h
    apply hℓ
    have := congrFun (congrFun h a) b
    simpa using this
  · ext i j
    have key := congrArg (fun M => ℓ (M i j)) (hXc γ)

    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, h1, h2] at key ⊢
    exact key

end GlobalTheory
