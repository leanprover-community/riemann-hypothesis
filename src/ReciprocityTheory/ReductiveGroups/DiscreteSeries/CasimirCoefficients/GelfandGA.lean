module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsOfFormula
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousOnFderivPhiP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandGB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiCasA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiFacts

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

namespace GelfandGA

local notation "𝕄" => Fin n → Fin n → ℂ

def conjK (ε : Fin n → Bool) (k : KG ε) : 𝕄 →L[ℂ] 𝕄 := Ps1.conjCLM (toMK k⁻¹) (toMK k)

lemma continuous_conjK (ε : Fin n → Bool) : Continuous (conjK ε) := by
  rw [continuous_clm_apply]
  intro y
  have h1 : Continuous (fun k : KG ε => toMK k) := by
    unfold toMK
    fun_prop
  have h2 : Continuous (fun k : KG ε => toMK k⁻¹) := h1.comp continuous_inv
  show Continuous (fun k : KG ε => toMK k⁻¹ * (show Matrix (Fin n) (Fin n) ℂ from y) * toMK k)
  exact (h2.matrix_mul continuous_const).matrix_mul h1

def Lop {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) : ℂ →L[ℂ] (T.V →L[ℂ] T.V) :=
  (ContinuousLinearMap.lsmul ℂ ℂ).flip (T.op k * projW T * T.op k⁻¹)

theorem psM_contDiffOn {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ) :
    ContDiffOn ℂ ∞ (psM T μ) (Ps1.Uset ε) := by
  have := compactSpace_KG ε
  have : IsFiniteMeasureOnCompacts (muK ε) := by unfold muK; infer_instance
  have : IsFiniteMeasure (muK ε) := inferInstance
  have hφ : ContDiffOn ℂ ∞ (Ps1.PhiP μ) (OmegaSet n : Set 𝕄) := fun z hz =>
    (contDiffAt_phiM μ hz).contDiffWithinAt
  have hL : Continuous (Lop T) :=
    ((ContinuousLinearMap.lsmul ℂ ℂ).flip).continuous.comp (Ps1.continuous_P T)
  have hU : IsOpen (Ps1.Uset ε : Set 𝕄) := Ps1.isOpen_Uset
  have hΩ : IsOpen (OmegaSet n : Set 𝕄) := isOpen_omega
  have h := GelfandGB.contDiffOn_param (muK ε) (conjK ε) (continuous_conjK ε) hU hΩ
    (fun x hx k => hx k) (Ps1.PhiP μ) (Lop T) hφ hL
  have h' : ContDiffOn ℂ ∞ (fun x : 𝕄 => psM T μ x) (Ps1.Uset ε : Set 𝕄) :=
    (h.const_smul ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ))).congr fun x _ => rfl
  exact h'

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma lhol_contDiffOn {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U)
    {F : Matrix (Fin n) (Fin n) ℂ → E} (hF : ContDiffOn ℂ ∞ F U) (X : Matrix (Fin n) (Fin n) ℂ) :
    ContDiffOn ℂ ∞ (Lhol X F) U := by
  have hlin : ContDiff ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => X * z) := by
    have h := (LinearMap.toContinuousLinearMap
      (LinearMap.mulLeft ℂ X : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)).contDiff
      (n := ∞)
    exact h
  unfold Lhol
  exact ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hF).2.clm_apply hlin.contDiffOn

lemma opPow_contDiffOn {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U)
    {F : Matrix (Fin n) (Fin n) ℂ → E} (hF : ContDiffOn ℂ ∞ F U)
    (Y : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) :
    ∀ j a b, ContDiffOn ℂ ∞ (opPow (fun a b => Lhol (Y a b)) j a b F) U := by
  intro j
  induction j with
  | zero =>
    intro a b
    simp only [opPow]
    split_ifs
    · exact hF
    · exact contDiffOn_const
  | succ k ih =>
    intro a b
    simp only [opPow]
    rw [Finset.sum_fn]
    exact ContDiffOn.sum fun c _ => lhol_contDiffOn hU (ih c b) (Y a c)

end GelfandGA

end ReciprocityTheory.ChartRestriction.DS.S7
