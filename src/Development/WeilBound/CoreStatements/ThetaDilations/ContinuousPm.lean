module

import CompanionTheory.AutomorphicTheory.ThetaDilations.ContinuousPm
public import Development.WeilBound.CoreStatements.ThetaDilations.ParAlg
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  (R : Type) [CommRing R] [Algebra F R]

theorem exists_anti (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  apply CompanionTheory.PlacePermOperatorBicommutantSpan.exists_anti <;> assumption

theorem norm_sigR (h : IsCMExt F E σ) (a : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.norm R a) = a * sigR R σ a := by
  apply CompanionTheory.PlacePermOperatorBicommutantSpan.norm_sigR <;> assumption

theorem cT_JR {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) : cT (sigR R σ) (JR R J) = JR R J := by
  ext i j; simp [cT, JR, sigR, inclR, hJ.1]

theorem hform_conj {K : Type} [CommRing K] {M : ℕ} {s : K →+* K} {J : Matrix (Fin M) (Fin M) K} (hs : ∀ x, s (s x) = x)
    (hJ : cT s J = J) (x y : Fin M → K) : s (hform s J x y) = hform s J y x := by
  have : ∀ i j, s (J j i) = J i j := fun i j => congrFun (congrFun hJ i) j

  simp only [hform, map_sum, map_mul, hs, this]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hform_add {K : Type} [CommRing K] {M : ℕ} (s : K →+* K) (J : Matrix (Fin M) (Fin M) K) (x y : Fin M → K) :
    hform s J (x + y) (x + y) = hform s J x x + hform s J x y + hform s J y x + hform s J y y := by
  have e : (s : K → K) ∘ (x + y) = s ∘ x + s ∘ y := funext fun _ => map_add s _ _
  simp only [hform_eq, e, Matrix.add_vecMul, add_dotProduct, dotProduct_add]; ring

theorem hform_U {K : Type} [CommRing K] {M : ℕ} {s : K →+* K} {J U : Matrix (Fin M) (Fin M) K} (hU : cT s U * J * U = J)
    (x : Fin M → K) : hform s J (U *ᵥ x) (U *ᵥ x) = hform s J x x := by
  have e : (s : K → K) ∘ (U *ᵥ x) = (s ∘ x) ᵥ* cT s U := by
    funext i; simp [Matrix.vecMul, Matrix.mulVec, dotProduct, cT, mul_comm]
  rw [hform_eq, hform_eq, e, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hU]

theorem hyp_inv {K : Type} [CommRing K] {M : ℕ} {J Ji : Matrix (Fin M) (Fin M) K} (h : Ji * J = 1) :
    hypJ Ji * hypJ J = 1 := by
  rw [← pm_one]
  simp [hypJ_eq, blk_mul, pm, h]

theorem continuous_pm {X K : Type} [TopologicalSpace X] [CommRing K] [TopologicalSpace K] {M : ℕ} {a b d : X → K}
    {r w : X → Fin M → K} {U : X → Matrix (Fin M) (Fin M) K} (ha : Continuous a) (hb : Continuous b)
    (hr : Continuous r) (hd : Continuous d) (hw : Continuous w) (hU : Continuous U) :
    Continuous fun x => pm (a x) (b x) (r x) (d x) (w x) (U x) := by
  refine continuous_matrix fun i j => ?_
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
  exacts [ha, hb, (continuous_apply j).comp hr, continuous_const, hd, continuous_const, continuous_const,
    (continuous_apply i).comp hw, hU.matrix_elem i j]


end PositivityTheory.PlacePermOperatorBicommutantSpan
