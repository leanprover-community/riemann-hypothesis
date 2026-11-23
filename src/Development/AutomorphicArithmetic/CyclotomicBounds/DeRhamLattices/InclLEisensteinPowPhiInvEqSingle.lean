module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.UpperTheory.KN.inclL_eisensteinPow_phiInv_eq_single : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (β : ℕ) (hβ : ∀ τ j i, E ↥LL.1 l e ^ β * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1) (i : ι), inclL (thetaW a LL) ϖ P (fun j => ϖ.iTot (thetaW a LL) ↥LL.1 (fun τ => ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩)) = Pi.single i (inclO l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1 (fun _ => ⟨E ↥LL.1 l e ^ β, pow_mem (E_mem l e _) β⟩))) := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P β hβ i
  ext i'
  rw [inclL_apply]

  simp only [Matrix.mulVec, dotProduct, ← ϖ.iW_of_mem (thetaW a LL) ↥LL.1, frobMat, Matrix.map_apply,
  Matrix.of_apply, ← map_mul, ← map_sum]
  simp only [Pi.single_apply]
  have key : ∀ i' i τ, ∑ j, P.mx τ i' j * (E ↥LL.1 l e ^ β * P.mxInv τ j i) =
      E ↥LL.1 l e ^ β * (1 : Matrix ι ι _) i' i := by
    intro i' i τ
    rw [← P.mx_mul_mxInv τ, Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  split_ifs with h
  · subst h
    refine congrArg _ (funext fun τ => Subtype.ext ?_)
    rw [Finset.sum_apply, AddSubmonoidClass.coe_finsetSum]
    have h1 := key i' i' τ
    rw [Matrix.one_apply_eq, mul_one] at h1
    exact h1
  · have hz : ∀ F : ZMod a → invE l e (A ↥(OL LL) ↥LL.1), (∀ τ, ((F τ : invE l e (A ↥(OL LL) ↥LL.1)) : PowerSeries ↥LL.1) = 0) →
        ϖ.iW (thetaW a LL) ↥LL.1 F = 0 := fun F hF => by
      have hF0 : F = 0 := funext fun τ => Subtype.ext (hF τ)
      rw [hF0]
      exact map_zero _
    refine hz _ fun τ => ?_
    rw [Finset.sum_apply, AddSubmonoidClass.coe_finsetSum]
    have h1 := key i' i τ
    rw [Matrix.one_apply_ne h, mul_zero] at h1
    exact h1
