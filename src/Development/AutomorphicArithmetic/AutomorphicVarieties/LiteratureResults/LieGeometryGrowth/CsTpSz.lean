module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAppSz
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsCompSz
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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

open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff

theorem UpperTheory.V.Lit.Geo.Cs.tpSz :
    TpSz := by
  intro V F _ _ _ _ q k c
  obtain ⟨C, hC, h⟩ := compSz V V (V [⋀^Fin q]→L[ℝ] F) k c
  refine ⟨|c| * |c| ^ q * C, by positivity, fun A B w p b hA hB hw hs => ?_⟩
  have hA' : ‖A‖ ≤ |c| := hA.trans (le_abs_self c)
  have hB' : ‖B‖ ≤ |c| := hB.trans (le_abs_self c)
  have h1 : Sz k (fun y => w (A y)) p (C * b) := by
    refine h w A p b A.contDiff.contDiffAt hw (fun i hi _ => ?_) hs
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [← norm_iteratedFDeriv_fderiv]
    have e : fderiv ℝ (A : V → V) = fun _ => A := funext fun x => A.fderiv
    rw [e]
    rcases j with _ | j
    · simpa using hA
    · rw [iteratedFDeriv_succ_const]
      simpa using (norm_nonneg A).trans hA
  let L₀ : (V [⋀^Fin q]→L[ℝ] F) →ₗ[ℝ] (V [⋀^Fin q]→L[ℝ] F) :=
    { toFun := fun m => B.compContinuousAlternatingMap (m.compContinuousLinearMap A)
      map_add' := fun m n => by ext v; simp
      map_smul' := fun r m => by ext v; simp }
  have hL : ∀ m, ‖L₀ m‖ ≤ |c| * |c| ^ q * ‖m‖ := fun m => by
    refine ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have a1 : ‖m fun i => A (v i)‖ ≤ ‖m‖ * ∏ i, ‖A (v i)‖ := m.le_opNorm _
    have a2 : ∏ i, ‖A (v i)‖ ≤ ∏ i, (|c| * ‖v i‖) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => A.le_of_opNorm_le hA' _
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at a2
    calc ‖L₀ m v‖ = ‖B (m fun i => A (v i))‖ := rfl
      _ ≤ |c| * ‖m fun i => A (v i)‖ := B.le_of_opNorm_le hB' _
      _ ≤ |c| * (‖m‖ * (|c| ^ q * ∏ i, ‖v i‖)) := by
        gcongr
        exact a1.trans (mul_le_mul_of_nonneg_left a2 (norm_nonneg _))
      _ = _ := by ring
  have hn : ‖L₀.mkContinuous _ hL‖ ≤ |c| * |c| ^ q := L₀.mkContinuous_norm_le (by positivity) hL
  have h2 := (appSz V (V [⋀^Fin q]→L[ℝ] F) (V [⋀^Fin q]→L[ℝ] F) k p).2.1 (L₀.mkContinuous _ hL)
    (fun y => w (A y)) (C * b) (hw.comp p A.contDiff.contDiffAt) h1
  refine Sz.mono h2 ?_
  rw [mul_assoc (|c| * |c| ^ q)]
  exact mul_le_mul_of_nonneg_right hn h1.nonneg
