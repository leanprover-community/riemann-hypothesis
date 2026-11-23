module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDirac
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
import GroundTheory.GlobalFields.KummerTheory.LocalIndex

@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section
open scoped ContDiff

namespace GlobalTheory.SmoothClosure

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem fderiv_chart_apply (F : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a)
    (hd : DifferentiableAt ℝ (chart F g) x) (Z : Lie E a) :
    fderiv ℝ (chart F g) x Z = chart (lieD (toL ((Matrix.of x)⁻¹ * Matrix.of Z)) F) g x := by
  obtain ⟨u, hu⟩ := id hx
  have e : x = toL u.val := hu.symm
  subst e
  rw [chart_val, lieD, chart_mul]
  have e1 : lmul (toL u.val) (oneL E a) = toL u.val := mul_one u.val
  rw [fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL u.val)).differentiableAt, e1, ContinuousLinearMap.fderiv]
  rw [ContinuousLinearMap.comp_apply]
  congr 1
  change Z = u.val * ((Matrix.of (toL u.val))⁻¹ * Matrix.of Z)
  have : (Matrix.of (toL u.val))⁻¹ = (↑(u⁻¹) : Matrix (Fin a) (Fin a) (Cinf E)) := by
    change (u.val)⁻¹ = _
    rw [Matrix.coe_units_inv]
  rw [this, ← mul_assoc, Units.mul_inv, one_mul]
  rfl

theorem chart_lieD_basis {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (Lie E a)) (F : GA E a → ℂ) (g : GA E a)
    {x : Lie E a} (hx : x ∈ invSet E a) (W : Lie E a) :
    chart (lieD W F) g x = ∑ k, b.repr W k • chart (lieD (b k) F) g x := by
  obtain ⟨u, hu⟩ := id hx
  have e : x = toL u.val := hu.symm
  subst e
  simp only [chart_val, lieD]
  conv_lhs => rw [← b.sum_repr W]

  rw [map_sum]
  simp only [map_smul]

theorem le_Sm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Submodule ℂ (GA E a → ℂ)),
    (∀ F ∈ S, ∀ g : GA E a, DifferentiableOn ℝ (chart F g) (invSet E a)) →
    (∀ F ∈ S, ∀ X : Lie E a, lieD X F ∈ S) → S ≤ Sm E a := by
  intro E _ _ _ a S hdiff hlie
  let b := Module.finBasis ℝ (Lie E a)
  have key : ∀ n : ℕ, ∀ F ∈ S, ∀ g : GA E a, ContDiffOn ℝ n (chart F g) (invSet E a) := by
    intro n
    induction n with
    | zero =>
      intro F hF g
      exact contDiffOn_zero.2 (hdiff F hF g).continuousOn
    | succ n ih =>
      intro F hF g
      rw [Nat.cast_succ]
      refine contDiffOn_succ_of_fderiv_apply (hdiff F hF g) (by simp) fun Z => ?_
      have hc : ∀ k, ContDiffOn ℝ n (fun x : Lie E a =>
          (b.coord k).toContinuousLinearMap (rmul Z (toL (Matrix.of x)⁻¹))) (invSet E a) := fun k =>
        (b.coord k).toContinuousLinearMap.contDiff.comp_contDiffOn
          ((rmul Z).contDiff.comp_contDiffOn (GlobalTheory.GLFin.Inhab.contDiffOn_invL.of_le (by exact_mod_cast le_top)))
      have hsum : ContDiffOn ℝ n (fun x => ∑ k ∈ Finset.univ, (b.coord k).toContinuousLinearMap
          (rmul Z (toL (Matrix.of x)⁻¹)) • chart (lieD (b k) F) g x) (invSet E a) :=
        ContDiffOn.sum fun k _ => (hc k).smul (ih _ (hlie F hF (b k)) g)
      refine hsum.congr fun x hx => ?_
      rw [fderivWithin_of_isOpen isOpen_invSet hx,
        fderiv_chart_apply F g hx ((hdiff F hF g).differentiableAt (isOpen_invSet.mem_nhds hx)) Z,
        chart_lieD_basis b F g hx]
      rfl
  intro F hF g
  exact contDiffOn_infty.2 fun n => key n F hF g

end GlobalTheory.SmoothClosure
