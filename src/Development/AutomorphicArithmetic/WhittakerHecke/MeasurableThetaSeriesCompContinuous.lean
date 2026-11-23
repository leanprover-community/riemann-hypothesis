module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import GroundTheory.AutomorphicForms.GL2.AdelicFourier2TensorCosetIndicatorAlgebraMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem sb_le : schwartzBruhatPi (K := ℚ) (ι := Fin 2) ≤ GroundTheory.Automorphic.Adele2.schwartzBruhat2 ℚ := by
  refine Submodule.span_le.mpr ?_
  rintro F ⟨φ, g, hg, rfl⟩
  exact GroundTheory.Automorphic.Adele2.schwartzBruhatTensor2_mem φ
    (show _ ∧ _ from (mem_finiteSchwartzBruhatPi ℚ).mp hg)

private theorem cont_iy : Continuous fun t : ℝ => iy (Real.exp t) := by
  let u : ℝ → (TR.Rinf ℚ)ˣ := fun t => ⟨fun _ => Real.exp t, fun _ => (Real.exp t)⁻¹,
    funext fun _ => mul_inv_cancel₀ (Real.exp_ne_zero t), funext fun _ => inv_mul_cancel₀ (Real.exp_ne_zero t)⟩
  have hu : Continuous u := by
    refine Units.continuous_iff.mpr ⟨continuous_pi fun _ => Real.continuous_exp, continuous_pi fun _ => ?_⟩
    exact Real.continuous_exp.inv₀ Real.exp_ne_zero
  have e : (fun t : ℝ => iy (Real.exp t)) = fun t => TR.infId ℚ (u t) := by
    funext t
    exact dite_eq_right (Real.exp_ne_zero t)
  rw [e]
  exact (TR.continuous_infId ℚ).comp hu

private theorem summable_row {Φ : (Fin 2 → A ℚ) → ℂ} (hΦ : Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2))
    (a : (A ℚ)ˣ) (g : GL (Fin 2) (A ℚ)) :
    Summable fun ξ : Rw ℚ => Φ fun j => (a : A ℚ) * ((fun i => rt (ξ.1 i)) ᵥ* g.val) j := by
  have hs := (GroundTheory.Automorphic.Adele2.poisson_rightTranslate (sb_le hΦ)
    (Matrix.GeneralLinearGroup.scalar (Fin 2) a * g)).1.of_norm
  have hv : ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))
      = (a : A ℚ) • g.val := by
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_apply]
  refine (hs.comp_injective (Subtype.val_injective (p := fun r : Fin 2 → ℚ => r ≠ 0))).congr fun ξ => ?_
  simp only [Function.comp_apply]
  rw [hv, Matrix.vecMul_smul]
  rfl

theorem UpperTheory.measurable_thetaSeries_comp_continuous :
    ∀ (Φ : (Fin 2 → A ℚ) → ℂ), Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2) → ∀ {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
        (τ : X → ℝ) (h : X → GL (Fin 2) (A ℚ)), Continuous τ → Continuous h → Measurable fun x => ThR Φ (τ x) (h x) := by
  intro Φ hΦ X _ _ _ τ h hτ hh
  have hc := continuous_of_mem_schwartzBruhatPi hΦ
  have ha : Continuous fun x => ((iy (Real.exp (τ x)) : (A ℚ)ˣ) : A ℚ) :=
    Units.continuous_val.comp (cont_iy.comp hτ)
  have hg : Continuous fun x => (h x).val := Units.continuous_val.comp hh
  have hterm : ∀ ξ : Rw ℚ, Continuous fun x =>
      Φ fun j => ((iy (Real.exp (τ x)) : (A ℚ)ˣ) : A ℚ) * ((fun i => rt (ξ.1 i)) ᵥ* (h x).val) j := fun ξ =>
    hc.comp (continuous_pi fun j => ha.mul
      ((continuous_apply j).comp (continuous_const.matrix_vecMul hg)))
  refine measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset (Rw ℚ)))
    (f := fun (s : Finset (Rw ℚ)) x => ∑ ξ ∈ s,
      Φ fun j => ((iy (Real.exp (τ x)) : (A ℚ)ˣ) : A ℚ) * ((fun i => rt (ξ.1 i)) ᵥ* (h x).val) j)
    (fun s => (continuous_finsetSum s fun ξ _ => hterm ξ).measurable) ?_
  exact tendsto_pi_nhds.mpr fun x => (summable_row hΦ (iy (Real.exp (τ x))) (h x)).hasSum
