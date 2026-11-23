module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
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
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem cont_aE {K : Type} [Field K] [NumberField K] : Continuous (aE : (A K)ˣ → GL (Fin 2) (A K)) := by
  refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    exacts [Units.continuous_val, continuous_const, continuous_const, continuous_const]
  · fin_cases i <;> fin_cases j
    exacts [Units.continuous_coe_inv, continuous_const, continuous_const, continuous_const]

theorem UpperTheory.measurable_whittaker_idele_diagTorus_mul :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ →
        Measurable (fun p : IdeleGroup ℚ × G1 ℚ => Wo D φ (em E (aE p.1 * gl p.2))) := by
  intro E _ _ D ω φ h
  have hem : Continuous (em E) := Continuous.units_map _
    (continuous_matrix fun i j => AdeleBaseChange.continuous_adeleMap.comp (continuous_id.matrix_elem i j))
  have h1 : Continuous fun p : IdeleGroup ℚ × G1 ℚ => em E (aE p.1 * gl p.2) :=
    hem.comp ((cont_aE.comp continuous_fst).mul (M.continuous_gl.comp continuous_snd))
  have hn : Continuous (nE D) :=
    M.continuous_gl.comp (M.continuous_nU.comp
      ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 0)).add
        ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 1)).mul continuous_const)))
  have hψ : Continuous (ψ (F := ℚ)) := continuous_subtype_val.comp continuous_adelicChar
  have h2 : Continuous fun q : (IdeleGroup ℚ × G1 ℚ) × (Fin 2 → A ℚ) => φ (nE D q.2 * em E (aE q.1.1 * gl q.1.2)) * ψ (q.2 1) :=
    (h.cont.comp ((hn.comp continuous_snd).mul (h1.comp continuous_fst))).mul
      (hψ.comp ((continuous_apply 1).comp continuous_snd))
  have : BorelSpace ((IdeleGroup ℚ × G1 ℚ) × (Fin 2 → A ℚ)) := inferInstance
  exact (h2.measurable.stronglyMeasurable.integral_prod_right' (ν := (adeleMeasurePi ℚ).restrict (FS2 ℚ))).measurable
