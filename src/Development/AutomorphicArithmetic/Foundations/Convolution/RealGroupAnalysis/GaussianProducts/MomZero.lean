module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.FockMul
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatFock
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatSurj
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.RowMul
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.momZero :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, (∀ φ ∈ Fock D.δ, W1 W M f.1 φ 1 = 0) → ∀ φ ∈ Fock D.δ, ∀ p ∈ polyOn F (Fin 2), ∀ T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F), IsCompact T → IsOpen T →
    ∫ x : IdeleGroup F × G1 F, p (row (mD x.1 * x.2)) * T.indicator 1 (finPartPi (row (mD x.1 * x.2))) * iw (w1 W f.1 φ 1) x ∂M.ν = 0 := by
  intro F E _ _ _ _ _ _ _ D W M π f hf h0 φ hφ p hp T hc ho
  obtain ⟨φ', hφ', he⟩ := hatSurj F D.δ D.neg _
    ((fockMul F D.δ).1 _ (hatFock F D.δ _ (mem_fock.1 hφ)) p hp T hc ho)
  have hrow := rowMul F E D W (fun r => p r * T.indicator 1 (finPartPi r)) φ φ'
    (fun v => by rw [he])
  have hw : ∀ g : G1 F, w1 W f.1 φ' 1 g =
      p (row g) * T.indicator 1 (finPartPi (row g)) * w1 W f.1 φ 1 g := by
    intro g
    have hr : (![(0 : A F), 1] ᵥ* g.1) = row g := by
      ext i
      simp [row, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    have h1 := hrow g ![0, 1, 1, 0]
    have h2 : (![(![0, 1, 1, 0] : V4 F) 0, (![0, 1, 1, 0] : V4 F) 1] : Fin 2 → A F) = ![0, 1] := by
      ext i
      fin_cases i <;> rfl
    rw [h2, hr] at h1
    simp only [w1, map_one, Module.End.one_apply]
    rw [h1]
    ring
  have hz := h0 φ' hφ'
  rw [← hz]
  simp only [W1, Meas.I0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [iw, hw]
  ring
