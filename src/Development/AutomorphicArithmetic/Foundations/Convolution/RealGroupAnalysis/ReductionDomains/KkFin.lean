module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
public import GroundTheory.AutomorphicForms.ReductionHeight
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.kkFin :
    ∀ (F : Type) [Field F] [NumberField F], ∀ (k : G1 F) (v : HeightOneSpectrum (𝓞 F)), IntAt v k ↔ Reduction.finAt v (gl k) ∈ GLnLocal.integralGL (v.adicCompletion F) 2 := by
  intro F _ _ k v
  have hinv : (Reduction.finAt v (gl k))⁻¹ = Reduction.finAt v (gl k⁻¹) := by
    have e : ∀ g : GL (Fin 2) (A F), Reduction.finAt v g = Matrix.GeneralLinearGroup.map (Reduction.finEval v) g := by
      intro g; ext i j; rfl
    rw [e, e, ← map_inv, ← map_inv]
  have hent : ∀ (g : G1 F) i j, (Reduction.finAt v (gl g)) i j = (g i j).2 v := fun _ _ _ => rfl
  rw [GLnLocal.mem_integralGL_iff, hinv]
  simp only [hent, GroundTheory.Global.mem_valuationInteger_iff]
  refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
  intro i j
  have e : (k⁻¹ : G1 F).1 = !![k.1 1 1, -k.1 0 1; -k.1 1 0, k.1 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  have hn : ∀ a b, (-(k.1 a b)).2 v ∈ v.adicCompletionIntegers F := fun a b =>
    neg_mem (h a b)
  show ((k⁻¹ : G1 F).1 i j).2 v ∈ _
  rw [e]
  fin_cases i <;> fin_cases j
  · exact h 1 1
  · exact hn 0 1
  · exact hn 1 0
  · exact h 0 0
