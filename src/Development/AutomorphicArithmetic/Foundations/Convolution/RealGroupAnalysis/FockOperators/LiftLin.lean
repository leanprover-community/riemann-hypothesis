module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.One
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private lemma th_add {F : Type} [Field F] [NumberField F] (a b : S4 F) :
    Th (a + b).1 = Th a.1 + Th b.1 := by
  have ha := (poisson_of_mem_schwartzBruhatPi a.2).1.of_norm
  have hb := (poisson_of_mem_schwartzBruhatPi b.2).1.of_norm
  exact ha.tsum_add hb

private lemma th_smul {F : Type} [Field F] [NumberField F] (c : ℂ) (a : S4 F) :
    Th (c • a).1 = c * Th a.1 :=
  tsum_mul_left

theorem UpperTheory.ConvolutionTheory.R2.Fo.liftLin :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ,
    (∀ f' ∈ π.V, lift W M (f + f').1 φ = lift W M f.1 φ + lift W M f'.1 φ) ∧ (∀ φ' ∈ Fock D.δ, lift W M f.1 (φ + φ') = lift W M f.1 φ + lift W M f.1 φ') ∧
    ∀ c : ℂ, lift W M (c • f).1 φ = c • lift W M f.1 φ ∧ lift W M f.1 (c • φ) = c • lift W M f.1 φ := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ
  have hI := fun f hf φ hφ h => (UpperTheory.ConvolutionTheory.R2.conv F E D W M π f hf φ hφ h).1
  refine ⟨fun f' hf' => ?_, fun φ' hφ' => ?_, fun c => ⟨?_, ?_⟩⟩
  · funext h
    have e : ∀ x, (f + f').1 x = f.1 x + f'.1 x := fun x => rfl
    simp only [lift, Pi.add_apply, e, add_mul]
    exact integral_add (hI f hf φ hφ h) (hI f' hf' φ hφ h)
  · funext h
    simp only [lift, Pi.add_apply, map_add (f := _), LinearMap.add_apply, th_add, mul_add]
    exact integral_add (hI f hf φ hφ h) (hI f hf φ' hφ' h)
  · funext h
    have e : ∀ x, (c • f).1 x = c * f.1 x := fun x => rfl
    simp only [lift, Pi.smul_apply, smul_eq_mul, e, mul_assoc]
    exact integral_const_mul _ _
  · funext h
    simp only [lift, Pi.smul_apply, smul_eq_mul, map_smul, th_smul, mul_left_comm _ c]
    exact integral_const_mul _ _
