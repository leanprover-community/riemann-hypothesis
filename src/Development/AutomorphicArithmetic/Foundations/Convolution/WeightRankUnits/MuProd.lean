module

public import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.DeltaProdAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharFinprodLocKMulInfEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMInfinityComponentGlobalUnit
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem muAt_unit {E : Type} [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (u : Pl E) (k : Eˣ) :
    UpperTheory.ConvolutionTheory.G2.muAt μ u (k : E) = ((μ.locK u k : ℂˣ) : ℂ) := by
  have h : algebraMap E (u.adicCompletion E) (k : E) ≠ 0 := by
    simpa using k.ne_zero
  rw [UpperTheory.ConvolutionTheory.G2.muAt, dite_eq_left h, HChar.locK, MonoidHom.comp_apply]
  have hu : Units.mk0 (algebraMap E (u.adicCompletion E) (k : E)) h = atFin u k := Units.ext rfl
  rw [hu]

theorem UpperTheory.ConvolutionTheory.G2.muProd :
    UpperTheory.ConvolutionTheory.G2.MuProd := by
  intro E _ _ _ μ e hμ R hR
  obtain ⟨hf, hp⟩ := GlobalTheory.HCharUnit.finprod_locK_mul_inf E μ (Units.mk0 R hR)
  have hfun : (fun u : Pl E => UpperTheory.ConvolutionTheory.G2.muAt μ u R) =
      fun u : Pl E => (Units.coeHom ℂ) (μ.locK u (Units.mk0 R hR)) :=
    funext fun u => muAt_unit μ u (Units.mk0 R hR)
  have hsub : (Function.mulSupport fun u : Pl E => (Units.coeHom ℂ) (μ.locK u (Units.mk0 R hR))) ⊆
      Function.mulSupport fun u : Pl E => μ.locK u (Units.mk0 R hR) := by
    intro u hu h1
    exact hu (by simp only [h1, map_one])
  rw [hfun]
  refine ⟨hf.subset hsub, ?_⟩
  rw [← MonoidHom.map_finprod _ hf]
  have hinf := GlobalTheory.BCT.inf_mu_unit E μ e hμ (Units.mk0 R hR)
  simp only [Units.val_mk0] at hinf
  rw [← hinf]
  have := congrArg (Units.coeHom ℂ) hp
  simpa using this
