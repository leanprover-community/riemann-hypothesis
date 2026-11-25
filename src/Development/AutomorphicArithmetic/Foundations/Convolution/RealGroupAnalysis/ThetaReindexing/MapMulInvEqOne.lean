module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.D

open GroundTheory.Heights₂.Theta NumberField.mixedEmbedding

section

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]

private noncomputable def infEquiv (g : GL ι (A K)) :
    (ι → mixedSpace K) ≃L[ℝ] (ι → mixedSpace K) :=
  let u := Matrix.GeneralLinearGroup.map adeleInfHom g
  LinearEquiv.toContinuousLinearEquiv ((Matrix.toLin'OfInv u.inv_mul u.mul_inv).restrictScalars ℝ)

private noncomputable def finHomeo (g : GL ι (A K)) :
    (ι → FiniteAdeleRing (𝓞 K) K) ≃ₜ (ι → FiniteAdeleRing (𝓞 K) K) :=
  let u := Matrix.GeneralLinearGroup.map adeleFinHom g
  { (Matrix.toLin'OfInv u.inv_mul u.mul_inv).toEquiv with
    continuous_toFun := show Continuous (u.val *ᵥ ·) from
      continuous_const.matrix_mulVec continuous_id
    continuous_invFun := show Continuous (u.inv *ᵥ ·) from
      continuous_const.matrix_mulVec continuous_id }

private theorem infPartPi_gl (g : GL ι (A K)) (x : ι → A K) :
    infPartPi (g.val *ᵥ x) = infEquiv g (infPartPi x) := by
  rw [infPartPi_eq_adeleInfHom, infPartPi_eq_adeleInfHom, map_mulVec_eq]
  rfl

private theorem finPartPi_gl (g : GL ι (A K)) (x : ι → A K) :
    finPartPi (g.val *ᵥ x) = finHomeo g (finPartPi x) := by
  rw [finPartPi_eq_adeleFinHom, finPartPi_eq_adeleFinHom, map_mulVec_eq]
  rfl

end

end UpperTheory.ConvolutionTheory.R2.D

theorem UpperTheory.ConvolutionTheory.R2.D.sClos :
    ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (g : GL ι (A F)) (φ : (ι → A F) → ℂ),
    φ ∈ schwartzBruhatPi (K := F) (ι := ι) → (fun v => φ (g.val *ᵥ v)) ∈ schwartzBruhatPi (K := F) (ι := ι) := by
  intro F _ _ ι _ _ g φ hφ
  induction hφ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, h, hh, rfl⟩ := hG
    have e : (fun v => schwartzBruhatTensorPi f h (g.val *ᵥ v)) =
        schwartzBruhatTensorPi (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (infEquiv g) f)
          (h ∘ finHomeo g) := by
      funext x
      simp only [schwartzBruhatTensorPi, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
        Function.comp_apply, infPartPi_gl, finPartPi_gl]
    rw [e]
    refine schwartzBruhatTensorPi_mem _ ((mem_finiteSchwartzBruhatPi F).2 ⟨?_, ?_⟩)
    · exact ((mem_finiteSchwartzBruhatPi F).1 hh).1.comp_continuous (finHomeo g).continuous
    · exact ((mem_finiteSchwartzBruhatPi F).1 hh).2.comp_homeomorph (finHomeo g)
  | zero => exact zero_mem _
  | add G H _ _ hG hH => exact add_mem hG hH
  | smul c G _ hG => exact Submodule.smul_mem _ c hG
