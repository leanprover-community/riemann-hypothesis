module

import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.ExistsSchwartzBruhatPiMajorant
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSetIntegralOfContinuousUncurry
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSummableMajorantLatticeSumStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.EpsteinThetaC

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem continuous_scalC : Continuous (scalC : IdeleGroup k → GL ι 𝔸[k]) := by
  apply GlobalTheory.CompanionTheory.EpsteinUnfold.Hd.continuous_scalC <;> assumption

theorem thetaC_ltr (A h : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) :
    thetaC (ltr A F) h = thetaC F (A * h) := by
  simp only [thetaC, ltr, Units.val_mul, Matrix.mulVec_mulVec]

theorem continuous_thetaC {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) :
    Continuous (thetaC F : GL ι 𝔸[k] → ℂ) := by
  refine continuous_iff_continuousAt.2 fun h₀ ↦ ?_
  obtain ⟨C, hC, hh₀⟩ := exists_compact_mem_nhds h₀
  obtain ⟨u, hu, hFu⟩ := GlobalTheory.T.exists_summable_majorant_lattice_sum hF hC
  have hcont : ContinuousOn (thetaC F : GL ι 𝔸[k] → ℂ) C := by
    refine continuousOn_tsum (fun ξ ↦ Continuous.continuousOn ?_) hu fun ξ h hh ↦ hFu h hh ξ
    refine (continuous_of_mem_schwartzBruhatPi hF).comp ?_
    exact Units.continuous_val.matrix_mulVec continuous_const
  exact hcont.continuousAt hh₀

noncomputable def translatedIntegrand (w : InfinitePlace k) (Ψ : (ι → 𝔸[k]) → ℂ)
    (ω : HeckeCharacter k) (p : {r : ℝ // 0 < r} × GL ι 𝔸[k]) (u : normOneSubgroup k) : ℂ :=
  thetaC Ψ (p.2 * scalC (moduleSection w p.1 * (u : IdeleGroup k))) *
    (ω.toIdele (u : IdeleGroup k) : ℂ)

theorem continuous_translatedIntegrand (w : InfinitePlace k) {Ψ : (ι → 𝔸[k]) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhatPi (K := k) (ι := ι)) (ω : HeckeCharacter k) :
    Continuous (Function.uncurry (translatedIntegrand w Ψ ω)) := by
  have hu : Continuous fun x : ({r : ℝ // 0 < r} × GL ι 𝔸[k]) × normOneSubgroup k ↦
      (x.2 : IdeleGroup k) := continuous_subtype_val.comp continuous_snd
  have hs : Continuous fun x : ({r : ℝ // 0 < r} × GL ι 𝔸[k]) × normOneSubgroup k ↦
      moduleSection w x.1.1 :=
    (continuous_moduleSection w).comp (continuous_fst.comp continuous_fst)
  have hg : Continuous fun x : ({r : ℝ // 0 < r} × GL ι 𝔸[k]) × normOneSubgroup k ↦
      x.1.2 := continuous_snd.comp continuous_fst
  exact ((continuous_thetaC hΨ).comp (hg.mul (continuous_scalC.comp (hs.mul hu)))).mul
    (continuous_subtype_val.comp (ω.continuous_toIdele.comp hu))

theorem continuous_thetaCInt_ltr {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι]
    [DecidableEq ι] (w : InfinitePlace k) {Ψ : (ι → 𝔸[k]) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhatPi (K := k) (ι := ι)) (ω : HeckeCharacter k) :
    Continuous fun p : {r : ℝ // 0 < r} × GL ι 𝔸[k] ↦ thetaCInt w (ltr p.2 Ψ) ω p.1 := by
  have h := GlobalTheory.CompanionTheory.EisRk1Theta.continuous_setIntegral_of_continuous_uncurry (normOneMeasure k)
    (isCompact_closure_normOneFundamentalDomain k)
    (normOneMeasure_normOneFundamentalDomain_lt_top k) (continuous_translatedIntegrand w hΨ ω)
  refine h.congr fun p ↦ ?_
  simp only [thetaCInt, thetaC_ltr, translatedIntegrand]

end GlobalTheory.CompanionTheory.EpsteinThetaC
