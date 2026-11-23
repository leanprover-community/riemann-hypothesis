module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExternalProductOnHermitianSumSmulLeft

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.PsiDifferent

open GlobalTheory.Idele WithZero
open scoped nonZeroDivisors
open GlobalTheory.StdDual (codiff codiff_ne_zero)

theorem not_dvd_different_of_psiUnr : ∀ {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ},
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {v : HeightOneSpectrum (𝓞 F)}, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr ψ v →
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := by
  intro F _ _ ψ hψ v hU hdvd
  have h0 : differentIdeal ℤ (𝓞 F) ≠ 0 := differentIdeal_ne_bot
  have hD : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (codiff F)⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have hcnt := FractionalIdeal.count_coe F v h0
  rw [hD, FractionalIdeal.count_inv] at hcnt
  have hne := (Associates.count_ne_zero_iff_dvd h0 v.irreducible).2 hdvd
  set c := FractionalIdeal.count F v (codiff F) with hc
  have hc1 : c ≤ -1 := by omega
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set x : Fv F v := algebraMap F (Fv F v) (π ^ c) with hx
  have hval : Valued.v x = WithZero.exp (-c) := by
    rw [hx, valued_algebraMap, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul]
    congr 1; ring
  have hmem : GlobalTheory.AdelicU.singleFin v x ∈ adelicIdeal (codiff F) := by
    refine (mem_adelicIdeal_iff codiff_ne_zero).2 fun u => ?_
    by_cases hu : u = v
    · subst hu
      rw [show (GlobalTheory.AdelicU.singleFin u x) u = x from GlobalTheory.AdelicU.evalV_singleFin_self u x, hval]
    · rw [show (GlobalTheory.AdelicU.singleFin v x) u = 0 from GlobalTheory.AdelicU.evalV_singleFin_ne hu x, map_zero]
      exact zero_le'
  rw [GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.PsiNontriv.isStd_fin_rat hψ)] at hmem
  have hint : x ∈ v.adicCompletionIntegers F := by
    refine (hU x).1 fun y hy => ?_
    have hα : ∀ u, (GlobalTheory.AdelicU.singleFin v y) u ∈ u.adicCompletionIntegers F := by
      intro u
      by_cases hu : u = v
      · subst hu
        rw [show (GlobalTheory.AdelicU.singleFin u y) u = y from GlobalTheory.AdelicU.evalV_singleFin_self u y]
        exact hy
      · rw [show (GlobalTheory.AdelicU.singleFin v y) u = 0 from GlobalTheory.AdelicU.evalV_singleFin_ne hu y]
        exact zero_mem _
    have e : GlobalTheory.AdelicU.singleFin v y * GlobalTheory.AdelicU.singleFin v x = GlobalTheory.AdelicU.singleFin v (x * y) := by
      apply GlobalTheory.AdelicU.af_ext
      intro u
      by_cases hu : u = v
      · subst hu
        rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self,
          GlobalTheory.AdelicU.evalV_singleFin_self, mul_comm]
      · rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu,
          GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
    have := hmem _ hα
    rw [e] at this
    exact this
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval, ← WithZero.exp_zero, WithZero.exp_le_exp] at hint
  omega

end GlobalTheory.PsiDifferent

end
