module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnramifiedAwayDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.PsiStdCond

theorem psi_std_conductor : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    (∀ᶠ v in cofinite, PsiUnr ψ v) ∧ ∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1 := by
  classical
  intro F _ _ ψ hψ
  refine ⟨?_, ?_⟩
  · have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ differentIdeal ℤ (𝓞 F)}.Finite :=
      Ideal.finite_factors differentIdeal_ne_bot
    refine Filter.eventually_cofinite.2 (hfin.subset fun v hv => ?_)
    by_contra h
    exact hv (GlobalTheory.StdCharUnrF.psiUnr_of_not_le F ψ hψ v fun h' => h (Ideal.dvd_iff_le.2 h'))
  · intro v
    by_contra! hcon
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
    set c : ℤ := FractionalIdeal.count F v (GlobalTheory.StdDual.codiff F) with hc
    set x : Fv F v := algebraMap F (Fv F v) (π ^ (c - 1)) with hx
    have hmem := (GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ)
      (GlobalTheory.AdelicU.singleFin v x)).2 (fun β hβ => by
        have e : β * GlobalTheory.AdelicU.singleFin v x = GlobalTheory.AdelicU.singleFin v (x * β v) := by
          apply GlobalTheory.AdelicU.af_ext
          intro u
          by_cases hu : u = v
          · subst hu
            rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
            change β u * x = x * β u
            ring
          · rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
        rw [e]
        exact hcon _)
    have h1 := (GlobalTheory.Idele.mem_adelicIdeal_iff GlobalTheory.StdDual.codiff_ne_zero).1 hmem v
    have h2 : Valued.v (GlobalTheory.AdelicU.singleFin v x v) = Valued.v x := by
      change Valued.v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ v (GlobalTheory.AdelicU.singleFin v x)) = _
      rw [GlobalTheory.AdelicU.evalV_singleFin_self]
    have h3 : Valued.v x = WithZero.exp (-(c - 1)) := by
      rw [hx, GlobalTheory.Idele.valued_algebraMap, map_zpow₀, hπ, ← WithZero.exp_zsmul]
      congr 1
      simp
    rw [← hc] at h1
    rw [h2, h3, WithZero.exp_le_exp] at h1
    omega

end GlobalTheory.PsiStdCond
