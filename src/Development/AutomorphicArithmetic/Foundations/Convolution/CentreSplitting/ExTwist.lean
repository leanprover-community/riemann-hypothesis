module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterCentralExponentProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdelicAbsValueCpowCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExSummand
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.exTwist :
    UpperTheory.ConvolutionTheory.Dp.ExTwist := by
  intro E _ _ _ n μ _ π hn
  let x : GlobalTheory.ResW.Letter E := ⟨n, π⟩
  have hd : ((n : ℂ) * (Module.finrank ℚ E : ℂ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  let z : ℂ := -GlobalTheory.ResW.cex x / ((n : ℂ) * (Module.finrank ℚ E : ℂ))
  let χ : Formalism.L2.Host.HChar E := GlobalTheory.CuspRep.Model.absC E z
  have hspec := (GlobalTheory.ResW.letter_centralExponent E x).1
  have htr : (Matrix.of (GlobalTheory.CuspRep.oneL E n)).trace = (n : ℝ) • (1 : GlobalTheory.CuspRep.Cinf E) := by
    change (Matrix.of (fun i j : Fin n => if i = j then (1 : GlobalTheory.CuspRep.Cinf E) else 0)).trace = _
    simp [Matrix.trace, Nat.cast_smul_eq_nsmul]
  have hz : ∀ φ ∈ (π.twist χ).V, GlobalTheory.CuspRep.lie E n (GlobalTheory.CuspRep.oneL E n) φ = 0 := by
    rintro _ ⟨ψ, hψ, rfl⟩
    have e0 : GlobalTheory.CuspRep.lie E n (GlobalTheory.CuspRep.oneL E n) ψ = GlobalTheory.ResW.cex x • ψ := hspec ψ hψ
    have e1 : GlobalTheory.CuspRep.dchi χ (Matrix.of (GlobalTheory.CuspRep.oneL E n)).trace = -GlobalTheory.ResW.cex x := by
      rw [htr, map_smul, GlobalTheory.ResW.dchi_absC_one_finrank]
      have hzd : z * ((n : ℂ) * (Module.finrank ℚ E : ℂ)) = -GlobalTheory.ResW.cex x := div_mul_cancel₀ _ hd
      simp only [Complex.real_smul, Complex.ofReal_natCast]
      linear_combination hzd
    change GlobalTheory.CuspRep.lie E n (GlobalTheory.CuspRep.oneL E n) (GlobalTheory.CuspRep.mulChi n χ ψ) = 0
    rw [GlobalTheory.CuspRep.lie_mulChi, e0, e1, ← add_smul, add_neg_cancel, zero_smul, map_zero]
  obtain ⟨b, hb⟩ := GlobalTheory.AbsTwist.exists_eq_mul_log_module (F := E) (GlobalTheory.Mem.Chr.CharModel.logNorm E)
    (GlobalTheory.Mem.Chr.CharModel.continuous_logNorm E) (GlobalTheory.Mem.Chr.CharModel.logNorm_mul E)
    (GlobalTheory.Mem.Chr.CharModel.logNorm_principal E)
  refine ⟨χ, ⟨z * b, fun y => ?_⟩, _,
    (UpperTheory.ConvolutionTheory.Dp.exSummand E n μ (π.twist χ) _).2 ⟨Cm.carrier_le_central _ hz, rfl⟩⟩
  change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E y) = _
  have hpos := (GroundTheory.Global.IdeleGroup.ideleModule E y).2
  rw [hb y, Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le]
  congr 1
  push_cast
  ring
