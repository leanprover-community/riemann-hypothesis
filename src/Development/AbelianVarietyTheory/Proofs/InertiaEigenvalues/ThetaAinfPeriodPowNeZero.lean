module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.ThetaPer

theorem thetaD_aDp_pow_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (n : ℕ), ((Per.θD l).comp (aDp l)) (τ ^ n) ≠ 0 := by
  intro l _ K bk τ hτ n
  obtain ⟨-, ε, η, hε, hφ⟩ := hτ
  have hinj : Function.Injective (WittVector.frobenius : Ainf l → Ainf l) := by
    intro x y h
    rw [WittVector.frobenius_eq_map_frobenius] at h
    exact WittVector.map_injective _ (frobeniusEquiv (OCb l) l).injective h
  have hpi : WittVector.frobenius (GlobalTheory.MemLoc.TiedUnif.piOne ε) = WittVector.teichmuller l ε - 1 := by
    rw [GlobalTheory.MemLoc.TiedUnif.piOne, map_sub, map_one, WittVector.frobenius_eq_map_frobenius]
    change WittVector.map (frobenius (OCb l) l) (WittVector.teichmuller l ((frobeniusEquiv (OCb l) l).symm ε)) - 1 = _
    rw [WittVector.map_teichmuller, frobenius_apply_frobeniusEquiv_symm]
  have hsurj : Function.Surjective (WittVector.frobenius : Ainf l → Ainf l) := by
    intro y
    obtain ⟨x, hx⟩ := WittVector.map_surjective _ (frobeniusEquiv (OCb l) l).surjective y
    exact ⟨x, by rw [WittVector.frobenius_eq_map_frobenius]; exact hx⟩
  obtain ⟨η₀, hη₀⟩ := hsurj (η : Ainf l)
  obtain ⟨η₁, hη₁⟩ := hsurj ((η⁻¹ : (Ainf l)ˣ) : Ainf l)
  have hu : η₀ * η₁ = 1 := hinj (by rw [map_mul, map_one, hη₀, hη₁, Units.mul_inv])
  have hτe : τ = η₀ * GlobalTheory.MemLoc.TiedUnif.piOne ε := hinj (by rw [hφ, map_mul, hη₀, hpi])
  set f := (Per.θD l).comp (aDp l)
  have hf0 : f η₀ ≠ 0 := by
    intro h
    have := congrArg f hu
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this
  have hf1 : f (GlobalTheory.MemLoc.TiedUnif.piOne ε) ≠ 0 := GlobalTheory.MemLoc.TiedUnif.theta_piOne hε
  rw [map_pow, hτe, map_mul]
  exact pow_ne_zero _ (mul_ne_zero hf0 hf1)

end GlobalTheory.ThetaPer
