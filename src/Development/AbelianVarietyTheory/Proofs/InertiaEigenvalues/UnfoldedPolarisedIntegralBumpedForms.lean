module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdeles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergLocalTermEqSphericalWhittakerProduc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCutOperatorTransferAdelicWhittaker
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfNotAntitoneInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerCommuteOfOneOff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerEqProdLocalDiagonal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdelicAbsDetPowDiagonalUniformizerMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.MirSet
public import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NegOneNotMemNatLat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCellPartUnfoldedIntegralPositive
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Group.End
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsuppVanishingOnEquivComplProd
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProduct
public import GroundTheory.AutomorphicForms.ReductionMeasure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedIntegrandMeasurableInvariantBounded
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Mathlib.Topology.Algebra.Group.Matrix

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdelesStatement, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelNatBumpRankinSelbergCell, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceIndicatorDiagonalUniformizerMul, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCellDecompositionLastRow, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCellDecompositionLastRowStatement, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergLocalTermEqSphericalWhittakerProducStatement, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDiagonalUniformizerEqZeroOfNotAntitone, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShintaniUnfoldedIntegrandEvalTorusCell, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedPolarisedIntegralBumpedForms

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdelesStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdelesStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdeles\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdelesStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelNatBumpRankinSelbergCell =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelNatBumpRankinSelbergCell", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.RSParams

variable {E : Type} [Field E] [NumberField E]

theorem valued_natCast (v : HeightOneSpectrum (𝓞 E)) (N : ℕ) :
    Valued.v (N : v.adicCompletion E) = v.intValuation (N : 𝓞 E) := by
  have h := v.valuedAdicCompletion_eq_valuation (K := E) (N : 𝓞 E)
  rw [v.valuation_of_algebraMap] at h
  simpa using h

theorem exists_nat (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∈ S, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ S) (k : ℕ) :
    ∃ N : ℕ, 0 < N ∧ (∀ v ∈ S, (N : 𝓞 E) ∈ v.asIdeal ^ k) ∧ ∀ v ∉ S, (N : 𝓞 E) ∉ v.asIdeal := by
  classical
  set q : HeightOneSpectrum (𝓞 E) → Ideal ℤ := fun w => Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal with hq
  have hq0 : ∀ w, q w ≠ ⊥ := fun w h => by
    have hm : ((Ideal.absNorm w.asIdeal : ℕ) : ℤ) ∈ q w := by
      rw [hq, Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at hm
    exact w.ne_bot hm
  set 𝔞 : Ideal ℤ := ∏ w ∈ S, q w with h𝔞
  set n : ℤ := Submodule.IsPrincipal.generator 𝔞 with hn
  have hspan : Ideal.span {n} = 𝔞 := Ideal.span_singleton_generator 𝔞
  have h𝔞0 : 𝔞 ≠ ⊥ := by
    rw [h𝔞, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    exact fun w _ => hq0 w
  have hn0 : n ≠ 0 := fun h => h𝔞0 (by rw [← hspan, h, Ideal.span_singleton_eq_bot])
  set N₀ : ℕ := n.natAbs with hN₀
  have hN₀q : ∀ w ∈ S, (N₀ : ℤ) ∈ q w := fun w hw => by
    have h1 : (N₀ : ℤ) ∈ 𝔞 := by
      rw [← hspan, Ideal.mem_span_singleton]
      exact Int.dvd_natAbs.2 dvd_rfl
    exact Ideal.prod_le_inf.trans (Finset.inf_le hw) h1
  refine ⟨N₀ ^ k, pow_pos (Int.natAbs_pos.2 hn0) k, fun v hv => ?_, fun v hv h => ?_⟩
  · have h1 : (N₀ : 𝓞 E) ∈ v.asIdeal := by
      have := hN₀q v hv
      rwa [hq, Ideal.mem_comap, map_natCast] at this
    rw [Nat.cast_pow]
    exact Ideal.pow_mem_pow h1 k
  · rw [Nat.cast_pow] at h
    have h1 : (N₀ : 𝓞 E) ∈ v.asIdeal := v.isPrime.mem_of_pow_mem k h
    have h2 : (N₀ : ℤ) ∈ q v := by rwa [hq, Ideal.mem_comap, map_natCast]
    have h3 : n ∈ q v := by
      obtain ⟨c, hc⟩ := (Int.natAbs_dvd.2 (dvd_refl n) : (N₀ : ℤ) ∣ n)
      rw [hc]
      exact Ideal.mul_mem_right _ _ h2
    haveI hp : (q v).IsPrime := Ideal.comap_isPrime _ _
    have h4 : 𝔞 ≤ q v := by rw [← hspan, Ideal.span_singleton_le_iff_mem]; exact h3
    obtain ⟨w, hw, hle⟩ := (Ideal.IsPrime.prod_le hp).1 h4
    have hmax : (q w).IsMaximal := (Ideal.comap_isPrime _ w.asIdeal).isMaximal (hq0 w)
    have heq : q w = q v := hmax.eq_of_le hp.ne_top hle
    exact hv (hS w hw v heq.symm)

variable [_root_.NumberField.IsTotallyComplex E]

theorem mem_natLat_iff {N : ℕ} (hN : 0 < N) (z : Af E) :
    z ∈ GlobalTheory.RSJ.natLat E N ↔ ∀ v : HeightOneSpectrum (𝓞 E), Valued.v (z v) ≤ Valued.v (N : v.adicCompletion E) := by
  constructor
  · rintro ⟨y, hy, rfl⟩ v
    change Valued.v ((N : v.adicCompletion E) * y v) ≤ _
    rw [map_mul]
    exact mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hy v))
  · intro h
    set c : Af E := algebraMap E (Af E) ((N : E)⁻¹) with hc
    have hcN : c * (N : Af E) = 1 := by
      rw [hc, ← map_natCast (algebraMap E (Af E)), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one]
    refine ⟨z * c, fun v => ?_, ?_⟩
    · have e : c v * (N : v.adicCompletion E) = 1 := congrArg (fun x : Af E => x v) hcN
      have e' : Valued.v (c v) * Valued.v (N : v.adicCompletion E) = 1 := by rw [← map_mul, e, map_one]
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (z v * c v) ≤ 1
      rw [map_mul, ← e', mul_comm (Valued.v (c v))]
      exact mul_le_mul_of_nonneg_right (h v) zero_le'
    · calc z = z * (c * (N : Af E)) := by rw [hcN, mul_one]
        _ = (N : Af E) * (z * c) := by ring

end GlobalTheory.RSParams


open GlobalTheory.RSParams in
theorem GlobalTheory.RSParams.exists_level_nat_bump : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∈ S, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ S) →
    ∀ V : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (V : Set (GL (Fin (m + 1)) (Af E))) →
    (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), locGL E (m + 1) w k ∈ V) →
    ∃ (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ (Pi.single (Fin.last m) 1) ≠ 0 ∧
      (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) ∧
      GlobalTheory.RSLocalPart.levelAt (m + 1) S J ⊆ V ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) ∧
      (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) := by
  intro E _ _ _ m S hS V hV hw
  classical
  obtain ⟨J, hJS, -, hJV⟩ := GlobalTheory.RSLocalPart.exists_levelAt_subset S V hV hw
  set k : ℕ := ∑ v ∈ S, (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat with hk
  obtain ⟨N, hN, hNS, hNc⟩ := exists_nat S hS k
  have hv1 : ∀ v : HeightOneSpectrum (𝓞 E), Valued.v (N : v.adicCompletion E) ≤ 1 := fun v => by
    rw [valued_natCast]; exact v.intValuation_le_one _
  have hvS : ∀ v ∈ S, Valued.v (N : v.adicCompletion E) ≤
      WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) := fun v hv => by
    rw [valued_natCast]
    refine ((v.intValuation_le_pow_iff_mem _ k).2 (hNS v hv)).trans (WithZero.exp_le_exp.2 ?_)
    have h1 : FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E) ≤
        ((FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat : ℤ) := Int.self_le_toNat _
    have h2 : (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat ≤ k :=
      Finset.single_le_sum (f := fun v => (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat)
        (fun _ _ => Nat.zero_le _) hv
    omega
  have hvn : ∀ v ∉ S, Valued.v (N : v.adicCompletion E) = 1 := fun v hv => by
    rw [valued_natCast]
    exact le_antisymm (v.intValuation_le_one _) (not_lt.1 fun h => hNc v hv ((v.intValuation_lt_one_iff_mem _).1 h))
  have he : (Pi.single (Fin.last m) 1 : Fin (m + 1) → Cinf E) ∈ GlobalTheory.RSTheta.rowSet E (Fin.last m) := fun w => by
    simp
  obtain ⟨ρ, hts, hcs, hcd, hr, h1⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    ((GlobalTheory.RSTheta.isOpen_rowSet (E := E) (Fin.last m)).mem_nhds he)
  have hr' : ∀ u, ρ u ∈ Set.Icc (0 : ℝ) 1 := fun u => hr ⟨u, rfl⟩
  refine ⟨N, J, fun u => (ρ u : ℂ), hN, Complex.ofRealCLM.contDiff.comp hcd, hcs.comp_left Complex.ofReal_zero,
    (tsupport_comp_subset Complex.ofReal_zero ρ).trans hts, fun u => ⟨by simpa using (hr' u).1, by simp⟩,
    by simp [h1], hJS, hJV, fun z hz v => ?_, fun z hz v hv => ?_, fun z z' hzz hz hz' => ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact ((mem_natLat_iff hN z).1 hz v).trans (hv1 v)
  · exact ((mem_natLat_iff hN z).1 hz v).trans (hvS v hv)
  · rw [mem_natLat_iff hN, mem_natLat_iff hN]
    refine forall_congr' fun v => ?_
    by_cases hv : v ∈ S
    · rw [hzz v hv]
    · rw [hvn v hv]
      exact ⟨fun _ => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hz' v hv),
        fun _ => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hz v hv)⟩
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelNatBumpRankinSelbergCell =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceIndicatorDiagonalUniformizerMul =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceIndicatorDiagonalUniformizerMul", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.CellLastRow

open GlobalTheory.CellDec GlobalTheory.ZEul

variable {E : Type} [Field E] [NumberField E]

theorem one_lt_v_zpow {v : HeightOneSpectrum (𝓞 E)} {ϖ : v.adicCompletion E} (h : IsUnifV E v ϖ) {a : ℤ}
    (ha : a < 0) : 1 < Valued.v (ϖ ^ a) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = -((n + 1 : ℕ) : ℤ) := ⟨(-a - 1).toNat, by omega⟩
  have h0 : ϖ ≠ 0 := fun e => by simp [IsUnifV, e] at h
  have h1 : Valued.v ϖ < 1 := by
    rw [h]; exact (by decide : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1)
  rw [zpow_neg, zpow_natCast, map_inv₀, map_pow]
  have hp : Valued.v ϖ ^ (n + 1) < 1 := pow_lt_one₀ zero_le' h1 (Nat.succ_ne_zero n)
  have hp0 : Valued.v ϖ ^ (n + 1) ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).2 h0)
  exact (one_lt_inv₀ (zero_lt_iff.2 hp0)).2 hp

end GlobalTheory.CellLastRow

namespace GlobalTheory.CellLastRow

open GlobalTheory.CellDec GlobalTheory.ZEul

theorem indN_lastRow_tl : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ N : ℕ,
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) →
    (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) →
    ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) S), ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S,
    ((∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) =
        GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i))) ∧
    ((∃ w, l.1 w (Fin.last m) < 0) →
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) = 0) := by
  intro E _ _ _ m S ϖ hϖ N hlat hloc l g hg
  obtain ⟨u, hu, k, hk, rfl⟩ := hg
  have hk' : ∀ v ∉ S, compV E (m + 1) v k ∈ GlobalTheory.LFun.KGL v (n := (m + 1)) := by
    simpa only [US, Subgroup.mem_iInf, Subgroup.mem_comap] using hk
  set c : (Af E)ˣ := adl ϖ (Finsupp.mapRange (fun x : Fin (m + 1) → ℤ => x (Fin.last m)) rfl l.1) with hc
  have hev : ∀ (x : Af E) v, x v = pLoc E v x := fun _ _ => rfl
  have hcv : ∀ v, pLoc E v (c : Af E) = ((ϖ v ^ l.1 v (Fin.last m) : (v.adicCompletion E)ˣ) : v.adicCompletion E) := by
    intro v
    change ((ϖ v ^ (Finsupp.mapRange (fun x : Fin (m + 1) → ℤ => x (Fin.last m)) rfl l.1) v :
      (v.adicCompletion E)ˣ) : v.adicCompletion E) = _
    rw [Finsupp.mapRange_apply]
  have hrow : ∀ i, lastRow (u * k) i = (k : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) i := by
    intro i
    have := congrFun (GlobalTheory.RSLocalPart.single_vecMul_unip (ℓ := Fin.last m) (fun j => Fin.le_last j) hu k) i
    simpa [lastRow, Units.val_mul, Matrix.single_one_vecMul] using this
  have hrow' : ∀ i, GlobalTheory.RSJ.pFin E (lastRow (tl (m + 1) ϖ l.1 * (u * k)) i) =
      (c : Af E) * GlobalTheory.RSJ.pFin E (lastRow (u * k) i) := by
    intro i
    simp only [lastRow, tl_eq_diagT, Units.val_mul, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_mul, map_mul]
    congr 1
    change GlobalTheory.RSJ.pFin E (1 - sFin E 1 + sFin E (c : Af E)) = _
    rw [map_add (f := _), map_sub, map_one]
    change 1 - 1 + (c : Af E) = _
    ring
  have hcomp : ∀ v i, pLoc E v (GlobalTheory.RSJ.pFin E (lastRow (u * k) i)) = (compV E (m + 1) v k).val (Fin.last m) i := by
    intro v i; rw [hrow]; rfl
  have hint : ∀ v ∉ S, ∀ i j, (compV E (m + 1) v k).val i j ∈ v.adicCompletionIntegers E := by
    intro v hv i j
    obtain ⟨k0, hk0⟩ := hk' v hv
    rw [← hk0]
    exact (k0.val i j).2
  have hinv : ∀ v ∉ S, ∀ i j, ((compV E (m + 1) v k)⁻¹).val i j ∈ v.adicCompletionIntegers E := by
    intro v hv i j
    obtain ⟨k0, hk0⟩ := hk' v hv
    rw [← hk0, ← map_inv]
    exact ((k0⁻¹).val i j).2
  have hδ : ∀ v (i : Fin (m + 1)), pLoc E v (if (i : ℕ) + 1 = m + 1 then (1 : Af E) else 0) ∈ v.adicCompletionIntegers E := by
    intro v i
    split_ifs
    · rw [map_one]; exact one_mem _
    · rw [map_zero]; exact zero_mem _
  refine ⟨fun hpos => ?_, fun ⟨w, hw⟩ => ?_⟩
  · have key : ∀ i : Fin (m + 1),
        (GlobalTheory.RSJ.pFin E (lastRow (tl (m + 1) ϖ l.1 * (u * k)) i) - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈
          GlobalTheory.RSJ.natLat E N ↔
        GlobalTheory.RSJ.pFin E (lastRow (u * k) i) - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈ GlobalTheory.RSJ.natLat E N) := by
      intro i
      refine (hloc _ _ (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_)).symm
      · rw [hev, hev, map_sub, map_sub, hrow', map_mul, hcv, l.2 v hv]
        simp
      · rw [hev, map_sub, hcomp]
        exact sub_mem (hint v hv _ _) (hδ v i)
      · rw [hev, map_sub, hrow', map_mul, hcomp, hcv]
        refine sub_mem (mul_mem ?_ (hint v hv _ _)) (hδ v i)
        rw [Units.val_zpow_eq_zpow_val, ← Int.toNat_of_nonneg (hpos v), zpow_natCast]
        exact pow_mem (GlobalTheory.LFun.mem_Ov_of_isUnifV (hϖ v)) _
    unfold GlobalTheory.RSJ.indN
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (fun i => (key i).1 (h1 i)) h2
    · exact absurd (fun i => (key i).2 (h2 i)) h1
    · rfl
  · have hwS : w ∉ S := fun h => by
      have h0 := l.2 w h
      rw [h0] at hw
      exact lt_irrefl _ hw
    have hex : ∃ j, ¬ Valued.v ((compV E (m + 1) w k).val (Fin.last m) j) < 1 := by
      by_contra hcon
      push_neg at hcon
      have h1 : ((compV E (m + 1) w k).val * ((compV E (m + 1) w k)⁻¹).val) (Fin.last m) (Fin.last m) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
      rw [Matrix.mul_apply] at h1
      have h2 : Valued.v (∑ j, (compV E (m + 1) w k).val (Fin.last m) j * ((compV E (m + 1) w k)⁻¹).val j (Fin.last m)) < 1 := by
        refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
        rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (hcon j) (hinv w hwS j (Fin.last m))
      rw [h1, map_one] at h2
      exact lt_irrefl _ h2
    obtain ⟨j, hj⟩ := hex
    have hj1 : Valued.v ((compV E (m + 1) w k).val (Fin.last m) j) = 1 :=
      le_antisymm (hint w hwS _ _) (not_lt.1 hj)
    unfold GlobalTheory.RSJ.indN
    rw [if_neg]
    intro hall
    have hz := hlat _ (hall j) w
    dsimp only at hz
    rw [hev, map_sub, hrow', map_mul, hcomp, hcv] at hz
    have ha := add_mem hz (hδ w j)
    rw [sub_add_cancel, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hj1, mul_one,
      Units.val_zpow_eq_zpow_val] at ha
    exact not_le.2 (one_lt_v_zpow (hϖ w) hw) ha

end GlobalTheory.CellLastRow
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceIndicatorDiagonalUniformizerMul =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCellDecompositionLastRow =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCellDecompositionLastRow", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.ZEul

open Matrix

theorem decomp_lastRow : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
    (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) → ∀ N : ℕ,
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) →
    ∀ Φ : (Fin (m + 1) → Cinf E) → ℂ, tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 →
    GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 →
    ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∃ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J,
      g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = u * p * finGL E (m + 1) κ := by
  intro E _ _ _ m S J hJ N hN Φ hs g hg hΦ hind
  have hrow : ∀ h : GA E (m + 1), Pi.single (Fin.last m) 1 ᵥ* h.val = fun j => GlobalTheory.ZEul.lastRow h j := fun h => by
    rw [Matrix.single_one_vecMul]; rfl
  have hℓ : ∀ i : Fin (m + 1), i ≤ Fin.last m := Fin.le_last
  have hi : (fun i => pInf E ((Pi.single (Fin.last m) 1 ᵥ* g.val) i)) ∈ GlobalTheory.RSTheta.rowSet E (Fin.last m) := by
    rw [hrow]; exact hs (subset_tsupport _ hΦ)
  have hind' : ∀ i : Fin (m + 1), GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i) - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈
      GlobalTheory.RSJ.natLat E N := by
    by_contra hc
    exact hind (by rw [GlobalTheory.RSJ.indN, if_neg hc])
  have hf : ∀ v ∈ S, ∀ j, Valued.v ((pFin E ((Pi.single (Fin.last m) 1 ᵥ* g.val) j) -
      (Pi.single (Fin.last m) 1 : Fin (m + 1) → Af E) j) v) ≤
      WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) := by
    intro v hv j
    rw [hrow]
    have e : (Pi.single (Fin.last m) 1 : Fin (m + 1) → Af E) j = if (j : ℕ) + 1 = m + 1 then 1 else 0 := by
      rw [Pi.single_apply]
      congr 1
      simp [Fin.ext_iff]
    rw [e]
    exact hN _ (hind' j) v hv
  obtain ⟨u, hu, p, hp, κ, hκ, e⟩ := GlobalTheory.RSLocalPart.exists_decomp hℓ hJ hg hi hf
  refine ⟨u, (GlobalTheory.SmGL.mem_unipB _).1 hu, p, ⟨hp.2, hp.1⟩, κ, hκ, ?_⟩
  rw [← e, hrow]
  congr 1
  rw [hrow] at hi
  have hu' := GlobalTheory.RSTheta.isUnit_of_mem_rowSet hi
  rw [← map_inv]
  congr 1
  have hm : GlobalTheory.RSJ.secRow (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) =
      GlobalTheory.RSTheta.rowMat (Fin.last m) (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) := by
    ext i j
    simp only [GlobalTheory.RSJ.secRow, GlobalTheory.RSTheta.rowMat, Matrix.of_apply, Matrix.updateRow_apply]
    simp [Fin.ext_iff]
  have hd : IsUnit (GlobalTheory.RSJ.secRow (fun i => pInf E (GlobalTheory.ZEul.lastRow g i))).det := by
    rw [hm, GlobalTheory.RSTheta.det_rowMat]; exact hu'
  rw [GlobalTheory.RSJ.secInv, dite_eq_left hd]
  congr 1
  exact Units.ext (hm.trans (GlobalTheory.RSTheta.val_rowGL hu').symm)

end GlobalTheory.ZEul
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCellDecompositionLastRow =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCellDecompositionLastRowStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCellDecompositionLastRowStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCellDecompositionLastRow\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCellDecompositionLastRowStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergLocalTermEqSphericalWhittakerProducStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergLocalTermEqSphericalWhittakerProducStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergLocalTermEqSphericalWhittakerProduc\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergLocalTermEqSphericalWhittakerProducStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDiagonalUniformizerEqZeroOfNotAntitone =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDiagonalUniformizerEqZeroOfNotAntitone", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCutOperatorTransferAdelicWhittaker\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfNotAntitoneInt\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.CellVanish

theorem eq_zero_of_not_antitone : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (w : HeightOneSpectrum (𝓞 E)), w ∉ S →
    (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), IsUnifV E w (ϖ w : w.adicCompletion E) →
    ∀ (W : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, W (g * finGL E (m + 1) κ) = W g) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ)), ¬ Antitone (l w) →
    ∀ p : GA E (m + 1), Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p = 1 →
    W (p * GlobalTheory.CellDec.tl (m + 1) ϖ l) = 0 := by
  intro E _ _ _ m S J w hwS hψ ϖ hϖ W hWN hWK l hl p hp
  set t := GlobalTheory.CellDec.tl (m + 1) ϖ l with ht
  set D : GL (Fin (m + 1)) (w.adicCompletion E) := GlobalTheory.CellDec.compV E (m + 1) w t with hD
  have hDv : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) =
      Matrix.diagonal fun a => ((ϖ w ^ l w a : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    rw [hD, ht, GlobalTheory.CellDec.tl, GlobalTheory.CellDec.compV_finGL]
    refine Matrix.ext fun i j => ?_
    change pLoc E w (((GlobalTheory.SmGL.diagT (Af E) (Fin (m + 1)) _ : GL (Fin (m + 1)) (Af E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) i j) = _
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin (m + 1) → ℤ => x i) rfl l) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  set t' := t * (finGL E (m + 1) (locGL E (m + 1) w D))⁻¹ with ht'
  have ht'w : Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t' = 1 := by
    change GlobalTheory.CellDec.compV E (m + 1) w t' = 1
    rw [ht', map_mul, map_inv, GlobalTheory.CellDec.compV_finGL_locGL_same, ← hD, mul_inv_cancel]
  have htt : t' * finGL E (m + 1) (locGL E (m + 1) w D) = t := by rw [ht', inv_mul_cancel_right]
  have hlev : ∀ k ∈ GlobalTheory.LFun.KGL w (n := (m + 1)), locGL E (m + 1) w k ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J := by
    intro k hk
    refine ⟨fun v => ?_, fun v hv i j => ?_⟩
    · by_cases hvw : v = w
      · subst hvw; rw [pLoc_locGL]; exact hk
      · rw [pLoc_locGL_of_ne hvw]; exact one_mem _
    · have hvw : v ≠ w := fun h => hwS (h ▸ hv)
      have h1 := congrArg (fun x : GL (Fin (m + 1)) (v.adicCompletion E) => (x : Matrix (Fin (m + 1)) (Fin (m + 1)) (v.adicCompletion E)) i j)
        (pLoc_locGL_of_ne hvw k)
      have h0 : ((locGL E (m + 1) w k).val - 1) i j v = 0 := by
        change pLoc E v (((locGL E (m + 1) w k).val - 1) i j) = 0
        rw [Matrix.sub_apply, map_sub]
        change (Matrix.GeneralLinearGroup.map (pLoc E v) (locGL E (m + 1) w k)).val i j - _ = 0
        rw [h1]
        simp [Matrix.one_apply]
      rw [h0, map_zero]
      exact zero_le'
  let f : GL (Fin (m + 1)) (w.adicCompletion E) → ℂ := fun g => W (p * t' * finGL E (m + 1) (locGL E (m + 1) w g))
  have hfD : f D = W (p * t) := by
    simp only [f]
    rw [mul_assoc, htt]
  have hpt : Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (p * t') = 1 := by
    rw [map_mul, hp, ht'w, mul_one]
  have hfN : ∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin (m + 1)), ∀ g,
      f (u * g) = GlobalTheory.JSW.psiLocChar w (GlobalTheory.Whittaker.superDiag u) * f g := by
    intro u hu g
    simp only [f]
    rw [map_mul, map_mul, ← mul_assoc (p * t'), GlobalTheory.JSW.commute_finGL_locGL w hpt, mul_assoc,
      hWN _ (GlobalTheory.JSW.CutTransfer.finGL_locGL_mem_NA' w hu), GlobalTheory.JSW.CutTransfer.psiN_finGL_locGL]
    rfl
  have hfK : ∀ g, ∀ k ∈ GlobalTheory.LFun.KGL w (n := (m + 1)), f (g * k) = f g := by
    intro g k hk
    simp only [f]
    rw [map_mul, map_mul, ← mul_assoc]
    exact hWK _ (hlev k hk) _
  have h := GlobalTheory.WhitTorus.eq_zero_of_not_antitone_int E w (m + 1) (GlobalTheory.JSW.psiLocChar w) hψ f hfN hfK (ϖ w) hϖ (l w) hl D hDv
  rwa [hfD] at h

end GlobalTheory.CellVanish
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDiagonalUniformizerEqZeroOfNotAntitone =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShintaniUnfoldedIntegrandEvalTorusCell =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShintaniUnfoldedIntegrandEvalTorusCell", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerCommuteOfOneOff\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerEqProdLocalDiagonal\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdelicAbsDetPowDiagonalUniformizerMul\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceIndicatorDiagonalUniformizerMul\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCellDecompositionLastRowStatement\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergLocalTermEqSphericalWhittakerProducStatement\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDiagonalUniformizerEqZeroOfNotAntitone\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.ZEul

theorem detPow_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (g : GA E n),
    GlobalTheory.RSJ.detPow E n 0 g = 1 := by
  intro E _ _ _ n g
  simp [GlobalTheory.RSJ.detPow, chiDet, GlobalTheory.HeckeGal.Model.absPow, GlobalTheory.Mem.Chr.CharModel.absHom_val]

theorem pInf_lastRow_tl_mul : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ))
    (g : GA E (m + 1)),
    (fun i => pInf E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l * g) i)) = fun i => pInf E (GlobalTheory.ZEul.lastRow g i) := by
  intro E _ _ _ m ϖ l g
  funext i
  have h := congrArg (fun M : GL (Fin (m + 1)) (Cinf E) => (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) i)
    (show Matrix.GeneralLinearGroup.map (pInf E) (GlobalTheory.CellDec.tl (m + 1) ϖ l * g) =
      Matrix.GeneralLinearGroup.map (pInf E) g by rw [map_mul, GlobalTheory.CellDec.tl, pInf_finGL, one_mul])
  exact h

theorem uInt_cell_eval : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (b : GA E (m + 1) → ℂ) (α α' : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ) (φ φ' : GA E (m + 1) → ℂ)
      (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ),
    (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) →
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) →
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) →
    (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) →
    tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, GlobalTheory.JSW.whit φ (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, GlobalTheory.JSW.whit φ' (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ' g) →
    (∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m),
      GlobalTheory.JSW.whit φ (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)) →
    (∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m),
      GlobalTheory.JSW.whit φ' (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α' w i : ℂ)) (l w)) →
    ∀ x : ℝ, ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S,
      GlobalTheory.ZEul.uInt φ φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g ∧ GlobalTheory.ZEul.uInt φ' φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g ∧
      ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S,
        (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) * GlobalTheory.ZEul.uInt φ φ' Φ N x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
          (l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ)) (fun i => (α' w i : ℂ)) x v) *
            GlobalTheory.ZEul.uInt φ φ Φ N 0 g * (GlobalTheory.RSJ.detPow E (m + 1) x g : ℂ) := by
  intro E _ _ _ m S hψ ϖ hϖ b α α' φ φ' N J Φ hJ hint hS hloc hΦ hNφ hNφ' hKφ hKφ' hWφ hWφ' x g hg
  have hWp : ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit φ p = b p ∧ GlobalTheory.JSW.whit φ' p = b p := by
    intro p hp
    have h0 : GlobalTheory.JSW.tl ϖ (0 : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ)) = 1 := by simp [GlobalTheory.JSW.tl]
    have e1 := hWφ 0 (by simp) p hp
    have e2 := hWφ' 0 (by simp) p hp
    rw [h0, mul_one] at e1 e2
    simp only [Finsupp.support_zero, Finset.prod_empty, mul_one] at e1 e2
    exact ⟨e1, e2⟩
  have hnorm : ∀ u : GA E (m + 1), ‖GlobalTheory.JSW.psiN u‖ = 1 := fun u => Circle.norm_coe _
  have hcc : ∀ c : ℂ, ‖c‖ = 1 → ∀ z z' : ℂ, c * z * conj (c * z') = z * conj z' := by
    intro c hc z z'
    rw [map_mul]
    have : c * conj c = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
    calc c * z * (conj c * conj z') = (c * conj c) * (z * conj z') := by ring
      _ = _ := by rw [this, one_mul]
  have hzero : ∀ F F' : GA E (m + 1) → ℂ, Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = 0 ∨
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) = 0 → GlobalTheory.ZEul.uInt F F' Φ N 0 g = 0 := by
    intro F F' h
    rcases h with h | h <;> simp only [GlobalTheory.ZEul.uInt, h, mul_zero, zero_mul]
  have hdec : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 →
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∃ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J,
        g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = u * p * finGL E (m + 1) κ ∧
        GlobalTheory.ZEul.uInt φ φ' Φ N 0 g = b p * conj (b p) * Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) *
          GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) ∧
        GlobalTheory.ZEul.uInt φ φ Φ N 0 g = b p * conj (b p) * Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) *
          GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) ∧
        GlobalTheory.ZEul.uInt φ' φ' Φ N 0 g = b p * conj (b p) * Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) *
          GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) := by
    intro h1 h2
    obtain ⟨u, hu, p, hp, κ, hκ, he⟩ := _root_.GlobalTheory.ZEul.decomp_lastRow E m S J hJ N hS Φ hΦ g hg h1 h2
    have k1 : GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) =
        GlobalTheory.JSW.psiN u * b p := by rw [he, hKφ κ hκ, hNφ u hu, (hWp p hp).1]
    have k2 : GlobalTheory.JSW.whit φ' (g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) =
        GlobalTheory.JSW.psiN u * b p := by rw [he, hKφ' κ hκ, hNφ' u hu, (hWp p hp).2]
    refine ⟨u, hu, p, hp, κ, hκ, he, ?_, ?_, ?_⟩ <;>
      simp only [GlobalTheory.ZEul.uInt, k1, k2, hcc _ (hnorm u), GlobalTheory.ZEul.detPow_zero, Complex.ofReal_one, mul_one]
  have h12 : GlobalTheory.ZEul.uInt φ φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g ∧
      GlobalTheory.ZEul.uInt φ' φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g := by
    by_cases h0 : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = 0 ∨
        GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) = 0
    · rw [hzero _ _ h0, hzero _ _ h0, hzero _ _ h0]; exact ⟨rfl, rfl⟩
    push_neg at h0
    obtain ⟨-, -, p, -, -, -, -, e1, e2, e3⟩ := hdec h0.1 h0.2
    rw [e1, e2, e3]; exact ⟨rfl, rfl⟩
  refine ⟨h12.1, h12.2, fun l => ?_⟩

  have hyt := GlobalTheory.ZEul.pInf_lastRow_tl_mul E m ϖ l.1 g
  obtain ⟨hind1, hind2⟩ := _root_.GlobalTheory.CellLastRow.indN_lastRow_tl E m S ϖ hϖ N hint hloc l g hg
  have hdt := _root_.GlobalTheory.CellEvalDet.detPow_tl_mul E (m + 1) ϖ hϖ l.1 x g
  have hL : GlobalTheory.ZEul.uInt φ φ' Φ N x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
      GlobalTheory.JSW.whit φ (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g *
        infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) *
      conj (GlobalTheory.JSW.whit φ' (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g *
        infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)))) *
      Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) *
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) *
      (GlobalTheory.RSJ.detPow E (m + 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) : ℂ) := by
    simp only [GlobalTheory.ZEul.uInt]; rw [hyt]
  rw [hL]
  have hprod0 : ∀ w ∈ l.1.support, GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
      (fun i => (α' w i : ℂ)) x (l.1 w) = 0 →
      (l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
        (fun i => (α' w i : ℂ)) x v) = 0 :=
    fun w hw h => Finset.prod_eq_zero hw h
  by_cases hz : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = 0 ∨
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) = 0
  · have hIt : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = 0 ∨
        GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) = 0 := by
      rcases hz with h | h
      · exact Or.inl h
      · right
        by_cases hl : ∀ w, 0 ≤ l.1 w (Fin.last m)
        · rw [hind1 hl, h]
        · push_neg at hl; exact hind2 hl
    rw [hzero φ φ hz]
    rcases hIt with h | h <;> simp [h]
  push_neg at hz
  by_cases hlast : ∀ w, 0 ≤ l.1 w (Fin.last m)
  swap
  · push_neg at hlast
    obtain ⟨w, hw⟩ := hlast
    have hws : w ∈ l.1.support := by
      rw [Finsupp.mem_support_iff]; intro h0; rw [h0] at hw; simp at hw
    rw [hind2 ⟨w, hw⟩, hprod0 w hws ?_]
    · simp
    · rw [GlobalTheory.ZEul.rsTerm, if_neg]; rintro ⟨h1, -⟩; exact absurd (h1 (Fin.last m)) (not_le.2 hw)
  rw [hind1 hlast]
  obtain ⟨u, hu, p, hp, κ, hκ, he, -, e0, -⟩ := hdec hz.1 hz.2
  rw [e0]
  set t := GlobalTheory.CellDec.tl (m + 1) ϖ l.1 with ht
  have hcomm : p * t = t * p := _root_.GlobalTheory.CellDec.TlComm.tl_commute_of_one_off E (m + 1) S ϖ l p hp.1
  have hu' : t * u * t⁻¹ ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)) :=
    (GlobalTheory.SmGL.mem_unipB (Ad E)).1 (GlobalTheory.CellDec.tl_conj_mem ϖ l.1 ((GlobalTheory.SmGL.mem_unipB (Ad E)).2 hu))
  have hσ : t * g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) =
      (t * u * t⁻¹) * (p * t) * finGL E (m + 1) κ := by
    rw [mul_assoc t g, he, hcomm]; group
  have hW : ∀ F : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, F (u * g) = GlobalTheory.JSW.psiN u * F g) →
      (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, F (g * finGL E (m + 1) κ) = F g) →
      F (t * g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) =
        GlobalTheory.JSW.psiN (t * u * t⁻¹) * F (p * t) := by
    intro F hN hK; rw [hσ, hK κ hκ, hN _ hu']
  rw [hW _ hNφ hKφ, hW _ hNφ' hKφ', hcc _ (hnorm _)]
  by_cases hanti : ∀ w, Antitone (l.1 w)
  swap
  · push_neg at hanti
    obtain ⟨w, hw⟩ := hanti
    have hw0 : l.1 w ≠ 0 := by rintro h0; rw [h0] at hw; exact hw antitone_const
    have hwS : w ∉ S := fun h => hw0 (l.2 w h)
    have hws : w ∈ l.1.support := Finsupp.mem_support_iff.2 hw0
    rw [_root_.GlobalTheory.CellVanish.eq_zero_of_not_antitone E m S J w hwS (hψ w hwS) ϖ (hϖ w) (GlobalTheory.JSW.whit φ) hNφ hKφ l.1 hw p (hp.1 w hwS), hprod0 w hws ?_]
    · simp
    · rw [GlobalTheory.ZEul.rsTerm, if_neg]; rintro ⟨-, h2⟩; exact hw h2
  have hnn : ∀ w i, 0 ≤ l.1 w i := fun w i => le_trans (hlast w) (hanti w (Fin.le_last i))
  obtain ⟨l', hl'app⟩ : ∃ l' : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), ∀ w, l' w = fun i => (l.1 w i).toNat :=
    ⟨Finsupp.mapRange (fun v i => (v i).toNat) (funext fun _ => rfl) l.1, fun w => Finsupp.mapRange_apply⟩
  have hl' : ∀ w i, ((l' w i : ℕ) : ℤ) = l.1 w i := fun w i => by
    rw [hl'app]; exact Int.toNat_of_nonneg (hnn w i)
  have hsupp : l'.support = l.1.support := by
    ext w
    simp only [Finsupp.mem_support_iff, ne_eq]
    constructor
    · intro h h0; apply h; rw [hl'app, h0]; rfl
    · intro h h0; apply h; funext i; have := hl' w i; rw [h0] at this; simpa using this.symm
  have htl : t = GlobalTheory.JSW.tl ϖ l' := _root_.GlobalTheory.CellDecNat.tl_eq_jsw_tl E (m + 1) ϖ l.1 l' hl'
  have hsS : ∀ w ∈ l'.support, w ∉ S := fun w hw hS' => by
    rw [hsupp, Finsupp.mem_support_iff] at hw; exact hw (l.2 w hS')
  rw [hdt, htl, hWφ l' hsS p hp, hWφ' l' hsS p hp, hsupp]
  have key : ((GlobalTheory.CellDec.dinv (m + 1) l.1 : ℝ) : ℂ) *
      ((∏ w ∈ l.1.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l' w)) *
        conj (∏ w ∈ l.1.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α' w i : ℂ)) (l' w))) *
      (((∏ w ∈ l.1.support, (qV E w : ℝ) ^ (-x * ∑ i, (l.1 w i : ℝ))) : ℝ) : ℂ) =
      l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
        (fun i => (α' w i : ℂ)) x v := by
    rw [map_prod, ← Finset.prod_mul_distrib, GlobalTheory.CellDec.dinv, Complex.ofReal_prod, Complex.ofReal_prod,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, Finsupp.prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hq : 0 < qV E w := Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    rw [hl'app]
    exact _root_.GlobalTheory.ZEulLocal.localTerm_eq (qV E w) hq (m + 1) _ _ x (l.1 w) (hnn w) (hanti w)
  rw [← key]
  simp only [map_mul, Complex.ofReal_mul]
  ring

end GlobalTheory.ZEul
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShintaniUnfoldedIntegrandEvalTorusCell =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedPolarisedIntegralBumpedForms =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedPolarisedIntegralBumpedForms", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir\npublic import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.MirSet\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NegOneNotMemNatLat\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdelesStatement\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCellPartUnfoldedIntegralPositive\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelNatBumpRankinSelbergCell\npublic import Mathlib.Algebra.BigOperators.Finsupp.Basic\npublic import Mathlib.Algebra.Group.End\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsuppVanishingOnEquivComplProd\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProduct\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShintaniUnfoldedIntegrandEvalTorusCell\npublic import GroundTheory.AutomorphicForms.ReductionMeasure\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedIntegrandMeasurableInvariantBounded\nimport Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenAdelicUnipotentTimesIntegralOutsideSet\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Algebra.Group.Matrix\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

namespace GlobalTheory.ZEul

set_option synthInstance.maxHeartbeats 100000 in
theorem unfolded_bump_eq :
∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
  (∀ w ∈ S, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal = Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ S) →
  (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
  ∀ b : GA E (m + 1) → ℂ, b 1 = 1 → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) →
  (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) →
  ∀ (π π' : CuspSub E (m + 1)) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → π.HasCentChar ω → π'.HasCentChar ω' →
  ∀ (α α' : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ),
  (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) →
  (∀ w ∉ S, HasSatGL w (π'.locRep w) (Finset.univ.val.map (α' w))) →
  ∀ φ φ' : GA E (m + 1) → ℂ, φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
  (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
      ∀ u ∈ U, ∀ g, φ (g * finGL E (m + 1) u) = φ g) →
  (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, φ (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ g) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
      ∀ u ∈ U, ∀ g, φ' (g * finGL E (m + 1) u) = φ' g) →
  (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, φ' (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ' g) →
  (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m),
      GlobalTheory.JSW.whit φ (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)) →
  (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m),
      GlobalTheory.JSW.whit φ' (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α' w i : ℂ)) (l w)) →
  φ ≠ 0 ∧ φ' ≠ 0 ∧ ∃ (N : ℕ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N ∧ ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
    tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) ∧ (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧
  ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
    IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
   ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
    0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
   ∀ x : ℝ, 1 < x →
     GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal) (fun w i => (α w.1 i : ℂ)) x ≠ ⊤ →
     GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal) (fun w i => (α' w.1 i : ℂ)) x ≠ ⊤ →
     ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ ∂μ ≠ ⊤ ∧ ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ ∂μ ≠ ⊤ ∧
     ∫ g in 𝓕₀, GlobalTheory.ZEul.uInt φ φ' Φ N x g ∂μ = (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ) * (∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ), l.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.1.asIdeal) (fun i => (α w.1 i : ℂ)) (fun i => (α' w.1 i : ℂ)) x v) ∧
     ∫ g in 𝓕₀, GlobalTheory.ZEul.uInt φ φ Φ N x g ∂μ = (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ) * (∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ), l.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.1.asIdeal) (fun i => (α w.1 i : ℂ)) (fun i => (α w.1 i : ℂ)) x v) ∧
     ∫ g in 𝓕₀, GlobalTheory.ZEul.uInt φ' φ' Φ N x g ∂μ = (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ) * (∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ), l.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.1.asIdeal) (fun i => (α' w.1 i : ℂ)) (fun i => (α' w.1 i : ℂ)) x v) := by
  intro E _ _ _ m S hsat hψ b hb1 hbN hbC π π' ω ω' hω hω' hπ hπ' α α' hα hα' φ φ' hφ hφ' hU hK hU' hK' hsh hsh'
  classical
  have hϖex : ∀ w : HeightOneSpectrum (𝓞 E), ∃ ϖ : (w.adicCompletion E)ˣ, IsUnifV E w (ϖ : w.adicCompletion E) := by
    intro w
    obtain ⟨ϖ, hϖ⟩ : ∃ ϖ, IsUnifV E w ϖ := ⟨_, Formalism.L2.Host.unif_spec w⟩
    refine ⟨Units.mk0 ϖ fun h => ?_, hϖ⟩
    rw [IsUnifV, h] at hϖ
    simp at hϖ
  choose ϖ hϖ using hϖex
  have hreg : ∀ {ρ : CuspSub E (m + 1)} {ν : HChar E}, ν.IsUnitary → ρ.HasCentChar ν → ∀ F ∈ GlobalTheory.JSW.mspanR ρ,
      GlobalTheory.JSW.IsBCC F := by
    intro ρ ν hν hρ F hF
    obtain ⟨ψ, rfl, h⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded ⟨ν, hν, CuspSub.hasCentral_iff.2 hρ⟩ F hF
    have h0 := (h []).2
    rwa [GlobalTheory.JSW.word_nil] at h0
  have hc := hreg hω hπ φ hφ
  have hc' := hreg hω' hπ' φ' hφ'
  have hW : ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g :=
    fun u hu g => GlobalTheory.JSW.WhitModel.whit_mul hc.cont (fun γ g => hc.left γ g) hu g
  have hW' : ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g :=
    fun u hu g => GlobalTheory.JSW.WhitModel.whit_mul hc'.cont (fun γ g => hc'.left γ g) hu g
  have hWc := _root_.GlobalTheory.JSW.WhitCont.continuous_whit E (m + 1) φ hc.cont hc.bdd
  have hWc' := _root_.GlobalTheory.JSW.WhitCont.continuous_whit E (m + 1) φ' hc'.cont hc'.bdd
  obtain ⟨U, hUo, hUi⟩ := hU
  obtain ⟨U', hUo', hUi'⟩ := hU'
  let stab : (GA E (m + 1) → ℂ) → Subgroup (GL (Fin (m + 1)) (Af E)) := fun F =>
    { carrier := {k | ∀ g, F (g * finGL E (m + 1) k) = F g}
      mul_mem' := fun {a c} ha hc g => by rw [map_mul, ← mul_assoc, hc, ha]
      one_mem' := fun g => by rw [map_one, mul_one]
      inv_mem' := fun {a} ha g => by
        rw [← ha (g * finGL E (m + 1) a⁻¹), mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] }
  let V : Subgroup (GL (Fin (m + 1)) (Af E)) := (U ⊓ U') ⊔ Subgroup.closure
    {k | ∃ w ∉ S, ∃ k' ∈ KGL w (n := (m + 1)), locGL E (m + 1) w k' = k}
  have hVle : ∀ F : GA E (m + 1) → ℂ, (∀ u ∈ U ⊓ U', ∀ g, F (g * finGL E (m + 1) u) = F g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, F (g * finGL E (m + 1) (locGL E (m + 1) w k)) = F g) → V ≤ stab F := by
    intro F h1 h2
    refine sup_le (fun k hk => h1 k hk) (Subgroup.closure_le _ |>.2 ?_)
    rintro _ ⟨w, hw, k, hk, rfl⟩
    exact h2 w hw k hk
  have hVφ := hVle φ (fun u hu => hUi u hu.1) hK
  have hVφ' := hVle φ' (fun u hu => hUi' u hu.2) hK'
  have hVo : IsOpen (V : Set (GL (Fin (m + 1)) (Af E))) :=
    Subgroup.isOpen_mono (le_sup_left : U ⊓ U' ≤ V) (by rw [Subgroup.coe_inf]; exact hUo.inter hUo')
  have hVK : ∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), locGL E (m + 1) w k ∈ V := fun w hw k hk =>
    (le_sup_right : Subgroup.closure _ ≤ V) (Subgroup.subset_closure ⟨w, hw, k, hk, rfl⟩)
  obtain ⟨N, J, Φ, hN, hΦs, hΦc, hΦt, hΦr, hΦe, hJ, hJV, hn1, hn2, hn3⟩ := _root_.GlobalTheory.RSParams.exists_level_nat_bump E m S hsat V hVo hVK
  have hWJ : ∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g,
      GlobalTheory.JSW.whit φ (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ g := by
    intro κ hκ g
    have e : (fun z => φ (z * finGL E (m + 1) κ)) = φ := funext fun z => hVφ (hJV hκ) z
    rw [GlobalTheory.JSW.whit_mul_right, e]
  have hWJ' : ∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g,
      GlobalTheory.JSW.whit φ' (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ' g := by
    intro κ hκ g
    have e : (fun z => φ' (z * finGL E (m + 1) κ)) = φ' := funext fun z => hVφ' (hJV hκ) z
    rw [GlobalTheory.JSW.whit_mul_right, e]
  have hb0 : ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit φ p = b p := by
    intro p hp
    simpa [GlobalTheory.JSW.tl] using hsh ϖ hϖ 0 (by simp) p hp
  have hb0' : ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit φ' p = b p := by
    intro p hp
    simpa [GlobalTheory.JSW.tl] using hsh' ϖ hϖ 0 (by simp) p hp
  have h1mem : (1 : GA E (m + 1)) ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) :=
    ⟨fun w _ => map_one _, fun j => by simp [Matrix.one_apply, eq_comm]⟩
  have hne : ∀ F : GA E (m + 1) → ℂ, GlobalTheory.JSW.whit F 1 = 1 → F ≠ 0 := by
    rintro F h rfl
    simp [GlobalTheory.JSW.whit, GroundTheory.Automorphic.FourierWhittaker.whittaker] at h
  refine ⟨hne φ (by rw [hb0 1 h1mem, hb1]), hne φ' (by rw [hb0' 1 h1mem, hb1]), N, Φ, hN, hΦs, hΦc, hΦt, hΦr, ?_⟩
  intro μ _ 𝓕₀ h𝓕
  have hC0 : MeasurableSet (GlobalTheory.CellDec.C0 E (m + 1) S) :=
    (_root_.GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet E (m + 1) S).measurableSet
  have hcell : ∃ f t : GA E (m + 1) → ℝ,
      Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
      0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
      (∀ g ∉ GlobalTheory.CellDec.C0 E (m + 1) S, f g = 0) ∧
      (∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, GlobalTheory.ZEul.uInt φ φ Φ N 0 g = (f g : ℂ)) ∧
      ∀ (x : ℝ) (g : GA E (m + 1)), (GlobalTheory.RSJ.detPow E (m + 1) x g : ℂ) = Complex.exp (x * t g) := by
    let B : GA E (m + 1) → ℝ := fun g => (GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re
    have hre := GlobalTheory.CellBump.uInt_self_zero hΦr φ N
    have hBc : Continuous B := Complex.continuous_re.comp
      (GlobalTheory.CellBump.continuous_uInt hN hWc hWc hΦs.continuous hΦt 0)
    obtain ⟨K, hKc, hKs⟩ := GlobalTheory.CellBump.exists_compact_support hJ hn2 hΦc hΦt hW hWJ hbC hb0
    have hBK : ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, B g ≠ 0 →
        ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * g ∈ K := by
      intro g hg hB
      apply hKs g hg
      intro hu
      apply hB
      simp [B, hu]
    have hy1 : (fun i => pInf E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)) =
        Pi.single (Fin.last m) 1 := by
      funext i
      by_cases h : i = Fin.last m
      · subst i; simp [GlobalTheory.ZEul.lastRow]
      · simp [GlobalTheory.ZEul.lastRow, Matrix.one_apply_ne (Ne.symm h), h]
    have hyl : (Pi.single (Fin.last m) 1 : Fin (m + 1) → Cinf E) =
        GlobalTheory.RSJ.Model.eLast (Cinf E) (m + 1) := by
      funext i
      rw [GlobalTheory.CellBump.single_last_eq]
      rfl
    have hf1 : GlobalTheory.RSJ.indN N
        (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)) = 1 := by
      unfold GlobalTheory.RSJ.indN
      refine ite_eq_left fun i => ?_
      have hi : GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i) =
          if (i : ℕ) + 1 = m + 1 then 1 else 0 := by
        rw [← GlobalTheory.CellBump.single_last_eq (R := Af E)]
        by_cases h : i = Fin.last m
        · subst i; simp [GlobalTheory.ZEul.lastRow]
        · simp [GlobalTheory.ZEul.lastRow, Matrix.one_apply_ne (Ne.symm h), h]
      change GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i) - _ ∈ _
      rw [hi, sub_self]
      exact ⟨0, fun v => zero_mem _, by simp⟩
    have hB1 : 0 < B 1 := by
      have heq : GlobalTheory.ZEul.uInt φ φ Φ N 0 1 = Φ (Pi.single (Fin.last m) 1) := by
        unfold GlobalTheory.ZEul.uInt
        rw [hf1, hy1, hyl, GlobalTheory.RSJ.Model.secInv_eLast, map_one, one_mul,
          hb0 1 h1mem, hb1, GlobalTheory.CellBump.detPow_eq, ← hyl]
        simp
      change 0 < (GlobalTheory.ZEul.uInt φ φ Φ N 0 1).re
      rw [heq]
      exact lt_of_le_of_ne (hΦr _).1 fun h => hΦe (Complex.ext h.symm (hΦr _).2)
    obtain ⟨hpos, -⟩ := GlobalTheory.RSLocalPart.lintegral_cell_pos_lt_top_continuous E (m + 1) μ S 𝓕₀ h𝓕
      (fun _ g => B g) (hBc.comp continuous_snd) (fun _ g => (hre g).2) (fun _ => hB1)
      (fun _ u hu g => by simp only [B, GlobalTheory.CellBump.uInt_unip_mul hW Φ N 0 hu g])
      ⟨K, hKc, fun _ => hBK⟩
    obtain ⟨hlpos, hltop⟩ := hpos 0
    have hIB : IntegrableOn B (𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S) μ :=
      ⟨hBc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun g => (hre g).2)).2 hltop⟩
    let t : GA E (m + 1) → ℝ := fun g =>
      GlobalTheory.Mem.Chr.CharModel.logNorm E (Matrix.GeneralLinearGroup.det g)
    have htc : Continuous t :=
      (GlobalTheory.Mem.Chr.CharModel.continuous_logNorm E).comp Matrix.GeneralLinearGroup.continuous_det
    have htu : ∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, t (u * g) = t g := fun u hu g => by
      simp only [t, map_mul, show Matrix.GeneralLinearGroup.det u = 1 from
        Units.ext (GlobalTheory.RSLocalPart.det_eq_one hu), one_mul]
    obtain ⟨R, hRK⟩ := hKc.exists_bound_of_continuousOn htc.continuousOn
    refine ⟨(GlobalTheory.CellDec.C0 E (m + 1) S).indicator B, t,
      hBc.measurable.indicator hC0, htc.measurable, fun g => Set.indicator_nonneg (fun g _ => (hre g).2) g,
      ?_, ?_, ⟨R, fun g hg => ?_⟩, fun g hg => Set.indicator_of_notMem hg _, fun g hg => ?_, fun x g => ?_⟩
    · unfold IntegrableOn
      rw [integrable_indicator_iff hC0]
      unfold IntegrableOn
      rw [Measure.restrict_restrict hC0, Set.inter_comm]
      exact hIB
    · rw [integral_indicator hC0, Measure.restrict_restrict hC0, Set.inter_comm,
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun g => (hre g).2) hBc.aestronglyMeasurable]
      exact ENNReal.toReal_pos hlpos.ne' hltop.ne
    · have hgC : g ∈ GlobalTheory.CellDec.C0 E (m + 1) S := by
        by_contra h
        exact hg (Set.indicator_of_notMem h _)
      rw [Set.indicator_of_mem hgC] at hg
      obtain ⟨u, hu, hk⟩ := hBK g hgC hg
      have huR := hRK _ hk
      rwa [htu u hu, Real.norm_eq_abs] at huR
    · rw [Set.indicator_of_mem hg]
      exact (hre g).1
    · rw [GlobalTheory.CellBump.detPow_eq, Complex.ofReal_exp]
      push_cast
      rfl
  obtain ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, hfC, hfu, hdet⟩ := hcell
  refine ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, ?_⟩
  intro x hx hd hd'
  have ev := _root_.GlobalTheory.ZEul.uInt_cell_eval E m S hψ ϖ hϖ b α α' φ φ' N J Φ hJ hn1 hn2 hn3 hΦt hW hW' hWJ hWJ' (hsh ϖ hϖ) (hsh' ϖ hϖ) x
  have ev1 := _root_.GlobalTheory.ZEul.uInt_cell_eval E m S hψ ϖ hϖ b α α φ φ N J Φ hJ hn1 hn2 hn3 hΦt hW hW hWJ hWJ (hsh ϖ hϖ) (hsh ϖ hϖ) x
  have ev2 := _root_.GlobalTheory.ZEul.uInt_cell_eval E m S hψ ϖ hϖ b α' α' φ' φ' N J Φ hJ hn1 hn2 hn3 hΦt hW' hW' hWJ' hWJ' (hsh' ϖ hϖ)
    (hsh' ϖ hϖ) x
  set I : ℂ := ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ with hI
  have hIC : ∫ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, (f g : ℂ) * Complex.exp (x * t g) ∂μ = I := by
    rw [hI, Set.inter_comm, ← Measure.restrict_restrict hC0, ← integral_indicator hC0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    by_cases hg : g ∈ GlobalTheory.CellDec.C0 E (m + 1) S
    · rw [Set.indicator_of_mem hg]
    · rw [Set.indicator_of_notMem hg]; simp [hfC g hg]
  obtain ⟨R, hR'⟩ := hR
  have hfe : IntegrableOn (fun g => (f g : ℂ) * Complex.exp (x * t g)) 𝓕₀ μ := by
    refine Integrable.mono' (hfi.mul_const (Real.exp (|x| * R))) ?_ (Filter.Eventually.of_forall fun g => ?_)
    · exact ((Complex.measurable_ofReal.comp hfm).mul (Complex.measurable_exp.comp
        (measurable_const.mul (Complex.measurable_ofReal.comp htm)))).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hf0 g)]
      by_cases h0 : f g = 0
      · simp [h0]
      · refine mul_le_mul_of_nonneg_left ?_ (hf0 g)
        rw [show (x : ℂ) * (t g : ℂ) = ((x * t g : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
        exact Real.exp_le_exp.2 ((le_abs_self _).trans
          (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hR' g h0) (abs_nonneg x)))
  have hA : ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, ‖(f g : ℂ) * Complex.exp (x * t g)‖ₑ ∂μ ≠ ⊤ :=
    (hfe.mono_set Set.inter_subset_left).2.ne
  have key : ∀ (B : GA E (m + 1) → ℂ) (P : GlobalTheory.CellDec.abelian₂ E (m + 1) S → ℂ),
      (∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S,
        (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) * B (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
          P l * ((f g : ℂ) * Complex.exp (x * t g))) →
      (∀ l, (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) *
        ∫ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, B (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ = P l * I) ∧
      (∀ l, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) *
        ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, ‖B (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g)‖ₑ ∂μ =
        ‖P l‖ₑ * ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, ‖(f g : ℂ) * Complex.exp (x * t g)‖ₑ ∂μ) := by
    intro B P hB
    have hs : NullMeasurableSet (𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S) μ :=
      h𝓕.nullMeasurableSet.inter hC0.nullMeasurableSet
    have hae : ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, ∀ᵐ g ∂μ.restrict (𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S),
        (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) * B (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
          P l * ((f g : ℂ) * Complex.exp (x * t g)) :=
      fun l => (ae_restrict_mem₀ hs).mono fun g hg => hB g hg.2 l
    refine ⟨fun l => ?_, fun l => ?_⟩
    · rw [← integral_const_mul, integral_congr_ae (hae l), integral_const_mul, hIC]
    · have hpos : 0 < GlobalTheory.CellDec.dinv (m + 1) l.1 :=
        Finset.prod_pos fun v _ => zpow_pos (by exact_mod_cast (GlobalTheory.LFun.qV_ne_zero v).bot_lt) _
      have hd : ‖(GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ)‖ₑ = ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) := by
        rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hpos.le]
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ eNorm_ne_top]
      refine lintegral_congr_ae ((hae l).mono fun g hg => ?_)
      dsimp only
      rw [← hd, ← eNorm_mul, hg, eNorm_mul]
  have k12 := key (GlobalTheory.ZEul.uInt φ φ' Φ N x) (fun l => l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal)
      (fun i => (α w i : ℂ)) (fun i => (α' w i : ℂ)) x v) (fun g hg l => by
    rw [(ev g hg).2.2 l, hfu g hg, hdet, mul_assoc])
  have k11 := key (GlobalTheory.ZEul.uInt φ φ Φ N x) (fun l => l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal)
      (fun i => (α w i : ℂ)) (fun i => (α w i : ℂ)) x v) (fun g hg l => by
    rw [(ev1 g hg).2.2 l, hfu g hg, hdet, mul_assoc])
  have k22 := key (GlobalTheory.ZEul.uInt φ' φ' Φ N x) (fun l => l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal)
      (fun i => (α' w i : ℂ)) (fun i => (α' w i : ℂ)) x v) (fun g hg l => by
    rw [(ev2 g hg).2.2 l, (ev g hg).2.1, hfu g hg, hdet, mul_assoc])
  obtain ⟨hm11, hinv11, -⟩ := _root_.GlobalTheory.ZEulProps.uInt_props E m φ φ Φ N x hWc hWc hW hW hΦs.continuous hΦr
  obtain ⟨hm22, hinv22, -⟩ := _root_.GlobalTheory.ZEulProps.uInt_props E m φ' φ' Φ N x hWc' hWc' hW' hW' hΦs.continuous hΦr
  obtain ⟨hm12, hinv12, hbd⟩ := _root_.GlobalTheory.ZEulProps.uInt_props E m φ φ' Φ N x hWc hWc' hW hW' hΦs.continuous hΦr
  obtain ⟨e, he⟩ := _root_.GlobalTheory.finsupp_vanishing_on_equiv_compl_prod S (m + 1)
  have hq : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S}, 2 ≤ Ideal.absNorm w.1.asIdeal := fun w => by
    have h1 : Ideal.absNorm w.1.asIdeal ≠ 1 := fun h => w.1.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have h0 : Ideal.absNorm w.1.asIdeal ≠ 0 := fun h => w.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    omega
  have hsum : ∀ a : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ,
      GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
        (fun w i => (a w.1 i : ℂ)) x ≠ ⊤ →
      (∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, ‖l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal)
        (fun i => (a w i : ℂ)) (fun i => (a w i : ℂ)) x v‖ₑ) ≠ ⊤ := by
    intro a ha
    have hs := (_root_.GlobalTheory.ZEul.hasSum_rsTerm_finsupp (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
      (fun w => a w.1) (fun w => a w.1) x hx hq ha ha).summable
    have h2 := e.summable_iff.2 hs
    have h3 : (fun l' => (fun l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ) => l.prod fun w v =>
        GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.1.asIdeal) (fun j => (a w.1 j : ℂ)) (fun j => (a w.1 j : ℂ)) x v) (e l')) =
        fun l : GlobalTheory.CellDec.abelian₂ E (m + 1) S => l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal)
          (fun i => (a w i : ℂ)) (fun i => (a w i : ℂ)) x v :=
      funext fun l => he ℂ (fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (a w i : ℂ))
        (fun i => (a w i : ℂ)) x v) (fun i => GlobalTheory.ZEul.rsTerm_zero _ _ _ _) l
    rw [Function.comp_def, h3] at h2
    have h4 := summable_norm_iff.2 h2
    have h5 : Summable fun l : GlobalTheory.CellDec.abelian₂ E (m + 1) S => ‖l.1.prod fun w v => GlobalTheory.ZEul.rsTerm
        (Ideal.absNorm w.asIdeal) (fun i => (a w i : ℂ)) (fun i => (a w i : ℂ)) x v‖₊ :=
      NNReal.summable_coe.1 (by simpa using h4)
    simpa [eNorm_eq_nnNorm] using ENNReal.tsum_coe_ne_top_iff_summable.2 h5
  have hlin : ∀ (B : GA E (m + 1) → ℂ) (P : GlobalTheory.CellDec.abelian₂ E (m + 1) S → ℂ), Measurable B →
      (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, B (u * g) = B g) →
      (∀ l, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) *
        ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, ‖B (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g)‖ₑ ∂μ =
        ‖P l‖ₑ * ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, ‖(f g : ℂ) * Complex.exp (x * t g)‖ₑ ∂μ) →
      (∑' l, ‖P l‖ₑ) ≠ ⊤ → ∫⁻ g in 𝓕₀, ‖B g‖ₑ ∂μ ≠ ⊤ := by
    intro B P hBm hBi hl hP
    rw [GlobalTheory.CellDec.cell_lintegral μ S ϖ hϖ 𝓕₀ h𝓕 (fun g => ‖B g‖ₑ) hBm.eNorm
      (fun u hu g => by simp only [hBi u hu g])]
    simp_rw [hl, ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top hP hA
  have liftZP_unit := hlin _ _ hm11 hinv11 k11.2 (hsum α hd)
  have lix_inf_of_locP_le := hlin _ _ hm22 hinv22 k22.2 (hsum α' hd')
  have i11 : Integrable (GlobalTheory.ZEul.uInt φ φ Φ N x) (μ.restrict 𝓕₀) := ⟨hm11.aestronglyMeasurable, liftZP_unit.lt_top⟩
  have i22 : Integrable (GlobalTheory.ZEul.uInt φ' φ' Φ N x) (μ.restrict 𝓕₀) := ⟨hm22.aestronglyMeasurable, lix_inf_of_locP_le.lt_top⟩
  have i12 : Integrable (GlobalTheory.ZEul.uInt φ φ' Φ N x) (μ.restrict 𝓕₀) :=
    Integrable.mono' ((i11.norm.add i22.norm).div_const 2) hm12.aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => hbd g)
  have hbo : ∀ (B : GA E (m + 1) → ℂ) (P : GlobalTheory.CellDec.abelian₂ E (m + 1) S → ℂ), Measurable B →
      Integrable B (μ.restrict 𝓕₀) → (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, B (u * g) = B g) →
      (∀ l, (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) *
        ∫ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, B (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ = P l * I) →
      ∫ g in 𝓕₀, B g ∂μ = I * ∑' l, P l := by
    intro B P hBm hBi hBinv hl
    have h := (GlobalTheory.CellDec.cell_integral μ S ϖ hϖ 𝓕₀ h𝓕 B hBm hBi hBinv).2
    simp_rw [hl] at h
    rw [← h.tsum_eq, tsum_mul_right, mul_comm]
  have hre : ∀ a c : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ,
      ∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, l.1.prod (fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal)
        (fun i => (a w i : ℂ)) (fun i => (c w i : ℂ)) x v) =
      ∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ), l.prod fun w v =>
        GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.1.asIdeal) (fun i => (a w.1 i : ℂ)) (fun i => (c w.1 i : ℂ)) x v := by
    intro a c
    rw [← e.tsum_eq]
    exact tsum_congr fun l => (he ℂ (fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (a w i : ℂ))
      (fun i => (c w i : ℂ)) x v) (fun i => GlobalTheory.ZEul.rsTerm_zero _ _ _ _) l).symm
  refine ⟨liftZP_unit, lix_inf_of_locP_le, ?_, ?_, ?_⟩
  · rw [hbo _ _ hm12 i12 hinv12 k12.1, hre]
  · rw [hbo _ _ hm11 i11 hinv11 k11.1, hre]
  · rw [hbo _ _ hm22 i22 hinv22 k22.1, hre]

end GlobalTheory.ZEul
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedPolarisedIntegralBumpedForms =====
