module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Mathlib.RingTheory.DedekindDomain.Factorization
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
import Mathlib.Data.Nat.Choose.Multinomial
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem mk_eq_finprod (K : Type) [Field K] [NumberField K]
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
    ClassGroup.mk K I = ∏ᶠ v : HeightOneSpectrum (𝓞 K), primeCl v ^ FractionalIdeal.count K v I.1 := by
  let P : HeightOneSpectrum (𝓞 K) → (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ := fun v =>
    FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
  have hfin : (Function.mulSupport fun v => P v ^ FractionalIdeal.count K v I.1).Finite :=
    (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I.1)).subset
      fun v hv h => hv (by simp only [h, zpow_zero])
  have hI : ∏ᶠ v, P v ^ FractionalIdeal.count K v I.1 = I := by
    apply Units.ext
    rw [← Units.coeHom_apply, map_finprod _ hfin]
    conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.ne_zero]
    exact finprod_congr fun v => by simp [Units.val_zpow_eq_zpow_val, P]
  conv_lhs => rw [← hI]
  rw [map_finprod _ hfin]
  exact finprod_congr fun v => by rw [map_zpow, ClassGroup.mk_mk0]; rfl

private theorem count_eq_ordv (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K)) = ordv v a := by
  have hI : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
        (algebraMap (𝓞 K) K (IsLocalization.sec (nonZeroDivisors (𝓞 K)) (a : K)).2)⁻¹ *
        ↑(Ideal.span {(IsLocalization.sec (nonZeroDivisors (𝓞 K)) (a : K)).1} : Ideal (𝓞 K)) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      IsLocalization.sec_spec' (nonZeroDivisors (𝓞 K)) (a : K), inv_mul_cancel_left₀]
    simpa using nonZeroDivisors.coe_ne_zero _
  rw [FractionalIdeal.count_well_defined K v (FractionalIdeal.spanSingleton_ne_zero_iff.2 a.ne_zero) hI]
  change _ = -Multiplicative.toAdd (v.valuationOfNeZeroToFun a)
  simp only [HeightOneSpectrum.valuationOfNeZeroToFun, toAdd_ofAdd]
  ring

theorem UpperTheory.V.Kum.clProd :
    ∀ (K : Type) [Field K] [NumberField K], (∀ I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ, ClassGroup.mk K I = ∏ᶠ v : HeightOneSpectrum (𝓞 K), primeCl v ^ FractionalIdeal.count K v I.1) ∧
    (∀ (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ), FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K)) = ordv v a) ∧ (∀ a : Kˣ, {v : HeightOneSpectrum (𝓞 K) | ordv v a ≠ 0}.Finite) ∧ ∀ a : Kˣ, radCl 1 a = 1 := by
  intro K _ _
  refine ⟨mk_eq_finprod K, count_eq_ordv K, fun a => ?_, fun a => ?_⟩
  · simp only [← count_eq_ordv]
    exact Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors _)
  · have h := mk_eq_finprod K (toPrincipalIdeal (𝓞 K) K a)
    rw [coe_toPrincipalIdeal] at h
    simp only [count_eq_ordv] at h
    simp only [radCl, Nat.cast_one, Int.ediv_one]
    rw [← h, ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal]
    exact (FractionalIdeal.isPrincipal_iff _).2 ⟨_, rfl⟩
