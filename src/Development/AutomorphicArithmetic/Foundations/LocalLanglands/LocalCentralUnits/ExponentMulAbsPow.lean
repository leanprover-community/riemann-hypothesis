module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.WDBasic
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.NormEqOneOfIsUnitarisableU
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
public import GroundTheory.LocalFields.LocalZetaChar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

section Abs

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem nabs_eq_residue (z : kˣ) :
    nabs k z = (GroundTheory.LocalField.residueCard k : ℝ) ^ (-GroundTheory.LocalField.ord (z : k)) := by
  rw [GlobalTheory.LGrp.nabs_eq_zpow]
  rfl

private theorem norm_smooth_char {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (z : kˣ) :
    ‖(χ z : ℂ)‖ = nabs k z ^ GroundTheory.LocalField.quasiCharExponent χ := by
  have hc : Continuous χ := by
    refine continuous_def.2 fun U _ => isOpen_iff_forall_mem_open.2 fun x hx => ?_
    refine ⟨(fun y => x⁻¹ * y) ⁻¹' (χ.ker : Set kˣ), fun y hy => ?_,
      hχ.preimage (continuous_const_mul _), by simp⟩
    have h : χ (x⁻¹ * y) = 1 := hy
    rw [map_mul, map_inv, inv_mul_eq_one] at h
    show χ y ∈ U
    rw [← h]
    exact hx
  rw [GroundTheory.LocalField.norm_quasiChar_apply hc z,
    GroundTheory.LocalField.modulus_of_ne_zero z.ne_zero, nabs_eq_residue]
  simp

private theorem exponent_mul_absPow {χ χ' : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hχ' : IsSmoothChar χ') (d : ℕ) (s : ℝ)
    (e : χ' = χ * absPow k (s : ℂ) ^ d) :
    GroundTheory.LocalField.quasiCharExponent χ' = GroundTheory.LocalField.quasiCharExponent χ + d * s := by
  subst e
  have hq : (1 : ℝ) < GroundTheory.LocalField.residueCard k := by
    exact_mod_cast GroundTheory.LocalField.one_lt_residueCard
  have hL := Real.log_pos hq
  have h1 : GroundTheory.LocalField.ord ((GroundTheory.LocalField.unifUnit k : kˣ) : k) = 1 := by
    simpa using GroundTheory.LocalField.ord_unifUnit_zpow (K := k) 1
  have hlog : Real.log (nabs k (GroundTheory.LocalField.unifUnit k)) =
      -Real.log (GroundTheory.LocalField.residueCard k) := by
    rw [nabs_eq_residue, h1, Real.log_zpow]
    push_cast
    ring
  have hpos := GlobalTheory.SmGL.nabs_pos' k (GroundTheory.LocalField.unifUnit k)
  have ha : ‖((χ (GroundTheory.LocalField.unifUnit k) : ℂˣ) : ℂ)‖ ≠ 0 := by
    simp
  unfold GroundTheory.LocalField.quasiCharExponent
  rw [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val,
    val_absPow_ofReal, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _)]
  have hb : (nabs k (GroundTheory.LocalField.unifUnit k) ^ s) ^ d ≠ 0 :=
    pow_ne_zero _ (Real.rpow_pos_of_pos hpos _).ne'
  simp only [Real.logb]
  rw [Real.log_mul ha hb, Real.log_pow, Real.log_rpow hpos, hlog]
  field_simp
  ring

end Abs

theorem expo : Expo := by
  intro E Ω _ _ _ _ _ A w h a ha
  let ω₀ : IrrGL (k := HeightOneSpectrum.adicCompletion E w) → ((HeightOneSpectrum.adicCompletion E w)ˣ →* ℂˣ) :=
    fun y => Classical.choose (clBasic (HeightOneSpectrum.adicCompletion E w) y).1
  have hω₀ : ∀ y, IsSmoothChar (ω₀ y) ∧ HasCentralChar y.rep (ω₀ y) ∧
      ∀ ω', HasCentralChar y.rep ω' → ω' = ω₀ y :=
    fun y => Classical.choose_spec (clBasic (HeightOneSpectrum.adicCompletion E w) y).1
  refine ⟨fun y => GroundTheory.LocalField.quasiCharExponent (ω₀ y) / y.fst, ?_⟩
  intro x hx
  have hn : (x.fst : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  constructor
  · intro s
    have hc := PositivityTheory.RgUd.UOrder.hasCentralChar_nu_u x (hω₀ x).2.1 (s : ℂ)
    have heq := (hω₀ (x.nu (s : ℂ))).2.2 _ hc
    have hfst : (x.nu (s : ℂ)).fst = x.fst := by
      unfold IrrGL.nu
      exact ((clBasic _ x).2.1 _ _).1
    have hsm : IsSmoothChar (ω₀ x * absPow (HeightOneSpectrum.adicCompletion E w) (s : ℂ) ^ x.fst) := by
      rw [heq]
      exact (hω₀ _).1
    show GroundTheory.LocalField.quasiCharExponent (ω₀ (x.nu (s : ℂ))) / ((x.nu (s : ℂ)).fst : ℝ) =
      GroundTheory.LocalField.quasiCharExponent (ω₀ x) / x.fst + s
    rw [← heq, hfst, exponent_mul_absPow (hω₀ x).1 hsm x.fst s rfl]
    field_simp
  · intro ω hω J hJ hunit σ
    have hωeq := (hω₀ x).2.2 ω hω
    subst hωeq
    obtain ⟨-, -, -, -, -, -, -, -, hξ⟩ := wDBasic E Ω A w h J
    unfold GlobalTheory.WeilDeligne.WD.lpTw
    rw [(hξ _ _).2.2.1 σ, norm_mul, norm_pow, hunit σ, one_mul, hJ, ← ha.absPow_comp,
      MonoidHom.comp_apply, val_absPow_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (GlobalTheory.SmGL.nabs_pos' _ _).le _),
      norm_smooth_char (hω₀ x).1, ← Real.rpow_natCast, ← Real.rpow_mul (GlobalTheory.SmGL.nabs_pos' _ _).le,
      div_mul_cancel₀ _ hn]

end UpperTheory.Zero.LLC

end
