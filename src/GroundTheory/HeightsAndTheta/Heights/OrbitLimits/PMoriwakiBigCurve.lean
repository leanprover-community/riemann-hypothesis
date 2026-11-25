module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsMoriwakiBigCurve
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveCountLower
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallPacking
import Mathlib.Algebra.Order.Star.Real

@[expose] public section
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Targets
open ReciprocityTheory.ChartRestriction.G.Geo Filter

theorem chartLat_le_chartLatNm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : chartLat y a τ ≤ chartLatNm y a τ := fun _ hs c hc =>
  (mem_integralClosure_iff _ _).mpr (isIntegral_algebraMap (R := chartRingZ y c) (A := Ω) (x := ⟨_, hs c hc⟩))

theorem MoriwakiBigCurve.proof (hL : CurveCountLower.Statement)
    (hPk : HilbertSamuel.SmallPacking.Statement) : MoriwakiBigCurve.Statement := by
  intro K _ ι _ Ω _ y A P0 II hII hP hB _ hS hC _ _
  set Q := IsSmallH (mCoordIdeal y) y A
  set La := chartLat y A.a
  obtain ⟨C, hC⟩ := hL K ι Ω y A II hII hP hB hS.1 hC
  obtain ⟨C', hC'⟩ := (hPk K ι Ω y 0 A La hP hB hS.1 (chartLat_le_chartLatNm y A.a)).2
  simp only [arVolP, Nat.zero_add, one_mul, Nat.factorial_one, Nat.cast_one, pow_one, div_one]
  refine le_of_forall_sub_le fun ε hε => le_limsup_of_frequently_le ?_ ?_
  · refine Eventually.frequently ((eventually_ge_atTop (⌈C / ε⌉₊ + 1)).mono fun k hk => ?_)
    have hk₁ := (Nat.le_add_left 1 _).trans hk
    refine (le_div_iff₀ (Nat.cast_pos.mpr hk₁)).2 ?_
    nlinarith [hC k hk₁, (div_le_iff₀ hε).mp ((Nat.le_ceil (C / ε)).trans
      (show (⌈C / ε⌉₊ : ℝ) ≤ k by exact_mod_cast (Nat.le_succ _).trans hk))]
  · refine ⟨2 * C', eventually_map.mpr ((eventually_ge_atTop 1).mono fun k hk => ?_)⟩
    refine (div_le_iff₀ (Nat.cast_pos.mpr hk)).2 ?_
    nlinarith [show smallSectionCount Q La k ≤ C' * ((k : ℝ) + 1) by simpa using hC' k,
      mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ k by exact_mod_cast hk)
        (show 0 ≤ C' by simpa using (Real.log_natCast_nonneg _).trans (hC' 0))]

end GroundTheory.Heights₂.Heights.Targets
