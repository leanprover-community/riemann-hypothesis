module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.IdeleModule
variable {E : Type} [Field E] [NumberField E]

theorem coord_ne (y : (Af E)ˣ) (v : HeightOneSpectrum (𝓞 E)) : Valued.v ((y : Af E) v) ≠ 0 := by
  have := (FiniteAdeleRing.isUnit_iff.1 y.isUnit).1 v
  simpa using this

theorem modF_finite (y : (Af E)ˣ) : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 E) =>
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (WithZero.log (Valued.v ((y : Af E) v)))).Finite := by
  have := (FiniteAdeleRing.isUnit_iff.1 y.isUnit).2
  rw [Filter.eventually_cofinite] at this
  refine this.subset fun v hv h1 => hv ?_
  simp [h1]

theorem absNorm_pos (v : HeightOneSpectrum (𝓞 E)) : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  positivity

theorem modF_mul (y y' : (Af E)ˣ) : modF (y * y') = modF y * modF y' := by
  unfold modF
  rw [← finprod_mul_distrib (modF_finite y) (modF_finite y')]
  refine finprod_congr fun v => ?_
  have : ((y * y' : (Af E)ˣ) : Af E) v = (y : Af E) v * (y' : Af E) v := rfl
  rw [this, map_mul, WithZero.log_mul (coord_ne y v) (coord_ne y' v), zpow_add₀ (absNorm_pos v).ne']

theorem modF_pos (y : (Af E)ˣ) : 0 < modF y :=
  finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun v => zpow_pos (absNorm_pos v) _

theorem modF_princ (k : Eˣ) :
    modF (Units.map (algebraMap E (Af E)).toMonoidHom k) = (|((Algebra.norm ℚ (k : E) : ℚ) : ℝ)|)⁻¹ := by
  have h := FinitePlace.prod_eq_inv_abs_norm (K := E) k.ne_zero
  push_cast at h
  rw [← h, ← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := E)).symm]
  unfold modF
  refine finprod_congr fun v => ?_
  rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding']
  have h0 : v.valuation E (k : E) ≠ 0 := by simp
  have h1 : Valued.v (((Units.map (algebraMap E (Af E)).toMonoidHom k : (Af E)ˣ) : Af E) v) = v.valuation E (k : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : E)
  rw [h1, WithZeroMulInt.toNNReal_neg_apply _ h0]
  push_cast
  congr 1

end GlobalTheory.CMVal.IdeleModule

theorem GlobalTheory.CMVal.modF_mul_pos_principal : ∀ (E : Type) [Field E] [NumberField E], (∀ y y' : (Af E)ˣ, modF (y * y') = modF y * modF y') ∧ (∀ y : (Af E)ˣ, 0 < modF y) ∧ ∀ k : Eˣ, modF (Units.map (algebraMap E (Af E)).toMonoidHom k) = (|(Algebra.norm ℚ (k : E) : ℝ)|)⁻¹ :=
  fun _ _ _ => ⟨IdeleModule.modF_mul, IdeleModule.modF_pos, IdeleModule.modF_princ⟩
