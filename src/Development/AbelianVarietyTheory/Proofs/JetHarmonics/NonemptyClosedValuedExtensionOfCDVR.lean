module

public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinSiteSiteAlg
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct

namespace GlobalTheory.CharDepth

theorem nonempty_valExt :
    ∀ (T : CDVR) (p : ℕ) [Fact p.Prime], ¬ IsUnit (p : T.V) → Nonempty (ValExt T p) := by
  intro T p hp hu
  have hp0 : (p : T.V) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hr0 : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  have hr1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  obtain ⟨C, _, _, _, _, _, hC, hCp⟩ :=
    exists_complete_isAlgClosed_of_isDiscreteValuationRing T.V T.Fr hp0
      ((IsLocalRing.mem_maximalIdeal _).2 hu) hr0 hr1
  rw [map_natCast] at hCp
  have : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)
  have : CharZero C := charZero_of_injective_ringHom (algebraMap T.Fr C).injective
  have hCp' : ‖(p : C)‖ = (p : ℝ)⁻¹ := by rwa [map_natCast] at hCp
  let v : Valuation C NNReal := NormedField.valuation
  have hO : v.Integers v.integer := Valuation.integer.integers v
  have hmem : ∀ x : C, ‖x‖ ≤ 1 → x ∈ v.integer := fun x hx => by
    change ‖x‖₊ ≤ 1
    exact_mod_cast hx
  have hpO : ‖algebraMap v.integer C (p : v.integer)‖ < 1 := by
    rw [map_natCast, hCp']; exact hr1
  haveI : Fact (¬ IsUnit (p : v.integer)) :=
    ⟨fun h => hpO.ne ((NormIntegers.isUnit_iff_norm_eq_one hO).1 h)⟩
  haveI := NormIntegers.isAdicComplete_span_singleton hO hpO
  haveI := NormIntegers.isLocalRing hO
  obtain ⟨j, hj⟩ := exists_padic_isometry (C := C) p hCp'
  letI : Algebra ℤ_[p] v.integer :=
    ((j.comp PadicInt.Coe.ringHom).codRestrict v.integer fun x =>
      hmem _ ((hj _).trans_le x.2)).toAlgebra
  have hf : ∀ a : T.V, ‖algebraMap T.Fr C (algebraMap T.V T.Fr a)‖ ≤ 1 := fun a => (hC _).2 ⟨a, rfl⟩
  let ι : T.V →+* v.integer :=
    ((algebraMap T.Fr C).comp (algebraMap T.V T.Fr)).codRestrict v.integer fun a => hmem _ (hf a)
  have hι : IsLocalHom ι := by
    refine ⟨fun a ha => ?_⟩
    have h1 : ‖algebraMap T.Fr C (algebraMap T.V T.Fr a)‖ = 1 :=
      (NormIntegers.isUnit_iff_norm_eq_one hO).1 ha
    have ha0 : algebraMap T.V T.Fr a ≠ 0 := fun h => by simp [h] at h1
    obtain ⟨b, hb⟩ := (hC (algebraMap T.V T.Fr a)⁻¹).1 (by rw [map_inv₀, norm_inv, h1, inv_one])
    refine IsUnit.of_mul_eq_one b (IsFractionRing.injective T.V T.Fr ?_)
    rw [map_mul, hb, mul_inv_cancel₀ ha0, map_one]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hpF : (p : T.Fr) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hzp := ArcQ.norm_map_eq_zpow_vV (algebraMap T.Fr C) hf hπ hpF
  have he : (vV T.V (p : T.Fr) : ℝ) ≠ 0 := by
    intro h
    have h' : vV T.V (p : T.Fr) = 0 := by exact_mod_cast h
    rw [h', zpow_zero, hCp] at hzp
    exact hr1.ne hzp
  refine ⟨{ C := C, v := v, O := v.integer, ints := hO, ι := ι, ι_local := hι,
            ιF := algebraMap T.Fr C, comp := fun _ => rfl, val := fun x hx => ?_ }⟩
  change ‖algebraMap T.Fr C x‖ = ‖(p : C)‖ ^ _
  rw [← map_natCast (algebraMap T.Fr C) p, hzp, ArcQ.norm_map_eq_zpow_vV (algebraMap T.Fr C) hf hπ hx,
    ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ he]

end GlobalTheory.CharDepth
