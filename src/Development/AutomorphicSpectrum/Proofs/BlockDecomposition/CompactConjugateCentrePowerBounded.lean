module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
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
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.CuspGrowth


open GlobalTheory.IdeleCovolume GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele in
theorem abs_le_of_conj_mem_compact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ Q : Set (GA E a), IsCompact Q → ∃ n₀ : ℕ, ∀ (γ : GL (Fin a) E) (n : ℤ) (x : GA E a),
      x⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * x ∈ Q → |n| ≤ n₀ := by
  intro E _ _ _ a ha Q hQ
  have hf : Continuous fun g : GA E a => Real.log (ideleNorm (E := E) (GeneralLinearGroup.det g)) :=
    (continuous_ideleNorm.comp GeneralLinearGroup.continuous_det).log fun _ => ideleNorm_ne_zero _
  obtain ⟨B, hB⟩ := (hQ.image hf).isBounded.exists_norm_le
  have hL : 0 < Real.log (ideleNorm (E := E) (eIdele E)) := Real.log_pos (one_lt_ideleNorm_eIdele E)
  set L := Real.log (ideleNorm (E := E) (eIdele E)) with hLdef
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  refine ⟨⌈B / (a * L)⌉₊, fun γ n x hx => ?_⟩
  have hd : GeneralLinearGroup.det (ratGL E a γ) = diag E (GeneralLinearGroup.det γ) :=
    Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)
  have hv : Real.log (ideleNorm (E := E) (GeneralLinearGroup.det
      (x⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * x))) = (n : ℝ) * (a * L) := by
    have h1 : GeneralLinearGroup.det (x⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * x) =
        diag E (GeneralLinearGroup.det γ) * (eIdele E ^ a) ^ n := by
      rw [map_mul, map_mul, map_mul, map_inv, map_zpow, hd, det_splitCentre_one, mul_comm, ← mul_assoc,
        mul_inv_cancel, one_mul]
    rw [h1, map_mul, show ideleNorm (E := E) (diag E _) = 1 from ideleNorm_principalIdele _, one_mul,
      map_zpow, map_pow, Real.log_zpow, Real.log_pow]
  have hb := hB _ ⟨_, hx, rfl⟩
  beta_reduce at hb
  rw [hv, Real.norm_eq_abs, abs_mul, abs_of_pos (mul_pos ha' hL)] at hb
  have h2 : ((|n| : ℤ) : ℝ) ≤ B / (a * L) := by
    rw [le_div_iff₀ (mul_pos ha' hL)]
    simpa using hb
  have h3 : ((|n| : ℤ) : ℝ) ≤ ((⌈B / (a * L)⌉₊ : ℤ) : ℝ) := by
    rw [Int.cast_natCast]
    exact h2.trans (Nat.le_ceil _)
  exact Int.cast_le.1 h3

end GlobalTheory.CompanionTheory.CuspGrowth
