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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

noncomputable section

namespace GlobalTheory.CentralExponent

open Matrix GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.IdeleCovolume GlobalTheory.UnitaryBC

theorem abs_le_of_conj_mem : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ W : Set (GA E a), IsCompact W → ∃ n₀ : ℕ, ∀ (γ : GL (Fin a) E) (n : ℤ) (g : GA E a),
      g⁻¹ * (ratGL E a γ * GlobalTheory.UnitaryBC.splitCentre E a 1 ^ n) * g ∈ W → |n| ≤ n₀ := by
  intro E _ _ _ a ha W hW
  have hL : 0 < Real.log (ideleNorm (E := E) (eIdele E)) := Real.log_pos (one_lt_ideleNorm_eIdele E)
  have hc : Continuous fun x : GA E a => Real.log (ideleNorm (E := E) (GeneralLinearGroup.det x)) :=
    (continuous_ideleNorm.comp GeneralLinearGroup.continuous_det).log fun _ => ideleNorm_ne_zero _
  obtain ⟨C, hC⟩ := hW.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨⌈C / Real.log (ideleNorm (E := E) (eIdele E))⌉₊, fun γ n g hmem => ?_⟩
  have hd : GeneralLinearGroup.det (ratGL E a γ) = diag E (GeneralLinearGroup.det γ) :=
    Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)
  have e : GeneralLinearGroup.det (g⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * g) =
      diag E (GeneralLinearGroup.det γ) * eIdele E ^ ((a : ℤ) * n) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_zpow, hd, det_splitCentre_one, ← zpow_natCast, ← _root_.zpow_mul,
      mul_comm _ (GeneralLinearGroup.det g), mul_inv_cancel_left]
  have key : Real.log (ideleNorm (E := E) (GeneralLinearGroup.det
      (g⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * g))) =
      ((a : ℤ) * n : ℤ) * Real.log (ideleNorm (E := E) (eIdele E)) := by
    rw [e, map_mul, show ideleNorm (E := E) (diag E _) = 1 from ideleNorm_principalIdele _, one_mul, map_zpow,
      Real.log_zpow]
  have h1 := hC _ hmem
  rw [key, Real.norm_eq_abs, abs_mul, abs_of_pos hL] at h1
  have h2 : (|n| : ℝ) ≤ |(((a : ℤ) * n : ℤ) : ℝ)| := by
    push_cast
    rw [abs_mul, Nat.abs_cast]
    exact le_mul_of_one_le_left (abs_nonneg _) (by exact_mod_cast ha)
  have h3 : (|n| : ℝ) ≤ ⌈C / Real.log (ideleNorm (E := E) (eIdele E))⌉₊ :=
    (h2.trans ((le_div_iff₀ hL).2 h1)).trans (Nat.le_ceil _)
  exact_mod_cast h3

end GlobalTheory.CentralExponent
