module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.ConjExtend

theorem exists_extension_of_le (M : IntermediateField ℚ ℂ) (hle : M ≤ Qbar) (ρ : M →ₐ[ℚ] ℂ) :
    ∃ ρ' : Qbar →ₐ[ℚ] ℂ, ∀ x ∈ M, ρ' (TaylorLogMetric.liftM Qbar x) = ρ (TaylorLogMetric.liftM M x) := by
  let _ : Algebra M Qbar := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have : IsScalarTower ℚ M Qbar := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  have : Algebra.IsAlgebraic M Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) M
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ) (L := M) (M := ℂ)
    (E := Qbar) ρ
  refine ⟨φ, fun x hx => ?_⟩
  rw [← hφ]
  unfold TaylorLogMetric.liftM
  rw [dite_eq_left hx, dite_eq_left (hle hx)]
  rfl

theorem fld_le (D : D7) (hI : GlobalTheory.NormSum.Inp D) (δ t0 : ℂ) (hc : Crv D D.host.ccK δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0) : GlobalTheory.KerConjMean.fld D δ t0 ≤ Qbar := by
  obtain ⟨hdata, htor⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 _ δ hc
  have hwp : wpF (lamOf D D.host.ccK δ) t0 ∈ Qbar := by
    refine (htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1
    obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have h1 := GlobalTheory.ArchNorm.mul_mem_lamOf D _ δ a h0
    rw [ha, mul_comm] at h1
    exact ht.2.1 h1
  unfold GlobalTheory.KerConjMean.fld
  rw [IntermediateField.adjoin_le_iff]
  rintro y (⟨x, rfl⟩ | rfl | rfl | rfl)
  · exact mem_algebraicClosure_iff.2
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.what₂.embLL.toRatAlgHom)
  · exact hdata.2.1
  · exact hdata.2.2
  · exact hwp

theorem exists_extension_conj : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (δ t0 : ℂ), Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ GlobalTheory.KerConjMean.ext D δ t0 σ, ∃ ρ' : Qbar →ₐ[ℚ] ℂ,
      (∀ x, Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (D.what₂.embLL x) = σ x) ∧
      lamConj Qbar ρ' (lamOf D D.host.ccK δ) = lamConj (GlobalTheory.KerConjMean.fld D δ t0) ρ (GlobalTheory.KerConjMean.lat D δ) := by
  intro D hI δ t0 hc ht σ ρ hρ
  obtain ⟨ρ', h⟩ := exists_extension_of_le _ (fld_le D hI δ t0 hc ht) ρ
  refine ⟨ρ', fun x => ?_, ?_⟩
  · unfold Formalism.MainNotions.StandardLatticesGL3.cj
    rw [h _ (GlobalTheory.KerConjMean.embLL_mem D δ t0 x), ← hρ x]
    unfold TaylorLogMetric.liftM
    rw [dite_eq_left (GlobalTheory.KerConjMean.embLL_mem D δ t0 x)]
  · have h2 : g2 (lamOf D D.host.ccK δ) ∈ GlobalTheory.KerConjMean.fld D δ t0 :=
      IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
    have h3 : g3 (lamOf D D.host.ccK δ) ∈ GlobalTheory.KerConjMean.fld D δ t0 :=
      IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
    unfold lamConj
    rw [h _ h2, h _ h3]

end GlobalTheory.ConjExtend
