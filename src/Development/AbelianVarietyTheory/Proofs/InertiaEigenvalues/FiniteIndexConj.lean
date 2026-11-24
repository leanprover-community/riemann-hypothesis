module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCongruenceConjContainsCongruence
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.CongIndex

theorem bounded_cover {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {J : Subgroup (GAf L n)}
    (hJ : IsBounded J) {M : ℕ} (hM : 0 < M) :
    ∃ F : Finset (GAf L n), ∀ κ ∈ J, ∃ f ∈ F, NG.Cong L n M (f⁻¹ * κ) := by
  classical
  obtain ⟨F0, hF0⟩ := hJ
  obtain ⟨F1, hF1⟩ := GlobalTheory.AlgFormsFin.exists_cover L n hM
  refine ⟨(F0 ×ˢ F1).image (fun p => p.1 * p.2), fun κ hκ => ?_⟩
  obtain ⟨f0, hf0, hu⟩ := hF0 κ hκ
  obtain ⟨j, hj, κ', hκ', e⟩ := hF1 _ hu
  refine ⟨f0 * j, Finset.mem_image.2 ⟨(f0, j), Finset.mem_product.2 ⟨hf0, hj⟩, rfl⟩, ?_⟩
  have h1 : (f0 * j)⁻¹ * κ = κ' := by
    rw [mul_inv_rev, mul_assoc, e, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [h1]
  exact hκ'

theorem finite_index_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J : Subgroup (GAf L n)),
    IsBounded J → ∀ (h : GAf L n) (N : ℕ), 0 < N →
      (∃ N' : ℕ, 0 < N' ∧ ∀ κ, NG.Cong L n N' κ → NG.Cong L n N (h⁻¹ * κ * h)) ∧
      (∃ F : Finset (GAf L n), ∀ κ ∈ J, ∃ f ∈ F, NG.Cong L n N (f⁻¹ * κ)) ∧
      IsBounded (J.map (MulAut.conj h).toMonoidHom) := by
  intro L _ _ _ n J hJ h N hN
  refine ⟨GlobalTheory.CongConjugate.congConj L n h N hN, bounded_cover hJ hN, ?_⟩
  classical
  obtain ⟨N', hN', hc⟩ := GlobalTheory.CongConjugate.congConj L n h⁻¹ 1 one_pos
  obtain ⟨F, hF⟩ := bounded_cover hJ hN'
  refine ⟨F.image (fun f => h * f * h⁻¹), fun x hx => ?_⟩
  obtain ⟨κ, hκ, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨f, hf, hcf⟩ := hF κ hκ
  refine ⟨h * f * h⁻¹, Finset.mem_image_of_mem _ hf, ?_⟩
  have hu := (hc _ hcf).1
  have e : (h * f * h⁻¹)⁻¹ * (MulAut.conj h).toMonoidHom κ = h⁻¹⁻¹ * (f⁻¹ * κ) * h⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
  rw [e]
  exact hu

end GlobalTheory.CongIndex

end
