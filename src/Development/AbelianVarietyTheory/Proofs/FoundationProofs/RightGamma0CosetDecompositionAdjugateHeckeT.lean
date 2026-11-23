module

public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftGamma0CosetDecompositionHeckeRepTOperatorStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem adjugate_mem_intMatricesDetLowerLeftDvd {L q : ℕ} {δ : M2} (h : δ ∈ DT L q) : δ.adjugate ∈ DT L q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_adjugate]; simpa using h1
  · rw [Matrix.adjugate_fin_two]; simpa using h2

theorem intMatrixTwo_adjugate_adjugate (δ : M2) : δ.adjugate.adjugate = δ := by
  rw [Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem rrep_DT_adj_repT : ∀ L q : ℕ, q.Prime → ¬ q ∣ L →
    RRep L (DT L q) (fun i => (repT q i).adjugate) := by
  intro L q hq hqL
  have hL := GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepTOperator L q hq hqL
  unfold LRep at hL
  unfold RRep
  let φ : Option (Fin q) × Gamma0 L → Gamma0 L × Option (Fin q) := fun p => (p.2⁻¹, p.1)
  have hφ : Set.BijOn φ Set.univ Set.univ := by
    rw [Set.bijOn_univ]
    refine ⟨fun a b h => ?_, fun b => ⟨(b.2, b.1⁻¹), by simp [φ]⟩⟩
    simp only [φ, Prod.mk.injEq, inv_inj] at h
    exact Prod.ext h.2 h.1
  have hA : Set.BijOn (fun δ : M2 => δ.adjugate) (DT L q) (DT L q) :=
    Set.InvOn.bijOn ⟨fun δ _ => intMatrixTwo_adjugate_adjugate δ, fun δ _ => intMatrixTwo_adjugate_adjugate δ⟩
      (fun δ h => adjugate_mem_intMatricesDetLowerLeftDvd h) (fun δ h => adjugate_mem_intMatricesDetLowerLeftDvd h)
  have hc := hA.comp (hL.comp hφ)
  convert hc using 1
  funext p
  dsimp only [Function.comp_apply, φ]
  rw [Matrix.adjugate_mul_distrib]
  congr 1
  rw [Subgroup.coe_inv, ← Matrix.SpecialLinearGroup.coe_inv, inv_inv]

end GlobalTheory.EisM
