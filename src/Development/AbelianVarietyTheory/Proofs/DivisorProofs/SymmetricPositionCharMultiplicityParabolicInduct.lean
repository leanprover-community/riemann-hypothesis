module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerateWhittakerDimParabolicInductionCuspidalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviWhittakerEqOneOfCuspidalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicityEqSumDegenerateStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicitySuccEqStatement
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.FinGL

open Formalism.L2.DIV Module

theorem finiteDimensional_coindV_blockTri {F : Type} [Field F] [Fintype F] {r : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) :
    FiniteDimensional ℂ (Representation.coindV (blockTri (κ := F) b).subtype σ) := by
  classical
  have : Finite (GL (Fin r) F) := inferInstance
  infer_instance

theorem nPos_parInd (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (r : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ)
    (σ : Representation ℂ (blockTri (κ := F) b) V) (hσ : IsCuspDatum b σ) (ρ k : ℕ) (h : ρ + k + 1 ≤ r) :
    nPos ψ (parInd b σ) ρ k = ∑ j ∈ Finset.range (k + 1), splitDoublingNBlock b j * gam (Fintype.card F) (k - j) := by
  have hfd := finiteDimensional_coindV_blockTri b σ
  induction ρ with
  | zero =>
    rw [GlobalTheory.T.symmetricPositionCharMultiplicity_eq_sum_degenerateWhittaker F ψ hψ r _ (parInd b σ) k (by omega)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [GlobalTheory.T.degenerateWhittakerDim_parabolicInduction_cuspidal F ψ hψ r V b σ hσ j (Or.inl (by omega)), GlobalTheory.T.levi_whittaker_eq_one_of_cuspidal F ψ hψ r V b σ hσ, mul_one, mul_comm]
  | succ ρ ih =>
    rw [← GlobalTheory.T.symmetricPositionCharMultiplicity_succ_eq F ψ hψ r _ (parInd b σ) ρ k (by omega)]
    exact ih (by omega)

end GlobalTheory.FinGL
