module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.RepIndep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem UpperTheory.V.Z.Sym.Tf.rLin :
    UpperTheory.V.Z.Sym.Tf.RLin := by
  classical
  intro Γ G V _ _ _ _ B s I S c f hf
  have hT : {x : G ⧸ B.U | ∃ i ∈ S, f i (s.θ x.out) ≠ 0}.Finite := by
    refine (Set.Finite.biUnion S.finite_toSet (fun i hi => (hf i hi).fin)).subset ?_
    rintro x ⟨i, hi, hx⟩
    exact Set.mem_biUnion (show i ∈ (S : Set I) from hi) hx
  have htest : s.IsTest (fun y => ∑ i ∈ S, c i * f i y) := by
    refine ⟨fun u y => ?_, fun u y => ?_, hT.subset ?_⟩
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(hf i hi).left]; ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(hf i hi).right]; ring
    · intro x hx
      obtain ⟨i, hi, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      exact ⟨i, hi, right_ne_zero_of_mul h⟩
  refine ⟨htest, ?_⟩
  refine LinearMap.ext fun φ => Subtype.ext ?_
  rw [UpperTheory.V.Z.Sym.Tf.rSpec Γ G V B s _ htest φ, LinearMap.sum_apply, Submodule.coe_sum]
  funext g
  rw [Finset.sum_apply]
  have key : ∀ h : G → ℂ, (∀ x : G ⧸ B.U, h (s.θ x.out) ≠ 0 → ∃ i ∈ S, f i (s.θ x.out) ≠ 0) →
      s.opF h φ.1 g = ∑ x ∈ hT.toFinset, h (s.θ x.out) • s.Θ (φ.1 (s.θ.symm g * x.out)) := by
    intro h hh
    refine finsum_eq_sum_of_support_subset _ fun x hx => ?_
    rw [Set.Finite.coe_toFinset]
    exact hh x (left_ne_zero_of_smul hx)
  rw [key _ (fun x hx => by
    obtain ⟨i, hi, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    exact ⟨i, hi, right_ne_zero_of_mul h⟩)]
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply,
    UpperTheory.V.Z.Sym.Tf.rSpec Γ G V B s _ (hf i hi) φ, key _ (fun x hx => ⟨i, hi, hx⟩), Finset.smul_sum]
  simp only [mul_smul]
