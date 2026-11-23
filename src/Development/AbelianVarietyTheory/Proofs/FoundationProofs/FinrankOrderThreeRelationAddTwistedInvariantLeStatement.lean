module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTwInv
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankOrderThreeRelationAddTwistedInvariantLe
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

open GlobalTheory.HeckeFamilyMatrices.CocBound

theorem _root_.GlobalTheory.T.finrank_orderThreeRelation_add_twistedInvariant_le : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (t : G), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → t ^ 6 = 1 → FiniteDimensional ℂ (twInv Γ (t ^ 3) (ρ (t ^ 3))) → FiniteDimensional ℂ (relThree Γ ρ t) ∧ Module.finrank ℂ (relThree Γ ρ t) + Module.finrank ℂ (twInv Γ t (ρ t)) ≤ Module.finrank ℂ (twInv Γ (t ^ 3) (ρ (t ^ 3))) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_relThree_add_finrank_twInv_le | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_relThree_add_finrank_twInv_le | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_relThree_add_finrank_twInv_le <;> assumption)
