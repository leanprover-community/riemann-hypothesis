module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Index
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetRegroupCommutative
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


theorem _root_.GlobalTheory.T.finsum_doubleCoset_regroup_commutative : ∀ (G : Type) [Group G] (T Γ C K' : Subgroup G) (φ : G → ℂ), (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) → C ≤ T → (∀ x : G, T ⊓ K'.map (MulAut.conj x).toMonoidHom ≤ C ∧ (T ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0) → (∀ t ∈ T, ∀ k ∈ K', ∀ x, φ (t * x * k) = φ x) → ∑ᶠ q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G), ((Nat.card ((Γ ⊓ T) ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℂ))⁻¹ * φ (Quotient.out q) = (Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (Γ ⊓ C : Subgroup G) : ℂ) * ∑ᶠ q : DoubleCoset.Quotient (T : Set G) (K' : Set G), (((T ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ) * φ (Quotient.out q) := by
  first | exact @GlobalTheory.finsum_doubleCoset_regroup | exact GlobalTheory.finsum_doubleCoset_regroup | (intros; apply GlobalTheory.finsum_doubleCoset_regroup <;> assumption)
