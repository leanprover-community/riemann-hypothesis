module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfDoubleAnnihilatorPairing
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


theorem _root_.GlobalTheory.T.card_le_of_double_annihilator_pairing : ∀ (O : Type) [CommRing O] (X Y E : Type) [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] [AddCommGroup E] [Module O E] [Finite X] (β : Y →ₗ[O] X →ₗ[O] E) (S : Submodule O X) (F : Finset Y) (Es : Finset E) (a : O), (∀ c, (∀ y, (∀ s ∈ S, β y s = 0) → β y c = 0) → c ∈ S) → (∀ y, (∀ s ∈ S, β y s = 0) → y ∈ F ∧ a • y = 0) → (∀ e : E, a • e = 0 → e ∈ Es) → Nat.card X ≤ Es.card ^ F.card * Nat.card S := by
  first | exact @GlobalTheory.card_le_of_double_annihilator | exact GlobalTheory.card_le_of_double_annihilator | (intros; apply GlobalTheory.card_le_of_double_annihilator <;> assumption)
