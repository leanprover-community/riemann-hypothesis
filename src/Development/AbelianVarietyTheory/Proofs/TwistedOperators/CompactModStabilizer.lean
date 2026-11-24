module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.PairingOne

section Alg
variable {k : Type*} [Field k] {m : Type*} [Fintype m] [DecidableEq m]

end Alg

variable {k : Type*} [Field k] [ValuativeRel k] {m : Type*} [Fintype m] [DecidableEq m]

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCompact_bounded (t : ValueGroupWithZero k) :
    IsCompact {w : GL m k | (∀ a b, valuation k (w.val a b) ≤ t) ∧ ∀ a b, valuation k ((w⁻¹).val a b) ≤ t} := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hK : IsCompact {A : Matrix m m k | ∀ i j, valuation k (A i j) ≤ t} := by
    have h : IsCompact (Set.pi Set.univ fun _ : m => Set.pi Set.univ fun _ : m => {x : k | valuation k x ≤ t}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k t
    have e : {A : Matrix m m k | ∀ i j, valuation k (A i j) ≤ t} =
        (Set.pi Set.univ fun _ : m => Set.pi Set.univ fun _ : m => {x : k | valuation k x ≤ t}) :=
      Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
    rw [e]; exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix m m k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, (MulOpposite.op_injective).mem_set_image]

end GlobalTheory.PairingOne
