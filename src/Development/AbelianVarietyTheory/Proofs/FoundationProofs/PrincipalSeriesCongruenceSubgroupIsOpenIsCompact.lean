module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePr
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem grp_isOpen_isCompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → IsOpen (grp ψ) ∧ IsCompact (grp ψ) := by
  intro k _ _ _ _ n ψ hψ
  have hT := (triv_ev_props k).2.2.2.2.2.1
  have hS : ∀ i j, IsOpen {x : k | Triv (ψ i / ψ j) x} ∧ IsClosed {x : k | Triv (ψ i / ψ j) x} := fun i j => by
    refine hT _ ?_
    rw [div_eq_mul_inv]
    exact (hψ i).mul (hψ j).inv
  have hc : ∀ i j : Fin n, Continuous fun g : GL (Fin n) k => g.val i j := fun i j =>
    by
    have h1 : Continuous fun g : GL (Fin n) k => (g.val : Matrix (Fin n) (Fin n) k) := Units.continuous_val
    exact (continuous_apply j).comp ((continuous_apply i).comp h1)
  have hE : grp ψ = (KO k (Fin n) : Set (GL (Fin n) k)) ∩
      ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j), (fun g : GL (Fin n) k => g.val i j) ⁻¹' {x : k | Triv (ψ i / ψ j) x} := by
    ext g; simp [grp]
  rw [hE]
  refine ⟨GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => (hS i j).1.preimage (hc i j)), ?_⟩
  exact GlobalTheory.SplitFlip.isCompact_KO.inter_right (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_iInter fun _ => (hS i j).2.preimage (hc i j))

end GlobalTheory.PsType
