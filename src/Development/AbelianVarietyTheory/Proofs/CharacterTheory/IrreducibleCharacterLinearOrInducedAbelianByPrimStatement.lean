module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleCharacterLinearOrInducedAbelianByPrim
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

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.irreducibleCharacter_linear_or_induced_abelianByPrimePower : ∀ (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G] (χ : G → L), AbByP G → IsIrrChar L L χ → (∃ lam : G →* Lˣ, ∀ g, χ g = (lam g : L)) ∨ ∃ T : Subgroup G, T ≠ ⊤ ∧ ∃ ψ : T → L, IsChar L L ψ ∧ χ = ind T ψ := by
  first | exact @GlobalTheory.BI.irrChar_linear_or_induced | exact GlobalTheory.BI.irrChar_linear_or_induced | (intros; apply GlobalTheory.BI.irrChar_linear_or_induced <;> assumption)
