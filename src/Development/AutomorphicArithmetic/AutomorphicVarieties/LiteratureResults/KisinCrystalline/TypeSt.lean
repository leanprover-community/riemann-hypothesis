module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TypeDeformAlg
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
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

@[expose] public section

noncomputable section

namespace UpperTheory.V.Lit

open Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Loc TensorProduct GlobalTheory.Pst

variable {l : ℕ} [Fact l.Prime] {B V : Type} [CommRing B] [Algebra ℚ_[l] B] [AddCommGroup V] [Module B V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] B V] (K : FinExt l) (ρ : Representation B ↥(GK K) V)

def TypeSt (n : ℕ) (t : ↥(GK K) → B) : Prop :=
  ∃ x : Fin n → V ⊗[ℚ_[l]] Bst (PP l), (∀ a, x a ∈ Dpst (PP l) (resCoef ℚ_[l] ρ)) ∧
    (∀ y ∈ Dpst (PP l) (resCoef ℚ_[l] ρ), ∃! c : Fin n → B ⊗[ℚ_[l]] ↥(MaximalUnramifiedExtension l),
      y = ∑ a, Thick.sm V (Bst (PP l)) (c a) (x a)) ∧
    ∀ γ : ↥(GK K), (γ : GQ l) ∈ Iq l → ∀ M : Matrix (Fin n) (Fin n) (B ⊗[ℚ_[l]] ↥(MaximalUnramifiedExtension l)),
      (∀ b, stRep (PP l) (resCoef ℚ_[l] ρ) γ (x b) = ∑ a, Thick.sm V (Bst (PP l)) (M a b) (x a)) →
      M.trace = t γ ⊗ₜ[ℚ_[l]] 1

end UpperTheory.V.Lit
