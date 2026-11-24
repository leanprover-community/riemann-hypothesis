module

public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastRowTopComponentDualWeylEqMonomialMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Foundations.GelfA
import Development.AbelianVarietyTheory.Definitions.Foundations.TracePowApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

theorem _root_.GlobalTheory.T.lastRow_top_component_dualWeyl_eq_monomial_mul : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : Fin n → ℕ) (G : BP K n), G ∈ dualWeyl K (n + 1) n lam → ∀ b : Fin n → ℕ, (∀ s, b s ≤ lam s) → (∀ β', zcomp K n β' G ≠ 0 → omg β' ≤ omg fun s => (b s : ℤ)) → ∃ f ∈ dualWeyl K n n (fun s => lam s - b s), zcomp K n (fun s => (b s : ℤ)) G = zmon K n b * emb K n f := by
  first | exact @GlobalTheory.BrCompare.zcomp_top_eq_zmon_mul_emb | exact GlobalTheory.BrCompare.zcomp_top_eq_zmon_mul_emb | (intros; apply GlobalTheory.BrCompare.zcomp_top_eq_zmon_mul_emb <;> assumption)
