module

public import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PairingKernelLeOfSaturatedSubmodule
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
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd

@[expose] public section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

theorem _root_.GlobalTheory.T.pairing_kernel_le_of_saturated_submodule : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J) (g : Fin 2) (a' : ZMod d), ¬ X.big g a' → ∀ U' : Fin X.n → I (1 - g) → C, X.SatIn (1 - g) a' U' → ∀ (N : ℕ) (ψ : Fin N → J g → C), (∀ ν κ, V.Ge 0 (ψ ν κ)) → (∀ ν κ, (X.G g).ty (Sum.inr κ) ≠ a' → ψ ν κ = 0) → IndepMod V ψ → (∀ ν b, V.MM (∑ κ : J g, ∑ k : I (1 - g), ψ ν κ * X.pair g κ k * U' b k)) → N ≤ X.j := by
  first | exact @GlobalTheory.PairCount.pair_kernel_le | exact GlobalTheory.PairCount.pair_kernel_le | (intros; apply GlobalTheory.PairCount.pair_kernel_le <;> assumption)
