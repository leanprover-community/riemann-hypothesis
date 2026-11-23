module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChainStepKernelRankLeModMaxIdeal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

theorem _root_.GlobalTheory.T.chainStep_kernel_rank_le_mod_maxIdeal : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ (i : ℕ) (S : Sys (X.G g)) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z (I g)), Adapted S D a i → ∀ s : ℕ, s + 1 < Formalism.BaseCaseIdentities.Kn i → ∀ (m : ℕ) (y : Fin m → I g → C), (∀ δ c, V.Ge 0 (y δ c)) → IndepMod V (fun δ c => if D.lev c = s then y δ c else 0) → ∀ (N : ℕ) (x : Fin N → Fin m → C), (∀ ν δ, V.Ge 0 (x ν δ)) → IndepMod V x → (∀ ν e, D.lev e = s + 1 → V.MM (∑ δ, x ν δ ^ (V.l ^ 2) * ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s), (V.l : C) * D.al c 2 e * y δ c ^ (V.l ^ 2))) → N ≤ X.j' := by
  first | exact @GlobalTheory.ChainStep.rank_le | exact GlobalTheory.ChainStep.rank_le | (intros; apply GlobalTheory.ChainStep.rank_le <;> assumption)
