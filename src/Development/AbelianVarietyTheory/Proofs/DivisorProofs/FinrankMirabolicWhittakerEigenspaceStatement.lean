module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMirabolicWhittakerEigenspace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem _root_.GlobalTheory.T.finrank_mirabolic_whittaker_eigenspace : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (k : ℕ) (P : Subgroup (GL (Fin (k + 1)) F)), (∀ g, g ∈ P ↔ ∀ j, (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (Fin.last k) j = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (Fin.last k) j) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Representation ℂ P V), finrank ℂ (eig π {p | (p : GL (Fin (k + 1)) F) ∈ unipSym F (k + 1) 0 k} fun p => ψ (edgeSum (symEdge 0 k) (p : GL (Fin (k + 1)) F))) = ∑ j ∈ Finset.range (k + 1), gam (Fintype.card F) (k - j) * finrank ℂ (eig π {p | (p : GL (Fin (k + 1)) F) ∈ unip F (k + 1)} fun p => ψ (edgeSum (cutEdge (j)) (p : GL (Fin (k + 1)) F))) := by
  first | exact @GlobalTheory.FinGL.Mir.mirabolic_whittaker | exact GlobalTheory.FinGL.Mir.mirabolic_whittaker | (intros; apply GlobalTheory.FinGL.Mir.mirabolic_whittaker <;> assumption)
