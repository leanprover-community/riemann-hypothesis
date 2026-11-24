module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionUpperLeftCommutesEmbedding
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

theorem _root_.GlobalTheory.T.fock_action_upper_left_commutes_embedding : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a a' : Fin P) (G : Mdl P Q), fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inl a')) (embR P Q R h k G) = embR P Q R h k (opR P Q R k (Sum.inl a) (Sum.inl a') G) := by
  first | exact @GlobalTheory.CharPair.FirstBlock.act_first_block | exact GlobalTheory.CharPair.FirstBlock.act_first_block | (intros; apply GlobalTheory.CharPair.FirstBlock.act_first_block <;> assumption)
