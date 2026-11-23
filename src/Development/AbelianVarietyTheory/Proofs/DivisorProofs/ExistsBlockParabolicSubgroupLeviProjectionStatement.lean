module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockParabolicSubgroupLeviProjection
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection : ∀ (F : Type) [Field F] (a b n : ℕ), n = a + b → ∃ (H : Subgroup (GL (Fin n) F)) (π : H →* GL (Fin a) F × GL (Fin b) F), (∀ x, x ∈ H ↔ InPar a x) ∧ Function.Surjective π ∧ (∀ p : H, π p = (tlG a p.1, brG a b p.1)) ∧ (∀ p : H, ((π p).1 : Matrix (Fin a) (Fin a) F) = tl a (p.1 : Matrix (Fin n) (Fin n) F) ∧ ((π p).2 : Matrix (Fin b) (Fin b) F) = br a b (p.1 : Matrix (Fin n) (Fin n) F)) ∧ ∀ p : H, Matrix.charpoly (p.1 : Matrix (Fin n) (Fin n) F) = Matrix.charpoly ((π p).1 : Matrix (Fin a) (Fin a) F) * Matrix.charpoly ((π p).2 : Matrix (Fin b) (Fin b) F) := by
  first | (exact @GlobalTheory.Shin.BlockPar.block_par) | (exact GlobalTheory.Shin.BlockPar.block_par) | (intros; apply GlobalTheory.Shin.BlockPar.block_par  <;> assumption)
