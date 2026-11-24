module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricUnipotentMemOfFlagCongruenceDual
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

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

theorem _root_.GlobalTheory.T.symmetricUnipotent_mem_of_flagCongruence_dual : ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ M M' : GL (Fin n) K, (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k → FlagCond (fun c : K => c = 0) ρ k 1 (M : Matrix (Fin n) (Fin n) K) → FlagCond (fun c : K => c = 0) ρ k 0 (M' : Matrix (Fin n) (Fin n) K) → M ∈ unipSym K n ρ k := by
  first | exact @GlobalTheory.FlagCase.flagCond_dual_unipSym | exact GlobalTheory.FlagCase.flagCond_dual_unipSym | (intros; apply GlobalTheory.FlagCase.flagCond_dual_unipSym <;> assumption)
