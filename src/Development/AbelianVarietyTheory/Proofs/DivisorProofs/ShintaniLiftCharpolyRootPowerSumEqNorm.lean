module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EveryElementIsNorm
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

namespace GlobalTheory.Shin

theorem rootSum_map_pullθ {F F' : Type} [Field F] [Field F'] [Algebra F F']
    (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ) (k : ℕ) (P : F[X]) :
    rootSum θ k (P.map (algebraMap F F')) = rootSum (pullθ ι θ) k P := by
  unfold rootSum pullθ
  have e1 : (P.map (algebraMap F F')).map (algebraMap F' (AlgebraicClosure F')) =
      (P.map (algebraMap F (AlgebraicClosure F))).map (ι : AlgebraicClosure F →+* AlgebraicClosure F') := by
    rw [Polynomial.map_map, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    congr 1
    ext x
    simp
  rw [e1, (IsAlgClosed.splits _).roots_map, Multiset.map_map]
  rfl

theorem charpoly_of_isConj {K : Type} [Field K] {n : ℕ} {a b : GL (Fin n) K} (h : IsConj a b) :
    Matrix.charpoly (a : Matrix (Fin n) (Fin n) K) = Matrix.charpoly (b : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

theorem shLift_chG_rootSum : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ) (k n : ℕ) (δ : GL (Fin n) F'), shLift s (chG (rootSum (pullθ ι θ) k) n) δ = chG (rootSum θ k) n (nrm s δ) := by
  intro F F' _ _ _ _ s hs ι θ k n δ
  have hex : ∃ γ, IsNorm s δ γ := GlobalTheory.T.every_element_is_norm F F' s hs n δ
  unfold shLift
  rw [dite_eq_left hex]
  generalize hex.choose = γ, hex.choose_spec = hγ
  unfold IsNorm at hγ
  unfold chG
  rw [← charpoly_of_isConj hγ]
  have hm : ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
      (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F F') := by
    ext i j; rfl
  rw [hm, Matrix.charpoly_map, rootSum_map_pullθ]

end GlobalTheory.Shin
