module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStableCharacterFlagOfCharpolyFactor
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

open Polynomial

theorem _root_.GlobalTheory.T.exists_stable_character_flag_of_charpoly_factor : ∀ (k Γ : Type) [Field k] [Group Γ] (n a t : ℕ) (r : Γ →* GL (Fin n) k) (ρ : Γ →* GL (Fin a) k) (ψ : Fin t → Γ →* kˣ), a + t = n → (∀ g, (r g : Matrix (Fin n) (Fin n) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly * ∏ s, (Polynomial.X - Polynomial.C ((ψ s g : kˣ) : k))) → ∃ (R : ℕ) (V : Fin (R + 1) → Submodule k (Fin n → k)) (rs : Fin t → Fin R), V 0 = ⊥ ∧ V (Fin.last R) = ⊤ ∧ Monotone V ∧ (∀ g j x, x ∈ V j → (r g : Matrix (Fin n) (Fin n) k).mulVec x ∈ V j) ∧ Function.Injective rs ∧ ∀ s, ∃ x ∈ V (rs s).succ, x ∉ V (rs s).castSucc ∧ V (rs s).succ = V (rs s).castSucc ⊔ Submodule.span k {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) k).mulVec x - ((ψ s g : kˣ) : k) • x ∈ V (rs s).castSucc := by
  first | exact @GlobalTheory.CharFlag.main | exact GlobalTheory.CharFlag.main | (intros; apply GlobalTheory.CharFlag.main <;> assumption)
