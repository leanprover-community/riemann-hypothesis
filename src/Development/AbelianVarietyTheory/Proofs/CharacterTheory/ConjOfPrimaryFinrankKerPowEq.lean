module

public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsPermOfSumMinEqPositiveFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.PrimaryEndomorphismCyclicDecompositionFinrankKerStatement
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

@[expose] public section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem exists_conj_of_aeval'_equiv {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (g g' : Module.End F V) (φ : Module.AEval' g ≃ₗ[F[X]] Module.AEval' g') :
    ∃ e : V ≃ₗ[F] V, e.conj g = g' := by
  let e : V ≃ₗ[F] V := (Module.AEval'.of g).trans
    ((φ.restrictScalars F).trans (Module.AEval'.of g').symm)
  have h : ∀ v, e (g v) = g' (e v) := by
    intro v
    have h1 : Module.AEval'.of g (g v) = (X : F[X]) • Module.AEval'.of g v :=
      (Module.AEval'.X_smul_of g v).symm
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, h1, map_smul]
    exact Module.AEval'.of_symm_X_smul g' _
  refine ⟨e, ?_⟩
  ext v
  simp [LinearEquiv.conj_apply, h]

theorem primary_conj_of_finrank_ker_eq : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g g' : Module.End F V) (f : F[X]) (m : ℕ), Irreducible f → aeval g (f ^ m) = 0 → aeval g' (f ^ m) = 0 → (∀ j : ℕ, Module.finrank F (LinearMap.ker (aeval g (f ^ j))) = Module.finrank F (LinearMap.ker (aeval g' (f ^ j)))) → ∃ e : V ≃ₗ[F] V, e.conj g = g' := by
  intro F _ V _ _ _ g g' f m hf hg hg' hk
  obtain ⟨d, e, he, ⟨φ⟩, hd⟩ := GlobalTheory.T.primary_endomorphism_cyclic_decomposition_finrank_ker F V g f m hf hg
  obtain ⟨d', e', he', ⟨φ'⟩, hd'⟩ := GlobalTheory.T.primary_endomorphism_cyclic_decomposition_finrank_ker F V g' f m hf hg'
  have hpos : 0 < f.natDegree := hf.natDegree_pos
  have hs : ∀ j : ℕ, ∑ i, min j (e i) = ∑ i, min j (e' i) := by
    intro j
    have := hk j
    rw [hd j, hd' j] at this
    exact Nat.eq_of_mul_eq_mul_left hpos this
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_perm_of_sum_min_eq_positive_family d d' e e' he he' hs
  obtain rfl : e = fun i => e' (σ i) := funext fun i => (hσ i).symm
  exact exists_conj_of_aeval'_equiv g g' (φ.trans
    ((LinearEquiv.piCongrLeft F[X] (fun i => F[X] ⧸ Ideal.span {f ^ e' i}) σ).trans φ'.symm))

end GlobalTheory.CuspGL
