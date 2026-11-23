module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLat
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap

@[expose] public section

open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrb

theorem isIntegral_of_mapsTo_lattice : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (M : Submodule O (Fin n → K)),
    IsLatV O M → ∀ c : Matrix (Fin n) (Fin n) K, (∀ v ∈ M, c *ᵥ v ∈ M) → IsIntegral O c := by
  intro O K _ _ _ n M hM c hc
  classical
  haveI : Module.Finite O M := Module.Finite.iff_fg.mpr hM.1
  let f : Module.End O M :=
    { toFun := fun v => ⟨c *ᵥ (v : Fin n → K), hc v v.2⟩
      map_add' := fun x y => by ext1; simp [Matrix.mulVec_add]
      map_smul' := fun a x => by
        ext1
        simp only [Submodule.coe_smul, RingHom.id_apply, SetLike.val_smul]
        rw [Matrix.mulVec_smul] }
  have hpow : ∀ k : ℕ, ∀ v : M, (c ^ k) *ᵥ (v : Fin n → K) = (((f ^ k) v : M) : Fin n → K) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, ← Matrix.mulVec_mulVec, pow_succ, Module.End.mul_apply]
      have h1 : ((f v : M) : Fin n → K) = c *ᵥ (v : Fin n → K) := rfl
      rw [← h1, ih]
  have key : ∀ q : O[X], ∀ v : M, aeval c q *ᵥ (v : Fin n → K) = (((aeval f q) v : M) : Fin n → K) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq => intro v; simp [Matrix.add_mulVec, hp, hq]
    | monomial k a =>
      intro v
      rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def,
        Matrix.smul_mulVec, LinearMap.smul_apply, Submodule.coe_smul, hpow]
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero O f
  refine ⟨p, hp, ?_⟩
  rw [← Polynomial.aeval_def]
  set A := aeval c p
  have hker : Submodule.span K (M : Set (Fin n → K)) ≤ LinearMap.ker (Matrix.mulVecLin A) := by
    rw [Submodule.span_le]
    intro v hv
    have := key p ⟨v, hv⟩
    rw [hpf] at this
    simpa using this
  rw [hM.2, top_le_iff, LinearMap.ker_eq_top] at hker
  have : Matrix.toLin' A = 0 := by rw [Matrix.toLin'_apply']; exact hker
  simpa using this

end GlobalTheory.LatOrb
