module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticNormsTraceUniformizerFactsStatement
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.SelfDualLattice

section Forms

variable {K : UQ} {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
  {h : V → V → K.E}

def formL (hadd : ∀ x y z, h (x + y) z = h x z + h y z) (hsmul : ∀ (c : K.E) x z, h (c • x) z = c * h x z)
    (z : V) : V →ₗ[K.E] K.E where
  toFun x := h x z
  map_add' x y := hadd x y z
  map_smul' c x := hsmul c x z

end Forms

end GlobalTheory.SelfDualLattice

namespace GlobalTheory.SelfDualLattice

variable {K : UQ} {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
  {h : V → V → K.E}

end GlobalTheory.SelfDualLattice

namespace GlobalTheory.SelfDualLattice

theorem exists_orthonormal_family (K : UQ)
    (hN : ∀ u : K.Oˣ, K.c (algebraMap K.O K.E u) = algebraMap K.O K.E u →
      ∃ z : K.Oˣ, algebraMap K.O K.E u = algebraMap K.O K.E z * K.c (algebraMap K.O K.E z))
    (hT : ∃ z : K.O, algebraMap K.O K.E z + K.c (algebraMap K.O K.E z) = 1) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
      [Module.Finite K.E V] (h : V → V → K.E), Module.finrank K.E V = n →
      (∀ x y z, h (x + y) z = h x z + h y z) → (∀ (c : K.E) x z, h (c • x) z = c * h x z) →
      (∀ x y, h y x = K.c (h x y)) → ∀ L : Submodule K.O V, L.FG →
      Submodule.span K.E (L : Set V) = ⊤ →
      (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
      ∃ m, ∃ v : Fin m → V, (∀ i j, h (v i) (v j) = if i = j then 1 else 0) ∧
        Submodule.span K.O (Set.range v) = L := by
  first
  | exact @_root_.GlobalTheory.UnitPairNorm.main
  | exact _root_.GlobalTheory.UnitPairNorm.main
  | (apply _root_.GlobalTheory.UnitPairNorm.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitPairNorm.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitPairNorm.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitPairNorm.main ..)

end GlobalTheory.SelfDualLattice

namespace GlobalTheory.SelfDualLattice

theorem exists_orthonormal_basis : ∀ (K : UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] [Module.Finite K.E V] (h : V → V → K.E),
    (∀ x y z, h (x + y) z = h x z + h y z) → (∀ (c : K.E) x z, h (c • x) z = c * h x z) →
    (∀ x y, h y x = K.c (h x y)) → ∀ L : Submodule K.O V, L.FG →
    Submodule.span K.E (L : Set V) = ⊤ →
    (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
    ∃ b : Module.Basis (Fin (Module.finrank K.E V)) K.E V, Submodule.span K.O (Set.range b) = L ∧
      ∀ i j, h (b i) (b j) = if i = j then 1 else 0 := by
  intro K V _ _ _ _ _ h hadd hsmul hsym L hfg hspan hdual
  obtain ⟨hN, hT, -, -⟩ := GlobalTheory.T.unramifiedQuadratic_norms_trace_uniformizer_facts K
  obtain ⟨m, v, hvo, hvs⟩ := exists_orthonormal_family K hN hT _ V h rfl hadd hsmul hsym L hfg hspan hdual
  have hli : LinearIndependent K.E v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (formL hadd hsmul (v i)) hg

    simp only [map_sum, map_smul, map_zero, smul_eq_mul] at this
    change ∑ j, g j * h (v j) (v i) = 0 at this
    simpa [hvo] using this
  have hsp : ⊤ ≤ Submodule.span K.E (Set.range v) := by
    rw [← hspan, ← hvs, Submodule.span_span_of_tower]
  set b0 := Module.Basis.mk hli hsp with hb0
  have hm : m = Module.finrank K.E V := by
    rw [Module.finrank_eq_card_basis b0, Fintype.card_fin]
  refine ⟨b0.reindex (finCongr hm), ?_, ?_⟩
  · rw [Module.Basis.range_reindex, hb0, Module.Basis.coe_mk, hvs]
  · intro i j
    simp only [Module.Basis.reindex_apply, hb0, Module.Basis.coe_mk, hvo]
    simp

end GlobalTheory.SelfDualLattice
