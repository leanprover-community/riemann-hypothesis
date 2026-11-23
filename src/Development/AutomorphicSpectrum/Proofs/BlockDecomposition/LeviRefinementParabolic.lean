module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import GroundTheory.AutomorphicForms.InductionParabolicGroups
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import GroundTheory.AutomorphicForms.FiniteBruhat
public import GroundTheory.AutomorphicForms.GeometricLemmaJacquetCell
public import GroundTheory.AutomorphicForms.GeometricLemmaModular
public import GroundTheory.AutomorphicForms.GeometricLemmaNormal
import GroundTheory.AutomorphicForms.GeometricLemmaOrbit

@[expose] public section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.RelUnipBridge

theorem one_apply_sigma {k n α : Type} [Zero k] [One k] [DecidableEq n] {m : α → Type}
    [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ n) (a : α) (r s : m a) :
    (1 : Matrix n n k) (e ⟨a, r⟩) (e ⟨a, s⟩) = (1 : Matrix (m a) (m a) k) r s := by
  by_cases h : r = s
  · subst h; simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne]
    intro h'
    have := e.injective h'
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at this
    exact h this

theorem mem_relUnip_iff_leviEmb_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {c : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (e : (Σ i, m i) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i) (δ : Fin N → ℕ) (hδ : ∀ i j j' (t : c i j) (t' : c i j'), δ (e ⟨i, f i ⟨j, t⟩⟩) < δ (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j') (x : Levi k m), x ∈ relUnip k f ↔ leviEmb k e x ∈ unipotentRadical k N δ := by
  intro k _ _ _ _ α β' _ _ _ _ N m _ _ c _ _ e f δ hδ x
  rw [GroundTheory.Automorphic.Parabolic.mem_unipotentRadical]
  constructor
  · intro hx
    have hx' : ∀ a, x a ∈ unipRad k (f a) := fun a => hx a trivial
    refine ⟨fun r s hrs => ?_, fun r s hrs => ?_⟩
    · obtain ⟨⟨a, r⟩, rfl⟩ := e.surjective r
      obtain ⟨⟨b, s⟩, rfl⟩ := e.surjective s
      by_cases hab : a = b
      · subst hab
        rw [leviEmb_apply_same]
        obtain ⟨⟨j, t⟩, rfl⟩ := (f a).surjective r
        obtain ⟨⟨j', t'⟩, rfl⟩ := (f a).surjective s
        exact mem_parab_iff.1 (mem_unipRad.1 (hx' a)).1 j j' t t' ((hδ a j' j t' t).1 hrs)
      · exact leviEmb_apply_ne k e x hab r s
    · obtain ⟨⟨a, r⟩, rfl⟩ := e.surjective r
      obtain ⟨⟨b, s⟩, rfl⟩ := e.surjective s
      by_cases hab : a = b
      · subst hab
        rw [leviEmb_apply_same, one_apply_sigma]
        obtain ⟨⟨j, t⟩, rfl⟩ := (f a).surjective r
        obtain ⟨⟨j', t'⟩, rfl⟩ := (f a).surjective s
        have hjj : j = j' := by
          rcases lt_trichotomy j j' with h | h | h
          · exact absurd ((hδ a j j' t t').2 h) hrs.not_lt
          · exact h
          · exact absurd ((hδ a j' j t' t).2 h) hrs.symm.not_lt
        subst hjj
        rw [one_apply_sigma]
        exact (mem_unipRad.1 (hx' a)).2 j t t'
      · rw [leviEmb_apply_ne k e x hab r s, Matrix.one_apply_ne]
        intro h
        exact hab (congrArg Sigma.fst (e.injective h))
  · rintro ⟨hP, h1⟩ a -
    refine mem_unipRad.2 ⟨mem_parab_iff.2 fun j j' t t' hjj => ?_, fun j t t' => ?_⟩
    · have := hP ((hδ a j' j t' t).2 hjj)
      rwa [leviEmb_apply_same] at this
    · have hd : δ (e ⟨a, f a ⟨j, t⟩⟩) = δ (e ⟨a, f a ⟨j, t'⟩⟩) := by
        rcases lt_trichotomy (δ (e ⟨a, f a ⟨j, t⟩⟩)) (δ (e ⟨a, f a ⟨j, t'⟩⟩)) with h | h | h
        · exact absurd ((hδ a j j t t').1 h) (lt_irrefl j)
        · exact h
        · exact absurd ((hδ a j j t' t).1 h) (lt_irrefl j)
      have := h1 _ _ hd
      rwa [leviEmb_apply_same, one_apply_sigma, one_apply_sigma] at this

end GlobalTheory.CompanionTheory.RelUnipBridge
