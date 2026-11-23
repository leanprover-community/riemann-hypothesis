module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import GroundTheory.AutomorphicForms.Iwasawa
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

namespace GlobalTheory.CompanionTheory.CellCompare

theorem mem_relParab_iff_leviEmb_mem_blockUpper :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ}
      {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {c : α → β' → Type}
      [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (e : (Σ i, m i) ≃ Fin N)
      (f : ∀ i, (Σ j, c i j) ≃ m i) (δ : Fin N → ℕ)
      (hδ : ∀ i j j' (t : c i j) (t' : c i j'),
        δ (e ⟨i, f i ⟨j, t⟩⟩) < δ (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j') (x : Levi k m),
      x ∈ relParab k f ↔ leviEmb k e x ∈ blockUpper k N δ := by
  intro k _ _ _ _ α β' _ _ _ _ N m _ _ c _ _ e f δ hδ x
  unfold relParab
  rw [Subgroup.mem_pi]
  change _ ↔ (leviEmb k e x : Matrix (Fin N) (Fin N) k).BlockTriangular δ
  constructor
  · intro hx p q hpq
    obtain ⟨⟨a, u⟩, rfl⟩ := e.surjective p
    obtain ⟨⟨b, v⟩, rfl⟩ := e.surjective q
    by_cases hab : a = b
    · subst hab
      obtain ⟨⟨j, t⟩, rfl⟩ := (f a).surjective u
      obtain ⟨⟨j', t'⟩, rfl⟩ := (f a).surjective v
      rw [leviEmb_apply_same]
      exact mem_parab_iff.1 (hx a trivial) j j' t t' ((hδ a j' j t' t).1 hpq)
    · exact leviEmb_apply_ne k e x hab u v
  · intro hx i _
    rw [mem_parab_iff]
    intro j j' t t' hjj
    have h := hx ((hδ i j' j t' t).2 hjj)
    rwa [leviEmb_apply_same] at h

end GlobalTheory.CompanionTheory.CellCompare
