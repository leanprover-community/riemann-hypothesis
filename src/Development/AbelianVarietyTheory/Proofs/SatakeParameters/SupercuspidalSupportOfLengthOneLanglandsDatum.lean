module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocGL.LenOneSupport

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_isCosocle_prodIrr_one (ρ x : IrrGL (k := k)) (y : Fin 1 → IrrGL (k := k)) (hy : ∀ a, y a = ρ)
    (hd : ∑ a, (y a).1 = x.1) (h : IsCosocle x.rep (prodIrr y hd)) : x = ρ := by
  have e : y = fun _ => ρ := funext hy
  subst e
  obtain ⟨n, c⟩ := x
  obtain ⟨m, r⟩ := ρ
  have hmn : m = n := by simpa using hd
  subst hmn
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one (⟨m, r⟩ : IrrGL (k := k)) hd
  have h2 := h.of_equiv (.refl _) ψ.symm
  obtain ⟨φ⟩ := (isCosocle_self r.rep.irr).unique h2
  have e1 := (IrrGL.of_eq_of (hs := c.rep.smooth) (hi := c.rep.irr) (hs' := r.rep.smooth) (hi' := r.rep.irr)).2 ⟨φ⟩
  exact (IrrGL.of_rep (⟨m, c⟩ : IrrGL (k := k))).symm.trans (e1.trans (IrrGL.of_rep (⟨m, r⟩ : IrrGL (k := k))))

theorem eq_first_of_isLSeg {Δ : Segment k} (hl : Δ.len = 1) {x : IrrGL (k := k)} (h : IsLSeg Δ x.rep) : x = Δ.first := by
  have e : Δ = Segment.single Δ.first Δ.isCusp_first := Segment.ext_first rfl hl
  rw [e] at h
  obtain ⟨hd, hc⟩ := h
  refine eq_of_isCosocle_prodIrr_one Δ.first x _ (fun a => ?_) hd hc
  rw [Fin.fin_one_eq_zero a]
  simp [Segment.term, Segment.single, Segment.ofFirst]
  rfl

theorem hasSupport_first_of_isL_len_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (c : ℕ) (Δ : Fin c → Segment k) (x : IrrGL (k := k)), (∀ i, (Δ i).len = 1) →
    IsL ((List.ofFn Δ : List (Segment k)) : Multiset (Segment k)) x.rep →
    HasSupport x.rep (Finset.univ.val.map fun i => (Δ i).first) := by
  intro k _ _ _ _ c Δ x hl hL
  obtain ⟨h, y, hd, ⟨Δ', ⟨hmap, -⟩, hy⟩, hcos⟩ := hL
  have hl' : ∀ i, (Δ' i).len = 1 := fun i => by
    have hm : Δ' i ∈ ((List.ofFn Δ : List (Segment k)) : Multiset (Segment k)) :=
      hmap ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
    obtain ⟨j, hj⟩ := List.mem_ofFn.1 (Multiset.mem_coe.1 hm)
    rw [← hj]; exact hl j
  have hyf : y = fun i => (Δ' i).first := funext fun i => eq_first_of_isLSeg (hl' i) (hy i)
  subst hyf
  have hs := hasSupport_of_isSubquotient hcos.1 (fun i => (Δ' i).isCusp_first) hcos.isSubquotient
  have e : (Finset.univ.val.map fun i => (Δ' i).first) = Finset.univ.val.map fun i => (Δ i).first := by
    have e2 : (Finset.univ.val.map Δ : Multiset (Segment k)) = ((List.ofFn Δ : List (Segment k)) : Multiset (Segment k)) := by
      rw [← Fin.univ_val_map]
    have m1 := Multiset.map_map Segment.first Δ' Finset.univ.val
    have m2 := Multiset.map_map Segment.first Δ Finset.univ.val
    simp only [Function.comp_def] at m1 m2
    rw [← m1, ← m2, hmap, e2]
  rw [e] at hs
  exact hs

end GlobalTheory.LocGL.LenOneSupport
