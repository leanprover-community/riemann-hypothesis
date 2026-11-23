module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalTwists.Reduce
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem exists_minimal_compl {M O : Type*} [AddCommGroup M] [Module ℂ M] (act : O → Module.End ℂ M)
    (C : Submodule ℂ M) (hC : ∀ o, ∀ x ∈ C, act o x ∈ C)
    (hc : ∀ U ≤ C, (∀ o, ∀ x ∈ U, act o x ∈ U) →
      ∃ D ≤ C, (∀ o, ∀ x ∈ D, act o x ∈ D) ∧ U ⊓ D = ⊥ ∧ U ⊔ D = C) {φ : M} (hφ : φ ∈ C) (h0 : φ ≠ 0) :
    ∃ V D : Submodule ℂ M, V ≤ C ∧ D ≤ C ∧ (∀ o, ∀ x ∈ V, act o x ∈ V) ∧ V ≠ ⊥ ∧
      (∀ W ≤ V, (∀ o, ∀ x ∈ W, act o x ∈ W) → W = ⊥ ∨ W = V) ∧ (∀ o, ∀ x ∈ D, act o x ∈ D) ∧
      V ⊓ D = ⊥ ∧ V ⊔ D = C ∧ φ ∉ D := by
  let U : Submodule ℂ M := sInf {W | φ ∈ W ∧ ∀ o, ∀ x ∈ W, act o x ∈ W}
  have hUC : U ≤ C := sInf_le ⟨hφ, hC⟩
  have hφU : φ ∈ U := Submodule.mem_sInf.2 fun W hW => hW.1
  have hUs : ∀ o, ∀ x ∈ U, act o x ∈ U := fun o x hx =>
    Submodule.mem_sInf.2 fun W hW => hW.2 o x (Submodule.mem_sInf.1 hx W hW)
  have hle := UpperTheory.V.TR.SS.le_sSup_minimal act U hUs fun W hW hs => by
    obtain ⟨D, -, d2, d3, d4⟩ := hc W (hW.trans hUC) hs
    refine ⟨D ⊓ U, inf_le_right, fun o x hx => ⟨d2 o x hx.1, hUs o x hx.2⟩, ?_, ?_⟩
    · rw [← inf_assoc, d3, bot_inf_eq]
    · rw [← sup_inf_assoc_of_le _ hW, d4, inf_eq_right.2 hUC]
  by_contra hn
  refine h0 ((Submodule.mem_bot ℂ).1 ((hle.trans (sSup_le ?_)) hφU))
  rintro V ⟨v1, v2, v3, v4⟩
  obtain ⟨D, d1, d2, d3, d4⟩ := hc V (v1.trans hUC) v2
  by_cases hD : φ ∈ D
  · rw [← d3]
    exact le_inf le_rfl (v1.trans (sInf_le ⟨hD, d2⟩))
  · exact absurd ⟨V, D, v1.trans hUC, d1, v2, v3, v4, d2, d3, d4, hD⟩ hn

private theorem exists_proj {M : Type*} [AddCommGroup M] [Module ℂ M] {C V D : Submodule ℂ M} (hV : V ≤ C) (hD : D ≤ C)
    (h1 : V ⊓ D = ⊥) (h2 : V ⊔ D = C) :
    ∃ p : C →ₗ[ℂ] V, (∀ x : C, x.1 - (p x).1 ∈ D) ∧ ∀ (x : C) (v : V), x.1 - v.1 ∈ D → p x = v := by
  have hc : IsCompl (V.comap C.subtype) (D.comap C.subtype) := by
    constructor
    · rw [disjoint_iff, ← Submodule.comap_inf, h1, Submodule.comap_bot, Submodule.ker_subtype]
    · rw [codisjoint_iff, eq_top_iff]
      rintro ⟨x, hx⟩ -
      obtain ⟨v, hv, d, hd, rfl⟩ := Submodule.mem_sup.1 (h2.ge hx)
      exact Submodule.mem_sup.2 ⟨⟨v, hV hv⟩, hv, ⟨d, hD hd⟩, hd, rfl⟩
  let p : C →ₗ[ℂ] V := (Submodule.comapSubtypeEquivOfLe hV).toLinearMap ∘ₗ Submodule.projectionOnto _ _ hc
  have hp : ∀ x : C, x.1 - (p x).1 ∈ D := fun x => by
    obtain ⟨v, hv, d, hd, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top.ge (Submodule.mem_top (x := x)))
    have e1 : Submodule.projectionOnto _ _ hc v = ⟨v, hv⟩ := Submodule.projectionOnto_apply_left hc ⟨v, hv⟩
    have e2 : Submodule.projectionOnto _ _ hc d = 0 := Submodule.projectionOnto_apply_right hc ⟨d, hd⟩
    have : (p (v + d)).1 = v.1 := by
      simp only [p, LinearMap.comp_apply, map_add (f := _), e1, e2, map_zero, add_zero]
      rfl
    rw [this]
    simpa using hd
  refine ⟨p, hp, fun x v h => Subtype.ext (sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 (h1.le ⟨V.sub_mem (p x).2 v.2, ?_⟩)))⟩
  have := D.sub_mem h (hp x)
  rwa [sub_sub_sub_cancel_left] at this

theorem UpperTheory.V.Cj.S.cuspProj :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.CiBasic → UpperTheory.V.Cj.S.CiCompl → UpperTheory.V.Cj.S.CuspProj := by
  intro _ hb hc E _ _ _ a ha m hm φ h0
  obtain ⟨V, D, v1, d1, v2, v3, v4, d2, h1, h2, hφ⟩ :=
    exists_minimal_compl act (CI a m) (hb E a m).1 (hc E a ha m) φ.2 fun h => h0 (Subtype.ext h)
  obtain ⟨p, p1, p2⟩ := exists_proj v1 d1 h1 h2
  refine ⟨⟨V, fun ψ hψ => (mem_CI.1 (v1 hψ)).1, v2, v3, v4⟩, fun t => ⟨hm t, fun u ψ hψ => (mem_CI.1 (v1 hψ)).2 t u⟩,
    p, fun h => hφ ?_, fun g x y hy => p2 _ _ ?_⟩
  · simpa [h] using p1 φ
  · have := d2 (.fin g) _ (p1 x)
    rw [map_sub] at this
    rw [hy]
    exact this
