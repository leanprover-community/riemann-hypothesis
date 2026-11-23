module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.MainNotions.N
open GlobalTheory.BlockSum (blockRep vecComp vecComp_mulVec)

namespace UpperTheory.Gal.Int.Div


variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

private def colRep (ρ : Γ →* GL (Fin n) k) : Representation k Γ (Fin n → k) where
  toFun g := Matrix.mulVecLin (ρ g).val
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [Matrix.mulVecLin_mul]

private theorem colRep_apply (ρ : Γ →* GL (Fin n) k) (g : Γ) (v : Fin n → k) :
    colRep ρ g v = (ρ g).val.mulVec v := rfl

private theorem isSSRep_iff (ρ : Γ →* GL (Fin n) k) : IsSSRep ρ ↔ (colRep ρ).IsSemisimpleRepresentation := by
  constructor
  · intro h
    refine ⟨fun a => ?_⟩
    obtain ⟨W', hW', hc⟩ := h a.toSubmodule fun g v hv => a.apply_mem_toSubmodule g hv
    exact ⟨⟨W', fun g v hv => hW' g v hv⟩,
      disjoint_iff.2 (Subrepresentation.toSubmodule_injective hc.inf_eq_bot),
      codisjoint_iff.2 (Subrepresentation.toSubmodule_injective hc.sup_eq_top)⟩
  · intro h W hW
    obtain ⟨b, hb⟩ := exists_isCompl (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation (colRep ρ))
    exact ⟨b.toSubmodule, fun g v hv => b.apply_mem_toSubmodule g hv,
      disjoint_iff.2 (congrArg Subrepresentation.toSubmodule hb.inf_eq_bot),
      codisjoint_iff.2 (congrArg Subrepresentation.toSubmodule hb.sup_eq_top)⟩


theorem sSBlock_of : SSBlock := by
  intro Γ k _ _ a m n e r hr
  rw [isSSRep_iff, Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).1
    ((isSSRep_iff r).1 hr)
  set R := blockRep (a := fun _ : Fin m => a) e fun _ => r
  let L : (colRep R).asModule ≃ₗ[k] (Fin m → (colRep r).asModule) :=
    (colRep R).asModuleEquiv.trans ((vecComp e k).trans
      (LinearEquiv.piCongrRight fun _ => (colRep r).asModuleEquiv.symm))
  have hL : ∀ (g : Γ) (x : (colRep R).asModule),
      L (MonoidAlgebra.single g (1 : k) • x) = MonoidAlgebra.single g (1 : k) • L x := by
    intro g x
    funext j
    apply (colRep r).asModuleEquiv.injective
    simp only [L, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply, Pi.smul_apply,
      Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single_one,
      LinearEquiv.apply_symm_apply, colRep_apply]
    exact vecComp_mulVec e (fun _ => r) g _ j
  exact IsSemisimpleModule.of_injective
    (MonoidAlgebra.equivariantOfLinearOfComm L.toLinearMap hL) L.injective

end UpperTheory.Gal.Int.Div
