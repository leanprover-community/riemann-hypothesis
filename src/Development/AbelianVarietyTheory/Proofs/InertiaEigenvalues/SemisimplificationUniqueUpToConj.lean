module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

noncomputable def bnMatRep {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W) :
    Γ →* GL (Fin a) k :=
  MonoidHom.toHomUnits
    (((LinearMap.toMatrixAlgEquiv b).toAlgHom.toRingHom.toMonoidHom).comp s)

theorem bnMatRep_val {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W) (g : Γ) :
    ((bnMatRep b s g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)
      = LinearMap.toMatrix b b (s g) := rfl

theorem bnMatRep_mulVec {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W) (g : Γ)
    (v : W) :
    ((bnMatRep b s g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).mulVec (b.equivFun v)
      = b.equivFun (s g v) := by
  rw [bnMatRep_val]
  exact LinearMap.toMatrix_mulVec_repr b b (s g) v

theorem bnMatRep_isSSRep {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W)
    (hs : IsSS s) : IsSSRep (bnMatRep b s) := by
  intro U hU
  obtain ⟨U', hU', hc⟩ := hs (U.comap (b.equivFun : W →ₗ[k] (Fin a → k))) (by
    intro g v hv
    have := hU g _ hv
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at this ⊢
    rw [← bnMatRep_mulVec]
    exact this)
  refine ⟨U'.map (b.equivFun : W →ₗ[k] (Fin a → k)), ?_, ?_⟩
  · rintro g _ ⟨v, hv, rfl⟩
    refine ⟨s g v, hU' g v hv, ?_⟩
    exact (bnMatRep_mulVec b s g v).symm
  · have h := (Submodule.orderIsoMapComap b.equivFun).isCompl hc
    have h1 : (Submodule.orderIsoMapComap b.equivFun)
        (U.comap (b.equivFun : W →ₗ[k] (Fin a → k))) = U :=
      Submodule.map_comap_eq_of_surjective b.equivFun.surjective U
    rw [h1] at h
    exact h

theorem brauerNesbitt_abstract_of_matrix : (∀ (Γ k : Type) [Group Γ] [Field k] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) k), IsSSRep ρ → IsSSRep ρ' → (∀ g, ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly = ((ρ' g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) → ∃ h : GL (Fin a) k, ∀ g, ρ' g = h * ρ g * h⁻¹) → ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (s : Representation k Γ W) (s' : Representation k Γ V), IsSS s → IsSS s' → (∀ g, LinearMap.charpoly (s g) = LinearMap.charpoly (s' g)) → ∃ e : W ≃ₗ[k] V, ∀ g v, e (s g v) = s' g (e v) := by
  intro H k Γ _ _ W _ _ _ V _ _ _ s s' hs hs' hc
  have hdim : Module.finrank k V = Module.finrank k W := by
    rw [← LinearMap.charpoly_natDegree (s 1), ← LinearMap.charpoly_natDegree (s' 1), hc]
  let b : Module.Basis (Fin (Module.finrank k W)) k W := Module.finBasis k W
  let b' : Module.Basis (Fin (Module.finrank k W)) k V := Module.finBasisOfFinrankEq k V hdim
  obtain ⟨h, hh⟩ := H Γ k _ (bnMatRep b s) (bnMatRep b' s') (bnMatRep_isSSRep b s hs)
    (bnMatRep_isSSRep b' s' hs') (by
      intro g
      rw [bnMatRep_val, bnMatRep_val, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix, hc])
  let m : (Fin (Module.finrank k W) → k) ≃ₗ[k] (Fin (Module.finrank k W) → k) :=
    (Matrix.GeneralLinearGroup.toLin h).toLinearEquiv
  have hm : ∀ x, m x = (h : Matrix _ _ k).mulVec x := fun x => rfl
  refine ⟨b.equivFun.trans (m.trans b'.equivFun.symm), fun g v => ?_⟩
  apply b'.equivFun.injective
  rw [← bnMatRep_mulVec]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, hm]
  rw [← bnMatRep_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul,
    ← Units.val_mul, hh g, inv_mul_cancel_right]

end GlobalTheory
