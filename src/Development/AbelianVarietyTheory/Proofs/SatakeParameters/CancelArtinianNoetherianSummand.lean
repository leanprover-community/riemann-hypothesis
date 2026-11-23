module

public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CancelProdSummandNilpotentOrBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndomorphismIndecomposableNilpotentOrBijectiveStatement
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
import Mathlib.Tactic.ENatToNat
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

namespace GlobalTheory

theorem ks_cancel_submodule (R P : Type) [Ring R] [AddCommGroup P] [Module R P] [IsArtinian R P]
    [IsNoetherian R P] (N : Submodule R P) :
    ∀ (M M' : Type) [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'],
      Nonempty ((M × N) ≃ₗ[R] (M' × N)) → Nonempty (M ≃ₗ[R] M') := by
  induction N using WellFoundedLT.induction with
  | _ N ih =>
  intro M M' _ _ _ _ e
  by_cases hind : ∀ A B : Submodule R N, IsCompl A B → A = ⊥ ∨ B = ⊥
  · exact GlobalTheory.T.cancel_prod_summand_nilpotent_or_bijective R M M' N (GlobalTheory.T.endomorphism_indecomposable_nilpotent_or_bijective R N hind) e
  · push_neg at hind
    obtain ⟨A, B, hAB, hA, hB⟩ := hind
    have hAlt : A.map N.subtype < N := by
      have h1 : A < ⊤ := lt_top_iff_ne_top.mpr (fun h => hB (by
        have := hAB.inf_eq_bot; rw [h, top_inf_eq] at this; exact this))
      have := Submodule.map_strictMono_of_injective N.injective_subtype h1
      rwa [Submodule.map_subtype_top] at this
    have hBlt : B.map N.subtype < N := by
      have h1 : B < ⊤ := lt_top_iff_ne_top.mpr (fun h => hA (by
        have := hAB.inf_eq_bot; rw [h, inf_top_eq] at this; exact this))
      have := Submodule.map_strictMono_of_injective N.injective_subtype h1
      rwa [Submodule.map_subtype_top] at this
    let eA : A ≃ₗ[R] A.map N.subtype := Submodule.equivMapOfInjective _ N.injective_subtype A
    let eB : B ≃ₗ[R] B.map N.subtype := Submodule.equivMapOfInjective _ N.injective_subtype B
    let eN : N ≃ₗ[R] (A.map N.subtype × B.map N.subtype) :=
      (Submodule.prodEquivOfIsCompl A B hAB).symm ≪≫ₗ LinearEquiv.prodCongr eA eB
    obtain ⟨e⟩ := e
    let f : ((M × A.map N.subtype) × B.map N.subtype) ≃ₗ[R]
        ((M' × A.map N.subtype) × B.map N.subtype) :=
      (LinearEquiv.prodAssoc R M _ _) ≪≫ₗ (LinearEquiv.prodCongr (LinearEquiv.refl R M) eN).symm ≪≫ₗ e ≪≫ₗ
        (LinearEquiv.prodCongr (LinearEquiv.refl R M') eN) ≪≫ₗ (LinearEquiv.prodAssoc R M' _ _).symm
    obtain ⟨g⟩ := ih _ hBlt _ _ ⟨f⟩
    exact ih _ hAlt M M' ⟨g⟩

theorem ks_cancel : ∀ (R M M' P : Type) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] [AddCommGroup P] [Module R P] [IsArtinian R P] [IsNoetherian R P],
    Nonempty ((M × P) ≃ₗ[R] (M' × P)) → Nonempty (M ≃ₗ[R] M') := by
  intro R M M' P _ _ _ _ _ _ _ _ _ ⟨e⟩
  let t : (⊤ : Submodule R P) ≃ₗ[R] P := Submodule.topEquiv
  exact ks_cancel_submodule R P ⊤ M M'
    ⟨(LinearEquiv.prodCongr (LinearEquiv.refl R M) t) ≪≫ₗ e ≪≫ₗ
      (LinearEquiv.prodCongr (LinearEquiv.refl R M') t).symm⟩

end GlobalTheory
