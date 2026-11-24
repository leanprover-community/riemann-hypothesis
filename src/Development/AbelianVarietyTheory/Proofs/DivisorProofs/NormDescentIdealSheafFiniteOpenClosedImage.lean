module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedNormIdealSheafFiniteNormalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftPointAffineHomSectionsRingHomStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoefficientIdealMapCompleteDvrEqProdLiftsStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

namespace GlobalTheory.NormSheaf

theorem normDescentSheaf : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z), IsFinite π → IsIntegral Y → IsLocallyNoetherian Y →
    GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme Z → IsOpen (Set.range π) →
    CharZero Γ(Y, ⊤) → ∀ I : Y.IdealSheafData, ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧
      (∀ x ∈ J.support, ∃ y ∈ I.support, π y = x) ∧
      ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
        IsAdicComplete (maximalIdeal V) V → ∀ ξ : Sp V ⟶ Z, ξ (closedPoint V) ∈ Set.range π →
        ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
          (f : V →+* V') (ψ : Fin d → (Sp V' ⟶ Y)), IsAdicComplete (maximalIdeal V') V' ∧ Function.Injective f ∧
          IsLocalHom f ∧ (∀ j, ψ j ≫ π = spMap f ≫ ξ) ∧ (idlAlong J ξ).map f = ∏ j, idlAlong I (ψ j) := by
  intro Y Z π hπ hY hYn hYN hZN hopen hchar I
  haveI : IsAffineHom π := hπ.toIsAffineHom
  obtain ⟨K, L, _, _, _, _, hK, J, hsupp, hJ⟩ := GlobalTheory.T.exists_descended_normIdealSheaf_finite_normal Y Z π hY hYn hYN hZN hopen hchar I
  refine ⟨Module.finrank K L, J, Module.finrank_pos, hsupp, ?_⟩
  intro V _ _ _ _ hV ξ hξ
  obtain ⟨U, hU, hxU, hUW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens
    (show ξ (closedPoint V) ∈ (⟨Set.range π, hopen⟩ : Z.Opens) from hξ)
  have hle : ⊤ ≤ ξ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem ξ hxU).ge
  let U' : Z.affineOpens := ⟨U, hU⟩
  obtain ⟨_, _, hA, hAc, hB, hfin, hKf, hLf, hsq, hJU⟩ := hJ U' hUW ⟨_, hxU⟩
  obtain ⟨V', _, _, _, _, f, ψ', hV', hf, hfl, hψc, hprod⟩ := GlobalTheory.T.normCoefficientIdeal_map_complete_dvr_eq_prod_lifts Γ(Z, U') Γ(Y, π ⁻¹ᵁ U) K L (π.app U).hom
    hfin hsq (I.ideal ⟨π ⁻¹ᵁ U, U'.2.preimage π⟩) V hV (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (.of V)).hom).hom
  choose ψ hψ hψI using fun j => GlobalTheory.T.exists_lift_point_affineHom_sections_ringHom Y Z π U' V V' ξ hle f (ψ' j) (hψc j)
  refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, f, ψ, hV', hf, hfl, hψ, ?_⟩
  have hidl : idlAlong J ξ = (J.ideal U').map
      (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (.of V)).hom).hom := by
    have hx : ξ (closedPoint V) ∈ U := hle trivial
    unfold idlAlong
    rw [ReciprocityTheory.AnForm.R.ds_stalkId_eq_map J U' _ hx, Ideal.map_map, ← CommRingCat.hom_comp,
      Scheme.germ_stalkClosedPointTo]
    congr 2
  rw [hidl, hJU, Ideal.map_map]
  simp only [hψI]
  exact hprod

end GlobalTheory.NormSheaf
