module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubNatCompSubIncl
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgLocalizationAwaySpanFinsetStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubmoduleFgOfLocallyLeFgStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub

theorem subMap_finite (X : Scheme.{0}) (_hX : IsNoetherian X) (F : X.Opensᵒᵖ ⥤ CommRingCat)
    (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    (hint : ∀ U : X.Opens, IsAffineOpen U → (α.app (op U)).hom.IsIntegral)
    {ι : Type} (V : ι → X.Opens) (_hV : ∀ j, IsAffineOpen (V j)) (hcov : ∀ x : X, ∃ j, x ∈ V j)
    (T : ∀ j, Set (F.obj (op (V j)))) (hT : ∀ j, (T j).Finite) (W : X.Opens)
    (hW : IsAffineOpen W) : (subMap F α V T W).Finite := by
  haveI : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  letI alg : Algebra Γ(X, W) (F.obj (op W)) := (α.app (op W)).hom.toAlgebra
  let S : Subalgebra Γ(X, W) (F.obj (op W)) :=
    { sub F α V T W with algebraMap_mem' := algebraMap_mem_sub F α V T W }
  let s : Set Γ(X, W) := {g | ∃ j, X.basicOpen g ≤ V j}
  have hs : Ideal.span s = ⊤ := by
    rw [← hW.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨j, hj⟩ := hcov x
    obtain ⟨g, hg, hxg⟩ := hW.exists_basicOpen_le (V := V j) ⟨x, hj⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, j, hg⟩, hxg⟩
  have hloc : ∀ g ∈ s, ∃ E : Finset (F.obj (op W)), ∀ b ∈ S.toSubmodule, ∃ m : ℕ,
      algebraMap Γ(X, W) (F.obj (op W)) g ^ m * b ∈ Submodule.span Γ(X, W) (E : Set _) := by
    rintro g ⟨j, hj⟩
    have hD : IsAffineOpen (X.basicOpen g) := hW.basicOpen g
    letI a1 : Algebra Γ(X, W) Γ(X, X.basicOpen g) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
    letI a2 : Algebra Γ(X, X.basicOpen g) (F.obj (op (X.basicOpen g))) :=
      (α.app (op (X.basicOpen g))).hom.toAlgebra
    letI a3 : Algebra (F.obj (op W)) (F.obj (op (X.basicOpen g))) :=
      (F.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
    letI a4 : Algebra Γ(X, W) (F.obj (op (X.basicOpen g))) :=
      ((α.app (op (X.basicOpen g))).hom.comp
        (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom).toAlgebra
    haveI : IsScalarTower Γ(X, W) (F.obj (op W)) (F.obj (op (X.basicOpen g))) :=
      IsScalarTower.of_algebraMap_eq fun r ↦ by
        have := congr($(α.naturality (homOfLE (X.basicOpen_le g)).op).hom r)
        simp only [CommRingCat.comp_apply] at this
        exact this
    haveI : IsScalarTower Γ(X, W) Γ(X, X.basicOpen g) (F.obj (op (X.basicOpen g))) :=
      IsScalarTower.of_algebraMap_eq fun r ↦ rfl
    haveI : IsLocalization.Away g Γ(X, X.basicOpen g) := hW.isLocalization_basicOpen g
    haveI : IsLocalization.Away (algebraMap Γ(X, W) (F.obj (op W)) g)
        (F.obj (op (X.basicOpen g))) := isLocalizationAway F α hα hW g
    let N : Submodule Γ(X, X.basicOpen g) (F.obj (op (X.basicOpen g))) :=
      (Algebra.adjoin Γ(X, X.basicOpen g) ((F.map (homOfLE hj).op).hom '' T j)).toSubmodule
    have hN : N.FG := fg_adjoin_of_finite ((hT j).image _) (fun x _ ↦ hint _ hD x)
    obtain ⟨E, hE⟩ := GlobalTheory.T.exists_finset_pow_mul_mem_span_of_fg_localizationAway (R := Γ(X, W)) (A := F.obj (op W)) (R' := Γ(X, X.basicOpen g))
      (A' := F.obj (op (X.basicOpen g))) g N hN
    refine ⟨E, fun b hb ↦ hE b ?_⟩
    have := (mem_sub F α V T).mp hb j (X.basicOpen g) hD (X.basicOpen_le g) hj
    rw [gen_eq_adjoin] at this
    exact this
  have hfg : S.toSubmodule.FG := GlobalTheory.T.submodule_fg_of_span_eq_top_of_locally_pow_mul_mem S.toSubmodule s hs hloc
  letI := (subMap F α V T W).toAlgebra
  have hfin : Module.Finite Γ(X, W) S.toSubmodule := Module.Finite.iff_fg.mpr hfg
  let e : S.toSubmodule ≃ₗ[Γ(X, W)] sub F α V T W :=
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      invFun := fun x ↦ ⟨x.1, x.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact Module.Finite.equiv e

end GlobalTheory.QcSub
