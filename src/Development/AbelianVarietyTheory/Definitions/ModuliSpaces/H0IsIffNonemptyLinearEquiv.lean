import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsFormOfEqRatioPowMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZV
variable {K : Type} [Field K] {X Y : Scheme.{0}}

theorem symB_iff_exists_gen {A : Over (Sp K)} [GrpObj A] (M : LB A.left) :
    SymB M ↔ ∃ u : LB.Gen (LB.LinComb M (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1]), u.IsGen := by
  have g : ∀ (y : A.left) (j j' : (PUnit → M.ι) × M.ι) (J J' : Fin 2 → M.ι), J 0 = j.1 PUnit.unit → J 1 = j.2 →
      J' 0 = j'.1 PUnit.unit → J' 1 = j'.2 →
      y ∈ (LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M).U j → y ∈ (LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M).U j' →
      y ∈ LB.wchart M (![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) J →
      y ∈ LB.wchart M (![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) J' →
      gm (𝟙 _) y _ ((LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M).g j j') =
        gm (𝟙 _) y _ ((LB.LinComb M (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1]).g J J') := by
    intro y j j' J J' a b c d hj hj' hJ hJ'
    obtain rfl : J = ![j.1 PUnit.unit, j.2] := by
      funext k; fin_cases k; exacts [a, b]
    obtain rfl : J' = ![j'.1 PUnit.unit, j'.2] := by
      funext k; fin_cases k; exacts [c, d]
    refine (gm_div M (M.pull (GrpObj.inv : A ⟶ A).left) (𝟙 _) y j j' ⟨hj, hj'⟩).trans
      (Eq.trans ?_ (gm_linComb M _ _ (𝟙 _) y _ _ hJ hJ').symm)
    refine Eq.trans (congrArg₂ (· * ·) ?_ ?_) (Fin.prod_univ_two _).symm
    · exact (gm_pull_g M _ _ y j.1 j'.1 hj.1 hj'.1).trans (zpow_one _).symm
    · exact (zpow_neg_one _).symm
  constructor
  · rintro ⟨u, hu⟩
    have le : ∀ J : Fin 2 → M.ι, LB.wchart M (![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) J ≤
        (LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M).U (fun _ => J 0, J 1) :=
      fun J y hy => ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0, Set.mem_iInter.1 hy 1⟩
    exact gen_chartPull (h := 𝟙 _) (A := LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M)
      (A' := LB.LinComb M (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1])
      ⟨fun J => (fun _ => J 0, J 1), le, fun y J J' hJ hJ' =>
        (g y _ _ J J' rfl rfl rfl rfl (le J hJ) (le J' hJ') hJ hJ').symm⟩ u hu
  · rintro ⟨u, hu⟩
    have le : ∀ j : (PUnit → M.ι) × M.ι, (LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M).U j ≤
        LB.wchart M (![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) ![j.1 PUnit.unit, j.2] :=
      fun j y hy => Set.mem_iInter.2 fun k => by
        fin_cases k
        exacts [Set.mem_iInter.1 hy.1 PUnit.unit, hy.2]
    exact gen_chartPull (h := 𝟙 _) (A' := LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M)
      (A := LB.LinComb M (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1])
      ⟨fun j => ![j.1 PUnit.unit, j.2], le, fun y j j' hj hj' =>
        g y j j' _ _ rfl rfl rfl rfl hj hj' (le j hj) (le j' hj')⟩ u hu

theorem symB_iff_sym {A : Over (Sp K)} [GrpObj A] {M : LB A.left} (hM : M.IsLB) : SymB M ↔ Out.Sym A M := by
  rw [symB_iff_exists_gen]
  have e : ∀ U : (Sp K).Opens, (fun k => (A.hom ⁻¹ᵁ U).ι ≫ (![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) k) =
      ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] := fun U => by
    funext k
    fin_cases k
    exacts [rfl, Category.comp_id _]
  constructor
  · rintro ⟨u, hu⟩ s
    refine ⟨⊤, trivial, ?_⟩
    rw [← e]
    exact ⟨_, DVR.pullGen_isGen M _ _ u hu _⟩
  · intro h
    refine DVR.gen_of_local_base hM _ _ fun s => ?_
    obtain ⟨U, hU, ht⟩ := h s
    exact ⟨U, hU, (e U).symm ▸ ht⟩

namespace Example

section Proj
open GlobalTheory.ProjSpace MvPolynomial






end Proj


def gmPts (K : Type) [Field K] : (Out.baseOver (Sp K) ⟶ Gm (Sp K)) ≃* Kˣ :=
  (splitTorusPointsEquiv (Sp K) (ULift ℤ) _).trans <|
    (MulEquiv.monoidHomCongrLeft (AddEquiv.ulift.toMultiplicative)).trans <|
      (zpowersMulHom _).symm.trans
        (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv)

theorem torsBasis_gm {k : ℕ} [NeZero k] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ k) :
    TorsBasis (Gm (Sp K)) k ![(gmPts K).symm ζ] := by
  refine ⟨Nat.pos_of_neZero k, fun i => ?_, fun y hy => ?_⟩
  · fin_cases i
    change (gmPts K).symm ζ ^ k = 1
    rw [← map_pow, hζ.pow_eq_one, map_one]
  · have hl : ∀ c : Fin 1 → ZMod k, Out.linComb ![(gmPts K).symm ζ] (fun i => (c i).val) =
        (gmPts K).symm (ζ ^ (c 0).val) := fun c => by simp [Out.linComb]
    have hy' : gmPts K y ∈ rootsOfUnity k K := by
      rw [mem_rootsOfUnity, ← map_pow, hy, map_one]
    obtain ⟨i, hi, e⟩ := hζ.eq_pow_of_mem_rootsOfUnity hy'
    refine ⟨fun _ => (i : ZMod k), ?_, fun c hc => ?_⟩
    · beta_reduce
      rw [hl, ZMod.val_cast_of_lt hi, e, MulEquiv.symm_apply_apply]
    · beta_reduce at hc
      rw [hl, MulEquiv.symm_apply_eq, ← e] at hc
      funext j
      obtain rfl : j = 0 := Subsingleton.elim _ _
      rw [← hζ.pow_inj (ZMod.val_lt _) hi hc, ZMod.natCast_zmod_val]


example : TorsBasis (Gm (Sp ℚ)) 2 ![(gmPts ℚ).symm (-1)] :=
  torsBasis_gm (IsPrimitiveRoot.coe_units_iff.1 (IsPrimitiveRoot.neg_one 0 (by decide)))

end Example
end GlobalTheory.ZV
end
