import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.XValuePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.Transport
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBalPow

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TauBalElem

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.TauBalBox

theorem exists_unbox {X X' Y : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}
    (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen)
    {K : Type} [Fintype K] (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    (b : LB.Gen (LB.LinComb M (K := K × Fin j) (fun p => φ' p.1 ≫ pr p.2) (fun p => ε p.1))) (hb : b.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb M' φ' ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (y : Z) (J J'),
      Good M y J → Good M' y J' →
      (∏ a, om w y J J' (q ≫ φ' a) ^ ε a) * val t' q y J' = val b q y J := by
  have le : ∀ jN : K → Fin j → M.ι, LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ≤
      LB.wchart M (K := K × Fin j) (fun p => φ' p.1 ≫ pr p.2) (fun p => jN p.1 p.2) := fun jN y hy =>
    Set.mem_iInter.2 fun p => Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2
  let b' : LB.Gen (LB.LinComb (LB.LinComb M pr (fun _ => 1)) φ' ε) :=
    ⟨fun jN => res (le jN) (b.s (fun p => jN p.1 p.2))⟩
  have hb' : b'.IsGen := fun jN jN' => unit_ext fun y hy => by
    have e := gen_trans hb (𝟙 Y) y (le jN hy.1) (le jN' hy.2)
    refine ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le jN) hy.1 _)).trans (e.trans (Eq.symm ?_))
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb _ φ' ε (𝟙 Y) y jN jN' hy.1 hy.2).trans ?_)
      ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le jN') hy.2 _)))
    rw [trF, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun a _ => ?_
    refine (congrArg (· ^ ε a) (gm_linComb M pr (fun _ => 1) (𝟙 Y ≫ φ' a) y (jN a) (jN' a)
      (Set.mem_iInter.1 hy.1 a) (Set.mem_iInter.1 hy.2 a))).trans ?_
    simp only [zpow_one, Category.assoc, Finset.prod_zpow]
  obtain ⟨t, ht, H⟩ := Transport.exists_transport (linComb_isLB M' hM' φ' ε)
    (linComb_isLB _ (linComb_isLB M hM pr (fun _ => 1)) φ' ε) (LB.linCombIso w φ' ε) (linCombIso_isGen w hw φ' ε) b' hb'
  refine ⟨t, ht, fun Z q y J J' hJ hJ' => ?_⟩
  have hm : q y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((q ≫ φ' a) ≫ pr i)) ⊓
      LB.wchart M' φ' (fun a => J' (q ≫ φ' a)) :=
    ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((q ≫ φ' a) ≫ pr i), hJ'.mem _ q⟩
  have E := congrArg (gm q y (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((q ≫ φ' a) ≫ pr i)) ⊓
    LB.wchart M' φ' (fun a => J' (q ≫ φ' a)))) (H (fun a i => J ((q ≫ φ' a) ≫ pr i), fun a => J' (q ≫ φ' a)))
  rw [val_of b q y J (fun p => J ((q ≫ φ' p.1) ≫ pr p.2)) (fun p => by rw [Category.assoc])]
  exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_linCombIso w φ' ε q y _ _ hm)
    (gm_res q y inf_le_right hm _))).symm.trans
    (E.symm.trans ((gm_res q y inf_le_left hm _).trans (gm_res q y (le _) hm.1 _)))



theorem tau_zero_left {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {y : (TK R).left} {J}
    (hJ : Good D.P.L y J) (b : D.X) : val (D.tau 0 b) (𝟙 _) y J = 1 := by
  have C : IsCub (cubV D.cub (T := TK R) y J) := isCub_cubV D.cub hJ
  have t := tauK_mul hJ hB 0 0 b
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
  exact mul_eq_left.1 t.symm


end GlobalTheory.TauBalElem
