import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMatrixRingAct
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointOfBoxProjections

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.MatrixRosati

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

theorem rosatiAdj_one {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left)
    (hL : L.IsLB) : RosatiAdj A L 1 1 := by
  intro s
  refine ⟨⊤, trivial, ?_⟩
  let W : (A ⊗ A).left.Opens := (A ⊗ A).hom ⁻¹ᵁ ⊤
  let T : Over S := Over.mk (W.ι ≫ (A ⊗ A).hom)
  let ρ : T ⟶ A ⊗ A := Over.homMk W.ι rfl
  obtain ⟨x, y, hxy⟩ : ∃ x y : T ⟶ A, (lift x y).left = W.ι :=
    ⟨ρ ≫ fst A A, ρ ≫ snd A A, congrArg (fun q => q.left) (lift_comp_fst_snd ρ)⟩
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := fun i => W.ι ≫ rosatiφ A 1 1 i) (ε' := rosatiε)
    (fun V _ k => by
      refine Eq.trans ?_ ((prod_ros 1 1 x y k).symm.trans
        (Finset.prod_congr rfl fun i _ => by rw [hxy]))
      rw [MonObj.comp_one, MonObj.comp_one, _root_.one_mul, _root_.mul_one]
      simp [mul_comm, mul_left_comm])
    (LB.oneGen L (Y := W)) (oneGen_isGen _)
  exact ⟨u, hu⟩



end GlobalTheory.MatrixRosati
