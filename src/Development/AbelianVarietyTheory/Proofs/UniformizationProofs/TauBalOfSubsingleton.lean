import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMatrixOrderActionOnPower
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBalAdd
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointBalancedPowerLift

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MatDeg

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R]

theorem c_add' (D : DegPre R) (a b : D.X) : D.c (a + b) = D.c a * D.c b := D.c_add a b

theorem c_zero' (D : DegPre R) : D.c 0 = 1 := by
  have h := c_add' D 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem c_sum (D : DegPre R) {J : Type} (s : Finset J) (x : J → D.X) :
    D.c (∑ l ∈ s, x l) = ∏ l ∈ s, D.c (x l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using c_zero' D
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, c_add', ih]

theorem comp_prod {S : Scheme.{0}} {T T' A : Over S} [GrpObj A] [IsCommMonObj A] (f : T' ⟶ T)
    {J : Type} (s : Finset J) (x : J → (T ⟶ A)) :
    f ≫ ∏ l ∈ s, x l = ∏ l ∈ s, f ≫ x l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]

theorem act_add {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {O : Type} [Ring O]
    (ρ : RingAct A O) (a b : O) : ρ.act (a + b) = ρ.act a * ρ.act b := ρ.map_add a b

theorem act_zero {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {O : Type} [Ring O]
    (ρ : RingAct A O) : ρ.act 0 = 1 := by
  have h := act_add ρ 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h



end GlobalTheory.MatDeg
end
end
