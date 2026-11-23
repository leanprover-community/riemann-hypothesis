module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing

section HrelGen

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

theorem hr_secScal_sval {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  have hc : LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k))
      (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k))) := by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e
  have e := H _ _ hc
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have le : LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) ≤
      h ⁻¹ᵁ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc])]
  have e2 := congrArg (gs r z _) e
  refine ((gs_res r z _ hm _).trans (gs_pull r h z _ (le hm.2) _)).symm.trans (e2.trans ?_)
  exact (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top hm _) (gs_res r z _ hm _))

theorem hr_gs_zero (f : Z ⟶ Y) (z : Z) (U : Y.Opens) : gs f z U 0 = 0 := by
  unfold gs
  split_ifs <;> simp

end HrelGen

section HrelInj

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V))

end HrelInj

section HrelForm

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

end HrelForm

section HrelMain

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable (D : DegData V (maximalIdeal V)) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

end HrelMain

end ReciprocityTheory.ChartRestriction.G.DVR
