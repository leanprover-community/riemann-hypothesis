import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_finite_point_mem_opens {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (W : X.Opens) (hW : (W : Set X).Nonempty) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra k L), FiniteDimensional k L ∧
      ∃ y : Spec (CommRingCat.of L) ⟶ X,
        y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧ Set.range y ⊆ W := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hxW, hx⟩ := nonempty_inter_closedPoints hW W.isOpen.isLocallyClosed
  have hc : IsClosedImmersion (X.fromSpecResidueField x) := isClosed_singleton_iff_isClosedImmersion.mp hx
  have hfin : IsFinite (X.fromSpecResidueField x ≫ f) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ f)
  rw [← hφ, IsFinite.SpecMap_iff] at hfin
  let : Algebra k (X.residueField x) := φ.hom.toAlgebra
  refine ⟨X.residueField x, inferInstance, inferInstance, hfin, X.fromSpecResidueField x, hφ.symm, ?_⟩
  rw [Scheme.range_fromSpecResidueField]
  simpa using hxW

theorem moduli_exists_algebraic_point :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W : (Xo.XF c).Opens), (W : Set (Xo.XF c)).Nonempty → ∃ (L : Type) (_ : Field L) (_ : Algebra c.F L), FiniteDimensional c.F L ∧ ∃ y : Sp L ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F L) ∧ Set.range y ⊆ W := by
  intro E _ _ _ H D l Xo c W hW
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  exact exists_finite_point_mem_opens (pullback.snd _ _) W hW

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem moduli_exists_numberField_point :
    N1c → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → Formalism.L2.PjFree.XoNumPt Xo c := by
  intro hN E _ _ _ H Dw l Xo c hr
  obtain ⟨x⟩ := (PeriodExists.typeFn_period_exist E H Dw).2.2 hN hr l Xo c
  obtain ⟨L, _, _, hfin, y, hy, -⟩ := moduli_exists_algebraic_point E H Dw l Xo c ⊤ ⟨x, trivial⟩
  have : NumberField L := NumberField.of_module_finite c.F L
  refine ⟨L, inferInstance, this, algebraMap c.F L, y ≫ pullback.fst _ _, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hy]
  simp only [sOf, spMap, ← Spec.map_comp]
  rfl

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.xoNumPt_of_p_add_q_pos : N1c → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → Formalism.L2.PjFree.XoNumPt Xo c := by
  first | exact @GlobalTheory.moduli_exists_numberField_point | exact GlobalTheory.moduli_exists_numberField_point | (intros; apply GlobalTheory.moduli_exists_numberField_point <;> assumption)
end
