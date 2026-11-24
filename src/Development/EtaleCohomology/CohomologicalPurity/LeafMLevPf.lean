module

public import Development.EtaleCohomology.CohomologicalPurity.LeafExcLevelPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Presentable.Type
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

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

abbrev levF (n : SimplexCategoryᵒᵖ) : Spc ⥤ Spc := (evaluation SimplexCategoryᵒᵖ PSh).obj n ⋙ disc

theorem LeafMLev_of : LeafMLev := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro P' P φ n
  let F := levF n
  have hc : F.map (P'.hom ≫ φ.right) = F.map P'.hom ≫ F.map φ.right := F.map_comp _ _
  let a : disc.obj ((MM φ).obj n) ≅ MM ((lev n).map φ) :=
    (PreservesPushout.iso F P'.hom (P'.hom ≫ φ.right)).symm ≪≫ pushout.congrHom rfl hc
  let b : disc.obj ((dbl P).obj n) ≅ dbl ((lev n).obj P) :=
    (PreservesPushout.iso F P.hom P.hom).symm
  refine ⟨a, b, ?_⟩
  rw [← Iso.inv_comp_eq]
  change (pushout.congrHom rfl hc).inv ≫ (PreservesPushout.iso F P'.hom (P'.hom ≫ φ.right)).hom ≫ F.map (gM φ) ≫
    (PreservesPushout.iso F P.hom P.hom).inv = gM ((lev n).map φ)
  apply pushout.hom_ext
  · rw [pushout.congrHom_inv, pushout.inl_desc_assoc, Category.id_comp]
    erw [PreservesPushout.inl_iso_hom_assoc, ← F.map_comp_assoc, pushout.inl_desc, pushout.inl_desc, F.map_comp_assoc]
    erw [PreservesPushout.inl_iso_inv]
    rfl
  · rw [pushout.congrHom_inv, pushout.inr_desc_assoc, Category.id_comp]
    erw [PreservesPushout.inr_iso_hom_assoc, ← F.map_comp_assoc, pushout.inr_desc, pushout.inr_desc]
    erw [PreservesPushout.inr_iso_inv]
    rfl

end LateralTheory.CohomologicalPurity.TubeCut
