module

public import GroundTheory.ProfiniteCohomology.GaloisModules.CoeGalRootsOfUnityHomApply
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology

section General

variable {G M : Type} [Group G] [CommGroup M] (φ : G →* Monoid.End M)

def cocycles₂IntRepAddEquiv :
    cocycles₂ (Rep.of (intRepOfMonoidEnd.{0} φ)) ≃+ cocycles₂ (Rep.of (zRepOfMonoidEnd φ)) where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem h2π_intRepOfMonoidEnd_surjective :
    Function.Surjective (H2π (Rep.of (intRepOfMonoidEnd.{0} φ))).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

theorem h2π_zRepOfMonoidEnd_surjective :
    Function.Surjective (H2π (Rep.of (zRepOfMonoidEnd φ))).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

theorem map_ker_h2π_intRepOfMonoidEnd :
    (H2π (Rep.of (intRepOfMonoidEnd.{0} φ))).hom.toAddMonoidHom.ker.map
        (cocycles₂IntRepAddEquiv φ).toAddMonoidHom =
      (H2π (Rep.of (zRepOfMonoidEnd φ))).hom.toAddMonoidHom.ker := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (H2π _).hom _ = 0
    change (H2π _).hom y = 0 at hy
    rw [H2π_eq_zero_iff] at hy ⊢
    exact hy
  · intro hx
    refine ⟨(cocycles₂IntRepAddEquiv φ).symm x, ?_, rfl⟩
    change (H2π _).hom x = 0 at hx
    change (H2π _).hom _ = 0
    rw [H2π_eq_zero_iff] at hx ⊢
    exact hx

noncomputable def h2IntRepAddEquiv :
    groupCohomology (Rep.of (intRepOfMonoidEnd.{0} φ)) 2 ≃+
      groupCohomology (Rep.of (zRepOfMonoidEnd φ)) 2 :=
  ((QuotientAddGroup.quotientKerEquivOfSurjective
      (H2π (Rep.of (intRepOfMonoidEnd.{0} φ))).hom.toAddMonoidHom
      (h2π_intRepOfMonoidEnd_surjective φ)).symm.trans
    (QuotientAddGroup.congr _ _ (cocycles₂IntRepAddEquiv φ)
      (map_ker_h2π_intRepOfMonoidEnd φ))).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (H2π (Rep.of (zRepOfMonoidEnd φ))).hom.toAddMonoidHom
      (h2π_zRepOfMonoidEnd_surjective φ))

theorem h2IntRepAddEquiv_H2_class (x : cocycles₂ (Rep.of (intRepOfMonoidEnd.{0} φ))) :
    h2IntRepAddEquiv φ ((H2π _).hom x) = (H2π _).hom (cocycles₂IntRepAddEquiv φ x) := by
  have h1 : (QuotientAddGroup.quotientKerEquivOfSurjective
      (H2π (Rep.of (intRepOfMonoidEnd.{0} φ))).hom.toAddMonoidHom
      (h2π_intRepOfMonoidEnd_surjective φ)).symm ((H2π _).hom x) = (QuotientAddGroup.mk x : _ ⧸ _) := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  rw [h2IntRepAddEquiv, AddEquiv.trans_apply, AddEquiv.trans_apply, h1]
  rfl

end General

section Galois

variable (K L : Type) [Field K] [Field L] [Algebra K L]

noncomputable def h2GalUnitsAddEquiv :
    groupCohomology (galUnits K L) 2 ≃+ groupCohomology (galUnitsZ K L) 2 :=
  h2IntRepAddEquiv (galUnitsHom K L)

theorem h2GalUnitsAddEquiv_H2_class (x : cocycles₂ (galUnits K L)) :
    h2GalUnitsAddEquiv K L ((H2π _).hom x) =
      (H2π _).hom (cocycles₂IntRepAddEquiv (galUnitsHom K L) x) :=
  h2IntRepAddEquiv_H2_class (galUnitsHom K L) x

end Galois

end GroundTheory.ProfCoh
