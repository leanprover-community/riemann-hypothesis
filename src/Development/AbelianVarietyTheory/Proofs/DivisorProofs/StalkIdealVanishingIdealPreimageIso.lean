module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VanishingIdealComapOfIsOpenImmersion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.WMultA
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.SurjOfCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.StalkVan

theorem comap_inv_eq_map {A B : CommRingCat.{0}} (e : A ≅ B) (I : Ideal A) :
    I.comap e.inv.hom = I.map e.hom.hom := by
  have := Ideal.map_comap_of_equiv (I := I) e.commRingCatIsoToRingEquiv
  exact this.symm

theorem ideal_comap_eq_map {X X' : Scheme.{0}} (f : X' ⟶ X) [IsIso f] (I : X.IdealSheafData)
    (V : X'.affineOpens) :
    (I.comap f).ideal V = (I.ideal ⟨f ''ᵁ V.1, V.2.image_of_isOpenImmersion f⟩).map
      (f.appLE (f ''ᵁ V.1) V.1 (f.preimage_image_eq V.1).ge).hom := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, comap_inv_eq_map, Scheme.Hom.appIso_hom']

theorem map_germ_app_congr {X X' : Scheme.{0}} (f : X' ⟶ X) (I : X.IdealSheafData) (x : X') :
    ∀ (W U : X.affineOpens), W = U → ∀ (hW : x ∈ f ⁻¹ᵁ W.1) (hU : x ∈ f ⁻¹ᵁ U.1),
      (I.ideal W).map ((X'.presheaf.germ (f ⁻¹ᵁ W.1) x hW).hom.comp (f.app W.1).hom) =
      (I.ideal U).map ((X'.presheaf.germ (f ⁻¹ᵁ U.1) x hU).hom.comp (f.app U.1).hom) := by
  rintro W U rfl hW hU
  rfl

theorem stalkId_vanishingIdeal_preimage : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsIso f]
    (Z : TopologicalSpace.Closeds X) (Z' : TopologicalSpace.Closeds X'),
    (Z' : Set X') = f ⁻¹' (Z : Set X) → ∀ (U : X.affineOpens) (x : X') (hx : x ∈ f ⁻¹ᵁ U.1),
    ReciprocityTheory.AnForm.R.FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal Z') x =
      ((Scheme.IdealSheafData.vanishingIdeal Z).ideal U).map
        ((X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom.comp (f.app U.1).hom) := by
  intro X X' f _ Z Z' hZ U x hx
  have hc : (Scheme.IdealSheafData.vanishingIdeal Z).comap f =
      Scheme.IdealSheafData.vanishingIdeal Z' :=
    GlobalTheory.vanishingIdeal_comap_of_isOpenImmersion X' X f Z Z' fun y => by
      rw [← SetLike.mem_coe, hZ]; rfl
  let V : X'.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
  have hxV : x ∈ V.1 := hx
  rw [ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ x V hxV, ← hc, ideal_comap_eq_map, Ideal.map_map]
  have hWU : (⟨f ''ᵁ V.1, V.2.image_of_isOpenImmersion f⟩ : X.affineOpens) = U := by
    apply Subtype.ext
    show f ''ᵁ (f ⁻¹ᵁ U.1) = U.1
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    refine inf_eq_right.2 fun y _ => ?_
    exact ⟨(inv f) y, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
  have hxW : x ∈ f ⁻¹ᵁ (f ''ᵁ V.1) := (f.preimage_image_eq V.1).ge hxV
  rw [← map_germ_app_congr f _ x _ U hWU hxW hx]
  congr 1
  rw [Scheme.Hom.appLE, CommRingCat.hom_comp, ← RingHom.comp_assoc, ← CommRingCat.hom_comp,
    TopCat.Presheaf.germ_res]

end GlobalTheory.StalkVan
