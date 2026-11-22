module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MinkowskiDivisible
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIsoOfIsOpenImmersionOfGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory
namespace SerreLemma

variable {k : Type} [Field k] [IsAlgClosed k]

theorem exists_lift {X Y : Over (Sp k)} (m : X ⟶ Y) [LocallyOfFiniteType m.left]
    (x : 𝟙_ (Over (Sp k)) ⟶ Y) (hx : x.left (IsLocalRing.closedPoint k) ∈ Set.range m.left) :
    ∃ a : 𝟙_ (Over (Sp k)) ⟶ X, a ≫ m = x := by
  let x' : Spec (CommRingCat.of k) ⟶ Y.left := x.left
  have hJ : JacobsonSpace ↥(pullback m.left x') :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd m.left x')
  obtain ⟨w, hw⟩ := hx
  obtain ⟨z₀, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := m.left) (g := x') w _ hw
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback m.left x')))
    ⟨z₀, trivial⟩ isClosed_univ.isLocallyClosed
  replace hz : IsClosed {z} := hz
  have e : (pointOfClosedPoint (pullback.snd m.left x') z hz ≫ pullback.fst _ _) ≫ m.left = x' := by
    rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  refine ⟨Over.homMk (pointOfClosedPoint (pullback.snd m.left x') z hz ≫ pullback.fst _ _) ?_,
    Over.OverMorphism.ext e⟩
  rw [← Over.w m, ← Category.assoc, e]
  exact Over.w x

theorem exists_pow_eq (G : Over (Sp k)) [GrpObj G] (hG : IsSemiAbelian G) (n : ℕ) (hn : (n : k) ≠ 0)
    (x : 𝟙_ (Over (Sp k)) ⟶ G) : ∃ y : 𝟙_ (Over (Sp k)) ⟶ G, y ^ n = x := by
  have := hG.comm
  have := hG.smooth
  have : IsIntegral G.left := isIntegral_left_of_isSemiAbelian G
  have hu : IsUnit (n : Γ(Sp k, ⊤)) := by
    simpa using (Ne.isUnit hn).map (Scheme.ΓSpecIso (.of k)).inv.hom
  have := GrpTangent.etale_mulN G hu
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  set U : Set G.left := Set.range (mulN G n).left with hU
  have hUo : IsOpen U := (mulN G n).left.isOpenMap.isOpen_range
  have hone : (1 : 𝟙_ _ ⟶ G).left (IsLocalRing.closedPoint k) ∈ U := by
    refine ⟨(1 : 𝟙_ _ ⟶ G).left (IsLocalRing.closedPoint k), ?_⟩
    exact congrArg (fun z : 𝟙_ (Over (Sp k)) ⟶ G => z.left (IsLocalRing.closedPoint k))
      (MonObj.one_comp (mulN G n))
  have hVo : IsOpen ((GrpObj.mulRight x).hom.left ⁻¹' U) := hUo.preimage (Scheme.Hom.continuous _)
  have hV : ((GrpObj.mulRight x).hom.left ⁻¹' U).Nonempty := by
    refine ⟨(x⁻¹).left (IsLocalRing.closedPoint k), ?_⟩
    rw [Set.mem_preimage, OpenSubgroupScheme.mulRight_apply, inv_mul_cancel]
    exact hone
  obtain ⟨y, ⟨hyU, hyV⟩, hyc⟩ := nonempty_inter_closedPoints
    (nonempty_preirreducible_inter hUo hVo ⟨_, hone⟩ hV) (hUo.inter hVo).isLocallyClosed
  obtain ⟨z, rfl⟩ := OpenSubgroupScheme.exists_point y hyc
  rw [Set.mem_preimage, OpenSubgroupScheme.mulRight_apply] at hyV
  obtain ⟨a, ha⟩ := exists_lift _ z hyU
  obtain ⟨b, hb⟩ := exists_lift _ _ hyV
  rw [GrpTangent.comp_mulN] at ha hb
  refine ⟨a⁻¹ * b, ?_⟩
  rw [mul_pow, inv_pow, ha, hb, inv_mul_cancel_left]

end SerreLemma

end GlobalTheory
