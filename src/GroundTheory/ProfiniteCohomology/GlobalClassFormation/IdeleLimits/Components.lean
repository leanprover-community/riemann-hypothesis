module

public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.LocalTransition
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Infinite
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

open CategoryTheory NumberField IntermediateField IsDedekindDomain GroundTheory.Global
  GroundTheory.Global.AdeleBaseChange FiniteSubfield IdeleLimit SemiLocal GroundTheory.Global.IdeleGroup

open scoped Pointwise NumberField.LiesOver NumberField.AdeleRing

noncomputable section

set_option synthInstance.maxHeartbeats 200000

private theorem cohomologyMapAlong_projection
    {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    [DiscreteTopology G] [DiscreteTopology H]
    {A B : Rep.{0} ℤ G} {C D : Rep.{0} ℤ H}
    {φ : H →* G} (hφ : Continuous φ)
    (f : A ⟶ B) (g : Rep.res φ B ⟶ C) (i : C ≅ D) (p : Rep.res φ A ⟶ D)
    (h : ∀ a : A, i.hom.hom (g.hom (f.hom a)) = p.hom a) (n : ℕ) :
    cohomologyMap f n ≫ (cohomologyMapAlong φ hφ g n ≫ (cohomologyIsoOfIso i n).hom) =
      cohomologyMapAlong φ hφ p n := by
  change HomologicalComplex.homologyMap (cochainsMap f) n ≫
      (HomologicalComplex.homologyMap (cochainsMapAlong φ hφ g) n ≫
        HomologicalComplex.homologyMap (cochainsMap i.hom) n) =
      HomologicalComplex.homologyMap (cochainsMapAlong φ hφ p) n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  apply congrArg (fun q : cochainsComplex A ⟶ cochainsComplex D =>
    HomologicalComplex.homologyMap q n)
  refine HomologicalComplex.hom_ext _ _ fun m => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  apply Subtype.ext
  funext t
  exact h ((x : locallyConstantCochains A m).1 (φ ∘ t))

private theorem cohomologyMapAlong_square
    {G H J L : Type} [Group G] [Group H] [Group J] [Group L]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace J] [TopologicalSpace L]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup J] [IsTopologicalGroup L]
    {A : Rep.{0} ℤ G} {B : Rep.{0} ℤ H} {C : Rep.{0} ℤ J} {D : Rep.{0} ℤ L}
    [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C] [IsDiscreteRep D]
    {φ : H →* G} {ψ : L →* H} {χ : J →* G} {ω : L →* J}
    (hφ : Continuous φ) (hψ : Continuous ψ) (hχ : Continuous χ) (hω : Continuous ω)
    (f : Rep.res φ A ⟶ B) (g : Rep.res ψ B ⟶ D)
    (p : Rep.res χ A ⟶ C) (q : Rep.res ω C ⟶ D)
    (hGroup : ∀ t, φ (ψ t) = χ (ω t)) (hRep : ∀ a : A, g.hom (f.hom a) = q.hom (p.hom a))
    (n : ℕ) : cohomologyMapAlong φ hφ f n ≫ cohomologyMapAlong ψ hψ g n =
      cohomologyMapAlong χ hχ p n ≫ cohomologyMapAlong ω hω q n := by
  unfold cohomologyMapAlong
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  refine Eq.trans ?_ (HomologicalComplex.homologyMap_comp _ _ n)
  apply congrArg (fun r : cochainsComplex A ⟶ cochainsComplex D =>
    HomologicalComplex.homologyMap r n)
  refine HomologicalComplex.hom_ext _ _ fun m => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  apply Subtype.ext
  funext t
  let a := (x : locallyConstantCochains A m).1
  change g.hom (f.hom (a (fun j => φ (ψ (t j))))) = q.hom (p.hom (a (fun j => χ (ω (t j)))))
  rw [show (fun j => φ (ψ (t j))) = (fun j => χ (ω (t j))) from funext (fun j => hGroup (t j))]
  exact hRep _

variable {K F : FiniteSubfield} [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

section Finite

variable {v : HeightOneSpectrum (𝓞 K.1)} (w : PlacesOver F.1 v)

theorem finiteProj_smul_of_mem_stabilizer (σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal)
    (x : IdeleGroup F.1) :
    finiteProj w.1 ((σ : F.1 ≃ₐ[K.1] F.1) • x) = σ • finiteProj w.1 x := by
  apply Units.ext
  have h : w.1 = (σ : F.1 ≃ₐ[K.1] F.1) • w.1 :=
    (congrArg Subtype.val ((mem_stabilizer_iff_smul_eq v w σ).1 σ.2)).symm
  rw [coe_finiteProj, coe_smul_idele, smul_snd_eq_galHom _ _ w.1 w.1 h, galHom_eq_decomposition]
  rfl

def finiteComponentRep :
    Rep.res (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal).subtype (ideleRep K.1 F.1) ⟶
      Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal)
        (w.1.adicCompletion F.1)ˣ :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (finiteProj w.1)).toIntLinearMap, fun σ => LinearMap.ext fun x =>
    congrArg Additive.ofMul (finiteProj_smul_of_mem_stabilizer w σ x.toMul)⟩

def finiteComponent (n : ℕ) :
    cohomology (ideleRep K.1 F.1) n ⟶
      cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal)
        (w.1.adicCompletion F.1)ˣ) n :=
  cohomologyMapAlong (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal).subtype
    continuous_of_discreteTopology (finiteComponentRep w) n



theorem placeProj_comp_finiteShapiroIso (n : ℕ) :
    cohomologyMap (finiteProjAboveRep (K := K.1) (L := F.1) v) n ≫ (finiteShapiroIso v w n).hom =
      finiteComponent w n := by
  refine cohomologyMapAlong_projection
    (continuous_subgroup_subtype (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal))
    (finiteProjAboveRep (K := K.1) (L := F.1) v)
    (orbitProj (permutesFactors_finiteUnitsAboveRep v) (mem_stabilizer_iff_smul_eq v w))
    (stabRepFiniteIso v w) (finiteComponentRep w) ?_ n
  intro a
  rfl


omit [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal] in
theorem ideleEmbedding_snd_of_below_eq {E : FiniteSubfield} [Algebra F.1 E.1]
    (w' : HeightOneSpectrum (𝓞 E.1)) (u : HeightOneSpectrum (𝓞 F.1)) (hu : below F.1 w' = u)
    [w'.asIdeal.LiesOver u.asIdeal] (x : IdeleGroup F.1) :
    ((ideleEmbedding F.1 E.1 x : IdeleGroup E.1) : 𝔸[E.1]).2 w' =
      SemiLocal.completionMap u w' ((x : 𝔸[F.1]).2 u) := by
  subst hu
  rfl

variable {E : FiniteSubfield} [Fact (K ≤ E)] [Fact (F ≤ E)] [E.1.fixingSubgroup.Normal]



theorem levelTransition_comp_finiteComponent (w' : PlacesOver E.1 v)
    [w'.1.asIdeal.LiesOver w.1.asIdeal] (n : ℕ) :
    levelTransition K F E n ≫ finiteComponent w' n =
      finiteComponent w n ≫ localTransition K F E w w' n := by
  refine cohomologyMapAlong_square (φ := levelRestrict K F E)
    (ψ := (MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1.asIdeal).subtype)
    (χ := (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal).subtype)
    (ω := decompRestrict (w := w) (w' := w'))
    continuous_levelRestrict continuous_of_discreteTopology
    continuous_of_discreteTopology continuous_of_discreteTopology
    (levelMap K F E) (finiteComponentRep w') (finiteComponentRep w) completionUnitsRep
    (fun _ => rfl) ?_ n
  intro x
  exact congrArg Additive.ofMul (Units.ext
    (ideleEmbedding_snd_of_below_eq w'.1 w.1 ((below_eq_iff w'.1 w.1).2 inferInstance) x.toMul))

end Finite

section Infinite

variable {v : InfinitePlace K.1} (w : v.placesOver F.1)

omit [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal] in
theorem fst_eq_completionCongr (a : 𝔸[F.1]) {u u' : InfinitePlace F.1} (h : u = u') :
    a.1 u' = completionCongr h (a.1 u) := by
  subst h
  rfl

omit [F.1.fixingSubgroup.Normal] in
theorem eq_comap_of_mem_stabilizer (σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1) :
    w.1 = w.1.comap (((σ : F.1 ≃ₐ[K.1] F.1) : F.1 ≃+* F.1) : F.1 →+* F.1) := by
  rw [comap_eq_inv_smul]
  exact (MulAction.mem_stabilizer_iff.1 (inv_mem σ.2)).symm

theorem infiniteProj_smul_of_mem_stabilizer (σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1)
    (x : IdeleGroup F.1) :
    infiniteProj w.1 ((σ : F.1 ≃ₐ[K.1] F.1) • x) = σ • infiniteProj w.1 x := by
  apply Units.ext
  rw [coe_infiniteProj, coe_smul_idele, smul_fst,
    fst_eq_completionCongr _ (eq_comap_of_mem_stabilizer w σ), infiniteCompletionMap_eq_decomposition]
  rfl

def infiniteComponentRep :
    Rep.res (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1).subtype (ideleRep K.1 F.1) ⟶
      Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1) (w.1.Completion)ˣ :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (infiniteProj w.1)).toIntLinearMap, fun σ => LinearMap.ext fun x =>
    congrArg Additive.ofMul (infiniteProj_smul_of_mem_stabilizer w σ x.toMul)⟩

def infiniteComponent (n : ℕ) :
    cohomology (ideleRep K.1 F.1) n ⟶
      cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1)
        (w.1.Completion)ˣ) n :=
  cohomologyMapAlong (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1).subtype
    continuous_of_discreteTopology (infiniteComponentRep w) n



theorem placeProj_comp_infiniteShapiroIso (n : ℕ) :
    cohomologyMap (infiniteProjAboveRep (K := K.1) (L := F.1) v) n ≫ (infiniteShapiroIso v w n).hom =
      infiniteComponent w n := by
  refine cohomologyMapAlong_projection
    (continuous_subgroup_subtype (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1))
    (infiniteProjAboveRep (K := K.1) (L := F.1) v)
    (orbitProj (permutesFactors_infiniteUnitsAboveRep v) (mem_stabilizer_iff_smul_eq_infinite v w))
    (stabRepInfiniteIso v w) (infiniteComponentRep w) ?_ n
  intro a
  rfl


omit [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal] in
theorem ideleEmbedding_fst_of_comap_eq {E : FiniteSubfield} [Algebra F.1 E.1]
    (w' : InfinitePlace E.1) (u : InfinitePlace F.1) (hu : w'.comap (algebraMap F.1 E.1) = u)
    [w'.LiesOver u] (x : IdeleGroup F.1) :
    ((ideleEmbedding F.1 E.1 x : IdeleGroup E.1) : 𝔸[E.1]).1 w' =
      AbsoluteValue.Completion.map u.1 w'.1 ((x : 𝔸[F.1]).1 u) := by
  subst hu
  exact (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply (x : 𝔸[F.1]).1 w').trans
    (AbsoluteValue.Completion.algebraMap_apply_of_liesOver
      (w'.comap (algebraMap F.1 E.1)).1 w'.1 _)

variable {E : FiniteSubfield} [Fact (K ≤ E)] [Fact (F ≤ E)] [E.1.fixingSubgroup.Normal]



theorem levelTransition_comp_infiniteComponent (w' : v.placesOver E.1) [w'.1.LiesOver w.1] (n : ℕ) :
    levelTransition K F E n ≫ infiniteComponent w' n =
      infiniteComponent w n ≫ infLocalTransition K F E w w' n := by
  refine cohomologyMapAlong_square (φ := levelRestrict K F E)
    (ψ := (MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1).subtype)
    (χ := (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1).subtype)
    (ω := infDecompRestrict (w := w) (w' := w'))
    continuous_levelRestrict continuous_of_discreteTopology
    continuous_of_discreteTopology continuous_of_discreteTopology
    (levelMap K F E) (infiniteComponentRep w') (infiniteComponentRep w) infCompletionUnitsRep
    (fun _ => rfl) ?_ n
  intro x
  exact congrArg Additive.ofMul (Units.ext
    (ideleEmbedding_fst_of_comap_eq w'.1 w.1 (InfinitePlace.LiesOver.comap_eq w'.1 w.1) x.toMul))

end Infinite

end

end GroundTheory.ProfCoh
