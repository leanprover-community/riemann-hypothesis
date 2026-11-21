import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearHomProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.PairingIsoPullback
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulAFiniteFlatSurjective
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsAbelianSchemeOfIsPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AutomorphicArithmetic.DivisorFrames.ExistsNsmulMemSumImageLatticeOfSurjectiveMod
import Development.AutomorphicArithmetic.DivisorFrames.ExistsInjectiveLatticeHomRingOfIntegersOfFinrank
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeIdPowFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGramMatricesCmUnitaryShimuraObject
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqOfLamEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersActionInjectiveOnAbelianScheme
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLamObjGoodOfCmObj
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.DimPosOfHasType

section
section
open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DivisibleLinear

variable {S S' : Scheme.{0}}

theorem eq_one_iff {G T : Over S} [GrpObj G] (z : T ⟶ G) : z = 1 ↔ z.left = T.hom ≫ η[G].left := by
  have hu : (toUnit T).left = T.hom := by simpa using Over.w (toUnit T)
  constructor
  · rintro rfl
    rw [Hom.one_def, Over.comp_left, hu]
  · intro h
    apply Over.OverMorphism.ext
    rw [h, Hom.one_def, Over.comp_left, hu]

section BaseChange

variable {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {g : G'.left ⟶ G.left}

theorem toBase_injective (hg : IsPullback g G'.hom G.hom f) {T : Over S'} {x y : T ⟶ G'}
    (h : Out.toBase hg.w x = Out.toBase hg.w y) : x = y := by
  apply Over.OverMorphism.ext
  apply hg.hom_ext
  · simpa [Out.toBase] using congrArg (·.left) h
  · rw [Over.w x, Over.w y]

variable (hg : IsPullback g G'.hom G.hom f)
  (hm : ∀ (T : Over S') (x y : T ⟶ G'), Out.toBase hg.w (x * y) = Out.toBase hg.w x * Out.toBase hg.w y)
include hm

theorem toBase_one (T : Over S') : Out.toBase hg.w (1 : T ⟶ G') = 1 := by
  have h := hm T 1 1
  rw [_root_.mul_one] at h
  exact mul_eq_left.mp h.symm

theorem toBase_pow {T : Over S'} (x : T ⟶ G') (n : ℕ) : Out.toBase hg.w (x ^ n) = Out.toBase hg.w x ^ n := by
  induction n with
  | zero => simpa using toBase_one hg hm T
  | succ k ih => rw [pow_succ, hm, ih, pow_succ]

end BaseChange

end GlobalTheory.DivisibleLinear

namespace GlobalTheory.DivisibleLinear

theorem torsion_comp_eq_one {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (P Q : Out.PolAV (Sp (𝓞 K))) (ψ : P.A ⟶ Q.A) [IsMonHom ψ] (n : ℕ) (hn : 0 < n)
    (h : ∀ u : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P.A, u ^ n = 1 → u ≫ ψ = 1)
    (T : Over (Sp (𝓞 K))) (x : T ⟶ P.A) (hx : x ^ n = 1) : x ≫ ψ = 1 := by
  set gc : 𝓞 K →+* ℂ := σ.comp (algebraMap (𝓞 K) K) with hgc
  set t : Sp ℂ ⟶ Sp (𝓞 K) := spMap gc with ht
  have hgci : Function.Injective gc :=
    σ.injective.comp (IsFractionRing.injective (𝓞 K) K)
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  obtain ⟨P', gA, hgA, -, hmA, -⟩ := hL.polBaseChange (Sp (𝓞 K)) (Sp ℂ) t P
  obtain ⟨Q', gB, hgB, -, hmB, -⟩ := hL.polBaseChange (Sp (𝓞 K)) (Sp ℂ) t Q
  have := Q.isAb.proper
  have := Q'.isAb.proper

  let ψ' : P'.A ⟶ Q'.A := Over.homMk (hgB.lift (gA ≫ ψ.left) P'.A.hom
    (by rw [Category.assoc, Over.w ψ, hgA.w])) (hgB.lift_snd _ _ _)
  have tb : ∀ (T' : Over (Sp ℂ)) (y : T' ⟶ P'.A),
      Out.toBase hgB.w (y ≫ ψ') = Out.toBase hgA.w y ≫ ψ := by
    intro T' y
    apply Over.OverMorphism.ext
    simp [Out.toBase, ψ']
  have : IsMonHom ψ' := GlobalTheory.DivisibleHom.isMonHom_of_mul_points ψ' fun T' y₁ y₂ =>
    toBase_injective hgB (by rw [tb, hmA, MonObj.mul_comp, hmB, tb, tb])

  have hC : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A, y ^ n = 1 → y ≫ ψ' = 1 := by
    intro y hy
    let e : Over.mk t ⟶ Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ t) := Over.homMk (𝟙 _) (by simp)
    have h1 : (e ≫ Out.toBase hgA.w y) ^ n = 1 := by
      rw [← MonObj.comp_pow, ← toBase_pow hgA hmA, hy, toBase_one hgA hmA, MonObj.comp_one]
    have h2 := h _ h1
    apply toBase_injective hgB
    rw [tb, toBase_one hgB hmB, eq_one_iff]
    have h3 := (eq_one_iff _).1 h2
    simpa [e] using h3
  obtain ⟨α, hα, hfac⟩ := GlobalTheory.HolUnifEnd.exists_factor_pow P'.A Q'.A P'.isAb n hn ψ' hC
  have kill' : ∀ (T' : Over (Sp ℂ)) (y : T' ⟶ P'.A), y ^ n = 1 → y ≫ ψ' = 1 := by
    intro T' y hy
    rw [← hfac, ← Category.assoc, MonObj.comp_pow, Category.comp_id, hy, MonObj.one_comp]

  obtain ⟨_, hfl, _, _, -⟩ := hL.mulN (Sp (𝓞 K)) P n hn
  let Z := pullback (Out.mulA P.A n) η[P.A]
  let inc : Z ⟶ P.A := pullback.fst (Out.mulA P.A n) η[P.A]
  have hinc : inc ^ n = 1 := by
    rw [← GlobalTheory.DivisibleHom.comp_mulA, pullback.condition, Hom.one_def,
      toUnit_unique (pullback.snd (Out.mulA P.A n) η[P.A]) (toUnit Z)]
  have hp := (IsPullback.of_hasPullback (Out.mulA P.A n) η[P.A]).map (Over.forget (Sp (𝓞 K)))
  have hf : Flat (pullback.snd (Out.mulA P.A n) η[P.A]).left :=
    MorphismProperty.of_isPullback (P := @Flat) hp hfl
  have hw : (pullback.snd (Out.mulA P.A n) η[P.A]).left = Z.hom := by
    simpa using Over.w (pullback.snd (Out.mulA P.A n) η[P.A])
  rw [hw] at hf
  have hx' : x ≫ Out.mulA P.A n = toUnit T ≫ η[P.A] := by
    rw [GlobalTheory.DivisibleHom.comp_mulA, hx, Hom.one_def]
  suffices hZ : inc ≫ ψ = 1 by
    rw [← pullback.lift_fst x (toUnit T) hx', Category.assoc]
    change _ ≫ inc ≫ ψ = 1
    rw [hZ, MonObj.comp_one]
  rw [eq_one_iff]
  refine GlobalTheory.ArcDataDescent.ext_of_injective hgci (IsPullback.of_hasPullback Z.hom t) Q.A.hom ?_ ?_
  · simp
  · let π := pullback.fst Z.hom t
    let p' := pullback.snd Z.hom t
    let w := hgA.lift (π ≫ inc.left) p' (by rw [Category.assoc, Over.w inc, pullback.condition])
    let x' : Over.mk p' ⟶ P'.A := Over.homMk w (hgA.lift_snd _ _ _)
    let πZ : Over.mk (p' ≫ t) ⟶ Z := Over.homMk π pullback.condition
    have hb : Out.toBase hgA.w x' = πZ ≫ inc := by
      apply Over.OverMorphism.ext
      simp [Out.toBase, x', w, πZ]
    have hx'n : x' ^ n = 1 := by
      apply toBase_injective hgA
      rw [toBase_pow hgA hmA, hb, ← MonObj.comp_pow, hinc, MonObj.comp_one, toBase_one hgA hmA]
    have k2 := congrArg (Out.toBase hgB.w) (kill' _ x' hx'n)
    rw [tb, toBase_one hgB hmB, hb, eq_one_iff] at k2
    simp only [Over.comp_left] at k2 ⊢
    rw [pullback.condition_assoc]
    simpa [πZ] using k2

end GlobalTheory.DivisibleLinear

namespace GlobalTheory.DivisibleLinear

theorem exists_linear_pow_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A B : GlobalTheory.CM.PAT H (Sp (𝓞 K)))
    (ψ : A.t.G ⟶ B.t.G), GlobalTheory.Serre.IsLinearHom A.t.act B.t.act ψ → ∀ n : ℕ, 0 < n →
    (∀ u : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.t.G, u ^ n = 1 → u ≫ ψ = 1) →
    ∃ χ : A.t.G ⟶ B.t.G, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act χ ∧ χ ^ n = ψ := by
  intro E _ _ _ H K _ _ σ A B ψ hψ n hn hk
  have := hψ.isMonHom
  have hker := torsion_comp_eq_one σ A.pol B.pol ψ n hn hk
  obtain ⟨⟨χ, hχ, hχψ⟩, -⟩ := GlobalTheory.DivisibleHom.exists_eq_pow_of_torsion_comp_eq_one
    (fun S _ P m hm => by
      obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.abelianSchemeLaws_all.1.mulN S P m hm
      exact ⟨h1, h2, h3, h4⟩)
    (Sp (𝓞 K)) A.pol B.t.G n hn ψ hψ.isMonHom hker
  refine ⟨χ, ⟨hχ, fun c => ?_⟩, hχψ.symm⟩
  have := B.t.act.hom c
  have := A.t.act.hom c
  obtain ⟨_, hfl, hsu, -⟩ := GlobalTheory.abelianSchemeLaws_all.1.mulN (Sp (𝓞 K)) A.pol n hn
  have : Flat (Out.mulA A.t.G n).left := hfl
  have : Surjective (Out.mulA A.t.G n).left := hsu
  apply GlobalTheory.DivisibleHom.cancel_of_flat_surjective (Out.mulA A.t.G n)
  rw [GlobalTheory.DivisibleHom.mulA_comp, GlobalTheory.DivisibleHom.mulA_comp, ← MonObj.comp_pow, ← hχψ, hψ.comm c, hχψ,
    MonObj.pow_comp]

end GlobalTheory.DivisibleLinear
end
end

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearHom_pow_eq_of_kills_complex_torsion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A B : GlobalTheory.CM.PAT H (Sp (𝓞 K)))
    (ψ : A.t.G ⟶ B.t.G), GlobalTheory.Serre.IsLinearHom A.t.act B.t.act ψ → ∀ n : ℕ, 0 < n →
    (∀ u : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.t.G, u ^ n = 1 → u ≫ ψ = 1) →
    ∃ χ : A.t.G ⟶ B.t.G, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act χ ∧ χ ^ n = ψ := by
  atlas_forward_decl GlobalTheory.DivisibleLinear.exists_linear_pow_eq
end

section
open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM.CplxGen

section Points

open scoped CategoryTheory.Obj

variable {S : Scheme.{0}} (f : Sp ℂ ⟶ S)

private def pt {G : Over S} (x : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback f).obj G) : Over.mk f ⟶ G :=
  Over.homMk (x.left ≫ pullback.fst G.hom f) (by
    have h : x.left ≫ pullback.snd G.hom f = 𝟙 _ := Over.w x
    rw [Category.assoc, pullback.condition, ← Category.assoc, h]
    exact Category.id_comp _)

private theorem pt_injective {G : Over S} : Function.Injective (pt f (G := G)) := fun a b e =>
  Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) e) ((Over.w a).trans (Over.w b).symm))

private theorem pt_surjective {G : Over S} : Function.Surjective (pt f (G := G)) := fun y =>
  ⟨Over.homMk (pullback.lift y.left (𝟙 _) ((Over.w y).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _),
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩

private theorem pt_map {G G' : Over S} (φ : G ⟶ G') (x : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback f).obj G) :
    pt f (x ≫ (Over.pullback f).map φ) = pt f x ≫ φ := by
  refine Over.OverMorphism.ext ?_
  simp only [pt, Over.homMk_left, Over.comp_left, Over.pullback_map_left, Category.assoc]
  exact congrArg (x.left ≫ ·) (pullback.lift_fst _ _ _)

private theorem pt_mul {G : Over S} [GrpObj G] (x y : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback f).obj G) :
    pt f (x * y) = pt f x * pt f y := by
  let ρ : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ f) ⟶ Over.mk f := Over.homMk (𝟙 _) (by simp)
  have h := (isGrpPullback_pullback G f).2 _ x y (ρ ≫ pt f x) (ρ ≫ pt f y) (Category.id_comp _) (Category.id_comp _)
  rw [← MonObj.comp_mul] at h
  refine Over.OverMorphism.ext ?_
  exact h.symm.trans (Category.id_comp _)

private theorem exists_unif (P : Out.PolAV S) : ∃ (L : LB ((Over.pullback f).obj P.A).left)
    (_ : HolUnif ((Over.pullback f).obj P.A) L P.g), IsAbelianScheme ((Over.pullback f).obj P.A) ∧
      SmoothOfRelativeDimension P.g ((Over.pullback f).obj P.A).hom := by
  have := P.isAb.comm
  let Q := TorsionTauCompare.polOfPullback P _ (isGrpPullback_pullback P.A f)
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨v, -⟩ := thetaUnifAV_all Q rig hrig
  exact ⟨_, v, Q.isAb, Q.smoothDim⟩

private theorem exists_unif_points (P Q : Out.PolAV S) :
    ∃ (ΛA : Submodule ℤ (Fin P.g → ℂ)) (ΛB : Submodule ℤ (Fin Q.g → ℂ))
      (eA : (Fin P.g → ℂ) → (Over.mk f ⟶ P.A)) (eB : (Fin Q.g → ℂ) → (Over.mk f ⟶ Q.A)),
      (∀ z w, eA (z + w) = eA z * eA w) ∧ Function.Surjective eA ∧ (∀ z, eA z = 1 ↔ z ∈ ΛA) ∧
      DiscreteTopology ΛA ∧ Submodule.span ℝ (ΛA : Set (Fin P.g → ℂ)) = ⊤ ∧
      (∀ z w, eB (z + w) = eB z * eB w) ∧ Function.Surjective eB ∧ (∀ z, eB z = 1 ↔ z ∈ ΛB) ∧
      DiscreteTopology ΛB ∧
      (∀ φ : P.A ⟶ P.A, IsMonHom φ → ∃ M : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), ∀ z, eA (M z) = eA z ≫ φ) ∧
      (∀ φ : Q.A ⟶ Q.A, IsMonHom φ → ∃ M : (Fin Q.g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ), ∀ z, eB (M z) = eB z ≫ φ) ∧
      (∀ φ : P.A ⟶ Q.A, IsMonHom φ → ∃ M : (Fin P.g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ), ∀ z, eB (M z) = eA z ≫ φ) := by
  obtain ⟨L, u, hA, hdA⟩ := exists_unif f P
  obtain ⟨L', v, hB, hdB⟩ := exists_unif f Q
  have hu := TorusTransfer.tangent_bijective u hdA
  have hv := TorusTransfer.tangent_bijective v hdB
  have one : ∀ {G : Over S} [GrpObj G] (x : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback f).obj G), pt f x = 1 ↔ x = 1 :=
    fun {G} _ x => map_eq_one_iff (MonoidHom.mk' (pt f (G := G)) (pt_mul f)) (pt_injective f)
  refine ⟨u.Λ, v.Λ, fun z => pt f (u.ex z), fun z => pt f (v.ex z),
    fun z w => by beta_reduce; rw [u.ex_add, pt_mul],
    (pt_surjective f).comp u.ex_onto, fun z => (one _).trans (u.ker z), u.discrete, u.full,
    fun z w => by beta_reduce; rw [v.ex_add, pt_mul], (pt_surjective f).comp v.ex_onto, fun z => (one _).trans (v.ker z),
    v.discrete, fun φ _ => ?_, fun φ _ => ?_, fun φ _ => ?_⟩
  · obtain ⟨M, hM, -⟩ := HomLinear.exists_linear_of_isMonHom _ _ hA hA _ _ _ _ u u hu.1 hu.2
      ((Over.pullback f).map φ) inferInstance
    exact ⟨M, fun z => by beta_reduce; rw [hM, pt_map]⟩
  · obtain ⟨M, hM, -⟩ := HomLinear.exists_linear_of_isMonHom _ _ hB hB _ _ _ _ v v hv.1 hv.2
      ((Over.pullback f).map φ) inferInstance
    exact ⟨M, fun z => by beta_reduce; rw [hM, pt_map]⟩
  · obtain ⟨M, hM, -⟩ := HomLinear.exists_linear_of_isMonHom _ _ hA hB _ _ _ _ u v hv.1 hv.2
      ((Over.pullback f).map φ) inferInstance
    exact ⟨M, fun z => by beta_reduce; rw [hM, pt_map]⟩

end Points

private theorem lattice_mem_closure (E : Type) [Field E] [NumberField E] (gA gB p : ℕ)
    (ΛA : Submodule ℤ (Fin gA → ℂ)) (ΛB : Submodule ℤ (Fin gB → ℂ)) (αA : 𝓞 E →+* Module.End ℂ (Fin gA → ℂ))
    (αB : 𝓞 E →+* Module.End ℂ (Fin gB → ℂ)) (J : Fin p → (Fin gA → ℂ) →ₗ[ℂ] (Fin gB → ℂ))
    (hdim : 2 * gA ≤ Module.finrank ℚ E) (hAd : DiscreteTopology ΛA)
    (hAf : Submodule.span ℝ (ΛA : Set (Fin gA → ℂ)) = ⊤) (hBd : DiscreteTopology ΛB)
    (sA : ∀ s, ∀ z ∈ ΛA, αA s z ∈ ΛA) (sB : ∀ s, ∀ z ∈ ΛB, αB s z ∈ ΛB)
    (inter : ∀ a s z, J a (αA s z) = αB s (J a z)) (hJ : ∀ a, ∀ z ∈ ΛA, J a z ∈ ΛB)
    (honto : ∀ w, ∃ v : Fin p → (Fin gA → ℂ), w - ∑ a, J a (v a) ∈ ΛB) (l : Fin gB → ℂ) (hl : l ∈ ΛB) :
    l ∈ AddSubmonoid.closure {w : Fin gB → ℂ | ∃ (m : ℕ) (z : Fin p → 𝓞 E) (x : Fin gA → ℂ), 0 < m ∧ x ∈ ΛA ∧
      (∀ x' ∈ ΛA, (m : ℂ)⁻¹ • ∑ a, J a (αA (z a) x') ∈ ΛB) ∧ w = (m : ℂ)⁻¹ • ∑ a, J a (αA (z a) x)} := by
  classical
  obtain ⟨N, x, hN, hx, hNl⟩ := UpperTheory.exists_nsmul_mem_sum_image_lattice_of_surjective_mod gA gB p ΛA ΛB J hAf hBd hJ honto l hl
  obtain ⟨j, hj, hjs⟩ := UpperTheory.exists_injective_lattice_hom_ringOfIntegers_of_finrank_ge E gA ΛA αA hdim hAd sA
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  let I : Ideal (𝓞 E) := Ideal.span (Set.range j)
  by_cases hI : I = ⊥
  · have h0 : ∀ a, x a = 0 := fun a => by
      have h : j ⟨x a, hx a⟩ ∈ I := Ideal.subset_span ⟨_, rfl⟩
      rw [hI, Ideal.mem_bot, ← map_zero j] at h
      exact congrArg Subtype.val (hj h)
    simp only [h0, map_zero, Finset.sum_const_zero] at hNl
    rw [(smul_eq_zero.1 hNl).resolve_left hN.ne']
    exact zero_mem _
  obtain ⟨c, hcI, hc⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨I', hI'⟩ : I ∣ Ideal.span {c} := Ideal.dvd_span_singleton.2 hcI
  have hmem : ∀ t ∈ I, ∃ y : ΛA, j y = t := fun t ht => by
    refine Submodule.span_induction (p := fun t _ => ∃ y : ΛA, j y = t) (fun t ht => ht) ⟨0, map_zero _⟩ ?_ ?_ ht
    · rintro _ _ - - ⟨y, rfl⟩ ⟨y', rfl⟩
      exact ⟨y + y', map_add _ _ _⟩
    · rintro s _ - ⟨y, rfl⟩
      exact ⟨_, hjs s y⟩
  have hdiv : ∀ b ∈ I', ∀ y : ΛA, ∃ u, u * c = j y * b := fun b hb y =>
    Ideal.mem_span_singleton'.1 (hI' ▸ Ideal.mul_mem_mul (Ideal.subset_span ⟨y, rfl⟩) hb)
  have key : ∀ t ∈ I * I', ∃ u, u * c = t ∧ αB u l ∈ AddSubmonoid.closure
      {w : Fin gB → ℂ | ∃ (m : ℕ) (z : Fin p → 𝓞 E) (x : Fin gA → ℂ), 0 < m ∧ x ∈ ΛA ∧
        (∀ x' ∈ ΛA, (m : ℂ)⁻¹ • ∑ a, J a (αA (z a) x') ∈ ΛB) ∧ w = (m : ℂ)⁻¹ • ∑ a, J a (αA (z a) x)} := by
    intro t ht
    refine Submodule.mul_induction_on ht (fun r hr b hb => ?_) ?_
    · obtain ⟨y, rfl⟩ := hmem r hr
      choose φ hφ using hdiv b hb
      have hsw : ∀ y y' : ΛA, αA (φ y) y' = αA (φ y') y := fun y y' => by
        have h : (⟨αA (φ y) y', sA _ _ y'.2⟩ : ΛA) = ⟨αA (φ y') y, sA _ _ y.2⟩ := hj (by
          rw [hjs, hjs]
          refine mul_right_cancel₀ hc ?_
          linear_combination j y' * hφ y - j y * hφ y')
        exact congrArg Subtype.val h
      have hval : ∀ y' : ΛA, (N : ℂ)⁻¹ • ∑ a, J a (αA (φ ⟨x a, hx a⟩) y') = αB (φ y') l := fun y' => by
        have : ∑ a, J a (αA (φ ⟨x a, hx a⟩) y') = N • αB (φ y') l := by
          rw [← map_nsmul, hNl, map_sum]
          exact Finset.sum_congr rfl fun a _ => by rw [hsw, inter]
        rw [this, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]
      refine ⟨φ y, hφ y, AddSubmonoid.subset_closure ⟨N, fun a => φ ⟨x a, hx a⟩, y, hN, y.2, fun x' hx' => ?_,
        (hval y).symm⟩⟩
      rw [hval ⟨x', hx'⟩]
      exact sB _ _ hl
    · rintro _ _ ⟨u, rfl, hu⟩ ⟨u', rfl, hu'⟩
      exact ⟨u + u', add_mul _ _ _, by rw [map_add, LinearMap.add_apply]; exact add_mem hu hu'⟩
  obtain ⟨u, hu, h⟩ := key c (hI' ▸ Ideal.mem_span_singleton_self c)
  obtain rfl : u = 1 := mul_right_cancel₀ hc (hu.trans (_root_.one_mul c).symm)
  simpa using h

section Unif

variable {P : Type} [CommGroup P] {g : ℕ} {e : (Fin g → ℂ) → P} {Λ : Submodule ℤ (Fin g → ℂ)}

private theorem eq_zero_of_smul_mem (hd : DiscreteTopology Λ) {z : Fin g → ℂ} (hz : ∀ t : ℂ, t • z ∈ Λ) : z = 0 := by
  have hc : Continuous fun t : ℂ => (⟨t • z, hz t⟩ : Λ) := by fun_prop
  have h := (IsLocallyConstant.iff_continuous _).2 hc |>.apply_eq_of_preconnectedSpace 1 0
  simpa using congrArg Subtype.val h

private theorem e_zero (hadd : ∀ z w, e (z + w) = e z * e w) : e 0 = 1 := by
  have h := hadd 0 0
  rw [add_zero] at h
  simpa using h.symm

private def eHom (hadd : ∀ z w, e (z + w) = e z * e w) : (Fin g → ℂ) →+ Additive P where
  toFun z := Additive.ofMul (e z)
  map_zero' := by rw [e_zero hadd]; rfl
  map_add' z w := by rw [hadd]; rfl

private theorem e_sub (hadd : ∀ z w, e (z + w) = e z * e w) (z w : Fin g → ℂ) : e (z - w) = e z * (e w)⁻¹ := by
  have h := hadd (z - w) w
  rw [sub_add_cancel] at h
  rw [h, mul_inv_cancel_right]

private theorem e_nsmul (hadd : ∀ z w, e (z + w) = e z * e w) (k : ℕ) (z : Fin g → ℂ) : e (k • z) = e z ^ k :=
  congrArg Additive.toMul (map_nsmul (eHom hadd) k z)

private theorem e_sum (hadd : ∀ z w, e (z + w) = e z * e w) {Idx : Type} (s : Finset Idx) (f : Idx → Fin g → ℂ) :
    e (s.sum f) = s.prod (fun i => e (f i)) :=
  congrArg Additive.toMul (map_sum (eHom hadd) f s)

private theorem mem_of_eq (hadd : ∀ z w, e (z + w) = e z * e w) (hker : ∀ z, e z = 1 ↔ z ∈ Λ) {z w : Fin g → ℂ}
    (h : e z = e w) : z - w ∈ Λ := by
  rw [← hker, e_sub hadd, h, mul_inv_cancel]

private theorem rigid (hadd : ∀ z w, e (z + w) = e z * e w) (hker : ∀ z, e z = 1 ↔ z ∈ Λ) (hd : DiscreteTopology Λ)
    {W : Type} [AddCommGroup W] [Module ℂ W] (M M' : W →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, e (M z) = e (M' z)) :
    M = M' := by
  ext1 z
  have := eq_zero_of_smul_mem hd (z := M z - M' z) fun t => by
    have := mem_of_eq hadd hker (h (t • z))
    rwa [map_smul, map_smul, ← smul_sub] at this
  exact sub_eq_zero.1 this

end Unif

private theorem comp_prod' {S : Scheme.{0}} {T A B : Over S} [MonObj B] [IsCommMonObj B] {Idx : Type} (s : Finset Idx)
    (x : T ⟶ A) (f : Idx → (A ⟶ B)) : x ≫ s.prod f = s.prod (fun i => x ≫ f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]

private theorem exists_widePullback_of_iteratedLine {P : Type} [CommGroup P] {p : ℕ} (f : Fin p ⊕ Fin 0 → P) (g : Fin p → P)
    (h : ∀ a, g a = f (Sum.inl a)) :
    (List.ofFn fun j : Fin (p + 0) => f (finSumFinEquiv.symm j)).prod * (∏ a, g a)⁻¹ = 1 := by
  rw [List.prod_ofFn, Equiv.prod_comp finSumFinEquiv.symm f, Fintype.prod_sum_type, mul_inv_eq_one]
  simp [h]

theorem _root_.GlobalTheory.T.cm_torsion_mem_closure_generators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (n : ℕ), 0 < n →
    ∀ y : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G, y ^ n = 1 →
    y ∈ Submonoid.closure {w : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G |
      ∃ (m : ℕ) (x : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G) (z : Fin p → 𝓞 E),
        0 < m ∧ x ^ (n * m) = 1 ∧
        (∀ x' : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G, x' ^ m = 1 →
          x' ≫ ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a) = 1) ∧
        w = x ≫ ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)} := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X n hn y hy
  classical
  obtain ⟨ΛA, ΛB, eA, eB, hAadd, hAsurj, hAker, hAd, hAf, hBadd, hBsurj, hBker, hBd, lA, lB, lJ⟩ :=
    exists_unif_points (spMap (σ₁.comp (algebraMap (𝓞 K) K))) (X.A true).pol X.B.pol
  choose αA hαA using fun s => lA ((X.A true).t.act.act s) ((X.A true).t.act.hom s)
  choose αB hαB using fun s => lB (X.B.t.act.act s) (X.B.t.act.hom s)
  choose J hJ using fun a : Fin p => lJ (GlobalTheory.FlatCM.phiP X a) (X.lin (Sum.inl a)).isMonHom
  have hdim : 2 * (X.A true).g ≤ Module.finrank ℚ E := by
    rw [GlobalTheory.CMSharedCompare.dim_eq (X.A true) X.split X.typeP X.ρ_sq]
    omega
  have act0 : ∀ {G : Over (Sp (𝓞 K))} [GrpObj G] (a : OAct (𝓞 E) G), a.act 0 = 1 := by
    intro G _ a
    have h := a.add 0 0
    rw [add_zero] at h
    simpa using h.symm

  let αA' : 𝓞 E →+* Module.End ℂ (Fin (X.A true).g → ℂ) :=
    { toFun := αA
      map_one' := rigid hAadd hAker hAd _ _ fun z => by
        rw [hαA, (X.A true).t.act.one, Category.comp_id]; rfl
      map_mul' := fun s t => rigid hAadd hAker hAd _ _ fun z => by
        show eA (αA (s * t) z) = eA (αA s (αA t z))
        rw [hαA, hαA, hαA, Category.assoc, ← (X.A true).t.act.mul, mul_comm]
      map_zero' := rigid hAadd hAker hAd _ _ fun z => by
        show eA (αA 0 z) = eA 0
        rw [hαA, act0, MonObj.comp_one, e_zero hAadd]
      map_add' := fun s t => rigid hAadd hAker hAd _ _ fun z => by
        show eA (αA (s + t) z) = eA (αA s z + αA t z)
        rw [hαA, hAadd, hαA, hαA, (X.A true).t.act.add, MonObj.comp_mul] }
  let αB' : 𝓞 E →+* Module.End ℂ (Fin X.B.g → ℂ) :=
    { toFun := αB
      map_one' := rigid hBadd hBker hBd _ _ fun z => by
        rw [hαB, X.B.t.act.one, Category.comp_id]; rfl
      map_mul' := fun s t => rigid hBadd hBker hBd _ _ fun z => by
        show eB (αB (s * t) z) = eB (αB s (αB t z))
        rw [hαB, hαB, hαB, Category.assoc, ← X.B.t.act.mul, mul_comm]
      map_zero' := rigid hBadd hBker hBd _ _ fun z => by
        show eB (αB 0 z) = eB 0
        rw [hαB, act0, MonObj.comp_one, e_zero hBadd]
      map_add' := fun s t => rigid hBadd hBker hBd _ _ fun z => by
        show eB (αB (s + t) z) = eB (αB s z + αB t z)
        rw [hαB, hBadd, hαB, hαB, X.B.t.act.add, MonObj.comp_mul] }
  have lin : ∀ a, Serre.IsLinearHom (X.A true).t.act X.B.t.act (GlobalTheory.FlatCM.phiP X a) := fun a => X.lin (Sum.inl a)
  have stabA : ∀ s, ∀ z ∈ ΛA, αA' s z ∈ ΛA := fun s z hz => by
    have := (X.A true).t.act.hom s
    rw [← hAker] at hz ⊢
    show eA (αA s z) = 1
    rw [hαA, hz, MonObj.one_comp]
  have stabB : ∀ s, ∀ z ∈ ΛB, αB' s z ∈ ΛB := fun s z hz => by
    have := X.B.t.act.hom s
    rw [← hBker] at hz ⊢
    show eB (αB s z) = 1
    rw [hαB, hz, MonObj.one_comp]
  have inter : ∀ a s z, J a (αA' s z) = αB' s (J a z) := fun a s z => by
    have h := rigid hBadd hBker hBd ((J a).comp (αA s)) ((αB s).comp (J a)) fun z => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hJ, hαA, hαB, hJ, Category.assoc, (lin a).comm,
        Category.assoc]
    exact congrArg (fun M : (Fin (X.A true).g → ℂ) →ₗ[ℂ] (Fin X.B.g → ℂ) => M z) h
  have hJΛ : ∀ a, ∀ z ∈ ΛA, J a z ∈ ΛB := fun a z hz => by
    have := (lin a).isMonHom
    rw [← hAker] at hz
    rw [← hBker, hJ, hz, MonObj.one_comp]
  have honto : ∀ w, ∃ v : Fin p → (Fin (X.A true).g → ℂ), w - ∑ a, J a (v a) ∈ ΛB := by
    intro w
    obtain ⟨x, hx⟩ := X.onto (eB w)
    choose v hv using fun a : Fin p => hAsurj (x (Sum.inl a))
    refine ⟨v, (hBker _).1 ?_⟩
    rw [e_sub hBadd, e_sum hBadd, hx]
    exact exists_widePullback_of_iteratedLine (fun j : Fin p ⊕ Fin 0 => (x j ≫ X.φ j :
      Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G)) (fun a => eB (J a (v a)))
      fun a => (hJ a (v a)).trans (congrArg (· ≫ GlobalTheory.FlatCM.phiP X a) (hv a))
  have hG : ∀ (u : Fin (X.A true).g → ℂ) (z : Fin p → 𝓞 E),
      eA u ≫ ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a) = eB (∑ a, J a (αA' (z a) u)) := by
    intro u z
    rw [comp_prod', e_sum hBadd]
    refine Finset.prod_congr rfl fun a _ => ?_
    show _ = eB (J a (αA (z a) u))
    rw [hJ, hαA, Category.assoc]
  obtain ⟨w, rfl⟩ := hBsurj y
  have hnw : n • w ∈ ΛB := (hBker _).1 (by rw [e_nsmul hBadd, hy])
  have hcl := lattice_mem_closure E (X.A true).g X.B.g p ΛA ΛB αA' αB' J hdim hAd hAf hBd
    stabA stabB inter hJΛ honto _ hnw
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have key : ∀ l ∈ AddSubmonoid.closure {w : Fin X.B.g → ℂ | ∃ (m : ℕ) (z : Fin p → 𝓞 E) (x : Fin (X.A true).g → ℂ),
      0 < m ∧ x ∈ ΛA ∧ (∀ x' ∈ ΛA, (m : ℂ)⁻¹ • ∑ a, J a (αA' (z a) x') ∈ ΛB) ∧
        w = (m : ℂ)⁻¹ • ∑ a, J a (αA' (z a) x)},
      eB ((n : ℂ)⁻¹ • l) ∈ Submonoid.closure {w : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G |
        ∃ (m : ℕ) (x : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G) (z : Fin p → 𝓞 E),
          0 < m ∧ x ^ (n * m) = 1 ∧
          (∀ x' : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G, x' ^ m = 1 →
            x' ≫ ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a) = 1) ∧
          w = x ≫ ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)} := by
    intro l hl
    induction hl using AddSubmonoid.closure_induction with
    | mem t ht =>
      obtain ⟨m, z, x, hm, hx, hkill, rfl⟩ := ht
      have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      refine Submonoid.subset_closure ⟨m, eA (((n * m : ℕ) : ℂ)⁻¹ • x), z, hm, ?_, ?_, ?_⟩
      · rw [← e_nsmul hAadd, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
          mul_inv_cancel₀ (by exact_mod_cast (Nat.mul_pos hn hm).ne'), one_smul]
        exact (hAker x).2 hx
      · intro x' hx'
        obtain ⟨u, rfl⟩ := hAsurj x'
        have hu : m • u ∈ ΛA := (hAker _).1 (by rw [e_nsmul hAadd, hx'])
        have h := hkill _ hu
        have e1 : (m : ℂ)⁻¹ • ∑ a, J a (αA' (z a) (m • u)) = ∑ a, J a (αA' (z a) u) := by
          simp only [map_nsmul, ← Finset.smul_sum]
          rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hm0, one_smul]
        rw [e1] at h
        rw [hG, (hBker _).2 h]
      · rw [hG]
        congr 1
        simp only [map_smul, ← Finset.smul_sum, smul_smul, Nat.cast_mul, mul_inv]
    | zero => rw [smul_zero, e_zero hBadd]; exact Submonoid.one_mem _
    | add a b _ _ ha hb => rw [smul_add, hBadd]; exact Submonoid.mul_mem _ ha hb
  have := key _ hcl
  rwa [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn0, one_smul] at this

end GlobalTheory.FlatCM.CplxGen

end
end

section
section
open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.TorsionKill

theorem eq_of_pullback_eq {S S' : Scheme.{0}} (t : S' ⟶ S) [IsSchemeTheoreticallyDominant t]
    [QuasiCompact t] {Y X : Over S} [Flat Y.hom] [IsSeparated X.hom] {a b : Y ⟶ X}
    (h : (Over.pullback t).map a = (Over.pullback t).map b) : a = b := by
  apply Over.OverMorphism.ext
  refine GlobalTheory.KernelNoTorsion.eq_of_isSchemeTheoreticallyDominant X.hom ((Over.w a).trans (Over.w b).symm)
    (pullback.fst Y.hom t) ?_
  have h' := congr(($h).left ≫ pullback.fst X.hom t)
  exact (pullback.lift_fst _ _ _).symm.trans (h'.trans (pullback.lift_fst _ _ _))

theorem isSchemeTheoreticallyDominant_complexPoint (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) :
    IsSchemeTheoreticallyDominant (spMap (σ.comp (algebraMap (𝓞 K) K))) := by
  have : IsDominant (spMap (σ.comp (algebraMap (𝓞 K) K))) := by
    rw [isDominant_iff]
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_
    have hinj : Function.Injective (σ.comp (algebraMap (𝓞 K) K)) := by
      rw [RingHom.coe_comp]; exact σ.injective.comp (IsFractionRing.injective (𝓞 K) K)
    exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

theorem flat_ker (S : Scheme.{0}) (P : Out.PolAV S) (m : ℕ) (hm : 1 ≤ m) :
    Flat (pullback (𝟙 P.A ^ m) η[P.A]).hom := by
  have hf := (GlobalTheory.PairKernel.mulA_finite_flat_surjective S P m hm).2.1
  have hp := (IsPullback.of_hasPullback (𝟙 P.A ^ m) η[P.A]).map (Over.forget S)
  have he : Flat (pullback.snd (𝟙 P.A ^ m) η[P.A]).left :=
    MorphismProperty.of_isPullback (P := @Flat) hp hf
  have hw : (pullback.snd (𝟙 P.A ^ m) η[P.A]).left = (pullback (𝟙 P.A ^ m) η[P.A]).hom := by
    simpa using Over.w (pullback.snd (𝟙 P.A ^ m) η[P.A])
  rwa [hw] at he

theorem kill_complex (A' B' : Over (Sp ℂ)) [GrpObj A'] [GrpObj B'] (hA : IsAbelianScheme A')
    [IsSeparated B'.hom] [LocallyOfFiniteType B'.hom] (N : ℕ) (hN : 1 ≤ N) (φ : A' ⟶ B')
    (h : ∀ p : Over.mk (𝟙 (Sp ℂ)) ⟶ pullback (𝟙 A' ^ N) η[A'],
      p ≫ pullback.fst (𝟙 A' ^ N) η[A'] ≫ φ = p ≫ 1) :
    pullback.fst (𝟙 A' ^ N) η[A'] ≫ φ = 1 := by
  have hunit : IsUnit ((N : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have := (IsUnit.mk0 (N : ℂ) (by exact_mod_cast (show N ≠ 0 by omega))).map
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨-, -, het, -⟩ := abelianScheme_id_pow_finite_etale_surjective _ A' N hA hunit
  have hp := (IsPullback.of_hasPullback ((𝟙 A' ^ N)) η[A']).map (Over.forget (Sp ℂ))
  have he : Etale (pullback.snd ((𝟙 A' ^ N)) η[A']).left :=
    MorphismProperty.of_isPullback (P := @Etale) hp het
  have hw : (pullback.snd ((𝟙 A' ^ N)) η[A']).left = (pullback (𝟙 A' ^ N) η[A']).hom := by
    simpa using Over.w (pullback.snd ((𝟙 A' ^ N)) η[A'])
  rw [hw] at he
  have : IsReduced (pullback (𝟙 A' ^ N) η[A']).left :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback (𝟙 A' ^ N) η[A']).hom
  refine Over.OverMorphism.ext ?_
  have : LocallyOfFiniteType ((pullback.fst (𝟙 A' ^ N) η[A'] ≫ φ).left ≫ B'.hom) := by
    rw [Over.w]; infer_instance
  refine ext_of_apply_eq B'.hom Set.univ isClosed_univ.isLocallyClosed dense_univ (fun z _ hz => ?_)
    ((Over.w _).trans (Over.w _).symm)
  let p : Over.mk (𝟙 (Sp ℂ)) ⟶ pullback (𝟙 A' ^ N) η[A'] :=
    Over.homMk (pointOfClosedPoint (pullback (𝟙 A' ^ N) η[A']).hom z hz) (pointOfClosedPoint_comp _ _ _)
  have e := h p
  have e' := congrArg (fun q => q.left (IsLocalRing.closedPoint ℂ)) e
  have hz' : p.left (IsLocalRing.closedPoint ℂ) = z := pointOfClosedPoint_apply _ z hz _
  simp only [Over.comp_left] at e'
  rw [← hz']
  exact e'

end GlobalTheory.TorsionKill

noncomputable section
namespace GlobalTheory.TorsionKill

def ptOf {S : Scheme.{0}} (t : Sp ℂ ⟶ S) {A : Over S}
    (y : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback t).obj A) : Over.mk t ⟶ A :=
  Over.homMk (y.left ≫ pullback.fst A.hom t) (by
    have hy : y.left ≫ pullback.snd A.hom t = 𝟙 _ := by simpa using Over.w y
    simp only [Over.mk_hom, Category.assoc, pullback.condition, reassoc_of% hy, Category.id_comp])

theorem ptOf_comp {S : Scheme.{0}} (t : Sp ℂ ⟶ S) {A B : Over S}
    (y : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback t).obj A) (f : A ⟶ B) :
    ptOf t (y ≫ (Over.pullback t).map f) = ptOf t y ≫ f := by
  ext
  simp [ptOf, pullback.lift_fst]

theorem ptOf_injective {S : Scheme.{0}} (t : Sp ℂ ⟶ S) {A : Over S} :
    Function.Injective (ptOf t (A := A)) := by
  intro y y' h
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg (fun q => q.left) h
  · have hy : y.left ≫ pullback.snd A.hom t = 𝟙 _ := by simpa using Over.w y
    have hy' : y'.left ≫ pullback.snd A.hom t = 𝟙 _ := by simpa using Over.w y'
    rw [hy, hy']

theorem ptOf_one {S : Scheme.{0}} (t : Sp ℂ ⟶ S) {A : Over S} [GrpObj A] :
    ptOf t (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback t).obj A) = 1 := by
  have e : (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback t).obj A) =
      (toUnit _ ≫ Functor.LaxMonoidal.ε (Over.pullback t)) ≫ (Over.pullback t).map η[A] := by
    rw [Hom.one_def, Category.assoc]; rfl
  rw [e, ptOf_comp, Hom.one_def, toUnit_unique (ptOf t _) (toUnit _)]

end GlobalTheory.TorsionKill

noncomputable section
namespace GlobalTheory.TorsionKill

theorem kill_torsion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (G : A.t.G ⟶ B.t.G),
    IsMonHom G → ∀ m : ℕ, 0 < m →
    (∀ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.t.G, x ^ m = 1 → x ≫ G = 1) →
    ∀ (T : Over (Sp (𝓞 K))) (x : T ⟶ A.t.G), x ^ m = 1 → x ≫ G = 1 := by
  intro E _ _ _ H K _ _ σ A B G _ m hm hpt T x hx
  let inc : pullback (𝟙 A.t.G ^ m) η[A.t.G] ⟶ A.t.G := pullback.fst _ _
  suffices hY : inc ≫ G = 1 by
    have hx' : x ≫ (𝟙 A.t.G ^ m) = toUnit T ≫ η[A.t.G] := by
      rw [MonObj.comp_pow, Category.comp_id]; exact hx
    rw [← pullback.lift_fst x (toUnit T) hx', Category.assoc]
    change _ ≫ inc ≫ G = 1
    rw [hY, MonObj.comp_one]
  have := flat_ker _ A.pol m hm
  have := isSchemeTheoreticallyDominant_complexPoint K σ
  have := B.ab.proper
  have := A.ab.proper
  have : IsSeparated B.t.G.hom := inferInstance
  refine eq_of_pullback_eq (spMap (σ.comp (algebraMap (𝓞 K) K))) ?_
  set t := spMap (σ.comp (algebraMap (𝓞 K) K)) with ht
  let F := Over.pullback t
  have hA' : IsAbelianScheme (F.obj A.t.G) := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A.t.G A.ab
  have : IsSeparated (F.obj B.t.G).hom := by change IsSeparated (pullback.snd _ _); infer_instance
  have : LocallyOfFiniteType (F.obj B.t.G).hom := by change LocallyOfFiniteType (pullback.snd _ _); infer_instance
  have hpow : F.map (𝟙 A.t.G ^ m) = 𝟙 (F.obj A.t.G) ^ m := by
    simpa using map_pow (F.homMonoidHom (X := A.t.G) (M := A.t.G)) (𝟙 A.t.G) m
  have hinc : inc ≫ (𝟙 A.t.G ^ m) = 1 := by
    rw [show inc ≫ (𝟙 A.t.G ^ m) = pullback.snd (𝟙 A.t.G ^ m) η[A.t.G] ≫ η[A.t.G] from pullback.condition,
      toUnit_unique (pullback.snd (𝟙 A.t.G ^ m) η[A.t.G]) (toUnit _)]
    rfl
  have hFinc : F.map inc ≫ (𝟙 (F.obj A.t.G) ^ m) = toUnit _ ≫ η[F.obj A.t.G] := by
    rw [← hpow, ← F.map_comp, hinc, Functor.map_one]; rfl
  have key := kill_complex (F.obj A.t.G) (F.obj B.t.G) hA' m hm (F.map G) (fun p => by
    let y := p ≫ pullback.fst (𝟙 (F.obj A.t.G) ^ m) η[F.obj A.t.G]
    have hy1 : y ≫ 𝟙 (F.obj A.t.G) ^ m = 1 := by
      have c : pullback.fst (𝟙 (F.obj A.t.G) ^ m) η[F.obj A.t.G] ≫ 𝟙 (F.obj A.t.G) ^ m =
          pullback.snd (𝟙 (F.obj A.t.G) ^ m) η[F.obj A.t.G] ≫ η[F.obj A.t.G] := pullback.condition
      simp only [y, Category.assoc, c]
      rw [← Category.assoc, toUnit_unique (p ≫ pullback.snd _ _) (toUnit _)]
      rfl
    have hyp : ptOf t y ^ m = 1 := by
      rw [← Category.comp_id (ptOf t y), ← MonObj.comp_pow, ← ptOf_comp, hpow, hy1, ptOf_one]
    have h2 : ptOf t (y ≫ F.map G) = ptOf t 1 := by
      rw [ptOf_comp, ptOf_one]; exact hpt _ hyp
    have h3 := ptOf_injective t h2
    simp only [y, Category.assoc] at h3
    rw [h3, MonObj.comp_one])
  have hl : F.map inc = pullback.lift (F.map inc) (toUnit _) hFinc ≫ pullback.fst _ _ :=
    (pullback.lift_fst _ _ _).symm
  rw [F.map_comp, Functor.map_one, hl, Category.assoc, key, MonObj.comp_one]

end GlobalTheory.TorsionKill
end
end
end
end

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hom_kills_torsion_of_complexPoints_oneEmbedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (G : A.t.G ⟶ B.t.G),
    IsMonHom G → ∀ m : ℕ, 0 < m →
    (∀ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.t.G, x ^ m = 1 → x ≫ G = 1) →
    ∀ (T : Over (Sp (𝓞 K))) (x : T ⟶ A.t.G), x ^ m = 1 → x ≫ G = 1 := by
  atlas_forward_decl GlobalTheory.TorsionKill.kill_torsion
end

section
section
set_option autoImplicit false

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FlatCM.TorsGen

theorem exists_linear_pow_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (G : A.t.G ⟶ B.t.G),
    GlobalTheory.Serre.IsLinearHom A.t.act B.t.act G → ∀ m : ℕ, 0 < m →
    (∀ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.t.G, x ^ m = 1 → x ≫ G = 1) →
    ∃ F : A.t.G ⟶ B.t.G, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act F ∧ F ^ m = G := by
  intro E _ _ _ H K _ _ σ A B G hG m hm hker
  have hGm := hG.isMonHom
  obtain ⟨_, hfl, hsu⟩ := GlobalTheory.PairKernel.mulA_finite_flat_surjective _ A.pol m hm
  have hc : IsCommMonObj A.t.G := A.ab.comm
  have hcB : IsCommMonObj B.t.G := B.ab.comm
  have hall := GlobalTheory.T.hom_kills_torsion_of_complexPoints_oneEmbedding E H K σ A B G hGm m hm hker
  obtain ⟨F, hF⟩ := GlobalTheory.DivisibleHom.exists_factor (A := A.t.G) m G hall
  have hFm : IsMonHom (ReciprocityTheory.ChartRestriction.G.Out.mulA A.t.G m ≫ F) := hF ▸ hGm
  have : IsMonHom F := GlobalTheory.DivisibleHom.isMonHom_of_factor m F
  refine ⟨F, ⟨this, fun c => ?_⟩, by rw [← hF, GlobalTheory.DivisibleHom.mulA_comp]⟩
  have := A.t.act.hom c
  have := B.t.act.hom c
  apply GlobalTheory.DivisibleHom.cancel_of_flat_surjective (ReciprocityTheory.ChartRestriction.G.Out.mulA A.t.G m)
  rw [← Category.assoc, GlobalTheory.DivisibleHom.mulA_comp, ← GlobalTheory.DivisibleHom.comp_mulA, Category.assoc, hF, hG.comm,
    ← Category.assoc, hF]

theorem gen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (n : ℕ), 0 < n →
    ∀ y : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G, y ^ n = 1 →
    y ∈ Submonoid.closure {w : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G |
      ∃ (x : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G) (f : (X.A true).t.G ⟶ X.B.t.G),
        x ^ n = 1 ∧ GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f ∧
        (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) ∧
        w = x ≫ f} := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X n hn y hy
  refine Submonoid.closure_mono ?_ (GlobalTheory.T.cm_torsion_mem_closure_generators E H hH K ρ σ₁ p X n hn y hy)
  rintro w ⟨m, x, z, hm, hx, hG, rfl⟩
  obtain ⟨F, hF, hFm⟩ := exists_linear_pow_eq E H K σ₁ (X.A true) X.B _
    (GlobalTheory.FlatCM.HomLat.isLinearHom_prod X z) m hm hG
  have := hF.isMonHom
  refine ⟨x ^ m, F, ?_, hF, ⟨m, hm, z, hFm⟩, ?_⟩
  · rw [← pow_mul, mul_comm, hx]
  · rw [← hFm, MonObj.comp_pow, MonObj.pow_comp]

end GlobalTheory.FlatCM.TorsGen

end
end

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_cmUnitaryShimura_mem_closure_linearHom_images : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (n : ℕ), 0 < n →
    ∀ y : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G, y ^ n = 1 →
    y ∈ Submonoid.closure {w : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G |
      ∃ (x : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G) (f : (X.A true).t.G ⟶ X.B.t.G),
        x ^ n = 1 ∧ GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f ∧
        (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) ∧
        w = x ≫ f} := by
  atlas_forward_decl GlobalTheory.FlatCM.TorsGen.gen
end

section
section
set_option autoImplicit false

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FlatCM.TorsKill

section Act

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O] (o : OAct O G) {T : Over S}

theorem comp_act_zero (x : T ⟶ G) : x ≫ o.act 0 = 1 := by
  have h : x ≫ o.act (0 + 0) = (x ≫ o.act 0) * (x ≫ o.act 0) := by rw [o.add, MonObj.comp_mul]
  rw [add_zero] at h
  exact mul_left_cancel (a := x ≫ o.act 0) (by rw [_root_.mul_one]; exact h.symm)

theorem comp_act_nat (x : T ⟶ G) (n : ℕ) : x ≫ o.act (n : O) = x ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, pow_zero, comp_act_zero]
  | succ n ih => rw [Nat.cast_succ, o.add, MonObj.comp_mul, ih, o.one, Category.comp_id, pow_succ]

theorem comp_act_nat_mul (x : T ⟶ G) (n : ℕ) (hx : x ^ n = 1) (r : O) : x ≫ o.act ((n : O) * r) = 1 := by
  have := o.hom r
  rw [o.mul, ← Category.assoc, comp_act_nat, hx, MonObj.one_comp]

end Act

theorem weilIs_one_left (hW : Out.WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {T : Over S}
    (k : ℕ) (y : T ⟶ P.A) (hy : y ^ k = 1) : Out.WeilIs P.A P.L k 1 y 1 := by
  obtain ⟨e, he, hu⟩ := (hW S P k T).1 1 y (one_pow k) hy
  have h2 := (hW S P k T).2.1 1 1 y e e he he
  rw [_root_.one_mul] at h2
  have h3 : e * e = e := hu _ h2
  have he1 : e = 1 := mul_left_cancel (a := e) (by rw [_root_.mul_one]; exact h3)
  rwa [he1] at he

theorem kill : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (ψ : (X.A true).t.G ⟶ X.B.t.G),
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act ψ → ∀ n : ℕ, 0 < n →
    (∀ f : (X.A true).t.G ⟶ X.B.t.G, GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
      (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) →
      ∃ r : 𝓞 E, GlobalTheory.CM.WeilEq X.B.t.PP.L f ψ (X.A true).t.PP.L ((X.A true).t.act.act ((n : 𝓞 E) * r)) (𝟙 _)
        (spMap (σ₁.comp (algebraMap (𝓞 K) K)))) →
    ∀ u : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G, u ^ n = 1 → u ≫ ψ = 1 := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X ψ hψ n hn hWe u hu
  have laws := GlobalTheory.lawsFieldsSeparately
  have hWS : Out.WeilSt := laws.2.2.2.2.2.2.2.2.2.1
  have hND : Out.WeilNondegSt := laws.2.2.2.2.2.2.2.2.2.2.1
  have hBC : Out.PolBaseChangeSt := laws.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have u1 : unitOn (1 : ℂˣ) = 1 := map_one _

  have hgen : ∀ (x : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G)
      (f : (X.A true).t.G ⟶ X.B.t.G), x ^ n = 1 → Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
      (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) →
      Out.WeilIs X.B.pol.A X.B.pol.L n (x ≫ f) (u ≫ ψ) 1 := by
    intro x f hx hf hm
    obtain ⟨r, hr⟩ := hWe f hf hm
    have h := (hr n x u 1 hn hx hu).2
    rw [u1] at h
    apply h
    rw [comp_act_nat_mul _ x n hx r, Category.comp_id]
    exact weilIs_one_left hWS (X.A true).pol n u hu
  have hall : ∀ y : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G, y ^ n = 1 →
      Out.WeilIs X.B.pol.A X.B.pol.L n (u ≫ ψ) y 1 := by
    intro y hy
    have hψn : (u ≫ ψ) ^ n = 1 := GlobalTheory.LevelRigid.pairing_tors u ψ hψ.isMonHom n hu
    suffices h : Out.WeilIs X.B.pol.A X.B.pol.L n y (u ≫ ψ) 1 by
      have := GlobalTheory.CommPairing.weilIs_symm X.B.pol.isLB h
      rwa [inv_one] at this
    have hmem := GlobalTheory.T.torsion_cmUnitaryShimura_mem_closure_linearHom_images E H hH K ρ σ₁ p X n hn y hy
    clear hy
    induction hmem using Submonoid.closure_induction with
    | mem w hw =>
      obtain ⟨x, f, hx, hf, hm, rfl⟩ := hw
      exact hgen x f hx hf hm
    | one => exact weilIs_one_left hWS X.B.pol n (u ≫ ψ) hψn
    | mul a b _ _ ha hb =>
      have := (hWS _ X.B.pol n _).2.1 a b (u ≫ ψ) 1 1 ha hb
      rwa [_root_.mul_one] at this
  exact GlobalTheory.LevelRigid.pairing_nondeg hWS hND hBC X.B.pol ℂ _ n (Nat.cast_ne_zero.2 hn.ne') (u ≫ ψ)
    (GlobalTheory.LevelRigid.pairing_tors u ψ hψ.isMonHom n hu) hall

end GlobalTheory.FlatCM.TorsKill
end
end

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearHom_kills_torsion_of_weilPairing_divisible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (ψ : (X.A true).t.G ⟶ X.B.t.G),
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act ψ → ∀ n : ℕ, 0 < n →
    (∀ f : (X.A true).t.G ⟶ X.B.t.G, GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
      (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) →
      ∃ r : 𝓞 E, GlobalTheory.CM.WeilEq X.B.t.PP.L f ψ (X.A true).t.PP.L ((X.A true).t.act.act ((n : 𝓞 E) * r)) (𝟙 _)
        (spMap (σ₁.comp (algebraMap (𝓞 K) K)))) →
    ∀ u : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G, u ^ n = 1 → u ≫ ψ = 1 := by
  atlas_forward_decl GlobalTheory.FlatCM.TorsKill.kill
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

namespace GlobalTheory.FlatCM.HomLat

section Calc

variable {S : Scheme.{0}} {X Y A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [GrpObj C] [IsCommMonObj C] {L : LB A.left} {M : LB B.left} {N : LB C.left}

theorem lamEq_symm' (hL : L.IsLB) (hM : M.IsLB) {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B}
    (h : LamEq L f₁ f₂ M g₁ g₂) : LamEq M g₁ g₂ L f₁ f₂ :=
  ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁ f₂ f₂ g₁ g₁ g₂ g₂ g₁ g₂).2.1 h).1

theorem lamEq_swap' (hL : L.IsLB) (hM : M.IsLB) {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B}
    (h : LamEq L f₁ f₂ M g₁ g₂) : LamEq L f₂ f₁ M g₂ g₁ :=
  ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁ f₂ f₂ g₁ g₁ g₂ g₂ g₁ g₂).2.1 h).2.1

theorem lamEq_trans' (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB) {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B}
    {g₂ : Y ⟶ B} {k₁ : X ⟶ C} {k₂ : Y ⟶ C} (h : LamEq L f₁ f₂ M g₁ g₂) (h' : LamEq M g₁ g₂ N k₁ k₂) :
    LamEq L f₁ f₂ N k₁ k₂ :=
  ((LamCalc.lamEq_calculus S X Y A B C L M N hL hM hN f₁ f₁ f₂ f₂ g₁ g₁ g₂ g₂ k₁ k₂).2.1 h).2.2.1 h'

theorem lamEq_pre (hL : L.IsLB) (hM : M.IsLB) {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B}
    (h : LamEq L f₁ f₂ M g₁ g₂) {X' Y' : Over S} (a : X' ⟶ X) (b : Y' ⟶ Y) :
    LamEq L (a ≫ f₁) (b ≫ f₂) M (a ≫ g₁) (b ≫ g₂) :=
  ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁ f₂ f₂ g₁ g₁ g₂ g₂ g₁ g₂).2.1 h).2.2.2.1 X' Y' a b

variable (hL : L.IsLB) (hM : M.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen) (hT' : ∃ t : LB.Gen (Theta B M), t.IsGen)
include hL hM hT hT'

theorem lamEq_mul_left' {f₁ f₁' : X ⟶ A} {f₂ : Y ⟶ A} {g₁ g₁' : X ⟶ B} {g₂ : Y ⟶ B}
    (h : LamEq L f₁ f₂ M g₁ g₂) (h' : LamEq L f₁' f₂ M g₁' g₂) : LamEq L (f₁ * f₁') f₂ M (g₁ * g₁') g₂ :=
  ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁' f₂ f₂ g₁ g₁' g₂ g₂ g₁ g₂).2.2.1 hT hT' h).1 h'

theorem lamEq_prod_left {J : Type} (s : Finset J) (f : J → (X ⟶ A)) (g : J → (X ⟶ B)) (f₂ : Y ⟶ A) (g₂ : Y ⟶ B)
    (h0 : LamEq L (1 : X ⟶ A) f₂ M (1 : X ⟶ B) g₂) (h : ∀ i ∈ s, LamEq L (f i) f₂ M (g i) g₂) :
    LamEq L (s.prod f) f₂ M (s.prod g) g₂ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM (f i) (s.prod f) f₂ f₂ (g i) (s.prod g) g₂ g₂
      (g i) g₂).2.2.1 hT hT' (h i (Finset.mem_insert_self i s))).1
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem lamEq_prod_right {J : Type} (s : Finset J) (f₁ : X ⟶ A) (g₁ : X ⟶ B) (f : J → (Y ⟶ A)) (g : J → (Y ⟶ B))
    (h0 : LamEq L f₁ (1 : Y ⟶ A) M g₁ (1 : Y ⟶ B)) (h : ∀ i ∈ s, LamEq L f₁ (f i) M g₁ (g i)) :
    LamEq L f₁ (s.prod f) M g₁ (s.prod g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁ (f i) (s.prod f) g₁ g₁ (g i) (s.prod g)
      g₁ (g i)).2.2.1 hT hT' (h i (Finset.mem_insert_self i s))).2
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Calc

section Act

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {O : Type} [CommRing O] (act : OAct O G)

theorem act_zero' : act.act 0 = 1 := by
  have h := act.add 0 0
  rw [add_zero] at h
  have := congrArg (fun u => (act.act 0)⁻¹ * u) h
  simpa using this.symm

theorem act_sum' {J : Type} (s : Finset J) (c : J → O) : act.act (s.sum c) = s.prod fun i : J => act.act (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using act_zero' act
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, act.add, ih]

end Act

theorem exists_thetaGen' (hL : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) :
    ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := by
  obtain ⟨ρ, hρ⟩ := P.rigid
  obtain ⟨⟨c⟩, -⟩ := hL.cube S P ⟨P.L, ρ, P.isLB, hρ⟩ rfl
  exact ⟨c.t, c.isGen⟩

theorem weilEq_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ → ∀ (m : ℕ), 0 < m → ∀ (z : Fin p → 𝓞 E) (f : (X.A true).t.G ⟶ X.B.t.G),
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
    f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a) →
    ∀ (x : Fin p → 𝓞 E) (r : 𝓞 E), (m : 𝓞 E) * r = ∑ a, ∑ b, z a * gP a b * (H.bar (x b) : 𝓞 E) →
    GlobalTheory.CM.WeilEq X.B.t.PP.L f (∏ b, ((X.A true).t.act.act (x b) ≫ GlobalTheory.FlatCM.phiP X b))
      (X.A true).t.PP.L ((X.A true).t.act.act r) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X gP gQ hG m hm z f hf hfm x r hr
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  haveI : IsLocallyNoetherian (Sp (𝓞 K)) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of (𝓞 K))))
  have hβ : Function.Injective (σ₁.comp (algebraMap (𝓞 K) K)) :=
    σ₁.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have lA : (X.A true).t.PP.L.IsLB := (X.A true).t.PP.isLB
  have lB : X.B.t.PP.L.IsLB := X.B.t.PP.isLB
  have tA := exists_thetaGen' hL (X.A true).pol
  have tB := exists_thetaGen' hL X.B.pol
  haveI : IsMonHom f := hf.1
  haveI hφ : ∀ a, IsMonHom (phiP X a) := fun a => (X.lin (Sum.inl a)).1
  haveI hact : ∀ s, IsMonHom ((X.A true).t.act.act s) := (X.A true).t.act.hom
  have toLam : ∀ (f₁ f₂ : (X.A true).t.G ⟶ X.B.t.G) (g₁ g₂ : (X.A true).t.G ⟶ (X.A true).t.G), IsMonHom f₁ →
      IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ →
      WeilEq X.B.t.PP.L f₁ f₂ (X.A true).t.PP.L g₁ g₂ (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
      LamEq X.B.t.PP.L f₁ f₂ (X.A true).t.PP.L g₁ g₂ := fun f₁ f₂ g₁ g₂ h₁ h₂ h₃ h₄ h =>
    (PairingFibre.lamEq_weilEq_over_ring hL (𝓞 K) (X.A true).pol (X.A true).pol X.B.pol (X.A true).pol f₁ f₂ g₁ g₂
      h₁ h₂ h₃ h₄ ℂ _).2 inferInstance hβ h

  have E1 : ∀ a b, LamEq X.B.t.PP.L ((X.A true).t.act.act (z a) ≫ phiP X a) ((X.A true).t.act.act (x b) ≫ phiP X b)
      (X.A true).t.PP.L ((X.A true).t.act.act (z a * gP a b)) ((X.A true).t.act.act (x b)) := by
    intro a b
    have := lamEq_pre lB lA (toLam _ _ _ _ (hφ a) (hφ b) (hact _) inferInstance (hG.1 a b))
      ((X.A true).t.act.act (z a)) ((X.A true).t.act.act (x b))
    rwa [← (X.A true).t.act.mul, Category.comp_id] at this

  have S1 : ∀ b, LamEq X.B.t.PP.L (f ^ m) ((X.A true).t.act.act (x b) ≫ phiP X b)
      (X.A true).t.PP.L ((X.A true).t.act.act (∑ a, z a * gP a b)) ((X.A true).t.act.act (x b)) := by
    intro b
    have h0 : LamEq X.B.t.PP.L (1 : (X.A true).t.G ⟶ X.B.t.G) ((X.A true).t.act.act (x b) ≫ phiP X b)
        (X.A true).t.PP.L (1 : (X.A true).t.G ⟶ (X.A true).t.G) ((X.A true).t.act.act (x b)) := by
      have := lamEq_pre lB lA (E1 b b) (1 : (X.A true).t.G ⟶ (X.A true).t.G) (𝟙 _)
      rwa [MonObj.one_comp, MonObj.one_comp, Category.id_comp, Category.id_comp] at this
    have := lamEq_prod_left lB lA tB tA Finset.univ (fun a => (X.A true).t.act.act (z a) ≫ phiP X a)
      (fun a => (X.A true).t.act.act (z a * gP a b)) _ _ h0 (fun a _ => E1 a b)
    rwa [← hfm, ← act_sum'] at this

  have M1 : ∀ t y : 𝓞 E, LamEq (X.A true).t.PP.L ((X.A true).t.act.act t) ((X.A true).t.act.act y)
      (X.A true).t.PP.L ((X.A true).t.act.act (t * H.bar y)) (𝟙 _) := by
    intro t y
    have h2 := lamEq_pre lA lA (lamEq_swap' lA lA (LamF.lamEq_adj (X.A true).t y)) ((X.A true).t.act.act t) (𝟙 _)
    rwa [Category.comp_id, Category.id_comp, Category.id_comp, ← (X.A true).t.act.mul] at h2
  have F2 : ∀ b, LamEq X.B.t.PP.L (f ^ m) ((X.A true).t.act.act (x b) ≫ phiP X b) (X.A true).t.PP.L (𝟙 _)
      ((X.A true).t.act.act (H.bar ((∑ a, z a * gP a b) * H.bar (x b)))) := fun b =>
    lamEq_trans' lB lA lA (lamEq_trans' lB lA lA (S1 b) (M1 _ _)) (LamF.lamEq_adj (X.A true).t _)

  obtain ⟨r', hr'⟩ := GramExists.exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP f
    (∏ b, ((X.A true).t.act.act (x b) ≫ phiP X b)) hf (isLinearHom_prod X x)
  haveI hψ : IsMonHom (∏ b, ((X.A true).t.act.act (x b) ≫ phiP X b)) := (isLinearHom_prod X x).1
  have R := toLam _ _ _ _ inferInstance hψ (hact r') inferInstance hr'
  have Rm : ∀ n : ℕ, LamEq X.B.t.PP.L (f ^ n) (∏ b, ((X.A true).t.act.act (x b) ≫ phiP X b)) (X.A true).t.PP.L
      ((X.A true).t.act.act ((n : 𝓞 E) * r')) (𝟙 _) := by
    intro n
    induction n with
    | zero =>
      have := lamEq_pre lB lA R (1 : (X.A true).t.G ⟶ (X.A true).t.G) (𝟙 _)
      rw [MonObj.one_comp, MonObj.one_comp, Category.id_comp, Category.id_comp] at this
      rwa [pow_zero, Nat.cast_zero, zero_mul, act_zero']
    | succ n ih =>
      rw [pow_succ, Nat.cast_succ, add_mul, _root_.one_mul, (X.A true).t.act.add]
      exact lamEq_mul_left' lB lA tB tA ih R
  have RmA := lamEq_trans' lB lA lA (Rm m) (LamF.lamEq_adj (X.A true).t ((m : 𝓞 E) * r'))
  have base2 : LamEq X.B.t.PP.L (f ^ m) (1 : (X.A true).t.G ⟶ X.B.t.G) (X.A true).t.PP.L (𝟙 _)
      (1 : (X.A true).t.G ⟶ (X.A true).t.G) := by
    have := lamEq_pre lB lA RmA (𝟙 _) (1 : (X.A true).t.G ⟶ (X.A true).t.G)
    rwa [MonObj.one_comp, MonObj.one_comp, Category.id_comp, Category.id_comp] at this
  have S2 := lamEq_prod_right lB lA tB tA Finset.univ (f ^ m) (𝟙 _)
    (fun b => (X.A true).t.act.act (x b) ≫ phiP X b)
    (fun b => (X.A true).t.act.act (H.bar ((∑ a, z a * gP a b) * H.bar (x b)))) base2 (fun b _ => F2 b)
  have hsum : (∑ b, H.bar ((∑ a, z a * gP a b) * H.bar (x b))) = H.bar ((m : 𝓞 E) * r) := by
    rw [hr, ← map_sum]
    congr 1
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
  rw [← act_sum', hsum] at S2

  have U := lamEq_swap' lA lA (lamEq_trans' lA lB lA (lamEq_symm' lB lA S2) RmA)
  have e₁ := PairingInj.eq_of_lamEq hL _ (X.A true).pol _ _ _ U
  have hg : 1 ≤ (X.A true).pol.g := NumInh.dim_pos_of_hasType X.split X.ρ_sq (X.A true) X.typeP
  have e₂ := H.bar.injective (LamF.Faithful.act_injective hL E K (X.A true).pol (X.A true).t.act hg e₁)
  have e₃ : r = r' := mul_left_cancel₀ (Nat.cast_ne_zero.2 hm.ne' : (m : 𝓞 E) ≠ 0) e₂
  rw [e₃]
  exact hr'

end GlobalTheory.FlatCM.HomLat

end
end

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_linearHom_span_gramForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ → ∀ (m : ℕ), 0 < m → ∀ (z : Fin p → 𝓞 E) (f : (X.A true).t.G ⟶ X.B.t.G),
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
    f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a) →
    ∀ (x : Fin p → 𝓞 E) (r : 𝓞 E), (m : 𝓞 E) * r = ∑ a, ∑ b, z a * gP a b * (H.bar (x b) : 𝓞 E) →
    GlobalTheory.CM.WeilEq X.B.t.PP.L f (∏ b, ((X.A true).t.act.act (x b) ≫ GlobalTheory.FlatCM.phiP X b))
      (X.A true).t.PP.L ((X.A true).t.act.act r) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  atlas_forward_decl GlobalTheory.FlatCM.HomLat.weilEq_gram
end

section
section
set_option autoImplicit false

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

namespace GlobalTheory.FlatCM.HomLat

theorem mem_lat_of_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
      ∀ d : Fin p → E, (∀ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b)) →
        d ∈ GlobalTheory.FlatCM.HomLat.lat X := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X gP gQ hG barE hbar d hd
  classical
  obtain ⟨y, hy0, hyi⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image d)
  have hsq : ((y.natAbs ^ 2 : ℕ) : ℤ) = y * y := by rw [Nat.cast_pow, Int.natCast_natAbs, sq_abs, sq]
  have hint : ∀ a, IsIntegral ℤ (((y.natAbs ^ 2 : ℕ) : E) * d a) := fun a => by
    have h1 := hyi (d a) (Finset.mem_image_of_mem d (Finset.mem_univ a))
    have e : ((y.natAbs ^ 2 : ℕ) : E) * d a = (algebraMap ℤ E y) * (y • d a) := by
      rw [zsmul_eq_mul, algebraMap_int_eq, eq_intCast, ← _root_.mul_assoc]
      congr 1
      rw [← Int.cast_natCast (R := E), hsq]
      try push_cast
      try ring
    rw [e]
    exact isIntegral_algebraMap.mul h1
  set n : ℕ := y.natAbs ^ 2 with hn_def
  have hn : 0 < n := pow_pos (Int.natAbs_pos.2 hy0) 2
  let x : Fin p → 𝓞 E := fun a => ⟨(n : E) * d a, hint a⟩
  have hx : ∀ a, (x a : E) = n * d a := fun a => rfl
  have hψ := GlobalTheory.FlatCM.HomLat.isLinearHom_prod X x
  have hk := GlobalTheory.T.linearHom_kills_torsion_of_weilPairing_divisible E H hH K ρ σ₁ p X _ hψ n hn (fun f hf ⟨m, hm, z, hfz⟩ => by
    have hm' : (m : E) ≠ 0 := by exact_mod_cast hm.ne'
    have hc : (fun a => (z a : E) / m) ∈ GlobalTheory.FlatCM.HomLat.lat X := Submodule.subset_span
      ⟨m, hm, z, fun a => by field_simp, f, hf, hfz⟩
    obtain ⟨w, hw⟩ := hd _ hc
    refine ⟨w, GlobalTheory.T.weilPairing_linearHom_span_gramForm E H hH K ρ σ₁ p X gP gQ hG m hm z f hf hfz x _ ?_⟩
    have hb : ∀ b, ((H.bar (x b) : 𝓞 E) : E) = n * barE (d b) := fun b => by
      rw [← hbar, hx, map_mul, map_natCast]
    have key : (m : E) * ((n : E) * (w : E)) =
        ∑ a, ∑ b, (z a : E) * (gP a b : E) * ((H.bar (x b) : 𝓞 E) : E) := by
      simp_rw [hb]
      rw [hw]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      field_simp
    apply RingOfIntegers.coe_injective
    push_cast
    exact key)
  obtain ⟨χ, hχ, hχn⟩ := GlobalTheory.T.exists_linearHom_pow_eq_of_kills_complex_torsion E H K σ₁ (X.A true) X.B _ hψ n hn hk
  exact Submodule.subset_span ⟨n, hn, x, hx, χ, hχ, hχn⟩

end GlobalTheory.FlatCM.HomLat
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_cmCoordinateLattice_of_integral_gramPairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
      ∀ d : Fin p → E, (∀ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b)) →
        d ∈ GlobalTheory.FlatCM.HomLat.lat X := by
  atlas_forward_decl GlobalTheory.FlatCM.HomLat.mem_lat_of_dual
end
