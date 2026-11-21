import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGenericGerm
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsHeightOneSections
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PHeightOneIntersection
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PBundlesAgree
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PVectorBundleRestrict

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace HeightOneSections

variable {X : Scheme.{0}} [IsIntegral X]

lemma genericPoint_mem {U : X.Opens} {x : X} (hx : x ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩

omit [IsIntegral X] in

lemma fromSpec_mem {V : X.Opens} (hV : IsAffineOpen V) (p : PrimeSpectrum Γ(X, V)) :
    hV.fromSpec p ∈ V := by
  have h : hV.fromSpec p ∈ Set.range hV.fromSpec := ⟨p, rfl⟩
  rwa [hV.range_fromSpec] at h

lemma isIntegrallyClosed_of_isAffineOpen (hN : IsNormalScheme X) {V : X.Opens}
    (hV : IsAffineOpen V) [Nonempty V] : IsIntegrallyClosed Γ(X, V) := by
  refine IsIntegrallyClosed.of_localization_maximal fun P _ hP => ?_
  have hy := fromSpec_mem hV ⟨P, hP.isPrime⟩
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf
    (⟨hV.fromSpec ⟨P, hP.isPrime⟩, hy⟩ : V)
  have : IsLocalization.AtPrime (X.presheaf.stalk (hV.fromSpec ⟨P, hP.isPrime⟩)) P :=
    hV.isLocalization_stalk' ⟨P, hP.isPrime⟩ hy
  have := hN (hV.fromSpec ⟨P, hP.isPrime⟩)
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv P.primeCompl (X.presheaf.stalk (hV.fromSpec ⟨P, hP.isPrime⟩))
      (Localization.AtPrime P)).toRingEquiv

def comb (E : X.Modules) {V : X.Opens} {n : ℕ} (s : Fin n → Γ(E, V)) (W : X.Opens) (h : W ≤ V)
    (r : Fin n → Γ(X, W)) : Γ(E, W) :=
  ∑ i, r i • (E.presheaf.map (homOfLE h).op).hom (s i)

omit [IsIntegral X] in

lemma germ_comb (E : X.Modules) {V : X.Opens} {n : ℕ} (s : Fin n → Γ(E, V)) (W : X.Opens)
    (h : W ≤ V) (r : Fin n → Γ(X, W)) (x : X) (hx : x ∈ W) :
    E.presheaf.germ W x hx (comb E s W h r) =
      ∑ i, X.presheaf.germ W x hx (r i) • E.presheaf.germ V x (h hx) (s i) := by
  rw [comb, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [BundlesAgree.germ_smul']
  congr 1
  exact TopCat.Presheaf.germ_res_apply E.presheaf (homOfLE h) x hx (s i)

omit [IsIntegral X] in

lemma comb_res (E : X.Modules) {V : X.Opens} {n : ℕ} (s : Fin n → Γ(E, V)) (W W' : X.Opens)
    (h : W ≤ V) (h' : W' ≤ W) (r : Fin n → Γ(X, W)) :
    E.presheaf.map (homOfLE h').op (comb E s W h r) =
      comb E s W' (h'.trans h) (fun i => X.presheaf.map (homOfLE h').op (r i)) := by
  rw [comb, comb, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.map_smul]
  congr 1
  show (E.presheaf.map (homOfLE h).op ≫ E.presheaf.map (homOfLE h').op) (s i) = _
  rw [← Functor.map_comp]
  rfl

omit [IsIntegral X] in

lemma germ_coeff_unique (E : X.Modules) {V : X.Opens} {n : ℕ} {s : Fin n → Γ(E, V)}
    (hs : IsBasisOn E V s) (x : X) (hxV : x ∈ V) {W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ V)
    (hx : x ∈ W) (hx' : x ∈ W') (r : Fin n → Γ(X, W)) (r' : Fin n → Γ(X, W'))
    (e : ∑ i, X.presheaf.germ W x hx (r i) • E.presheaf.germ V x hxV (s i) =
      ∑ i, X.presheaf.germ W' x hx' (r' i) • E.presheaf.germ V x hxV (s i)) (i : Fin n) :
    X.presheaf.germ W x hx (r i) = X.presheaf.germ W' x hx' (r' i) := by
  rw [← germ_comb E s W h r x hx, ← germ_comb E s W' h' r' x hx'] at e
  obtain ⟨W'', hx'', iU, iV, e'⟩ := E.presheaf.germ_eq x hx hx' _ _ e
  have hU : iU = homOfLE iU.le := rfl
  have hV : iV = homOfLE iV.le := rfl
  rw [hU, hV, comb_res, comb_res] at e'
  have := (hs W'' (iU.le.trans h)).1 e'
  have hi := congrFun this i
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf iU x hx'' (r i),
    ← TopCat.Presheaf.germ_res_apply X.presheaf iV x hx'' (r' i)]
  exact congrArg (X.presheaf.germ W'' x hx'') hi

theorem exists_section_of_isBasisOn (hHOI : HeightOneIntersection.Statement)
    [IsLocallyNoetherian X] (hN : IsNormalScheme X) (E : X.Modules) {V : X.Opens}
    (hV : IsAffineOpen V) (hη : genericPoint X ∈ V) {n : ℕ} {s : Fin n → Γ(E, V)}
    (hs : IsBasisOn E V s) (v : E.presheaf.stalk (genericPoint X))
    (hv : ∀ y : X, y ∈ V → ringKrullDim (X.presheaf.stalk y) = 1 → v ∈ genericImage E y) :
    ∃ σ : Γ(E, V), E.presheaf.germ V (genericPoint X) hη σ = v := by
  have : Nonempty V := ⟨⟨genericPoint X, hη⟩⟩
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have := isIntegrallyClosed_of_isAffineOpen hN hV
  have := functionField_isFractionRing_of_isAffineOpen X V hV

  obtain ⟨W0, hW0, t0, ht0⟩ := E.presheaf.exists_germ_eq v
  have hW1 : genericPoint X ∈ W0 ⊓ V := ⟨hW0, hη⟩
  obtain ⟨r, hr⟩ := (hs (W0 ⊓ V) inf_le_right).2
    ((E.presheaf.map (homOfLE (inf_le_left : W0 ⊓ V ≤ W0)).op).hom t0)
  have hvc : v = ∑ i, X.presheaf.germ (W0 ⊓ V) _ hW1 (r i) •
      E.presheaf.germ V (genericPoint X) hη (s i) := by
    rw [← germ_comb E s (W0 ⊓ V) inf_le_right r _ hW1]
    change v = E.presheaf.germ (W0 ⊓ V) _ hW1 (comb E s (W0 ⊓ V) inf_le_right r)
    rw [show comb E s (W0 ⊓ V) inf_le_right r = _ from hr, ← ht0]
    exact (TopCat.Presheaf.germ_res_apply E.presheaf _ _ hW1 t0).symm

  have hmem : ∀ i, X.presheaf.germ (W0 ⊓ V) _ hW1 (r i) ∈
      Subalgebra.toSubmodule (⊥ : Subalgebra Γ(X, V) X.functionField) := by
    intro i
    rw [hHOI Γ(X, V) X.functionField, Submodule.mem_iInf]
    intro p
    rw [Submodule.mem_iInf]
    intro hp1
    have hy := fromSpec_mem hV p
    let y := hV.fromSpec p
    let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hy⟩ : V)
    have hloc : IsLocalization.AtPrime (X.presheaf.stalk y) p.asIdeal :=
      hV.isLocalization_stalk' p hy
    have hdim : ringKrullDim (X.presheaf.stalk y) = 1 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal, hp1]
      rfl
    obtain ⟨w, hw⟩ := hv y hy hdim
    obtain ⟨W2, hW2, t, rfl⟩ := E.presheaf.exists_germ_eq w
    have hη3 : genericPoint X ∈ W2 ⊓ V := genericPoint_mem (show y ∈ W2 ⊓ V from ⟨hW2, hy⟩)
    obtain ⟨r', hr'⟩ := (hs (W2 ⊓ V) inf_le_right).2
      ((E.presheaf.map (homOfLE (inf_le_left : W2 ⊓ V ≤ W2)).op).hom t)
    have hvc' : v = ∑ i, X.presheaf.germ (W2 ⊓ V) _ hη3 (r' i) •
        E.presheaf.germ V (genericPoint X) hη (s i) := by
      rw [← germ_comb E s (W2 ⊓ V) inf_le_right r' _ hη3]
      change v = E.presheaf.germ (W2 ⊓ V) _ hη3 (comb E s (W2 ⊓ V) inf_le_right r')
      rw [show comb E s (W2 ⊓ V) inf_le_right r' = _ from hr', ← hw]
      rw [TopCat.Presheaf.germ_res_apply]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply E.presheaf hW2
        (genericPoint_specializes y) t
    have hc := germ_coeff_unique E hs _ hη inf_le_right inf_le_right hW1 hη3 r r'
      (hvc.symm.trans hvc') i
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj p.asIdeal.primeCompl
      (X.presheaf.germ (W2 ⊓ V) y ⟨hW2, hy⟩ (r' i))
    refine ⟨b, b.2, Algebra.mem_bot.mpr ⟨a, ?_⟩⟩
    have hab' := congrArg (X.presheaf.stalkSpecializes (genericPoint_specializes y)) hab
    rw [map_mul] at hab'
    have h1 : X.presheaf.stalkSpecializes (genericPoint_specializes y)
        (X.presheaf.germ (W2 ⊓ V) y ⟨hW2, hy⟩ (r' i)) = X.presheaf.germ (W2 ⊓ V) _ hη3 (r' i) :=
      TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    have h2 : ∀ c : Γ(X, V), X.presheaf.stalkSpecializes (genericPoint_specializes y)
        (algebraMap Γ(X, V) (X.presheaf.stalk y) c) = algebraMap Γ(X, V) X.functionField c :=
      fun c => TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    rw [h1, h2, h2, ← hc] at hab'
    rw [Algebra.smul_def, ← hab', mul_comm]
  choose a ha using fun i => Algebra.mem_bot.mp (hmem i)
  refine ⟨∑ i, a i • s i, ?_⟩
  rw [map_sum, hvc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [BundlesAgree.germ_smul', ← ha i]
  rfl

end HeightOneSections

end

end GroundTheory.Heights₂.Heights.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem HeightOneSections.proof (h₁ : GenericGermInjective.Statement) :
    HeightOneSections.Statement := by
  intro X _ _ hN E hE U hU v hv
  have inj := h₁ X E hE

  have loc : ∀ x : U, ∃ (V : X.Opens) (_ : V ≤ U) (_ : (x : X) ∈ V) (σ : Γ(E, V)),
      ∀ hη : genericPoint X ∈ V, E.presheaf.germ V _ hη σ = v := by
    rintro ⟨x, hx⟩
    obtain ⟨W, -, hxW, n, s, hs⟩ := hE x
    obtain ⟨V, hVa, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ W ⊓ U from ⟨hxW, hx⟩)
    have hη := HeightOneSections.genericPoint_mem hxV
    obtain ⟨σ, hσ⟩ := HeightOneSections.exists_section_of_isBasisOn HeightOneIntersection.proof
      hN E hVa hη (hs.restrict (hVle.trans inf_le_left)) v
      (fun y hy hy1 => hv y (hVle hy).2 hy1)
    exact ⟨V, hVle.trans inf_le_right, hxV, σ, fun _ => hσ⟩
  choose V hVU hxV σ hσ using loc

  have hcomp : TopCat.Presheaf.IsCompatible E.presheaf V σ := by
    intro i j
    refine BundlesAgree.section_ext E inj fun hη => ?_
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hσ, hσ]
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨E.presheaf, E.isSheaf⟩ V U
    (fun x => homOfLE (hVU x)) (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩) σ hcomp
  refine ⟨t, ?_⟩
  let x : U := ⟨genericPoint X, hU⟩
  have hη := HeightOneSections.genericPoint_mem (hxV x)
  have hx : E.presheaf.map (homOfLE (hVU x)).op t = σ x := ht x
  rw [← hσ x hη, ← hx, TopCat.Presheaf.germ_res_apply]

end GroundTheory.Heights₂.Heights.Model
end
