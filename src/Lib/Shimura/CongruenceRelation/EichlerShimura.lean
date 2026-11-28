module

public import Aesop.BuiltinRules
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Lib.Cohomology.Etale.EllAdicCohomology
public import Lib.General.Geometry.EtaleCharts
import Lib.Cohomology.Etale.DenseSubfunctors
import Lib.Cohomology.SmoothBaseChange
import Lib.General.Geometry.PointsOfProperSchemes

/-!
# The congruence relation and the trivial action of inertia on ℓ-adic cohomology

The Eichler–Shimura argument: a relation between Frobenius twists of points in characteristic p
gives a relation between pull-backs and Galois action on ℓ-adic cohomology.

* `New.Variety.ellAdicCohom.ellAdicPull_frobEnd`: the absolute Frobenius acts trivially on
  cohomology.
* `New.Variety.ellAdicCohom.congruence_relation`: the congruence relation
  `New.Variety.CongruenceRelation` on points gives ∑ mᵢ uᵢ^* g^(−eᵢ) = 0 on Vⁿ(Y), for a Frobenius
  element g.
* `New.Variety.ellAdicCohom.galoisAction_eq_one_of_inertia`: inertia acts trivially (the case q = 1
  of the relation).

The idea: extend classes from Ω to the valuation ring A, then restrict to the special fibre.
`New.Variety.ellAdicCohom` is X ↦ Vⁿ(X) = ℚ_ℓ ⊗ Hⁿ(X_Ω, ℤ_ℓ), with the action
`New.Variety.ellAdicCohom.galoisAction` of Γ; `New.Variety.ellAdicPull` is the pull-back along a map
of free abelian functors (`freeAb` sends a functor to its pointwise free abelian group);
`New.Variety.IsCharted` is the hypothesis on Y that stands in for smoothness: it gives smooth base
change, so that pull-back from A to Ω is bijective on the cohomology of Y.

Notions from other files:
* `New.IsFrob`: σ stabilises the valuation subring A and σx ≡ x^q modulo the maximal ideal for all x
  in A; for q = 1 this is membership in the inertia group.
* `New.Variety.mapOnTests`: For a map u: X → Y of set-valued functors on rings, its restriction to a
  map of functors on test rings.
* `New.Variety.ellAdicCoeff`: The coefficient `ℤ_ℓ`: a test ring `A` goes to the Witt vectors of the
  ring of locally constant functions `Spec A → 𝔽_ℓ`.

## Relation to the literature

Known result: Smooth proper reduction gives unramified ℓ-adic cohomology, and Frobenius relations
pass to it. Here the base is the valuation ring of a place. Source: Stacks project, Tags 0GKD (SGA4
XVI 2.2) and 03SN (SGA5 XV); Deligne, Formes modulaires et représentations ℓ-adiques, Sém. Bourbaki
355 (1969).
-/

@[expose] public section

namespace New.Variety.ellAdicCohom

open CategoryTheory AlgebraicGeometry CommRingCat ellAdicPull Comparison

variable {ℓ : ℕ} [ThePrime ℓ]
  {R : CommRingCat} [Algebra R Ω]
  {Γ : Type*} [Group Γ] [MulSemiringAction Γ Ω] [SMulCommClass Γ R Ω]
  {A : ClosurePlace} (hR : ∀ r : R, algebraMap R Ω r ∈ A) (hℓ : IsUnit (ℓ : A))
  {W Y : Over (Spec R)} [IsCharted Y R] [IsProper Y.hom]
  {n p f : ℕ} [Fact p.Prime] (hp : A.valuation p < 1)
  {U : PointFunctor} (hU_char : ∀ B : CommRingCat, U B → (p : B) = 0) (j : ℕ)

/-- For a functor U on rings with points only in rings where p = 0, the endomorphism sending x
in U(B) to its image under b ↦ b^(p^j). -/
def frobEnd : U ⟶ U where
  app B := ↾fun x ↦ U.map (ofHom (frobPow (hU_char B x) j)) x
  naturality X Y f := by
    ext x
    change U.map (ofHom (frobPow (hU_char Y (U.map f x)) j)) (U.map f x) =
      U.map f (U.map (ofHom (frobPow (hU_char X x) j)) x)
    rw [← U.map_comp_apply, ← U.map_comp_apply]
    have h_hom : f ≫ ofHom (frobPow (hU_char Y (U.map f x)) j) =
        ofHom (frobPow (hU_char X x) j) ≫ f :=
      CommRingCat.hom_ext <| RingHom.ext fun b ↦ (map_pow f.hom b (p ^ j)).symm
    rw [h_hom]

/-- The absolute Frobenius acts trivially on ℓ-adic cohomology. Let p = 0 in every ring B in which
U has a point (`hU_char`). Then the endomorphism `New.Variety.ellAdicCohom.frobEnd` of U, which
moves a point x ∈ U(B) along the ring map b ↦ b^(p^j) of B, pulls back to the identity of
ℚ_ℓ ⊗ Hⁿ(U, ℤ_ℓ). -/
lemma ellAdicPull_frobEnd (hU_char : ∀ B : CommRingCat, U B → (p : B) = 0) (j : ℕ) :
    ellAdicPull n (freeAb.map (mapOnTests (frobEnd hU_char j))) = 1 := by
  ext x
  refine congrArg (1 ⊗ₜ ·) ?_
  -- Frobenius as an endomorphism `η` of the functor `(A, x) ↦ A` on the category of points of `U`
  let η : elementsProj (testIncl ⋙ U) ⟶ elementsProj (testIncl ⋙ U) :=
    { app A := ⟨ofHom (frobPow (hU_char _ A.val) j)⟩
      naturality _ _ _ := by
        ext
        exact (map_pow ..).symm }
  -- it acts trivially on the coefficients, since it fixes every prime ideal
  have h_coef : Functor.whiskerRight η (ellAdicCoeff (ℓ := ℓ)) ≫ 𝟙 _ = 𝟙 _ := by
    ext A ⟨⟨y⟩⟩
    -- the coefficients at `A` are functions on `Spec A`, moved along `comap` of `η`
    congrm ⟨WittVector.mk _ fun i ↦ ⟨_ ∘ ?_, _⟩⟩
    change PrimeSpectrum.comap (Hom.hom (testIncl.map (η.app A))) = fun q ↦ q
    ext q
    simp [η, q.isPrime.pow_mem_iff_mem, NeZero.pos]
  -- pulling back to the category of points along the tautological point is injective
  refine (hasUniversalPoints_elements.isBijective n).injective ?_
  -- `frobEnd` moves the tautological point as `η` does
  have h_square : 𝟙 (freeAb.obj (onePointFunctor (testIncl ⋙ U).Elements)) ≫
      freeAbMap tautologicalSection ≫ Functor.whiskerRight η (freeAb.obj (testIncl ⋙ U)) =
        freeAbMap tautologicalSection ≫ (restrict (elementsProj (testIncl ⋙ U))
          ellAdicCoeff).functor.whiskerLeft (freeAb.map (mapOnTests (frobEnd hU_char j))) :=
    rfl
  calc
    _ = (Comparison.restrict (elementsProj _) ellAdicCoeff).pull
      (freeAbMap tautologicalSection ≫ Functor.whiskerRight η _) n x :=
      (map_pull_eq_pull_map h_square n x).symm.trans (H.map_id _)
    -- `η` can be moved from the point to the coefficients, where it is trivial
    _ = pull ⟨_, Functor.whiskerRight η ellAdicCoeff ≫ 𝟙 _⟩ (freeAbMap tautologicalSection) n x :=
      (DFunLike.congr_fun (pull_whiskerRight η ..) x).symm
    _ = _ := congrArg (fun c ↦ pull ⟨_, c⟩ (freeAbMap tautologicalSection) n x) h_coef

/-- Precomposing with the absolute Frobenius does not change pull-backs: for a map φ out of U,
pull-back along `New.Variety.ellAdicCohom.frobEnd` followed by φ is pull-back along φ. -/
lemma ellAdicPull_frobEnd_comp {X : PointFunctor} (φ : U ⟶ X) :
    ellAdicPull (ℓ := ℓ) n (freeAb.map (mapOnTests (frobEnd hU_char j ≫ φ))) =
      ellAdicPull n (freeAb.map (mapOnTests φ)) := by
  have h_map : freeAb.map (mapOnTests (frobEnd hU_char j ≫ φ)) =
      freeAb.map (mapOnTests (frobEnd hU_char j)) ≫ freeAb.map (mapOnTests φ) := by
    dsimp only [mapOnTests]
    rw [Functor.whiskerLeft_comp, freeAb.map_comp]
  refine LinearMap.ext fun x ↦ ?_
  rw [h_map, ← comp, ellAdicPull_frobEnd, one_apply_eq_self]

/-- Let Z be proper over a ring (`hs`), and let Fᵢ : V → Z be maps of functors on rings whose values
at every geometric point z of V cancel with multiplicities mᵢ (`New.Variety.Cancels`). Then
∑ mᵢ Fᵢ^* = 0 on ℓ-adic cohomology. -/
private lemma ellAdicPull_sum_eq_zero_of_cancels {V Z : PointFunctor} {D : CommRingCat}
    {s : Z ⟶ reprBy D} (hs : IsProperOver s) {I : Type} [Fintype I] (m : I → ℤ)
    (F : I → (V ⟶ Z))
    (h_cancel : ∀ (k : Type) [Field k] [IsAlgClosed k] (z : V.obj (of k)),
      Cancels m fun i ↦ (F i).app (of k) z) :
    ellAdicPull (ℓ := ℓ) n (∑ i, m i • freeAb.map (mapOnTests (F i))) = 0 := by
  -- the sum vanishes on the locus where the points `F i x` cancel; it is enough that this locus
  -- is dense
  suffices h_dense : IsCohomDense (locConstCoeff ⟨ZMod ℓ⟩)
      (relationLocus m fun i ↦ mapOnTests (F i)) by
    refine LinearMap.ext fun y ↦
      h_dense.isCohomEquiv.bijective_ellAdicPull.injective ((comp ..).trans ?_)
    simp [relationLocus_sum_eq_zero]
  -- by properness it is enough to treat points `x` at which the `F i` coincide whenever they do
  -- at some geometric point `z` (`h_coinc`)
  exact hs.isCohomDense_of_coincidences F fun z _ _ h_coinc ↦
    (h_cancel _ z).mono fun i i' h_eq ↦ h_coinc i i' h_eq

/-- Let g be a Frobenius element for q at A. Then g⁻¹ lifts the inverse of the q-th power map of
the residue field: every x in A is congruent to (g⁻¹ x)^q modulo the maximal ideal. -/
lemma valuation_sub_inv_smul_pow_lt_one {q : ℕ} {g : Γ} (hg : IsFrob A q g) {x : Ω}
    (hx : A.valuation x ≤ 1) : A.valuation (x - (g⁻¹ • x) ^ q) < 1 := by
  have h_mem : g⁻¹ • x ∈ A :=
    (mem_decompGroup_iff.mp (inv_mem hg.mem_decompGroup) x).mpr ((A.valuation_le_one_iff x).mp hx)
  simpa using hg.valuation_sub_pow_lt_one ((A.valuation_le_one_iff _).mpr h_mem)

omit [Algebra R Ω] [IsCharted Y R] [IsProper Y.hom] in
/-- For u : W → Y and a ring endomorphism σ of an R-algebra S that fixes the image of R (`hσ`), the
map (w, ω) ↦ (u w, ω ∘ σ) from the points of W ×_R S to those of Y ×_R S. -/
noncomputable def twistedMap {S : Type} [CommRing S] [Algebra R S] (u : W ⟶ Y) (σ : S →+* S)
    (hσ : ofHom (algebraMap R S) ≫ ofHom σ = ofHom (algebraMap R S)) :
    geomPoints R S W ⟶ geomPoints R S Y :=
  (geomPoints R S).map u ≫ baseChangeTransition _ (ofHom σ) hσ

omit [Algebra R Ω] [IsCharted Y R] in
include hℓ hp in
/-- The congruence relation over A. Let A ⊂ Ω be a valuation ring and an R-algebra, with p in its
maximal ideal (`hp`) and ℓ a unit (`hℓ`), let W, Y be proper over R, and let σᵢ be ring
endomorphisms of A over R (`hσ_alg`) lifting the inverse of the p^(aᵢ)-th power map of the residue
field (`hσ_frob`). If uᵢ : W → Y satisfy ∑ mᵢ [Frob_(p^aᵢ) uᵢ(w)] = 0 at the field points w of W
of characteristic p killing the preimage in R of A's maximal ideal
(`New.Variety.CongruenceRelation`), then ∑ mᵢ μᵢ^* y = 0 for every class y of Y over A, where μᵢ
(`New.Variety.ellAdicCohom.twistedMap`) sends a point (w, ω) of W over A to (uᵢ w, ω ∘ σᵢ). -/
lemma sum_ellAdicPull_eq_zero_of_congruenceRelation [Algebra R A] [IsProper W.hom] {I : Type}
    [Fintype I] (u : I → (W ⟶ Y)) (a : I → ℕ) (m : I → ℤ)
    (h_cong : CongruenceRelation m (algebraMap R A ⁻¹' {b | A.valuation b < 1}) p a u)
    (σ : I → A →+* A)
    (hσ_alg : ∀ i, ofHom (algebraMap R A) ≫ ofHom (σ i) = ofHom (algebraMap R A))
    (hσ_frob : ∀ i (b : A), A.valuation ((b : Ω) - (σ i b : Ω) ^ p ^ a i) < 1)
    (y : TensorProduct ℤ_[ℓ] ℚ_[ℓ] (H (freeAb.obj (testIncl ⋙ geomPoints R A Y)) ellAdicCoeff n)) :
    ∑ i, m i • ellAdicPull n (freeAb.map (mapOnTests (twistedMap (u i) (σ i) (hσ_alg i)))) y =
      0 := by
  -- Restrict to the special fibre `U₀`, where `σ i` is undone by Frobenius, and use the relation
  -- at geometric points of `U₀`.
  -- the special fibre: the points that kill the maximal ideal of `A`; they have characteristic `p`
  let s₀ : geomPoints R A W ⟶ reprBy (of A) :=
    fiberProd.snd (pointsToBase W.hom) (reprMap (ofHom (algebraMap R A)))
  let U₀ : Subfunctor (geomPoints R A W) := zeroPoints s₀ {b | A.valuation b < 1}
  have h_char (B : CommRingCat) (x : U₀.toFunctor.obj B) : (p : B) = 0 := by
    simpa using x.property p hp
  -- restriction to `U₀` is injective by proper base change
  have h_res : IsCohomEquiv (locConstCoeff ⟨ZMod ℓ⟩) (freeAb.map (mapOnTests U₀.ι)) := by
    have h_max : (IsLocalRing.maximalIdeal A : Set A) = {b : A | A.valuation b < 1} :=
      Set.ext A.valuation_lt_one_iff
    unfold U₀
    rw [← h_max]
    exact ((isProperOver_pointsToBase _).baseChange _).proper_base_change hℓ
  refine h_res.bijective_ellAdicPull.injective ?_
  -- `F i` is `μ i` after the Frobenius of exponent `p ^ a i` on `U₀`, which acts trivially
  let F (i : I) : U₀.toFunctor ⟶ geomPoints R A Y :=
    frobEnd h_char (a i) ≫ U₀.ι ≫ twistedMap (u i) (σ i) (hσ_alg i)
  trans ellAdicPull n (∑ i, m i • freeAb.map (mapOnTests (F i))) y
  · let pullU := ellAdicPull (ℓ := ℓ) n (freeAb.map (mapOnTests U₀.ι))
    rw [map_sum pullU, map_sum (ellAdicPull n), LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_zsmul pullU, map_zsmul (ellAdicPull n), LinearMap.smul_apply]
    refine congrArg (m i • ·) ?_
    rw [show F i = frobEnd h_char (a i) ≫ U₀.ι ≫ twistedMap (u i) (σ i) (hσ_alg i) from rfl,
      ellAdicPull_frobEnd_comp, comp, ← freeAb.map_comp]
    rfl
  · -- by properness, the sum vanishes if the points `F i z` cancel at every geometric point `z`
    refine (LinearMap.congr_fun (ellAdicPull_sum_eq_zero_of_cancels
      ((isProperOver_pointsToBase _).baseChange _) m F fun k _ _ z ↦ ?_) y).trans (map_zero _).symm
    -- at `z = (w, ω)`, with `w` the `W`-component `z.val.val.fst`: `ω b = ω (σ i b) ^ p ^ a i`, as
    -- `σ i` lifts the inverse of the Frobenius
    let ω : of A ⟶ of k := baseRingMap s₀ z.val
    have h_frob (i : I) (b : A) : ω b = ω (σ i b) ^ p ^ a i := by
      have h_zero : ω (b - σ i b ^ p ^ a i) = 0 := z.property _ (hσ_frob i b)
      rwa [map_sub, map_pow, sub_eq_zero] at h_zero
    -- so `F i z = (Frob (u i w), ω)`, and these points cancel by the congruence relation
    have hk_char : CharP k p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr (h_char _ z)
    have h_cancel : Cancels m fun i ↦
        Spec.map (ofHom (iterateFrobenius k p (a i))) ≫ z.val.val.fst.down ≫ (u i).left :=
      h_cong k _ fun r hr ↦
        (congrArg (fun t ↦ t.down.hom r) z.val.property).trans (z.property _ hr)
    refine h_cancel.mono fun i i' hij ↦ baseChangeOf.ext (congrArg ULift.up hij) fun b ↦ ?_
    -- the ring map of `F i z` is `ω ∘ σ i` followed by the Frobenius of exponent `p ^ a i`
    change ω (σ i b) ^ p ^ a i = ω (σ i' b) ^ p ^ a i'
    rw [← h_frob i, ← h_frob i']

/-- Pull-back from A to Ω. For a subring A ⊂ Ω that is an R-algebra compatibly with Ω (`h_alg`),
the map ℚ_ℓ ⊗ Hⁿ(X ×_R A, ℤ_ℓ) → Vⁿ(X) = ℚ_ℓ ⊗ Hⁿ(X ×_R Ω, ℤ_ℓ) given by pull-back along the map
of points (x, ω) ↦ (x, ω restricted to A). -/
noncomputable def baseChangePull [Algebra R A]
    (h_alg : ofHom (algebraMap R A) ≫ ofHom A.subtype = ofHom (algebraMap R Ω))
    (X : Over (Spec R)) :
    TensorProduct ℤ_[ℓ] ℚ_[ℓ]
        (H (freeAb.obj (testIncl ⋙ geomPoints R A X)) ellAdicCoeff n) →ₗ[ℚ_[ℓ]]
      (ellAdicCohom R Ω n).obj (Opposite.op X) :=
  ellAdicPull n (freeAb.map (mapOnTests (X := geomPoints R Ω X) (Y := geomPoints R A X)
    (baseChangeTransition (pointsToBase X.hom) (ofHom A.subtype) h_alg)))

omit [IsCharted Y R] [IsProper Y.hom] in
/-- Let A ⊂ Ω be a subring that is an R-algebra compatibly with Ω (`h_alg`), let γ ∈ Γ, and let σ be
a ring endomorphism of A over R (`hσ_alg`) that is γ on A (`hσ`). For u : W → Y and a class y of Y
over A, u^* γ maps the pull-back of y to Ω (`New.Variety.ellAdicCohom.baseChangePull`) to the
pull-back to Ω of the pull-back of y along (w, ω) ↦ (u w, ω ∘ σ)
(`New.Variety.ellAdicCohom.twistedMap`). -/
lemma map_galoisAction_baseChangePull [Algebra R A]
    (h_alg : ofHom (algebraMap R A) ≫ ofHom A.subtype = ofHom (algebraMap R Ω)) (u : W ⟶ Y)
    {γ : Γ} {σ : A →+* A} (hσ : ∀ a, (σ a : Ω) = γ • (a : Ω))
    (hσ_alg : ofHom (algebraMap R A) ≫ ofHom σ = ofHom (algebraMap R A))
    (y : TensorProduct ℤ_[ℓ] ℚ_[ℓ] (H (freeAb.obj (testIncl ⋙ geomPoints R A Y)) ellAdicCoeff n)) :
    (ellAdicCohom R Ω n).map u.op (galoisAction R Ω Γ Y n γ (baseChangePull h_alg Y y)) =
      baseChangePull h_alg W
        (ellAdicPull n (freeAb.map (mapOnTests (twistedMap u σ hσ_alg))) y) := by
  -- both sides are pull-backs along a composite, and the two composites are the same map
  let toA_W : testIncl ⋙ geomPoints R Ω W ⟶ testIncl ⋙ geomPoints R A W :=
    mapOnTests (X := geomPoints R Ω W) (Y := geomPoints R A W)
      (baseChangeTransition (pointsToBase W.hom) (ofHom A.subtype) h_alg)
  let toA_Y : testIncl ⋙ geomPoints R Ω Y ⟶ testIncl ⋙ geomPoints R A Y :=
    mapOnTests (X := geomPoints R Ω Y) (Y := geomPoints R A Y)
      (baseChangeTransition (pointsToBase Y.hom) (ofHom A.subtype) h_alg)
  let g_aut := MulSemiringAction.toAlgAut Γ R Ω γ
  let fm := mapOnTests ((geomPoints R Ω).map u)
  let tr := mapOnTests (X := geomPoints R Ω Y) (Y := geomPoints R Ω Y)
    (baseChangeTransition (pointsToBase Y.hom) (ofHom g_aut) (by ext r; exact g_aut.commutes r))
  have h_eq : (fm ≫ tr) ≫ toA_Y = toA_W ≫ mapOnTests (twistedMap u σ hσ_alg) := by
    ext B z
    exact baseChangeOf.ext rfl fun a ↦ congrArg z.val.2.down.hom (hσ a).symm
  have h_pull : ellAdicPull n (freeAb.map fm) (ellAdicPull n (freeAb.map tr)
      (ellAdicPull n (freeAb.map toA_Y) y)) =
        ellAdicPull n (freeAb.map toA_W)
          (ellAdicPull n (freeAb.map (mapOnTests (twistedMap u σ hσ_alg))) y) := by
    rw [comp, ← freeAb.map_comp, comp, ← freeAb.map_comp, h_eq, freeAb.map_comp, ← comp]
  exact h_pull

include hR hℓ hp

/-- The Eichler–Shimura relation. Let A ⊂ Ω (an algebraic closure of ℚ) be a valuation ring
containing the image of R (`hR`), with p in its maximal ideal (`hp`) and ℓ a unit (`hℓ`); let Γ act
on Ω by R-algebra automorphisms, and let g ∈ Γ be a Frobenius for p^f at A, i.e. g stabilises A and
acts as x ↦ x^(p^f) modulo its maximal ideal. Let W, Y be proper over R with Y charted over R
(`New.Variety.IsCharted`); if uᵢ : W → Y satisfy ∑ mᵢ [Frob_(p^(f eᵢ)) uᵢ(w)] = 0 (in the sense of
`Cancels`; Frob_q composes a k-point with Spec of the map x ↦ x^q of k) at the field points w of W
of characteristic p killing the preimage in R of A's maximal ideal
(`New.Variety.CongruenceRelation`), then ∑ mᵢ uᵢ^*(g^(−eᵢ) x) = 0 for every x in Vⁿ(Y) = ℚ_ℓ ⊗ Hⁿ(Y
×_R Ω, ℤ_ℓ), with Γ acting through Ω. -/
lemma congruence_relation [IsProper W.hom] {g : Γ} (hg : IsFrob A (p ^ f) g) {I : Type} [Fintype I]
    (u : I → (W ⟶ Y)) (e : I → ℕ) (m : I → ℤ)
    (h_cong : CongruenceRelation m (algebraMap R Ω ⁻¹' A.nonunits) p (fun i : I ↦ e i * f) u)
    (x : (ellAdicCohom R Ω n).obj (Opposite.op Y)) :
    ∑ i : I,
      m i • (ellAdicCohom R Ω n).map (u i).op (galoisAction R Ω Γ Y n (g⁻¹ ^ e i) x) = 0 := by
  -- Lift `x` to a class `y` over the valuation ring `A`, on which `g⁻¹ ^ e i` acts through a ring
  -- endomorphism `σ i` of `A`, and use the relation over `A`.
  algebraize [RingHom.codRestrict _ A hR]
  -- smooth base change: pull-back from `A` to `Ω` is bijective on the cohomology of `Y`
  obtain ⟨y, rfl⟩ : ∃ y, baseChangePull rfl Y y = x :=
    (isTestCohomEquiv_baseChangeTransition hp hℓ Y).bijective_ellAdicPull.surjective x
  -- `σ i` is `g⁻¹ ^ e i` on `A`
  let σ (i : I) : A →+* A := (MulSemiringAction.toRingHom ..).restrict A A fun a ↦
    (mem_decompGroup_iff.mp (pow_mem (inv_mem hg.left) (e i)) a).mpr
  -- `σ i` fixes the image of `R`
  have h_σ_alg (i : I) : ofHom (algebraMap R A) ≫ ofHom (σ i) = ofHom (algebraMap R A) :=
    CommRingCat.hom_ext <| RingHom.ext fun r ↦ Subtype.ext <| smul_algebraMap _ r
  -- `σ i` lifts the inverse of the Frobenius of exponent `p ^ (e i * f)`, as `g ^ e i` is a
  -- Frobenius for `(p ^ f) ^ e i`
  have h_σ_frob (i : I) (a : A) : A.valuation ((a : Ω) - (σ i a : Ω) ^ p ^ (e i * f)) < 1 := by
    have h := valuation_sub_inv_smul_pow_lt_one (hg.pow (e i)) (A.valuation_le_one a)
    rw [← inv_pow, ← pow_mul'] at h
    exact h
  -- each term is the pull-back to `Ω` of the matching term over `A`, and the sum vanishes over `A`
  have h_term (i : I) := map_galoisAction_baseChangePull rfl (u i) (γ := g⁻¹ ^ e i) (σ := σ i)
    (fun _ ↦ rfl) (h_σ_alg i) y
  have h_sum := sum_ellAdicPull_eq_zero_of_congruenceRelation hℓ hp u (fun i ↦ e i * f) m h_cong σ
    h_σ_alg h_σ_frob y
  let pullToΩ := baseChangePull (ℓ := ℓ) (n := n) (A := A) rfl W
  exact (Finset.sum_congr rfl fun i _ ↦
    (congrArg (m i • ·) (h_term i)).trans (map_zsmul pullToΩ ..).symm).trans <|
    (map_sum pullToΩ ..).symm.trans <| (congrArg pullToΩ h_sum).trans (map_zero pullToΩ)

/-- Inertia acts trivially. Let Ω be an algebraic closure of ℚ and an R-algebra, A ⊂ Ω a valuation
ring that contains the image of R (`hR`), with a prime p in its maximal ideal (`hp`) and ℓ a unit
(`hℓ`). For Y proper over R and as in `New.Variety.IsCharted`, the inertia group of A acts
trivially on Vⁿ(Y). -/
lemma galoisAction_eq_one_of_inertia {g : Γ} (hg : g ∈ inertiaGroup Γ A) :
    galoisAction R Ω Γ Y n g = 1 := by
  ext x
  -- apply `congruence_relation` to `g⁻¹`, a Frobenius for `p ^ 0`: the relation on points reads
  -- `-[y] + [y] = 0`
  have h_cong : CongruenceRelation ![-1, 1] (algebraMap R Ω ⁻¹' A.nonunits) p
      (fun i : Fin 2 ↦ i * 0) ![𝟙 Y, 𝟙 Y] := by simp [CongruenceRelation, Cancels]
  have h := congruence_relation hR hℓ hp (f := 0) (inv_mem hg) ![𝟙 Y, 𝟙 Y] Fin.val ![-1, 1] h_cong x
  rw [Fin.sum_univ_two] at h
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, inv_inv, op_id, map_one, one_apply_eq_self, neg_smul, one_smul] at h
  rw [(ellAdicCohom R Ω n).map_id, ModuleCat.id_apply, ModuleCat.id_apply, neg_add_eq_zero] at h
  rw [one_apply_eq_self]
  exact h.symm

end New.Variety.ellAdicCohom
