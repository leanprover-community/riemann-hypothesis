module

public import Lib.PadicComparison.Primitive.PeriodCoefficients

/-!
# The perfect projective line glued from two perfect discs has the cohomology of a point

The perfect projective line on p-adic tests S is a model on which classes on ℙ¹ are computed. Its
two discs are represented in the tilt S^♭ by O^♭[ℚ≥0], and its torus by O^♭[ℚ].

* `New.Variety.PerfectLine.gluing`: the gluing map ℤ[torus ⊔ point] → ℤ[two discs]; it is injective
  (a monomorphism). Its cokernel plays the role of the perfect line with the point ∞ killed.
* `New.Variety.PerfectLine.oneSub_comp_gluing`: the operators 1 − (T^s ↦ χ(s) T^s) commute with the
  gluing map.
* `New.Variety.PerfectLine.isCohomEquiv_gluing_tilt`,
  `New.Variety.PerfectLine.isCohomEquiv_gluing_generic`: over each test c the gluing map induces
  bijections on cohomology. This holds for coefficients G(S^♭), where G is built from an O^♭-module
  N and is assumed acyclic on perfect rings. It also holds for S[1/p].
* `New.Variety.PerfectLine.subsingleton_H_cokernel_gluing`: then M ⊗ cokernel has no cohomology, for
  every M with flat values.

Idea: all cohomology is in degree 0, where the map is the splitting of a Laurent polynomial into two
parts according to the sign of the exponent. `New.Period.OFlat` is O^♭, the tilt of the ring of
integers O_C of ℂ_p.

Notions from other files:
* `New.Variety.PadicTest`: A p-adic test: a non-empty family of cells (`New.Variety.IsCell`) with a
  ring map from O_C to their product.
* `New.Variety.freeAb`: The functor sending a set-valued functor Y to Z[Y], whose value at A is the
  free abelian group on Y(A). ℤ[Y] has flat base change (`HasFlatBaseChange`) when tensoring by a
  flat module M commutes with its cohomology with module coefficients.

## Relation to the literature

Known; see `Lib.Cohomology.ProjectiveLine.ConstantLineFormula` for sources.
-/

@[expose] public section

noncomputable section


namespace New.Variety

open CategoryTheory Function AddMonoidAlgebra Period MonoidalCategory PadicTest NNRat
open CommAlgCat hiding of

/-- The objectwise tensor product of two functors with flat values has flat values. -/
instance {C : Type 1} [Category C] {F A : AbFunctor C} [HasFlatValues F] [HasFlatValues A] :
    HasFlatValues (abTensor F A) := by
  refine ⟨fun c ↦ ?_⟩
  -- The field `HasFlatValues.flat` is not an instance, so the two facts are stated here.
  have h_flat_F : Module.Flat ℤ (F.obj c) := HasFlatValues.flat c
  have h_flat_A : Module.Flat ℤ (A.obj c) := HasFlatValues.flat c
  exact .instTensorProduct

namespace PerfectLine

variable {p : ℕ} [ThePrime p]
  (χ : Multiplicative ℚ →* OFlat) {S : Type} [AddCommMonoid S]
  (f : S →+ ℚ) (g : ℚ≥0 →+ ℚ) {b b' : CommAlg OFlat} (a : ULift.{1} Bool)
  (X : PadicTest ⥤ Type 1 := onePointFunctor PadicTest)

/-! ### The discs, the torus and the gluing map -/

/-- For an additive commutative monoid S, the monoid algebra O^♭[S], as a commutative
O^♭-algebra. -/
abbrev monoidAlg (S : Type) [AddCommMonoid S] : CommAlgCat OFlat := CommAlgCat.of OFlat OFlat[S]

/-- For a character χ of ℚ with values in O^♭ and an additive map f: S → ℚ, the O^♭-algebra
endomorphism T^s ↦ χ(f(s)) T^s of O^♭[S]. -/
def charTwist : monoidAlg S ⟶ monoidAlg S :=
  ofHom (lift OFlat OFlat[S] S
    ((algebraMap OFlat OFlat[S]).toMonoidHom.comp (χ.comp f.toMultiplicative) * of OFlat S))

/-- For an additive map g: ℚ≥0 → ℚ, the map of monoid algebras O^♭[ℚ≥0] → O^♭[ℚ] over O^♭
sending T^a to T^{g(a)}. -/
abbrev discToTorus : monoidAlg ℚ≥0 ⟶ monoidAlg ℚ := ofHom (mapDomainAlgHom OFlat OFlat g)

/-- Evaluation at T = 0: the O^♭-algebra map from O^♭[ℚ_{≥0}] to b sending T^0 to 1 and T^a to 0
for a > 0. -/
abbrev evalZero (b : CommAlgCat OFlat) : monoidAlg ℚ≥0 ⟶ b :=
  ofHom (lift OFlat b ℚ≥0 ⟨⟨fun s ↦ if s = 1 then 1 else 0, ite_eq_left rfl⟩, by aesop⟩)

variable (B : ULift.{1} Bool → CommAlg OFlat)
  (ψ : CommAlg OFlat ⥤ CommAlg OFlat := 𝟭 (CommAlg OFlat))

/-- The family of two `O^♭`-algebras: the ring `O^♭[ℚ]` of the perfect torus at the index `true`,
and the ring `O^♭` of a point at the index `false`. -/
def pointOrTorus : ULift.{1} Bool → CommAlg OFlat
  | ⟨true⟩ => monoidAlg ℚ
  | ⟨false⟩ => CommAlgCat.of OFlat OFlat

lemma pointOrTorus_true : pointOrTorus ⟨true⟩ = monoidAlg ℚ := rfl

lemma pointOrTorus_false : pointOrTorus ⟨false⟩ = CommAlgCat.of OFlat OFlat := rfl

/-- For O^♭-algebras B_i indexed by Bool and an endofunctor ψ of O^♭-algebras (default the
identity), the functor S ↦ ⊔_i Hom(ψ(B_i), S^♭) on p-adic tests. -/
abbrev tiltPointsSum : PadicTest ⥤ Type 1 := sigma fun a ↦ tilt ⋙ reprBy (ψ (B a))

/-- Two affine lines with all roots of the coordinate: for an endofunctor ψ of O^♭-algebras (default
the identity), the disjoint union of two copies of the functor of points of ψ(O^♭[ℚ_{≥0}]) in the
tilts of p-adic tests. -/
abbrev twoDiscs : PadicTest ⥤ Type 1 := tiltPointsSum (fun _ ↦ monoidAlg ℚ≥0) ψ

/-- The map ℤ[torus ⊔ point] → ℤ[two discs] sending a point t of the torus to t⁻¹ in the disc
`false` minus t in the disc `true`, and the point to the origin of the disc `false`. -/
abbrev gluing : freeAb (tiltPointsSum pointOrTorus ψ) ⟶ freeAb (twoDiscs ψ) :=
  freeAb.desc
    (fun
      | _, ⟨⟨true⟩, t⟩ =>
        .of ⟨⟨false⟩, ⟨ψ.map (discToTorus (-coeHom)) ≫ t.1⟩⟩ -
          .of ⟨⟨true⟩, ⟨ψ.map (discToTorus coeHom) ≫ t.1⟩⟩
      | _, ⟨⟨false⟩, t⟩ =>
        FreeAddCommGroup.of ⟨⟨false⟩, ⟨ψ.map (evalZero (pointOrTorus { down := false })) ≫ t.1⟩⟩)
    (by bound)

@[simp]
lemma evalZero_comp (g : b ⟶ b') : evalZero b ≫ g = evalZero b' := by aesop

variable {B : ULift.{1} Bool → CommAlg OFlat} (Δ : ∀ b : ULift.{1, 0} Bool, B b ⟶ B b)
  {N : ModuleCat OFlat}

/-! ### Origins, the operator 1 − Δ, and injectivity of the gluing map -/

/-- For a set-valued functor X on p-adic tests (by default the point), the morphism
ℤ[X] → ℤ[two discs] sending every point to the origin T = 0 of the disc with index a. -/
abbrev origin : freeAb X ⟶ freeAb twoDiscs :=
  freeAb.desc (fun _ _ ↦ FreeAddCommGroup.of ⟨a, ⟨evalZero _⟩⟩) fun _ _ _ _ ↦ by
    congr
    simp

/-- The map ℤ[Hom(B_true, S^♭) ⊔ Hom(B_false, S^♭)] → ℤ[Hom(B_true, S^♭)] that keeps the points
of the first part and sends those of the second to 0. -/
abbrev projFirst : freeAb (tiltPointsSum B) ⟶ freeAb (tilt ⋙ reprBy (B ⟨true⟩)) :=
  freeAb.desc (fun | _, ⟨⟨true⟩, t⟩ => FreeAddCommGroup.of t | _, ⟨⟨false⟩, _⟩ => 0) (by bound)

/-- For endomorphisms Δ_b of the O^♭-algebras B_b, the endomorphism 1 − Δ of the functor S ↦
ℤ[⊔_b Hom(B_b, S^♭)], sending [x] to [x] − [x∘Δ_b]. -/
abbrev oneSub : freeAb (tiltPointsSum B) ⟶ freeAb (tiltPointsSum B) :=
  freeAb.desc (fun _ x ↦ .of x - .of ⟨x.fst, ⟨Δ x.fst ≫ x.2.down⟩⟩) (by bound)

@[simp]
lemma charTwist_comp_evalZero : charTwist χ g ≫ evalZero b = evalZero b := by
  ext
  simp_all [charTwist]

/-- For an additive map `g : ℚ≥0 → ℚ`, twisting `O^♭[ℚ≥0]` by `χ ∘ g` and then sending `T^a` to
`T^{g(a)}` is the same as first sending `T^a` to `T^{g(a)}` and then twisting `O^♭[ℚ]` by `χ`. -/
@[reassoc]
lemma charTwist_comp_discToTorus :
    charTwist χ g ≫ discToTorus g = discToTorus g ≫ charTwist χ (AddMonoidHom.id ℚ) := by
  ext
  simp [charTwist]

/-- The endomorphism `T^s ↦ χ(s) T^s` of the ring of the torus, and the identity of the ring of
the point. -/
def pointOrTorusTwist : ∀ i : ULift.{1} Bool, pointOrTorus i ⟶ pointOrTorus i
  | ⟨true⟩ => charTwist χ (AddMonoidHom.id ℚ)
  | ⟨false⟩ => 𝟙 (pointOrTorus ⟨false⟩)

/-- The endomorphism `T^s ↦ χ(s) T^s` of the ring of the disc `true`, and `T^s ↦ χ(-s) T^s` of
the ring of the disc `false`. -/
def discTwist : ULift.{1} Bool → (monoidAlg ℚ≥0 ⟶ monoidAlg ℚ≥0)
  | ⟨true⟩ => charTwist χ coeHom
  | ⟨false⟩ => charTwist χ (-coeHom)

/-- The twist of either disc fixes the evaluation at `T = 0`. -/
lemma discTwist_comp_evalZero : discTwist χ a ≫ evalZero b = evalZero b := by
  rcases a with ⟨_ | _⟩ <;> simp only [discTwist, charTwist_comp_evalZero]

/-- The gluing map commutes with the operators `1 - Δ`, where `Δ` is the twist by `χ` on the
torus and on the two discs, and the identity on the point. -/
lemma oneSub_comp_gluing :
    oneSub (pointOrTorusTwist χ) ≫ gluing = gluing ≫ oneSub (discTwist χ) := by
  -- Check on generators: `charTwist` fixes evaluation at `0` (the point) and is compatible with the
  -- inclusions of the rings of the two discs in the ring of the torus.
  refine freeAb.hom_ext fun c x ↦ ?_
  let g := ((gluing : freeAb (tiltPointsSum pointOrTorus) ⟶ freeAb twoDiscs).app c).hom
  let u := ((oneSub (pointOrTorusTwist χ)).app c).hom
  let v := ((oneSub (discTwist χ)).app c).hom
  have h_u (y : (tiltPointsSum pointOrTorus).obj c) :
      u (FreeAddCommGroup.of y) = FreeAddCommGroup.of y -
        FreeAddCommGroup.of ⟨y.fst, ⟨pointOrTorusTwist χ y.fst ≫ y.snd.down⟩⟩ := by
    change FreeAddCommGroup.lift _ (FreeAddCommGroup.of y) = _
    exact FreeAddCommGroup.lift_apply_of _ _
  have h_v (y : twoDiscs.obj c) :
      v (FreeAddCommGroup.of y) = FreeAddCommGroup.of y -
        FreeAddCommGroup.of ⟨y.fst, ⟨discTwist χ y.fst ≫ y.snd.down⟩⟩ := by
    change FreeAddCommGroup.lift _ (FreeAddCommGroup.of y) = _
    exact FreeAddCommGroup.lift_apply_of _ _
  have h_g_false (t : ((tilt ⋙ reprBy (pointOrTorus ⟨false⟩))).obj c) :
      g (FreeAddCommGroup.of ⟨⟨false⟩, t⟩) =
        FreeAddCommGroup.of ⟨⟨false⟩, ⟨evalZero (tilt.obj c)⟩⟩ := by
    change FreeAddCommGroup.lift _ (FreeAddCommGroup.of _) = _
    erw [FreeAddCommGroup.lift_apply_of]
    exact congrArg (fun f ↦ FreeAddCommGroup.of (⟨⟨false⟩, ⟨f⟩⟩ : twoDiscs.obj c))
      (evalZero_comp t.down)
  have h_g_true (t : ((tilt ⋙ reprBy (pointOrTorus ⟨true⟩))).obj c) :
      g (FreeAddCommGroup.of ⟨⟨true⟩, t⟩) =
        FreeAddCommGroup.of ⟨⟨false⟩, ⟨discToTorus (-coeHom) ≫ t.down⟩⟩ -
        FreeAddCommGroup.of ⟨⟨true⟩, ⟨discToTorus coeHom ≫ t.down⟩⟩ := by
    change FreeAddCommGroup.lift _ (FreeAddCommGroup.of _) = _
    erw [FreeAddCommGroup.lift_apply_of]
    rfl
  change g (u (FreeAddCommGroup.of x)) = v (g (FreeAddCommGroup.of x))
  rcases x with ⟨⟨_ | _⟩, t⟩
  · erw [h_u, map_sub, h_g_false, h_v]
    erw [discTwist_comp_evalZero]
    rfl
  · erw [h_u, map_sub, h_g_true]
    erw [h_g_true]
    erw [map_sub, h_v]
    erw [h_v]
    dsimp only [pointOrTorusTwist, discTwist, Sigma.fst, Sigma.snd, ULift.down]
    erw [← charTwist_comp_discToTorus_assoc χ (-coeHom),
      ← charTwist_comp_discToTorus_assoc χ coeHom, sub_sub_sub_comm]
    rfl

/-- In `O^♭[ℚ]`, the monomial of the absolute value `mabs s` is `T^t` for the rational
`t = s.nnabs`. -/
private lemma of_mabs_eq_single_nnabs (s : Multiplicative ℚ) :
    of OFlat ℚ (mabs s) = single ((s.nnabs : ℚ≥0) : ℚ) (1 : OFlat) :=
  rfl

/-- The gluing map is a monomorphism: on each test it has a retraction. -/
instance : Mono gluing := by
  -- Two maps out of the ring of the torus that agree on `T ^ |s|` agree on `T ^ s`: the exponents
  -- where they agree form a subgroup.
  have h_epi : Epi (discToTorus coeHom) := by
    refine ⟨fun x y h_comp ↦ hom_ext (algHom_ext' (MonoidHom.ext fun s ↦ ?_) (by ext))⟩
    refine mabs_mem_iff (H := MonoidHom.eqLocus ..).mp ?_
    show x (of OFlat ℚ (mabs s)) = y (of OFlat ℚ (mabs s))
    rw [of_mabs_eq_single_nnabs]
    simpa using congrArg (fun φ ↦ φ (single s.nnabs (1 : OFlat))) h_comp
  -- On each test `gluing` has a retraction: a point of the disc `false` goes to the point `∗`; a
  -- point of the disc `true` goes to `∗ - t` if it comes from a point `t` of the torus (unique by
  -- `h_epi`), and to `∗` otherwise.
  refine (NatTrans.mono_iff_mono_app _).mpr fun c ↦ ?_
  let originPoint : (tiltPointsSum pointOrTorus).obj c :=
    ⟨⟨false⟩, ⟨structureMap⟩⟩
  let r : (twoDiscs.obj c) → FreeAddCommGroup ((tiltPointsSum pointOrTorus).obj c) :=
    fun ⟨⟨b⟩, ⟨t⟩⟩ ↦ FreeAddCommGroup.of originPoint -
      cond b (extend (fun s ↦ discToTorus coeHom ≫ s) (fun s ↦ .of ⟨⟨true⟩, ⟨s⟩⟩) 0 t) 0
  refine SplitMono.mono ⟨AddCommGrpCat.ofHom (FreeAddCommGroup.lift r), ?_⟩
  apply AddCommGrpCat.hom_ext
  apply FreeAddCommGroup.lift_ext
  intro x
  change FreeAddCommGroup.lift r ((gluing.app c).hom (FreeAddCommGroup.of x)) =
    FreeAddCommGroup.of x
  change FreeAddCommGroup.lift r (FreeAddCommGroup.lift _ (FreeAddCommGroup.of x)) = _
  erw [FreeAddCommGroup.lift_apply_of]
  rcases x with ⟨⟨_ | _⟩, ⟨t⟩⟩
  · erw [FreeAddCommGroup.lift_apply_of]
    change FreeAddCommGroup.of originPoint - 0 = _
    rw [sub_zero]
    have ht : structureMap = t := CommAlgCat.hom_ext (AlgHom.ext fun a ↦ (t.hom.commutes a).symm)
    exact congrArg
      (fun f ↦ FreeAddCommGroup.of (⟨⟨false⟩, ⟨f⟩⟩ : (tiltPointsSum pointOrTorus).obj c)) ht
  · change FreeAddCommGroup.lift r
      (FreeAddCommGroup.of ⟨⟨false⟩, ⟨discToTorus (-coeHom) ≫ t⟩⟩ -
        FreeAddCommGroup.of ⟨⟨true⟩, ⟨discToTorus coeHom ≫ t⟩⟩) = _
    erw [map_sub, FreeAddCommGroup.lift_apply_of, FreeAddCommGroup.lift_apply_of]
    change FreeAddCommGroup.of originPoint - 0 -
      (FreeAddCommGroup.of originPoint -
        extend (fun s ↦ discToTorus coeHom ≫ s)
          (fun s ↦ FreeAddCommGroup.of ⟨⟨true⟩, ⟨s⟩⟩) 0 (discToTorus coeHom ≫ t)) = _
    erw [Injective.extend_apply h_epi.left_cancellation, sub_zero, sub_sub_cancel]

open Abelian.Ext TensorProduct LinearEquiv H Comparison

/-- For a test `c` and a perfect `O^♭`-algebra `b`, the algebra `c^♭ ⊗ b` is a perfect ring. -/
lemma perfectRing_tensorLeft_tilt (c : PadicTest) (b : CommAlg OFlat) (hb : PerfectRing b p) :
    PerfectRing ((tensorLeft (tilt c)) b) p :=
  perfectRing_tensor natCast_eq_zero_of_algebra_oFlat ⟨tilt c, c.isPerfectTorsionFree_tilt.1⟩
    ⟨b, hb⟩

/-- If the coefficient functor `G = – ⊗ N` is acyclic on perfect `O^♭`-algebras (for b perfect,
Hom(b, –^♭) has cohomology G(b) in degree 0 and none above), then `ℤ[⊔_b Hom(ψ(B_b), –^♭)]` has no
cohomology in positive degree with coefficients in `S ↦ G(S^♭)`, for `O^♭`-algebras `B_b` indexed by
`Bool` and an endofunctor `ψ` with the `ψ(B_b)` perfect. -/
lemma subsingleton_H_freeAb_tiltPointsSum
    (h_acyclic : IsAcyclicOnPerfect (moduleCoeff (tensorCoeff N)))
    (B : ULift.{1} Bool → CommAlg OFlat) (ψ : CommAlg OFlat ⥤ CommAlg OFlat)
    (h_perf : ∀ b : ULift.{1} Bool, PerfectRing (ψ (B b)) p) (n : ℕ) :
    Subsingleton (H (freeAb (tiltPointsSum B ψ)) (tilt ⋙ moduleCoeff (tensorCoeff N)) (n + 1)) := by
  -- Each part has no cohomology in positive degree, and cohomology turns the disjoint union into a
  -- product.
  have h_part (b : ULift.{1} Bool) (m : ℕ) :
      Subsingleton (H (freeAb (tilt ⋙ reprBy (ψ (B b))))
        (tilt ⋙ moduleCoeff (tensorCoeff N)) (m + 1)) :=
    (isBijective_reprBy_iff.1 (h_acyclic (ψ (B b)))).2 m
  exact (sigma_bijective ..).injective.subsingleton

/-- For `O^♭`-algebras `B_b` indexed by `Bool` and an endofunctor `ψ` of `O^♭`-algebras such that
the `ψ(B_b)` are perfect rings, the functor `ℤ[⊔_b Hom(ψ(B_b), –^♭)]` has flat base change. -/
lemma hasFlatBaseChange_freeAb_tiltPointsSum (B : ULift.{1} Bool → CommAlg OFlat)
    (ψ : CommAlg OFlat ⥤ CommAlg OFlat) (h_perf : ∀ b : ULift.{1} Bool, PerfectRing (ψ (B b)) p) :
    HasFlatBaseChange (freeAb (tiltPointsSum B ψ)) := by
  -- `M ⊗ –` commutes with the finite product, and each part is representable by a perfect
  -- algebra, so it has flat base change.
  intro S T M instS instT instAlg instM instSM instTM instTower instFlat Φ n
  let e : M ⊗[S] H (freeAb (tiltPointsSum B ψ)) (moduleCoeff Φ) n ≃ₗ[S]
      ∀ b : ULift.{1} Bool, M ⊗[S] H (freeAb (tilt ⋙ reprBy (ψ (B b)))) (moduleCoeff Φ) n :=
    (ofBijective (.pi fun _ ↦ mapₗ ..) (sigma_bijective ..)).lTensor M ≪≫ₗ piRight ..
  refine (bijective_iff_of_comm_sq (fun x ↦ ?_) e.bijective (sigma_bijective ..)).2
    (.piMap fun _ ↦ hasFlatBaseChange_of_iso_reprBy homTiltIso.symm ..)
  induction x with
  | tmul m y => simp [e, mapₗ, map_push, funext_iff]
  | add x y hx hy => simp_all [e, mapₗ, funext_iff]

/-- The projection of a pair `(y₀, y₁)` of elements of `O^♭[ℚ≥0]` to `y₀` (for `false`) or to
`y₁` (for `true`). -/
private def pairProj (b : Bool) :
    ModuleCat.of OFlat (monoidAlg ℚ≥0 × monoidAlg ℚ≥0) ⟶ ModuleCat.of OFlat (monoidAlg ℚ≥0) :=
  ModuleCat.ofHom (cond b (.snd ..) (.fst ..))

/-- The `O^♭`-linear maps that describe the gluing map in degree `0`. A pair `(y₀, y₁)` of
elements of `O^♭[ℚ≥0]` goes to the value `y₀(0)` in the ring `O^♭` of the point, and to
`y₀(T⁻¹) - y₁(T)` in the ring `O^♭[ℚ]` of the torus. -/
private def glueLinear : ∀ b : ULift.{1} Bool,
    ModuleCat.of OFlat (monoidAlg ℚ≥0 × monoidAlg ℚ≥0) ⟶
      (asModules (𝟭 (CommAlg OFlat))) (pointOrTorus b)
  | ⟨false⟩ => pairProj false ≫ (asModules (𝟭 (CommAlg OFlat))).map (evalZero _)
  | ⟨true⟩ =>
    pairProj false ≫ (asModules (𝟭 (CommAlg OFlat))).map (discToTorus (-coeHom)) -
      pairProj true ≫ (asModules (𝟭 (CommAlg OFlat))).map (discToTorus coeHom)

/-- The map `(y₀, y₁) ↦ (y₀(0), y₀(T⁻¹) - y₁(T))` from pairs of elements of `O^♭[ℚ≥0]` to pairs
in `O^♭ × O^♭[ℚ]` is bijective. -/
private lemma bijective_glueLinear :
    Bijective fun x : monoidAlg ℚ≥0 × monoidAlg ℚ≥0 ↦
      (glueLinear ⟨false⟩ x, glueLinear ⟨true⟩ x) := by
  -- The inverse sends `(a, w)` to `(a + w₋, a - w₊)`, where `w₊` and `w₋(T⁻¹)` are the parts of
  -- `w` of exponent `≥ 0` and `< 0`.
  have {B : Type} [CommRing B] [Algebra OFlat B] :
      ZeroHomClass (OFlat[ℚ≥0] →ₐ[OFlat] B) OFlat[ℚ≥0] B :=
    RingHomClass.toAddMonoidHomClass.toZeroHomClass
  let split : (ℚ →₀ OFlat) →ₗ[OFlat] OFlat[ℚ≥0] × OFlat[ℚ≥0] :=
    Finsupp.linearCombination OFlat fun t : ℚ ↦
      if 0 ≤ t then (0, -single t.toNNRat 1) else (single (-t).toNNRat 1, 0)
  let glueInv : OFlat × OFlat[ℚ] →ₗ[OFlat] OFlat[ℚ≥0] × OFlat[ℚ≥0] :=
    .coprod (Algebra.linearMap OFlat _) (split ∘ₗ (coeffLinearEquiv OFlat).toLinearMap)
  refine (ofLinearMap (.prod (glueLinear ⟨false⟩).hom (glueLinear ⟨true⟩).hom) glueInv
    ?glue_comp_inv ?inv_comp_glue : (OFlat[ℚ≥0] × OFlat[ℚ≥0]) ≃ₗ[OFlat] OFlat × OFlat[ℚ]).bijective
  · -- The gluing maps after the inverse are the identity of `O^♭ × O^♭[ℚ]`: check it on `1` and on
    -- the monomials `T^t`, whose image under the inverse depends on the sign of `t`.
    dsimp +zetaDelta [glueLinear, pairProj, pointOrTorus, Bool.cond_true, Bool.cond_false]
    ext : 3
    · simp
    · simp
    · simp
      split_ifs with h_nonneg
      · simp_all [Rat.coe_toNNRat, ← single_neg]
      · simp_all [le_of_lt, Rat.coe_toNNRat]
  · -- The inverse after the gluing maps is the identity of `O^♭[ℚ≥0] × O^♭[ℚ≥0]`: check it on the
    -- monomials of each factor; for `T^a` in the first factor the case `a = 0` is done separately.
    dsimp +zetaDelta [glueLinear, pairProj, pointOrTorus, Bool.cond_true, Bool.cond_false]
    ext : 3
    · simp
      split_ifs with h_zero
      · simp_all [← one_def, Prod.ext_iff]
      · simp_all
    · simp

lemma perfectRing_monoidAlg_nnrat : PerfectRing (monoidAlg ℚ≥0) p := by
  simp [perfectRing_monoidAlgebra]

lemma perfectRing_pointOrTorus (b : ULift.{1} Bool) : PerfectRing (pointOrTorus b) p := by
  rcases b with ⟨_ | _⟩
  · rw [pointOrTorus_false]
    exact instPerfectRingOFlat
  · rw [pointOrTorus_true]
    exact perfectRing_monoidAlgebra ℚ

/-- For a test `c`, the target `ℤ[two discs]` of the gluing map formed with the algebras `c^♭ ⊗ B`
has flat base change. -/
lemma hasFlatBaseChange_freeAb_twoDiscs (c : PadicTest) :
    HasFlatBaseChange (freeAb (twoDiscs (tensorLeft (tilt c)))) :=
  hasFlatBaseChange_freeAb_tiltPointsSum _ _ fun _ ↦
    perfectRing_tensorLeft_tilt c _ perfectRing_monoidAlg_nnrat

/-- For a test `c`, the source `ℤ[torus ⊔ point]` of the gluing map formed with the algebras
`c^♭ ⊗ B` has flat base change. -/
lemma hasFlatBaseChange_freeAb_tiltPointsSum_pointOrTorus (c : PadicTest) :
    HasFlatBaseChange (freeAb (tiltPointsSum pointOrTorus (tensorLeft (tilt c)))) :=
  hasFlatBaseChange_freeAb_tiltPointsSum _ _ fun b ↦
    perfectRing_tensorLeft_tilt c _ (perfectRing_pointOrTorus b)

/-- Let `G` be the coefficient functor `b ↦ b ⊗ N` on `O^♭`-algebras, and assume it is acyclic on
perfect algebras: for every perfect `O^♭`-algebra b, the functor S ↦ Hom(b, S^♭) on p-adic tests has
cohomology `G(b)` in degree 0 with coefficients S ↦ G(S^♭). Then for every p-adic test `c`, the
gluing map ℤ[torus ⊔ point] → ℤ[two discs] is an equivalence for the coefficients S ↦ G(S^♭), that
is, it induces bijections on all Extⁿ. Here the discs are the points of c^♭ ⊗ O^♭[ℚ≥0] in tilts, and
the map sends t to t⁻¹ in disc `false` minus t in disc `true`, and the point to the origin of disc
`false`. -/
lemma isCohomEquiv_tensorCoeff_gluing (c : PadicTest)
    (h_acyclic : IsAcyclicOnPerfect (moduleCoeff (tensorCoeff N))) :
    IsCohomEquiv (tilt ⋙ moduleCoeff (tensorCoeff N)) (gluing (tensorLeft (tilt c))) := by
  -- Source and target are sums of two functors `Hom(ψc (A b), –^♭)` with `ψc (A b)` perfect, so
  -- their cohomology is `∏ b, G (ψc (A b))`, in degree `0`. Both products are identified with
  -- `U Y = (c^♭ ⊗ Y) ⊗ N` for `Y` the module of pairs of elements of `monoidAlg ℚ≥0`, compatibly
  -- with `gluing`.
  let G : AbFunctor (CommAlg OFlat) := moduleCoeff (tensorCoeff N)
  let ψc : CommAlg OFlat ⥤ CommAlg OFlat := tensorLeft (tilt c)
  let L : CommAlg OFlat ⥤ ModuleCat OFlat := asModules (𝟭 (CommAlg OFlat))
  let U : AbFunctor (ModuleCat OFlat) :=
    tensorWith (S := OFlat) OFlat (tilt c) ⋙ moduleCoeff (tensorRight N)
  -- The section of `G` attached to `x : U Y` by linear maps `f b` from `Y` to the rings `A b`.
  let sectionOfMaps {Y : ModuleCat OFlat} (A : ULift.{1} Bool → CommAlg OFlat)
      (f : ∀ b, Y ⟶ L (A b)) (x : U Y) : freeAb (tiltPointsSum A ψc) ⟶ tilt ⋙ G :=
    freeAb.desc (fun _ t ↦ G.map t.snd.down (U.map (f t.fst) x))
      (by solve_by_elim [G.map_comp_apply])
  -- In degree `0`: `U` keeps finite products, so `U Y` is the product of the
  -- `U (A b) = G (ψc (A b))`, and these are the sections of the parts.
  have h_sections {Y : ModuleCat OFlat} (A : ULift.{1} Bool → CommAlg OFlat)
      (hA : ∀ b, PerfectRing (A b) p) (f : ∀ b, Y ⟶ L (A b))
      (hf : Bijective fun x ↦ (f ⟨false⟩ x, f ⟨true⟩ x)) :
      Bijective (mk₀ ∘ sectionOfMaps A f) := by
    have h_perf (b : ULift.{1} Bool) : PerfectRing (ψc (A b)) p :=
      perfectRing_tensorLeft_tilt c (A b) (hA b)
    have h_zero (b : ULift.{1} Bool) :
        Bijective ((Comparison.restrict tilt G).homOfValue (𝟙 (tilt ⋙ reprBy (ψc (A b))))) :=
      (isBijective_reprBy_iff.1 (h_acyclic (ψc (A b)))).1
    have h_prod : Bijective fun (x : U Y) b ↦ U.map (f b) x := by
      have h_pair : Bijective fun x : U Y ↦ (U.map (f ⟨false⟩) x, U.map (f ⟨true⟩) x) :=
        hf.map_prod (U ⋙ forget _)
      refine (bijective_iff_existsUnique _).2 fun y ↦ ?_
      simpa [funext_iff] using h_pair.existsUnique (y ⟨false⟩, y ⟨true⟩)
    refine (bijective_iff_of_comm_sq (fun _ ↦ ?_) (.comp (.piMap h_zero) h_prod)
      (sigma_bijective ..)).2 (.piMap fun _ ↦ mk₀_bijective ..)
    ext
    simpa [H.map] using congrArg _ freeAb.hom_ext
  have h_perf_discs (_ : ULift.{1} Bool) : PerfectRing (monoidAlg ℚ≥0) p :=
    perfectRing_monoidAlg_nnrat
  rintro (_ | n)
  · -- In degree `0`, pulling the section `sectionOfMaps _ (fun b ↦ pairProj b.down) x` back along
    -- `gluing` gives `sectionOfMaps pointOrTorus glueLinear x`.
    have h_pullback :
        ⇑(H.map (tilt ⋙ G) (gluing ψc) 0) ∘ mk₀ ∘
            sectionOfMaps (fun _ ↦ monoidAlg ℚ≥0) (fun b ↦ pairProj b.down) =
          mk₀ ∘ sectionOfMaps pointOrTorus glueLinear := by
      -- `G (ψc b)` and `U (L b)` are the same module `(c^♭ ⊗ b) ⊗ N`, with the same maps.
      have h_GU {b b' : CommAlg OFlat} (g : b ⟶ b') : G.map (ψc.map g) = U.map (L.map g) := rfl
      ext x
      simp [H.map]
      congr
      apply freeAb.hom_ext
      intro d y
      change FreeAddCommGroup.lift _ (FreeAddCommGroup.lift _ (FreeAddCommGroup.of y)) =
        FreeAddCommGroup.lift _ (FreeAddCommGroup.of y)
      erw [FreeAddCommGroup.lift_apply_of, FreeAddCommGroup.lift_apply_of]
      rcases y with ⟨⟨_ | _⟩, ⟨t⟩⟩
      · erw [FreeAddCommGroup.lift_apply_of]
        simp [glueLinear, h_GU, L, -Functor.comp_obj]
        rfl
      · erw [map_sub, FreeAddCommGroup.lift_apply_of, FreeAddCommGroup.lift_apply_of]
        dsimp only [glueLinear]
        let f₀ := discToTorus (-coeHom)
        let f₁ := discToTorus coeHom
        erw [G.map_comp (ψc.map f₀) t, G.map_comp (ψc.map f₁) t, h_GU f₀, h_GU f₁]
        erw [Functor.map_sub U (f := pairProj false ≫ L.map f₀) (g := pairProj true ≫ L.map f₁)]
        erw [U.map_comp (pairProj false) (L.map f₀), U.map_comp (pairProj true) (L.map f₁)]
        let a := (U.map (L.map f₀)).hom ((U.map (pairProj false)).hom x)
        let b := (U.map (L.map f₁)).hom ((U.map (pairProj true)).hom x)
        change (G.map t).hom a - (G.map t).hom b = (G.map t).hom (a - b)
        exact (_root_.map_sub (G.map t).hom a b).symm

    refine ((h_sections _ h_perf_discs (fun b ↦ pairProj b.down) bijective_id).of_comp_iff _).1 ?_
    rw [h_pullback]
    exact h_sections pointOrTorus perfectRing_pointOrTorus glueLinear bijective_glueLinear
  · -- In positive degree both groups vanish.
    have h_vanish (A : ULift.{1} Bool → CommAlg OFlat) (hA : ∀ b, PerfectRing (A b) p) :
        Subsingleton (H (freeAb (tiltPointsSum A ψc)) (tilt ⋙ G) (n + 1)) :=
      subsingleton_H_freeAb_tiltPointsSum h_acyclic A ψc
        (fun b ↦ perfectRing_tensorLeft_tilt c (A b) (hA b)) n
    exact ⟨fun x y _ ↦ (h_vanish _ h_perf_discs).elim x y,
      fun y ↦ ⟨0, (h_vanish _ perfectRing_pointOrTorus).elim _ y⟩⟩

/-- Let `G` be the coefficient functor `b ↦ b ⊗ N` on `O^♭`-algebras, acyclic on perfect
`O^♭`-algebras, and form the gluing map with the algebras `c^♭ ⊗ B`. Its target and its source have
flat base change, and it induces bijections on cohomology with coefficients in `S ↦ G(S^♭)`. -/
lemma isCohomEquiv_gluing_tilt (c : PadicTest)
    (h_acyclic : IsAcyclicOnPerfect (moduleCoeff (tensorCoeff N))) :
    HasFlatBaseChange (freeAb (twoDiscs (tensorLeft (tilt c)))) ∧
    HasFlatBaseChange (freeAb (tiltPointsSum pointOrTorus (tensorLeft (tilt c)))) ∧
    IsCohomEquiv (tilt ⋙ moduleCoeff (tensorCoeff N)) (gluing (tensorLeft (tilt c))) :=
  ⟨hasFlatBaseChange_freeAb_twoDiscs c, hasFlatBaseChange_freeAb_tiltPointsSum_pointOrTorus c,
    isCohomEquiv_tensorCoeff_gluing c h_acyclic⟩

/-- For every test `c`, the gluing map formed with the algebras `c^♭ ⊗ B` induces bijections on
cohomology with coefficients in `genericCoeff`, the coefficients S ↦ S[1/p]. -/
lemma isCohomEquiv_gluing_generic (c : PadicTest) :
    IsCohomEquiv genericCoeff (gluing (tensorLeft (tilt c))) := by
  -- `isCohomEquiv_tensorCoeff_gluing` gives the claim for the coefficients `S ↦ S^♭ ⊗ N ⊗ 𝔪`, where
  -- `N = O^♭ ⊗_{A_inf} O_C` is killed by `p^♭` and `𝔪` is the maximal ideal of `O^♭`.
  -- `CoeffCompBijective.periodAlg_of_almostCoeff` lifts it to `ℂ_p ⊗ (O_C ⊗ W(S^♭))^`, which is
  -- `genericCoeff` by `exists_periodAlg_iso_genericAlg`.
  let α : freeAb (tiltPointsSum pointOrTorus (tensorLeft (tilt c))) ⟶
      𝟭 PadicTest ⋙ freeAb (twoDiscs (tensorLeft (tilt c))) :=
    gluing (tensorLeft (tilt c))
  have h_tilt : CoeffCompBijective (𝟙 (𝟭 _ ⋙ tilt)) α (almostCoeff (OFlat ⊗[Ainf] OC)) :=
    (coeffCompBijective_id_iff_restrict (.refl _)).2 (isCohomEquiv_tensorCoeff_gluing c
      (isAcyclicOnPerfect_almostCoeff isPeriodRingPair_OC.pFlat_smul_eq_zero)).bij
  have h_lift :
      CoeffCompBijective (𝟙 (𝟭 _ ⋙ tilt)) α (asModules (periodAlg OC) ⋙ tensorWith ℂ_[p] ℂ_[p]) :=
    .periodAlg_of_almostCoeff (hasFlatBaseChange_freeAb_twoDiscs c) isPeriodRingPair_OC
      (fun _ ↦ by apply hasFlatBaseChange_freeAb_tiltPointsSum_pointOrTorus c)
      isPerfectTorsionFree_tilt isPerfectTorsionFree_tilt h_tilt
  obtain ⟨θ, -⟩ := exists_periodAlg_iso_genericAlg (p := p)
  -- `by exact` delays elaborating `θ` until the expected type is known.
  exact ((coeffCompBijective_id_iff_restrict (by exact θ)).1 h_lift).eqv

open Algebra.TensorProduct Functor in
/-- The perfect projective line has the cohomology of a point. For an endofunctor ψ of
`O^♭`-algebras, `gluing ψ` is the map ℤ[torus ⊔ point] → ℤ[two discs] of functors on p-adic tests,
where the discs are the points of ψ(O^♭[ℚ≥0]) in tilts; it sends t in the torus to t⁻¹ in the disc
`false` minus t in the disc `true`, and the point to the origin of the disc `false`, so its cokernel
for ψ = id is the perfect line with a point collapsed. Suppose that for every p-adic test `c` the
gluing with ψ = c^♭ ⊗ − induces bijections Extⁿ(ℤ[two discs], F) → Extⁿ(ℤ[torus ⊔ point], F) for all
n; then for every `S` whose values are flat ℤ-modules, every Extⁿ(S ⊗ coker gluing, F) is zero. -/
lemma subsingleton_H_cokernel_gluing {F : AbFunctor PadicTest}
    (h_rep : ∀ c : PadicTest, IsCohomEquiv F (gluing (tensorLeft (tilt c))))
    (S : AbFunctor PadicTest) [HasFlatValues S] :
    ∀ n : ℕ, Subsingleton (H (abTensor S (Limits.cokernel (gluing (𝟭 (CommAlg OFlat))))) F n) := by
  -- It suffices that `S ⊗ gluing` be an equivalence, and by dévissage `S` may be taken to be
  -- `ℤ[⊔ h_{c j}]`, with `h_c = reprBy c` the functor represented by `c`. Then
  -- `h_{c j} × Hom(B, –^♭) = Hom((c j)^♭ ⊗ B, –^♭)` turns `S ⊗ gluing` into the sum of the maps in
  -- the hypothesis.
  suffices h_eqv : IsCohomEquiv F ((abTensor S).map gluing) from
    (isCohomEquiv_iff_subsingleton (.map ⟨ShortComplex.exact_cokernel gluing⟩ (abTensor S))).1 h_eqv
  -- Dévissage of the comparison along `– ⊗ gluing`.
  have h_devissage := (Comparison.id F).devissage (abTensor.flip _) (abTensor.flip.map gluing)
  refine Comparison.IsBijective.eqv (h_devissage.allBijective_of_allBijective_sigma_reprBy
    (fun ι c n ↦ ?_) S)
  let ψ (j : ι) : CommAlg OFlat ⥤ CommAlg OFlat := tensorLeft (tilt (c j))
  -- A map out of `(c j)^♭ ⊗ B b` is sent to its two restrictions; `tilt` is fully faithful.
  let u (B : ULift.{1} Bool → CommAlg OFlat) :
      (sigma fun j ↦ tiltPointsSum B (ψ j)) ⟶ (sigma fun j ↦ reprBy (c j)) ⊗ tiltPointsSum B :=
    { app _ := ↾fun ⟨j, b, t⟩ ↦
        (⟨j, ⟨tilt.preimage (tensorInl ≫ t.down)⟩⟩, ⟨b, ⟨tensorInr ≫ t.down⟩⟩)
      naturality d d' f := by
        ext ⟨j, b, t⟩
        have h_restrict : tilt.preimage ((tensorInl ≫ t.down) ≫ tilt.map f) =
            tilt.preimage (tensorInl ≫ t.down) ≫ f := by
          rw [Functor.preimage_comp, Functor.preimage_map]
        exact Prod.ext (Sigma.ext rfl (heq_of_eq (congrArg ULift.up h_restrict))) rfl }
  have hu_bijective (B : ULift.{1} Bool → CommAlg OFlat) (d : PadicTest) : Bijective (u B d) := by
    -- The inverse sends a pair of maps to the induced map on the tensor product.
    let uInv : ((sigma fun j ↦ reprBy (c j)) ⊗ tiltPointsSum B).obj d →
        (sigma fun j ↦ tiltPointsSum B (ψ j)).obj d :=
      fun (⟨j, ⟨f⟩⟩, ⟨b, ⟨t⟩⟩) ↦ ⟨j, b, ⟨ofHom (productMap (tilt.map f).hom t.hom)⟩⟩
    refine bijective_iff_has_inverse.mpr ⟨uInv, fun ⟨j, b, t⟩ ↦ ?_, fun ⟨⟨j, ⟨f⟩⟩, b, ⟨t⟩⟩ ↦ ?_⟩
    · -- An algebra map out of `(c j)^♭ ⊗ B b` is determined by its two restrictions.
      have h_product :
          productMap (t.down.hom.comp includeLeft) (t.down.hom.comp includeRight) = t.down.hom :=
        Algebra.TensorProduct.ext (productMap_left ..) (productMap_right ..)
      change ⟨j, b, ⟨ofHom (productMap
        (tilt.map (tilt.preimage (tensorInl ≫ t.down))).hom (tensorInr ≫ t.down).hom)⟩⟩ =
        (⟨j, b, t⟩ : (sigma fun j ↦ tiltPointsSum B (ψ j)).obj d)
      rw [Functor.map_preimage]
      exact congrArg (fun h ↦ (⟨j, b, ⟨ofHom h⟩⟩ :
        (sigma fun j ↦ tiltPointsSum B (ψ j)).obj d)) h_product
    · let h := ofHom (productMap (tilt.map f).hom t.hom)
      have h_left : tensorInl ≫ h = tilt.map f := hom_ext (productMap_left ..)
      have h_right : tensorInr ≫ h = t := hom_ext (productMap_right ..)
      change ((⟨j, ⟨tilt.preimage (tensorInl ≫ h)⟩⟩, ⟨b, ⟨tensorInr ≫ h⟩⟩) :
        ((sigma fun j ↦ reprBy (c j)) ⊗ tiltPointsSum B).obj d) = _
      rw [h_left, h_right, Functor.preimage_map]
  -- So the cohomology of `ℤ[⊔ h_{c j}] ⊗ ℤ[⊔ Hom(B b, –^♭)]` is the product over `j` of that of
  -- the `ℤ[⊔ Hom((c j)^♭ ⊗ B b, –^♭)]`.
  let v (B : ULift.{1} Bool → CommAlg OFlat) :
      freeAb (sigma fun j ↦ tiltPointsSum B (ψ j)) ⟶
        abTensor (freeAb (sigma fun j ↦ reprBy (c j))) (freeAb (tiltPointsSum B)) :=
    freeAb.map (u B) ≫ freeAb.prod _ _
  have hv_bijective (B : ULift.{1} Bool → CommAlg OFlat) : Bijective fun x j ↦
      map F (freeAb.map (sigma.ι (fun j ↦ tiltPointsSum B (ψ j)) j)) n (map F (v B) n x) :=
    have hv_eqv : IsCohomEquiv F (v B) :=
      (IsCohomEquiv.of_bijective (hu_bijective B)).comp_iff.2 (.of_isIso _)
    (sigma_bijective ..).comp (hv_eqv n)
  -- The square commutes already on generators of the sources, since the maps `discToTorus` and
  -- `evalZero` do not change the restriction to `(c j)^♭`.
  have h_square (j : ι) :
      gluing (ψ j) ≫ freeAb.map (sigma.ι (fun k ↦ twoDiscs (ψ k)) j) ≫ v (fun _ ↦ monoidAlg ℚ≥0) =
        freeAb.map (sigma.ι (fun k ↦ tiltPointsSum pointOrTorus (ψ k)) j) ≫ v pointOrTorus ≫
          (abTensor (freeAb (sigma fun k ↦ reprBy (c k)))).map gluing := by
    let T := tilt.obj (c j)
    have h_inl {A B : CommAlg OFlat} (f : A ⟶ B) :
        tensorInl (A := T) (B := A) ≫ T ◁ f = tensorInl (A := T) (B := B) := by
      apply CommAlgCat.hom_ext
      ext x
      change Algebra.TensorProduct.map (AlgHom.id OFlat T) f.hom (x ⊗ₜ 1) = x ⊗ₜ 1
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
    have h_inr {A B : CommAlg OFlat} (f : A ⟶ B) :
        tensorInr (A := T) (B := A) ≫ T ◁ f = f ≫ tensorInr (A := T) (B := B) := by
      apply CommAlgCat.hom_ext
      ext x
      change Algebra.TensorProduct.map (AlgHom.id OFlat T) f.hom (1 ⊗ₜ x) = 1 ⊗ₜ f.hom x
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have h_inl_assoc {A B Q : CommAlg OFlat} (f : A ⟶ B) (t : T ⊗ B ⟶ Q) :
        tensorInl (A := T) (B := A) ≫ T ◁ f ≫ t = tensorInl (A := T) (B := B) ≫ t := by
      rw [← Category.assoc, h_inl]
    have h_inr_assoc {A B Q : CommAlg OFlat} (f : A ⟶ B) (t : T ⊗ B ⟶ Q) :
        tensorInr (A := T) (B := A) ≫ T ◁ f ≫ t = f ≫ tensorInr (A := T) (B := B) ≫ t := by
      rw [← Category.assoc, h_inr, Category.assoc]
    refine freeAb.hom_ext fun d y ↦ ?_
    change FreeAddCommGroup.lift _
      (FreeAddCommGroup.map _ (FreeAddCommGroup.map _ (FreeAddCommGroup.lift _ (FreeAddCommGroup.of y)))) =
      _
    erw [FreeAddCommGroup.lift_apply_of]
    rcases y with ⟨⟨_ | _⟩, ⟨t⟩⟩
    · erw [FreeAddCommGroup.map_of_apply, FreeAddCommGroup.lift_apply_of]
      change _ = _ ⊗ₜ _
      simp only [u, ψ, sigma.ι, ConcreteCategory.hom]
      erw [TypeCat.Fun.mk_apply, TypeCat.Fun.mk_apply]
      erw [TypeCat.Fun.mk_apply, TypeCat.Fun.mk_apply]
      simp [← Category.assoc]
      erw [h_inl, h_inr]
      simp only [evalZero_comp]
      rfl
    · erw [_root_.map_sub, _root_.map_sub, _root_.map_sub]
      repeat' first | erw [FreeAddCommGroup.map_of_apply] | erw [FreeAddCommGroup.lift_apply_of]
      change _ = _ ⊗ₜ _
      simp only [u, ψ, sigma.ι, ConcreteCategory.hom]
      repeat' erw [TypeCat.Fun.mk_apply]
      let t' : T ⊗ monoidAlg ℚ ⟶ tilt.obj d := t
      let left (f : T ⟶ tilt.obj d) : FreeAddCommGroup ((sigma fun j ↦ reprBy (c j)).obj d) :=
        FreeAddCommGroup.of (⟨j, ⟨tilt.preimage f⟩⟩ : (sigma fun j ↦ reprBy (c j)).obj d)
      let right (b : ULift.{1} Bool) (f : monoidAlg ℚ≥0 ⟶ tilt.obj d) :
          FreeAddCommGroup (twoDiscs.obj d) :=
        FreeAddCommGroup.of (⟨b, ⟨f⟩⟩ : twoDiscs.obj d)
      change Sub.sub
        (left (tensorInl ≫ T ◁ discToTorus (-coeHom) ≫ t') ⊗ₜ
          right ⟨false⟩ (tensorInr ≫ T ◁ discToTorus (-coeHom) ≫ t'))
        (left (tensorInl ≫ T ◁ discToTorus coeHom ≫ t') ⊗ₜ
          right ⟨true⟩ (tensorInr ≫ T ◁ discToTorus coeHom ≫ t')) = _
      rw [h_inl_assoc, h_inl_assoc, h_inr_assoc, h_inr_assoc]
      refine (tmul_sub (R := ℤ) (left (tensorInl ≫ t'))
        (right ⟨false⟩ (discToTorus (-coeHom) ≫ tensorInr ≫ t'))
        (right ⟨true⟩ (discToTorus coeHom ≫ tensorInr ≫ t'))).symm.trans ?_
      congr 1

  refine (bijective_iff_of_comm_sq (fun x ↦ ?_) (hv_bijective _) (hv_bijective _)).2
    (.piMap fun j ↦ h_rep (c j) n)
  ext j
  simpa [← H.map_comp, ψ] using congrArg (fun φ ↦ map F φ n x) (h_square j)

end PerfectLine

end New.Variety

end
