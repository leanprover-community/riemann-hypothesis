module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Lib.PadicComparison.Completion
public import Lib.PadicComparison.Descent.TestCovers

/-!
# Products of p-adic tests under tilting and period coefficients

A product of two `p`-adic tests is recognised by the map `x ↦ (f x, g x)` being bijective. This
file shows that tilting keeps such products, and that a functor isomorphic to the period
coefficient `c ↦ K ⊗ (S ⊗ W(R♭))^` has partitions.

## Main results

* `New.Variety.bijective_prod_tilt`: bijectivity of `x ↦ (f x, g x)`, which recognises a product,
  passes from the rings of `p`-adic tests to their tilts.
* `New.Variety.hasPartitions_periodAlg`: a functor `Ψ` with an isomorphism `θ` from the period
  coefficients `asModules (tilt ⋙ periodAlg S) ⋙ tensorWith K K` turns a product of two tests into a
  product (`New.Variety.HasPartitions`).
-/

@[expose] public section

noncomputable section

namespace New.Variety

/-!
## Products of p-adic tests under tilting and product-preserving functors

A product of two objects is recognised here by the map `x ↦ (f x, g x)` being bijective.
-/

section TiltProducts

open CategoryTheory Limits PadicTest Perfection Equiv Function

/-- If `x ↦ (f x, g x)` is bijective for linear maps `f : X ⟶ Y` and `g : X ⟶ Z`, then so is
`x ↦ (U.map f x, U.map g x)` for every functor `U` from modules to types that preserves the
product of `Y` and `Z`. -/
lemma _root_.Function.Bijective.map_prod {S : Type*} [Ring S] {X Y Z : ModuleCat S} {f : X ⟶ Y}
    {g : X ⟶ Z} (hfg : Bijective fun x : X ↦ (f x, g x)) (U : ModuleCat S ⥤ Type*)
    [PreservesLimit (pair Y Z) U] :
    Bijective fun x : U.obj X ↦ (U.map f x, U.map g x) := by
  -- `X` with `f` and `g` is a product of `Y` and `Z`, so its image under `U` is a product of types.
  have h_iso : IsIso ((Y.binaryProductLimitCone Z).isLimit.lift (BinaryFan.mk f g)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hfg
  let h_prod : IsLimit (BinaryFan.mk f g) := (Y.binaryProductLimitCone Z).isLimit.ofPointIso
  exact ((mapIsLimitOfPreservesOfIsLimit U _ _ h_prod).conePointUniqueUpToIso
    (Types.binaryProductLimit (U.obj Y) (U.obj Z))).toEquiv.bijective

/-- Tilting keeps the product of two tests: if maps of `p`-adic tests `f : c ⟶ d` and `g : c ⟶ d'`
present the ring of `c` as the product of the rings of `d` and `d'`, then the induced maps present
the tilt of `c`, read as an `O♭`-module (`asModules tilt`), as the product of the tilts of `d` and
`d'`. -/
lemma bijective_prod_tilt {p : ℕ} [ThePrime p] {c d d' : PadicTest} (f : c ⟶ d) (g : c ⟶ d')
    (hfg : Bijective fun x : c.ProdRing ↦ (f.toRingHom x, g.toRingHom x)) :
    Bijective fun x : (asModules tilt).obj c ↦
      ((asModules tilt).map f x, (asModules tilt).map g x) := by
  -- As a set, the tilt of a test is the set of sequences `x` in its ring with
  -- `x (n + 1) ^ p = x n`, and such sequences in a product are pairs of such sequences.
  let e {b : PadicTest} : Perfection b.ProdRing p ≃ tilt.obj b :=
    (quotientMulEquiv p (Ideal.span {(p : b.ProdRing)})).toEquiv
  let seqs : (ℕ → c.ProdRing) ≃ (ℕ → d.ProdRing) × (ℕ → d'.ProdRing) :=
    (ofBijective _ hfg.comp_left).trans
      (arrowProdEquivProdArrow ℕ (fun _ ↦ d.ProdRing) (fun _ ↦ d'.ProdRing))
  have compatible_iff (x : ℕ → c.ProdRing) : (∀ n : ℕ, x (n + 1) ^ p = x n) ↔
      (∀ n : ℕ, (seqs x).fst (n + 1) ^ p = (seqs x).fst n) ∧
        ∀ n : ℕ, (seqs x).snd (n + 1) ^ p = (seqs x).snd n := by
    simp [seqs, forall_and, ← hfg.injective.eq_iff]
  let perf : Perfection c.ProdRing p ≃ Perfection d.ProdRing p × Perfection d'.ProdRing p :=
    (seqs.subtypeEquiv compatible_iff).trans subtypeProdEquivProd
  -- By definition of the tilt of a map, the map in question composed with `e` is `perf` followed
  -- by `e × e`.
  exact (e.bijective_comp _).mp (perf.trans (e.prodCongr e)).bijective

end TiltProducts

section PeriodPairs

open CategoryTheory Algebra TensorProduct Period PadicTest Equiv

variable (p : ℕ) (S : Type) [CommRing S]
  (K : Type _) [CommRing K] [Algebra S K] [ThePrime p] [Algebra Ainf S]
  {Ψ : PadicTest ⥤ ModuleCat K}

variable {p S}

/-- Let `Ψ` be isomorphic (by `θ`) to the period coefficient `c ↦ K ⊗ (S ⊗ W(R♭))^`. Then `Ψ` has
partitions: tests can be cut along idempotents, and `Ψ` sends a product of two tests to the
product of its values. -/
lemma hasPartitions_periodAlg (θ : asModules (tilt ⋙ periodAlg S) ⋙ tensorWith K K ≅ Ψ) :
    HasPartitions ringFunctor (moduleCoeff Ψ) := by
  refine ⟨exists_isQuotientByElem, fun {A B₁ B₂ : PadicTest} f g hfg ↦ ?_⟩
  -- Tilting keeps the product, and so do Witt vectors, which are sequences of coordinates.
  let e {R : Type} : WittVector p R ≃ (ℕ → R) := mk WittVector.coeff (.mk p)
  let W : PadicTest ⥤ ModuleCat Ainf := asModules (tilt ⋙ wittFunctor)
  have h_witt : Function.Bijective fun x : W.obj A ↦ (W.map f x, W.map g x) :=
    ((arrowProdEquivProdArrow ℕ (fun _ ↦ tilt.obj B₁) (fun _ ↦ tilt.obj B₂)).trans
      (e.prodCongr e).symm).bijective.comp
      ((bijective_prod_tilt f g hfg).comp_left.comp e.bijective)
  -- So do base change to `S`, completion of modules and base change to `K`.
  let Φ : PadicTest ⥤ ModuleCat K :=
    asModules (tilt ⋙ wittFunctor ⋙ algBaseChange S) ⋙ moduleCompletion S p ⋙ tensorWith K K
  have h_ten : Function.Bijective fun x : Φ.obj A ↦ (Φ.map f x, Φ.map g x) :=
    (h_witt.map_prod (tensorWith S S ⋙ forget _)).map_prod
      (moduleCompletion S p ⋙ tensorWith K K ⋙ forget _)
  -- The composite `Φ` is isomorphic to `Ψ`, by `moduleCompletionIso` and `θ`. The whiskering `κ`
  -- is stated for any functors `Q`, `Q'` in place of the two completions.
  let κ {Q : ModuleCat S ⥤ ModuleCat S} {Q' : CommAlg S ⥤ CommAlg S}
      (ι : asModules (𝟭 (CommAlg S)) ⋙ Q ≅ asModules Q') :
      asModules (tilt ⋙ wittFunctor ⋙ algBaseChange S) ⋙ Q ⋙ tensorWith K K ≅
        asModules (tilt ⋙ wittFunctor ⋙ algBaseChange S ⋙ Q') ⋙ tensorWith K K :=
    (Functor.isoWhiskerRight ((tilt ⋙ wittFunctor ⋙ algBaseChange S).isoWhiskerLeft ι)
      (tensorWith K K) :)
  let θ' : Φ ≅ Ψ := κ (moduleCompletionIso S p) ≪≫ θ
  -- The square of `θ'` with the two pairs of maps commutes, by naturality of `θ'`.
  have h_comm (x : Φ.obj A) : (Ψ.map f (θ'.hom.app A x), Ψ.map g (θ'.hom.app A x)) =
      Prod.map (θ'.hom.app B₁) (θ'.hom.app B₂) (Φ.map f x, Φ.map g x) := by
    simp
  have hθ' (A : PadicTest) : Function.Bijective (θ'.hom.app A) := (θ'.app A).toLinearEquiv.bijective
  exact ((Comparison.bijective_iff_of_comm_sq h_comm (hθ' A) ((hθ' B₁).prodMap (hθ' B₂))).mp
    h_ten).map_prod (forget _ ⋙ uliftFunctor.{1})

end PeriodPairs

end New.Variety

end
