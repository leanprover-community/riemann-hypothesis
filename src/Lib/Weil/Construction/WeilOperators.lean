module

public import Lib.Weil.Construction.HeisenbergModel
public import TauCeti.Analysis.HeisenbergModel.OrthogonalSum
import TauCeti.Analysis.HeisenbergModel.Wiener

/-!
# Weil operators, orthogonal sums and transport of the reproducing model

This file defines the Weil operators of a multiplier action of a group `G` on `W` on the
reproducing model of a vacuum. It proves their cocycle relation, and shows that they preserve the
inner product. For cocycle `1` it defines the Weil representation and proves that it intertwines
the Heisenberg operators and is continuous. The file then treats orthogonal sums `W = W₁ × W₂`,
with tensor products of model vectors and Wiener's bound, and the transport of the model along
isomorphisms.

## Main definitions and results

* `New.Heisenberg.IsVacuum.weilOp_mul`, `New.Heisenberg.IsVacuum.modelInner_weilOp`: if c(g, 1) = 1,
  the Weil operators `New.Heisenberg.IsVacuum.weilOp` multiply up to the cocycle c and preserve the
  inner product.
* `New.Heisenberg.IsVacuum.weilRep`: for c = 1 the Weil representation; it intertwines ρ(x) and
  ρ(gx) (`New.Heisenberg.IsVacuum.weilRep_heisenbergOp`) and, for first countable G, is jointly
  continuous (`New.Heisenberg.IsVacuum.continuous_weilRep`). Elements that preserve `e` act by Δ(g)
  times substitution (`New.Heisenberg.IsVacuum.weilRep_apply_of_vacuum_smul`). The operator of g
  has norm at most ‖vac‖ |Δ(g)| (`New.Heisenberg.IsVacuum.norm_weilRep_le`).

Notions from other files:
* `New.Heisenberg.IsVacuum.Model`: the integrable functions v with v x = ∫ v y β(y, x) e(x - y),
  with the L¹ norm and the inner product `New.Heisenberg.IsVacuum.modelInner`.
* `New.Heisenberg.MultiplierAction`: an action of `G` on `W` preserving `β` and `μ`, with a
  multiplier `Δ` and a cocycle `c`.
* `New.Heisenberg.IsVacuum.heisenbergOp`, `New.Heisenberg.IsVacuum.vacElem`: the Heisenberg
  operators ρ(x) on the model and the vacuum `e` as an element of the model.

## Relation to the literature

This file contributes to the adelic Weil representation of a unitary group and the invariant theta
functional. See `Lib.Weil.MixedModel.ZeroTerm`. Sources: Weil; Kudla.

The usual proof of the product rule ω(g) ω(h) = ω(gh) compares ω with a Schrödinger model on a
Siegel parabolic subgroup of a split space, and then uses the Iwasawa decomposition and the sum
V ⊕ V⁻. The proof here does not use a Schrödinger model. The scalar c(g, h) in
ω(g) ω(h) = c(g, h) ω(gh) is an integral of three vacua times values of the multiplier
(`New.Heisenberg.IsVacuum.weilOp_inv_mul_weilOp_mul_weilOp`). Later files show directly that it is
1, from three local facts: a Gaussian determinant at the real places (`New.Fock.realAction`),
positivity at the split places and the sign of a Gauss sum at the inert places
(`New.stdLattice.mem_cocycleRadical`). The formulas of the Schrödinger model are then proved for the
slices in `Lib.Weil.MixedModel.ZeroTerm`.
-/

@[expose] public section

noncomputable section

/-!
## Weil operators: cocycle relation, unitarity and continuity

Below, `B` is an action of `G` on `W` with multiplier `Δ` and cocycle `c`
(`New.Heisenberg.MultiplierAction`), `A` one with cocycle `1`, `ρ = heisenbergOp` and
`vac = vacElem`.

* `New.Heisenberg.IsVacuum.weilOp`: the operator v ↦ Δ(g) ∫ v(y) ρ(gy) vac dμ(y).
* `New.Heisenberg.IsVacuum.integrated_moveBy_vacElem_eq_smul`: a nonzero overlap with the vacuum
  determines a unitary intertwining operator.
* `New.Heisenberg.IsVacuum.cocycleRadical`: the elements s with c(g, s) = 1 for all g, a subgroup.
-/

namespace New.Heisenberg.IsVacuum

open MeasureTheory Heisenberg.Rep ContinuousLinearMap TauCeti

variable {W : Type*} [AddCommGroup W] [TopologicalSpace W]
  {H : Heisenberg W} [MeasurableSpace W] [IsTopologicalAddGroup W] [BorelSpace W]
  [SecondCountableTopology W] {μ : Measure W} [μ.IsAddHaarMeasure]
  {e : W → ℂ} [he : IsVacuum H μ e]
  {G : Type*} [Group G] [TopologicalSpace G] [DistribMulAction G W] [ContinuousSMul G W]
  {c : G → G → ℂ} (B : H.MultiplierAction μ e G c) (A : H.MultiplierAction μ e G) (g h k : G)
  (x : W) (v w : Model H)

/-! ### The operators of an action with a cocycle -/

private lemma moveBy_toTauCeti :
    (heisenbergRep.moveBy B g).toTauCeti =
      (ReproducingModel.heisenbergRep (β := H.toDatum) (μ := μ) (e := e)).twist B.toTauCeti g :=
  representation_ext fun x (v : ReproducingModel H.toDatum μ e) ↦
    (congrArg (· v) (heisenbergOp_eq_tauCeti (g • x))).trans
      (ReproducingModel.heisenbergRep.twist_apply B.toTauCeti g x v).symm

/-- The Weil operator of `g` for the action `B`: the operator v ↦ Δ(g) ∫ v(y) ρ(g • y) vac dμ(y) on
the model space, where `Δ = B.Δ`, `ρ = heisenbergOp` and `vac = vacElem`. The integral is the
integrated action of `v` on `vac` for the representation `y ↦ ρ (g • y)`
(`New.Heisenberg.Rep.moveBy`). -/
def weilOp : Model H →L[ℂ] Model H := B.Δ g • (heisenbergRep.moveBy B g).integrated.flip vacElem

private lemma weilOp_eq_tauCeti :
    weilOp B g = ReproducingModel.weilOp e B.toTauCeti g := by
  ext1 v
  refine (congrArg (fun R : H.toDatum.Representation (ReproducingModel H.toDatum μ e) ↦
    B.Δ g • R.integrated μ e v vacElem) (moveBy_toTauCeti B g)).trans ?_
  rw [vacElem_eq_tauCeti]
  exact (ReproducingModel.weilOp_apply_eq B.toTauCeti g v).symm

/-- Write P_g(w) for the operator ∫ w(y) ρ(g • y) dμ(y) on the model space, the integrated action
`(heisenbergRep.moveBy B g).integrated w` of `w`. For vectors `v`, `w`, `x` of the model space,
P_g(P_k(w) v) x = P_{gk}(w) (P_g(v) x). -/
lemma integrated_moveBy_integrated (x v w : Model H) :
    (heisenbergRep.moveBy B g).integrated ((heisenbergRep.moveBy B k).integrated w v) x =
      (heisenbergRep.moveBy B (g * k)).integrated w
        ((heisenbergRep.moveBy B g).integrated v x) := by
  -- `v ↦ (heisenbergRep.moveBy B g).integrated v x` intertwines the twists by `k` and `g * k`, so
  -- it commutes with the integral that defines `integrated w`.
  rw [← flip_apply, map_integrated]
  · rfl
  · simp [mul_smul]

/-- For a bounded functional `T` on the model space, `T` of the integrated action of `w` on `v` for
the representation `y ↦ ρ (g • y)` is ∫ w(g⁻¹ • y) T(ρ(y) v) dμ(y). -/
lemma map_integrated_moveBy (T : Model H →L[ℂ] ℂ) :
    T ((heisenbergRep.moveBy B g).integrated w v) =
      ∫ y : W, w (g⁻¹ • y) * T (heisenbergOp y v) ∂μ :=
  (congrArg (fun R : H.toDatum.Representation (ReproducingModel H.toDatum μ e) ↦
    T (R.integrated μ e w v)) (moveBy_toTauCeti B g)).trans <|
    (ReproducingModel.map_integrated_twist B.toTauCeti g v w T).trans <|
      integral_congr_ae (.of_forall fun y ↦
        congrArg (fun f ↦ w (g⁻¹ • y) * T (f v)) (heisenbergOp_eq_tauCeti y).symm)

/-- Let `e` be a vacuum for the Heisenberg datum `H` and Haar measure `μ`, and let `Model H` be the
space of integrable `v` with v(x) = ∫ v(y) β(y,x) e(x−y) dμ(y). Then the pairing ∫ conj(e) v dμ
(`modelInner`) of the vacuum `vacElem` (the function `e` itself) with any `v` in `Model H` equals
v(0). -/
@[simp]
lemma modelInner_vacElem : he.modelInner vacElem v = v 0 := by
  rw [vacElem_eq_tauCeti]
  exact ReproducingModel.innerSL_vacuum v

/-- Let `B` be a multiplier action of `G` on the vacuum datum (`H`, `μ`, `e`) with cocycle `c`. On
the model space of `e` let ρ(y) = `heisenbergOp y` and vac = `vacElem`. If `T` is a bounded
surjective operator on the model that preserves `modelInner` and satisfies T ρ(y) = ρ(g • y) T, then
for every model vector `v`, ∫ v(y) ρ(g • y) vac dμ(y) = conj((T vac)(0)) · T v. So the overlap ⟨vac,
T vac⟩ = (T vac)(0) determines `T` when it is not zero. -/
lemma integrated_moveBy_vacElem_eq_smul (T : Model H →L[ℂ] Model H)
    (hT_surj : Function.Surjective T)
    (hT_inner : ∀ v w : Model H, modelInner (T v) (T w) = modelInner v w)
    (hT_heis : ∀ (y : W) (w : Model H), T (heisenbergOp y w) = heisenbergOp (g • y) (T w)) :
    (heisenbergRep.moveBy B g).integrated v vacElem = starRingEnd ℂ (T vacElem 0) • T v := by
  -- Apply `T` to `integrated_eq_smul` for the vector `u` with `T u = vac`.
  obtain ⟨u, hu⟩ : ∃ u : Model H, T u = vacElem := hT_surj vacElem
  have h_overlap : u 0 = starRingEnd ℂ (T vacElem 0) := by
    calc u 0 = modelInner vacElem u := (modelInner_vacElem u).symm
      _ = modelInner (T vacElem) vacElem := by rw [← hT_inner, hu]
      _ = starRingEnd ℂ (T vacElem 0) := by rw [← conj_modelInner, modelInner_vacElem]
  calc (heisenbergRep.moveBy B g).integrated v vacElem
      = (heisenbergRep.moveBy B g).integrated v (T u) := by rw [hu]
    _ = T (heisenbergRep.integrated v u) := (map_integrated heisenbergRep T v u hT_heis).symm
    _ = starRingEnd ℂ (T vacElem 0) • T v := by rw [integrated_eq_smul, map_smul, h_overlap]

/-- The cocycle relation: the product of the Weil operators of (gh)⁻¹, g and h, in this order, is
the scalar c(g, h). -/
lemma weilOp_inv_mul_weilOp_mul_weilOp : weilOp B (g * h)⁻¹ * weilOp B g * weilOp B h = c g h •
  1 := by
  simp_rw [weilOp_eq_tauCeti, ← B.cocycle_toTauCeti g h]
  exact ReproducingModel.weilOp_inv_mul_weilOp_mul_weilOp B.toTauCeti g h

omit [μ.IsAddHaarMeasure] in
/-- For a representation R on the model space and a vector v, the operator sending w in the model
space to ∫ w(y) R.ρ(y) v dμ(y) has norm at most ‖v‖. -/
lemma norm_integrated_flip_le (R : H.Rep (Model H)) : ‖R.integrated.flip v‖ ≤ ‖v‖ :=
  opNorm_le_bound _ (norm_nonneg v) fun w ↦
    ((R.integrated w).le_opNorm v).trans <| by
      simpa [mul_comm] using mul_le_mul_of_nonneg_right (R.norm_integrated_le w) (norm_nonneg v)

lemma weilOp_one : weilOp B 1 = 1 := by
  rw [weilOp_eq_tauCeti]
  exact ReproducingModel.weilOp_one B.toTauCeti

/-- Cocycle relation for the Weil operators ω = `weilOp B` of an action with cocycle c: if
c(g, 1) = 1 for all g, then ω(g)ω(h) = c(g, h)·ω(gh). -/
lemma weilOp_mul (hc_one : ∀ g : G, c g 1 = 1) (h : G) :
    weilOp B g * weilOp B h = c g h • weilOp B (g * h) := by
  simp_rw [weilOp_eq_tauCeti, ← B.cocycle_toTauCeti g h]
  exact ReproducingModel.weilOp_mul B.toTauCeti g h fun k ↦
    (B.cocycle_toTauCeti k 1).trans (hc_one k)

/-- If c(g, 1) = 1, the Weil operator `weilOp B g` preserves the inner product
`New.Heisenberg.IsVacuum.modelInner` (v, w) ↦ ∫ conj(v) w dμ of the model space. -/
lemma modelInner_weilOp (hc_one : c g 1 = 1) :
    modelInner (weilOp B g v) (weilOp B g w) = modelInner v w := by
  simp_rw [weilOp_eq_tauCeti]
  exact ReproducingModel.innerSL_weilOp B.toTauCeti g v w
    ((B.cocycle_toTauCeti g 1).trans hc_one)

/-- For an action `B` with cocycle c such that c(g, 1) = 1 for all g, the subgroup of those s in G
with c(g, s) = 1 for every g. -/
def cocycleRadical (h1 : ∀ g : G, c g 1 = 1) : Subgroup G :=
  (ReproducingModel.cocycleRadical B.toTauCeti fun g ↦ (B.cocycle_toTauCeti g 1).trans (h1 g)).copy
    {s : G | ∀ g : G, c g s = 1} <| by
      ext s
      simp [ReproducingModel.mem_cocycleRadical, B.cocycle_toTauCeti]

/-! ### The Weil representation -/

/-- The Weil representation of an action `A` with cocycle 1: the homomorphism
g ↦ (v ↦ Δ(g) ∫ v(y) ρ(g • y) vac dμ(y)) from G to the bounded operators on the model space, whose
value at g is `weilOp A g`. -/
def weilRep : G →* Model H →L[ℂ] Model H :=
  MonoidHom.mk ⟨weilOp A, weilOp_one A⟩ (by simp [weilOp_mul])

private lemma weilRep_eq_tauCeti :
    weilRep A g = ReproducingModel.weilRep e A.toTauCeti (fun g h ↦ A.cocycle_toTauCeti g h) g := by
  ext1 v
  exact (DFunLike.congr_fun (weilOp_eq_tauCeti A g) v).trans
    (ReproducingModel.weilRep_apply_eq A.toTauCeti g v _).symm

/-- Let `e` be a vacuum for `H` and `μ`, with model space `Model H` of integrable `v` satisfying
v(x) = ∫ v(y) β(y,x) e(x−y) dμ(y). Let `A` be an action of `G` on `W` that preserves β and μ and has
multiplier Δ and cocycle 1. Then each Weil operator `weilRep A g`, v ↦ Δ(g) ∫ v(y) ρ(g • y) e dμ(y),
preserves the pairing `modelInner` (v, w) = ∫ conj(v) w dμ. -/
lemma modelInner_weilRep : modelInner (weilRep A g v) (weilRep A g w) = modelInner v w := by
  simp [weilRep, modelInner_weilOp]

attribute [simp] weilOp modelInner_weilRep

/-- The Weil operator of `g` intertwines ρ(x) with ρ(g • x): ω(g) ρ(x) v = ρ(g • x) ω(g) v. Here
ρ(x) is `heisenbergOp x`, v ↦ (z ↦ β(x,z) v(z − x)), acting on the model space of the vacuum `e`.
`A` is an action of `G` on `W` that preserves β and μ and has multiplier Δ and cocycle 1. -/
lemma weilRep_heisenbergOp :
    weilRep A g (heisenbergOp x v) = heisenbergOp (g • x) (weilRep A g v) := by
  simp_rw [weilRep_eq_tauCeti, heisenbergOp_eq_tauCeti]
  exact ReproducingModel.weilRep_heisenbergRep A.toTauCeti g x v fun g h ↦ A.cocycle_toTauCeti g h

/-- The Weil operator of `g` sends `v` to Δ(g) ∫ v(g⁻¹ • y) ρ(y) vac dμ(y). -/
lemma weilRep_eq_integral :
    weilRep A g v = A.Δ g • ∫ y : W, v (g⁻¹ • y) • heisenbergOp y vacElem ∂μ := by
  -- Substitute `y ↦ g • y`, which preserves `μ`.
  rw [← (A.measurePreserving g).integral_comp' (f := .smul g)]
  simp only [MeasurableEquiv.smul_apply, inv_smul_smul]
  simp [weilRep, Rep.integrated_apply, Rep.moveBy]

/-- The value at `x` of the Weil operator of `g` on `v` is Δ(g) ∫ v(y) β(g • y, x) e(x − g • y)
dμ(y). -/
lemma weilRep_apply_eq_integral :
    weilRep A g v x = A.Δ g * ∫ y : W, v y * (H.β (g • y) x * e (x - g • y)) ∂μ := by
  rw [weilRep_eq_tauCeti]
  exact ReproducingModel.weilRep_apply A.toTauCeti g x v fun g h ↦ A.cocycle_toTauCeti g h

/-- Let `A` be a multiplier action of `G` on the vacuum datum (`H`, `μ`, `e`) with cocycle 1 and
multiplier `A.Δ`, and let ω = `weilRep A` be its Weil representation on the model space of `e`. If
`g` preserves the vacuum function, that is e(g • y) = e(y) for all `y`, then `g` acts by
substitution up to its multiplier: for every model vector `v`, `(ω g v) x = Δ g * v (g⁻¹ x)`. -/
lemma weilRep_apply_of_vacuum_smul (hg : ∀ y : W, e (g • y) = e y) (x : W) :
    weilRep A g v x = A.Δ g * v (g⁻¹ • x) := by
  rw [weilRep_eq_tauCeti]
  exact ReproducingModel.weilRep_apply_of_vacuum A.toTauCeti g x v
    (fun g h ↦ A.cocycle_toTauCeti g h) hg

/-- Let e be a vacuum for β and μ, and let `A` be a multiplier action of G on W with trivial
cocycle, that is, an action preserving β and μ with multiplier Δ. Let ω = `weilRep A` be the Weil
representation on `Model H` (the integrable v with v(x) = ∫ v(y) β(y,x) e(x−y) dμ(y)), given by
ω(g)v = Δ(g) ∫ v(y) ρ(g • y) e dμ(y). Then the overlap ⟨vac, ω(g) vac⟩ = (ω(g) vac)(0) of the Weil
operator of `g` is the inverse of conj Δ(g): conj Δ(g) · (ω(g) e)(0) = 1. -/
lemma conj_delta_mul_weilRep_vacElem : starRingEnd ℂ (A.Δ g) * weilRep A g vacElem 0 = 1 := by
  rw [weilRep_eq_tauCeti, vacElem_eq_tauCeti]
  exact ReproducingModel.conj_mul_weilRep_vacuum_apply_zero A.toTauCeti g
    fun g h ↦ A.cocycle_toTauCeti g h

/-- For a multiplier action `A` of `G` on `W` with cocycle 1, preserving β and `μ`, with vacuum `e`,
consider the Weil operator `weilRep A g` on the model space `Model H`, which carries the L¹ norm.
Its operator norm is at most the norm of `he.vacElem` (the vacuum `e` as an element of the model
space) times the modulus of the complex multiplier `A.Δ g`. -/
lemma norm_weilRep_le : ‖weilRep A g‖ ≤ ‖he.vacElem‖ * ‖A.Δ g‖ := by
  rw [weilRep_eq_tauCeti, vacElem_eq_tauCeti]
  exact ReproducingModel.norm_weilRep_le A.toTauCeti g fun g h ↦ A.cocycle_toTauCeti g h

/-- Let e be a vacuum for β and μ, and let `A` be a multiplier action of G on W with trivial
cocycle, that is, a continuous action preserving β and μ with multiplier Δ. For a first countable
group `G`, the map (g, v) ↦ `weilRep A g v` on `G × Model H` is continuous, where ω(g)v = Δ(g) ∫
v(y) ρ(g • y) e dμ(y) and `Model H` is the space of integrable v with v(x) = ∫ v(y) β(y,x) e(x−y)
dμ(y), with the L¹ norm. -/
@[fun_prop]
lemma continuous_weilRep [FirstCountableTopology G] :
    Continuous ↿(fun (g : G) (v : Model H) ↦ weilRep A g v) := by
  have h : (fun p : G × Model H ↦ weilRep A p.1 p.2) =
      fun p : G × ReproducingModel H.toDatum μ e ↦
        ReproducingModel.weilRep e A.toTauCeti (fun g h ↦ A.cocycle_toTauCeti g h) p.1 p.2 :=
    funext fun p ↦ DFunLike.congr_fun (weilRep_eq_tauCeti A p.1) p.2
  change Continuous fun p : G × Model H ↦ weilRep A p.1 p.2
  rw [h]
  exact ReproducingModel.continuous_weilRep A.toTauCeti fun g h ↦ A.cocycle_toTauCeti g h

attribute [irreducible] weilRep

end New.Heisenberg.IsVacuum

/-!
## Orthogonal sums, tensor products of model vectors and Wiener's bound

* `New.Heisenberg.IsVacuum.wiener_bound`: a sum of coefficients along a group homomorphism into `W₁`
  is bounded by the number of terms that fall in a fixed compact set, times a constant `M` and the
  norm of the model vector `v`.
* `New.Heisenberg.OrthogonalSum.tmul`: the tensor product of model vectors, a product of functions.
  It is multiplicative for inner products (`New.Heisenberg.OrthogonalSum.modelInner_tmul`).
* `New.Heisenberg.OrthogonalSum.weilRep_tmul`, `New.Heisenberg.Rep.integrated_tmul`: the tensor
  product is compatible with the Weil representation and with the integrated action.
-/

namespace New.Heisenberg

open MeasureTheory Heisenberg.Rep IsVacuum Measure ENNReal Set MultiplierAction TauCeti

variable {W : Type*} [AddCommGroup W] [TopologicalSpace W]
  {H : Heisenberg W} [MeasurableSpace W] [IsTopologicalAddGroup W] [BorelSpace W]
  [SecondCountableTopology W] {μ : Measure W} [μ.IsAddHaarMeasure] {e : W → ℂ}
  {W₁ : Type*} [AddCommGroup W₁] [TopologicalSpace W₁]
  {H₁ : Heisenberg W₁} [MeasurableSpace W₁] [IsTopologicalAddGroup W₁] [BorelSpace W₁]
  [SecondCountableTopology W₁] {μ₁ : Measure W₁} [μ₁.IsAddHaarMeasure] {e₁ : W₁ → ℂ}
  {W₂ : Type*} [AddCommGroup W₂] [TopologicalSpace W₂]
  {H₂ : Heisenberg W₂} [MeasurableSpace W₂] [IsTopologicalAddGroup W₂] [BorelSpace W₂]
  [SecondCountableTopology W₂] {μ₂ : Measure W₂} [μ₂.IsAddHaarMeasure] {e₂ : W₂ → ℂ}
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- An isomorphism φ: W₁ × W₂ → W of topological groups under which the bicharacter of H and the
function e are the products of those of the factors (β₁β₂, e₁e₂). -/
structure OrthogonalSum (H : Heisenberg W) (H₁ : Heisenberg W₁) (H₂ : Heisenberg W₂) (e : W → ℂ)
    [IsVacuum H₁ μ₁ e₁] [IsVacuum H₂ μ₂ e₂] where
  /-- The isomorphism of topological groups from `W₁ × W₂` onto `W`. -/
  equiv : W₁ × W₂ ≃ₜ+ W
  /-- Along `equiv`, the cocycle of `H` is the product of the cocycles of `H₁` and `H₂`. -/
  beta_equiv (x y : W₁ × W₂) : β H (equiv x) (equiv y) = β H₁ x.1 y.1 * β H₂ x.2 y.2
  /-- Along `equiv`, the function `e` is the product of the two vacua `e₁` and `e₂`. -/
  vac_equiv (x : W₁ × W₂) : e (equiv x) = e₁ x.1 * e₂ x.2

/-- View a `New.Heisenberg.OrthogonalSum` as a `TauCeti.HeisenbergDatum.OrthogonalSum`. -/
def OrthogonalSum.toTauCeti [IsVacuum H₁ μ₁ e₁] [IsVacuum H₂ μ₂ e₂]
    (S : OrthogonalSum H H₁ H₂ e) :
    H.toDatum.OrthogonalSum H₁.toDatum H₂.toDatum e e₁ e₂ :=
  ⟨S.equiv, S.beta_equiv, S.vac_equiv⟩

variable [he : IsVacuum H μ e] [he₁ : IsVacuum H₁ μ₁ e₁] [he₂ : IsVacuum H₂ μ₂ e₂]
  (S : OrthogonalSum H H₁ H₂ e) (R : H.Rep X) (v : Model H₁) (w : Model H₂) (x : W) (f : X)

/-! ### Wiener's bound -/

omit [he₁ : IsVacuum H₁ μ₁ e₁] in
/-- Wiener's bound for a bounded map `T` from the model space `Model H` to a Banach space `X`. Let
`u` be a model vector with `u 0 ≠ 0`, `κ : W₁ → W` a continuous homomorphism from a locally compact
Hausdorff group `W₁` with Haar measure `μ₁`, and `ρ = heisenbergOp`. Assume
`‖T ρ(z + κ x) u‖ = ‖g (t z + x)‖` for all `z` in `W` and `x` in `W₁`, with an integrable `g` on
`W₁` and some function `t : W → W₁`. Then there are a compact set `B` in `W₁` and a constant `M`
with the following property. For every additive group `I`, every homomorphism `φ : I → W₁` and
every `v`, the sum over `i` of `‖T ρ(κ (φ i)) v‖` is at most `M ‖v‖` times the number of `i` with
`φ i ∈ B`. -/
lemma IsVacuum.wiener_bound [LocallyCompactSpace W] [LocallyCompactSpace W₁]
    [T2Space W₁] (T : Model H →L[ℂ] X) {u : Model H} (hu : u 0 ≠ 0)
    (κ : W₁ →ₜ+ W) {g : W₁ → X} (hg : Integrable g μ₁) (t : W → W₁)
    (h_enorm_eq : ∀ (z : W) (x : W₁), ‖T (heisenbergOp (z + κ x) u)‖ₑ = ‖g (t z + x)‖ₑ) :
    ∃ B : Set W₁,
      IsCompact B ∧
      ∃ M : NNReal, ∀ {I : Type*} [AddGroup I] (φ : I →+ W₁) (v : Model H),
        ∑' i : I, ‖T (heisenbergOp (κ (φ i)) v)‖ₑ ≤ (φ ⁻¹' B).encard * M * ‖v‖ₑ := by
  simp_rw [heisenbergOp_eq_tauCeti] at h_enorm_eq ⊢
  exact ReproducingModel.exists_isCompact_tsum_enorm_le T hu κ hg t h_enorm_eq

/-! ### Tensor products along a splitting -/

/-- For a representation `R` of `H` on `X` and an orthogonal splitting `S` with `φ = S.equiv`, the
representation x ↦ R.ρ(φ(x, 0)) of `H₁` on `X`. -/
@[local simp]
def Rep.left : H₁.Rep X where
  ρ x := R.ρ (S.equiv (x, 0))
  mul := by simp [mul, OrthogonalSum.beta_equiv, ← map_add]
  norm_map := by simp [norm_map]
  cont := by fun_prop

/-- For a representation `R` of `H` on `X` and an orthogonal splitting `S` with `φ = S.equiv`, the
representation x ↦ R.ρ(φ(0, x)) of `H₂` on `X`. -/
@[local simp]
def Rep.right : H₂.Rep X where
  ρ x := R.ρ (S.equiv (0, x))
  mul := by simp [mul, OrthogonalSum.beta_equiv, ← map_add]
  norm_map := by simp [norm_map]
  cont := by fun_prop

/-- The tensor product of model vectors, a bounded bilinear map
`Model H₁ →L[ℂ] Model H₂ →L[ℂ] Model H`. With `φ = S.equiv`, it sends `v`, `w` to the iterated
integral `∫ v(y₁) ρ(φ(y₁, 0)) (∫ w(y₂) ρ(φ(0, y₂)) e dμ₂) dμ₁`, where `ρ` acts on the model space of
`e`. As a function it is `φ(x₁, x₂) ↦ v x₁ * w x₂`, see
`New.Heisenberg.OrthogonalSum.tmul_apply`. -/
noncomputable def OrthogonalSum.tmul : Model H₁ →L[ℂ] Model H₂ →L[ℂ] Model H :=
  (((heisenbergRep.left S).integrated).flip.comp
    ((heisenbergRep.right S).integrated.flip vacElem)).flip

omit [μ₁.IsAddHaarMeasure] [IsTopologicalAddGroup W₂] [BorelSpace W₂]
  [SecondCountableTopology W₂] [μ₂.IsAddHaarMeasure] in
private lemma OrthogonalSum.left_integrated_eq_tauCeti (v : Model H₁) (u : Model H) :
    (heisenbergRep.left S).integrated v u =
      ((ReproducingModel.heisenbergRep (β := H.toDatum) (μ := μ) (e := e)).restrictLeft
        S.toTauCeti).integrated μ₁ e₁ v u :=
  congrArg (fun R : H₁.toDatum.Representation (ReproducingModel H.toDatum μ e) ↦
    R.integrated μ₁ e₁ v u) <|
  representation_ext fun x (w : ReproducingModel H.toDatum μ e) ↦
    (congrArg (· w) (heisenbergOp_eq_tauCeti (S.equiv (x, 0)))).trans
      (ReproducingModel.heisenbergRep.restrictLeft_apply S.toTauCeti x w).symm

private lemma OrthogonalSum.tmul_eq_tauCeti : S.tmul = S.toTauCeti.tmul μ := by
  obtain ⟨r, hr1, hr2⟩ := S.toTauCeti.exists_restriction (μ := μ) (μ₁ := μ₁) (μ₂ := μ₂)
  ext1 v
  ext1 w
  set u : Model H := (heisenbergRep.right S).integrated w vacElem
  have hru : r u = w := ext fun b ↦
    (hr1 u b).trans <|
      ((heisenbergRep.right S).toTauCeti.map_integrated
        (valueAt (S.equiv (0, b))) w vacElem).trans <| by
        simp [Rep.toTauCeti, S.beta_equiv, ← map_sub, S.vac_equiv, he₁.apply_zero]
        exact w.integral_mul_beta_mul_eq b
  exact (S.left_integrated_eq_tauCeti v u).trans <|
    (hr2 v u).trans (congrArg (S.toTauCeti.tmul μ v) hru)

/-- Let `S` split `H` along `S.equiv : W₁ × W₂ ≃ W`, with `e` the product of the vacua `e₁` (for
`μ₁`) and `e₂` (for `μ₂`). Then `e` is a vacuum for `H` and the image of `μ₁ × μ₂` under
`S.equiv`. -/
lemma OrthogonalSum.isVacuum [LocallyCompactSpace W₁] [LocallyCompactSpace W₂] :
    H.IsVacuum ((μ₁.prod μ₂).map S.equiv) e := by
  have h := S.toTauCeti.isVacuum he₁.toTauCeti he₂.toTauCeti
  exact ⟨h.continuous, h.apply_zero, h.apply_neg, h.conj_apply, h.integral_mul_apply, h.integrable⟩

/-- Let `S` split `H` along `S.equiv : W₁ × W₂ ≃ W`, with `e` the product of the vacua `e₁` (for
`μ₁`) and `e₂` (for `μ₂`), and `e` a vacuum for `μ`. Then `S.equiv` sends `μ₁ × μ₂` to `μ`. -/
lemma OrthogonalSum.measurePreserving_equiv [LocallyCompactSpace W] [LocallyCompactSpace W₁]
    [LocallyCompactSpace W₂] : MeasurePreserving S.equiv (μ₁.prod μ₂) μ :=
  S.toTauCeti.measurePreserving_equiv

omit [CompleteSpace X] in
lemma OrthogonalSum.integral_eq_integral_prod [LocallyCompactSpace W] [LocallyCompactSpace W₁]
    [LocallyCompactSpace W₂] (f : W → X) :
    ∫ x : W, f x ∂μ = ∫ x : W₁ × W₂, f (S.equiv x) ∂μ₁.prod μ₂ :=
  S.toTauCeti.integral_eq_integral_prod f

/-- Let `S` be an orthogonal sum, that is, an isomorphism φ = `S.equiv` : W₁ × W₂ → W of topological
groups under which β and e are the products β₁β₂ and e₁e₂. Let v and w lie in the model spaces of e₁
and e₂, the integrable functions reproduced by e₁ and e₂. Read through φ, the tensor product
`S.tmul v w` is the function (x₁, x₂) ↦ v x₁ * w x₂, so its value at x is
v((φ⁻¹x).1) · w((φ⁻¹x).2). -/
@[local simp]
lemma OrthogonalSum.tmul_apply : S.tmul v w x = v (S.equiv.symm x).1 * w (S.equiv.symm x).2 := by
  rw [S.tmul_eq_tauCeti]
  exact S.toTauCeti.tmul_apply v w x

open scoped ComplexConjugate in
/-- Let `S` be an orthogonal sum, that is, an isomorphism φ: W₁ × W₂ → W of topological groups under
which β and e are the products β₁β₂ and e₁e₂. The tensor product `S.tmul` of model vectors (elements
of the reproducing spaces of e₁ and e₂) is multiplicative for the inner products ⟨v, w⟩ = ∫ conj(v)
w dμ: `⟨v ⊗ w, v' ⊗ w'⟩ = ⟨v, v'⟩ ⟨w, w'⟩`. -/
lemma OrthogonalSum.modelInner_tmul [LocallyCompactSpace W] [LocallyCompactSpace W₁]
    [LocallyCompactSpace W₂] (v v' : Model H₁) (w w' : Model H₂) :
    modelInner (S.tmul v w) (S.tmul v' w') = modelInner v v' * modelInner w w' := by
  rw [S.tmul_eq_tauCeti]
  exact S.toTauCeti.innerSL_tmul v v' w w'

/-- The product rule for the Weil representation of an orthogonal sum. Identify `W` with
`W₁ × W₂` by `S.equiv`, and let `A`, `A₁`, `A₂` be actions with cocycle 1 of groups `G`, `G₁`,
`G₂` on `W`, `W₁`, `W₂`. If `g` acts as `(g₁, g₂)` and its multiplier is the product of theirs,
then the Weil operator of `g` is the tensor product of those of `g₁` and `g₂`. -/
lemma OrthogonalSum.weilRep_tmul [LocallyCompactSpace W] [LocallyCompactSpace W₁]
    [LocallyCompactSpace W₂] {G G₁ G₂ : Type*} [Group G] [TopologicalSpace G]
    [DistribMulAction G W] [ContinuousSMul G W] [Group G₁] [TopologicalSpace G₁]
    [DistribMulAction G₁ W₁] [ContinuousSMul G₁ W₁] [Group G₂] [TopologicalSpace G₂]
    [DistribMulAction G₂ W₂] [ContinuousSMul G₂ W₂] (A : H.MultiplierAction μ e G)
    (A₁ : H₁.MultiplierAction μ₁ e₁ G₁) (A₂ : H₂.MultiplierAction μ₂ e₂ G₂) {g : G} {g₁ : G₁}
    {g₂ : G₂} (h_delta_eq : Δ A g = Δ A₁ g₁ * Δ A₂ g₂)
    (h_smul_equiv : ∀ x : W₁ × W₂, g • S.equiv x = S.equiv (g₁ • x.1, g₂ • x.2)) (v : Model H₁)
    (w : Model H₂) :
    weilRep A g (S.tmul v w) = S.tmul (weilRep A₁ g₁ v) (weilRep A₂ g₂ w) := by
  simp_rw [S.tmul_eq_tauCeti, weilRep_eq_tauCeti]
  exact S.toTauCeti.weilRep_tmul v w A.toTauCeti A₁.toTauCeti A₂.toTauCeti
    (fun g h ↦ A.cocycle_toTauCeti g h) (fun g h ↦ A₁.cocycle_toTauCeti g h)
    (fun g h ↦ A₂.cocycle_toTauCeti g h) h_delta_eq h_smul_equiv

/-- Integrating `v ⊗ w` against `R` is integrating `w` against the restriction `R.right S` of `R` to
`W₂`, then `v` against its restriction `R.left S` to `W₁`. -/
lemma Rep.integrated_tmul [LocallyCompactSpace W] [LocallyCompactSpace W₁]
    [LocallyCompactSpace W₂] :
    R.integrated (S.tmul v w) f = (R.left S).integrated v ((R.right S).integrated w f) := by
  -- Rewrite the LHS via Fubini's theorem and simplify the iterated integral on the RHS.
  rw [integrated_apply, (R.left S).integrated_apply, S.integral_eq_integral_prod]
  simp_rw [S.tmul_apply, S.equiv.symm_apply_apply]
  rw [integral_prod (fun x : W₁ × W₂ ↦ (v x.1 * w x.2) • R.ρ (S.equiv x) f)
    ((v.integrable.mul_prod w.integrable).smul_bdd ‖f‖ (by fun_prop) (by simp [norm_map]))]
  simp_rw [map_integrated_eq_integral, ← integral_smul, smul_smul]
  simp [mul, OrthogonalSum.beta_equiv, ← map_add]

/-- Let `S` be an orthogonal sum: an isomorphism φ : W₁ × W₂ ≃ W of topological groups under which
β = β₁β₂ and e = e₁e₂. Then the tensor product `S.tmul`, which sends `v`, `w` to the function φ(x₁,
x₂) ↦ v(x₁) w(x₂) in `Model H`, takes the pair of vacua `vacElem` (e₁ and e₂) to the vacuum
`vacElem` (e). -/
lemma OrthogonalSum.tmul_vacElem : S.tmul vacElem vacElem = vacElem := by
  simp_rw [S.tmul_eq_tauCeti, vacElem_eq_tauCeti]
  exact S.toTauCeti.tmul_vacuum

/-- Let `S` be an orthogonal sum φ : W₁ × W₂ ≃ W, under which β = β₁β₂ and e = e₁e₂, and let
v ⊗ w = `S.tmul v w` be the model vector φ(x₁, x₂) ↦ v(x₁) w(x₂). Then ρ(x) of `v ⊗ w` is ρ₁(x₁)
v ⊗ ρ₂(x₂) w, where (x₁, x₂) = `S.equiv.symm x` and ρ(x) is `heisenbergOp x`, v ↦ (z ↦ β(x,z)
v(z − x)). -/
lemma OrthogonalSum.heisenbergOp_tmul :
    IsVacuum.heisenbergOp x (S.tmul v w) =
      S.tmul (IsVacuum.heisenbergOp (S.equiv.symm x).1 v)
        (IsVacuum.heisenbergOp (S.equiv.symm x).2 w) := by
  simp_rw [S.tmul_eq_tauCeti, heisenbergOp_eq_tauCeti]
  exact S.toTauCeti.heisenbergRep_tmul v w x

/-- A translate of the vacuum is the product of translates of the two vacua. -/
lemma OrthogonalSum.heisenbergOp_equiv_vacElem (a : W₁) (b : W₂) :
    IsVacuum.heisenbergOp (S.equiv (a, b)) vacElem =
      S.tmul (IsVacuum.heisenbergOp a vacElem) (IsVacuum.heisenbergOp b vacElem) := by
  simp_rw [S.tmul_eq_tauCeti, heisenbergOp_eq_tauCeti, vacElem_eq_tauCeti]
  exact S.toTauCeti.heisenbergRep_equiv_vacuum (μ := μ) (μ₁ := μ₁) (μ₂ := μ₂) a b

/-- Restriction of functions to `W₂` along `φ = S.equiv` is a bounded map `r` from the model of `e`
to the model of `e₂`, and ∫ v(y) ρ(φ(y, 0)) u dμ₁(y) = v ⊗ r u for `v` in the model of `e₁` and
`u` in the model of `e`. -/
lemma OrthogonalSum.exists_restriction :
    ∃ r : Model H →L[ℂ] Model H₂,
      (∀ (u : Model H) (b : W₂), r u b = u (S.equiv (0, b))) ∧
      ∀ (v : Model H₁) (u : Model H), (heisenbergRep.left S).integrated v u = S.tmul v (r u) := by
  obtain ⟨r, hr1, hr2⟩ := S.toTauCeti.exists_restriction (μ := μ) (μ₁ := μ₁) (μ₂ := μ₂)
  exact ⟨r, hr1, fun v u ↦
    (S.left_integrated_eq_tauCeti v u).trans <| (hr2 v u).trans <|
      congrArg (fun f : Model H₁ →L[ℂ] Model H₂ →L[ℂ] Model H ↦ f v (r u)) S.tmul_eq_tauCeti.symm⟩

end New.Heisenberg

/-!
## Transport of the model along a linear or conjugate linear isomorphism

Let `e`, `e'` be vacua (`New.Heisenberg.IsVacuum`) for Heisenberg cocycles on `W`, `W'`, and let
`φ : W' ≃ W` be an isomorphism of topological groups that matches the vacua and matches the cocycles
up to `σ`, the identity or the conjugation of `ℂ`. `New.Heisenberg.IsVacuum.transport` is the
`σ`-semilinear map `v ↦ σ ∘ v ∘ φ` between the models `New.Heisenberg.IsVacuum.Model` (integrable
functions reproduced by the vacuum kernel); `New.Heisenberg.IsVacuum.map_integral_and_map_vacuum` is
the change of variables behind it.
-/

section ModelTransport

open MeasureTheory Measure Complex TauCeti

namespace New.Heisenberg.IsVacuum

variable {W W' : Type*} [AddCommGroup W] [TopologicalSpace W] [MeasurableSpace W]
  [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W] [LocallyCompactSpace W]
  [AddCommGroup W'] [TopologicalSpace W'] [MeasurableSpace W'] [IsTopologicalAddGroup W']
  [BorelSpace W']
  {H : Heisenberg W} {μ : Measure W} {e : W → ℂ} {H' : Heisenberg W'} {μ' : Measure W'}
  {e' : W' → ℂ} [IsAddHaarMeasure μ] [IsAddHaarMeasure μ'] [he : IsVacuum H μ e]
  [he' : IsVacuum H' μ' e'] {σ : ℂ →+* ℂ} [RingHomIsometric σ] {φ : W' ≃ₜ+ W}

include he he'

variable (H H') in
/-- Let `e`, `e'` be vacua for the Haar measures `μ`, `μ'`. An isomorphism of topological groups
`φ : W' ≃ W` with `e ∘ φ = e'` carries `μ'` to `μ`. -/
lemma measurePreserving_equiv (hφ : ∀ x : W', e (φ x) = e' x) : MeasurePreserving φ μ' μ :=
  ReproducingModel.measurePreserving_of_vacuum (β := H.toDatum) (β' := H'.toDatum) μ μ' hφ

variable (H H') in
/-- Let `e`, `e'` be vacua for the Haar measures `μ`, `μ'`. Change of variables along an isometric
ring map `σ` of `ℂ` (the identity or the conjugation) and an isomorphism `φ : W' ≃ W` with
`e ∘ φ = e'`: `σ (∫ f dμ) = ∫ σ ∘ f ∘ φ dμ'` for every `f`. -/
lemma map_integral_eq_integral_comp_equiv (hφ : ∀ x : W', e (φ x) = e' x) (f : W → ℂ) :
    σ (integral μ f) = ∫ x : W', σ (f (φ x)) ∂μ' := by
  -- `φ` preserves the measures, and `σ`, the identity or the conjugation, commutes with integrals.
  rw [← (measurePreserving_equiv H H' hφ).integral_comp φ.measurableEmbedding f]
  rcases ringHom_eq_id_or_conj_of_continuous σ.isometry.continuous with rfl | rfl
  · simp
  · simp [integral_conj]

omit he in
variable (H' μ') in
omit [MeasurableSpace W] [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W]
  [LocallyCompactSpace W] [IsTopologicalAddGroup W'] [BorelSpace W'] [IsAddHaarMeasure μ'] in
/-- For an isometric ring map `σ` of `ℂ` and `φ : W' ≃ W` with `e ∘ φ = e'`, also `σ ∘ e ∘ φ = e'`,
as the vacuum `e'` of `H'` and `μ'` is real-valued. -/
lemma map_vacuum_comp_equiv (hφ : ∀ x : W', e (φ x) = e' x) (x : W') : σ (e (φ x)) = e' x := by
  rcases ringHom_eq_id_or_conj_of_continuous σ.isometry.continuous with rfl | rfl
  · simp [hφ]
  · simp [hφ, he'.conj_apply]

variable (H H') in
/-- Change of variables along an isometric ring map `σ` and a topological group isomorphism
`φ : W' ≃ W` that matches the vacua. -/
lemma map_integral_and_map_vacuum (hφ : ∀ x : W', e (φ x) = e' x) :
    (∀ f : W → ℂ, σ (integral μ f) = ∫ x : W', σ (f (φ x)) ∂μ') ∧
      ∀ x : W', σ (e (φ x)) = e' x :=
  ⟨map_integral_eq_integral_comp_equiv H H' hφ, map_vacuum_comp_equiv H' μ' hφ⟩

/-- For a topological isomorphism `φ : W' ≃ W` matching the vacua and, up to `σ`, the
bicharacters, the continuous `σ`-semilinear map `v ↦ σ ∘ v ∘ φ` between the reproducing spaces. -/
noncomputable def transport (hβ : ∀ x y : W', σ (H.β (φ x) (φ y)) = H'.β x y)
    (hφ : ∀ x : W', e (φ x) = e' x) : Model H →SL[σ] Model H' :=
  let T := ReproducingModel.transport (β := H.toDatum) (β' := H'.toDatum) μ μ' hβ hφ
  LinearMap.mkContinuous
    { toFun v := ⟨fun x ↦ σ (v (φ x)),
        (congrArg (· ∈ reproducingSubmodule H'.toDatum μ' e')
          (funext (ReproducingModel.transport_apply hβ hφ v))).mp (T v).property⟩
      map_add' v w := ext fun x ↦ map_add σ (v (φ x)) (w (φ x))
      map_smul' c v := ext fun x ↦ map_mul σ c (v (φ x)) }
    1 fun v ↦
      have h_eq : (⟨fun x ↦ σ (v (φ x)),
          (congrArg (· ∈ reproducingSubmodule H'.toDatum μ' e')
            (funext (ReproducingModel.transport_apply hβ hφ v))).mp (T v).property⟩ : Model H') =
          T v := ext fun x ↦ (ReproducingModel.transport_apply hβ hφ v x).symm
      le_of_eq (((congrArg (norm : Model H' → ℝ) h_eq).trans
        (ReproducingModel.norm_transport hβ hφ v)).trans (one_mul ‖v‖).symm)

@[simp]
lemma transport_apply (hβ : ∀ x y : W', σ (H.β (φ x) (φ y)) = H'.β x y)
    (hφ : ∀ x : W', e (φ x) = e' x) (v : Model H) (x : W') :
    transport hβ hφ v x = σ (v (φ x)) := rfl

end New.Heisenberg.IsVacuum

end ModelTransport

end
