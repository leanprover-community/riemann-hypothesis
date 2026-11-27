module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.PiTensorProduct
public import Lib.Speed
public import TauCeti.Analysis.HeisenbergModel.Model

/-!
# Heisenberg cocycles, vacua, the reproducing model and Schur's lemma

This file sets up an abstract setting for the Weil representation that covers the real places
and the adeles. The data are a topological abelian group `W` with a measure `μ`, a Heisenberg
cocycle `β` on `W`, and a vacuum `e` for it. It also defines multiplier actions of a group `G` on
`W`. The vacuum defines a space of integrable functions reproduced by a kernel, on which `W` acts
by a Heisenberg representation `ρ`. The file proves superposition and Schur's lemma for this model.

## Main definitions and results

* `New.Heisenberg W`: a continuous alternating bicharacter `β`, the cocycle of a Heisenberg group.
* `New.Heisenberg.IsVacuum`: a function `e` on `W` that plays the part of the matrix coefficient of
  a vacuum vector (a Gaussian, or a lattice indicator times a semicharacter).
* `New.Heisenberg.MultiplierAction`: a group `G` acting on `W` by symmetries, with a multiplier `Δ`
  that turns a double integral of `e` and `β` attached to the action into a given `c` (by default
  `1`).
* `New.Heisenberg.IsVacuum.Model`: integrable v with v x = ∫ v y β(y, x) e(x - y), a Banach space
  for the L¹ norm, with the representation `New.Heisenberg.IsVacuum.heisenbergRep`, the vector
  `New.Heisenberg.IsVacuum.vacElem` and the form `New.Heisenberg.IsVacuum.modelInner`.
* `New.Heisenberg.IsVacuum.eq_smul_one_of_commute`,
  `New.Heisenberg.IsVacuum.integral_form_eq_mul_modelInner`: Schur's lemma. A bounded operator that
  commutes with the representation is a scalar, and an invariant form given as an integral of
  bounded forms is a multiple of the inner product.

## Relation to the literature

Known; see `Lib.Weil.Construction.WeilOperators` for sources.
-/

@[expose] public section

noncomputable section

/-!
## Heisenberg cocycles, representations, vacua and multiplier actions

* `New.Heisenberg.Rep`: isometric operators `ρ x` with `ρ x ∘ ρ y = β x y • ρ (x + y)`.
-/

section Heisenberg

open MeasureTheory ComplexConjugate

variable (W : Type*) [AddCommGroup W] [TopologicalSpace W]

/-- A continuous function β on W × W, W an abelian group with a topology, with values of modulus
one, multiplicative in each variable, and β(x,x) = 1. -/
structure New.Heisenberg where
  /-- The bicharacter `β x y`, a complex-valued function on `W × W`. -/
  β : W → W → ℂ
  /-- `β` is multiplicative in its first variable. -/
  add_left (x x' y : W) : β (x + x') y = β x y * β x' y
  /-- `β` is multiplicative in its second variable. -/
  add_right (x y y' : W) : β x (y + y') = β x y * β x y'
  /-- `β` is alternating: it is `1` on the diagonal. -/
  self_eq_one (x : W) : β x x = 1
  /-- The values of `β` have modulus one. -/
  norm_eq_one (x y : W) : ‖β x y‖ = 1
  /-- `β` is jointly continuous on `W × W`. -/
  cont : Continuous fun p : W × W ↦ β p.1 p.2

namespace New.Heisenberg

variable {W} [MeasurableSpace W]
  (H : Heisenberg W) (μ : outParam (Measure W)) (e : outParam (W → ℂ))

/-- View a `New.Heisenberg` datum as a `TauCeti.HeisenbergDatum`. -/
def toDatum : TauCeti.HeisenbergDatum W :=
  ⟨H.β, H.add_left, H.add_right, H.self_eq_one, H.norm_eq_one, H.cont⟩

/-- A representation of the Heisenberg datum `H`: linear isometries `ρ x`, `x : W`, of a complex
normed space `X`, with `ρ x ∘ ρ y = β x y • ρ (x + y)` and `(x, v) ↦ ρ x v` continuous. -/
structure Rep (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] where
  /-- The operator `ρ x` on `X` attached to the vector `x` of `W`. -/
  ρ : W → X →L[ℂ] X
  /-- The Heisenberg relation `ρ x ∘ ρ y = β x y • ρ (x + y)`. -/
  mul (x y : W) (v : X) : ρ x (ρ y v) = β H x y • ρ (x + y) v
  /-- Each `ρ x` is an isometry. -/
  norm_map (x : W) (v : X) : ‖ρ x v‖ = ‖v‖
  /-- The map `(x, v) ↦ ρ x v` is jointly continuous on `W × X`. -/
  cont : Continuous fun p : W × X ↦ ρ p.1 p.2

/-- View a `New.Heisenberg.Rep` as a `TauCeti.HeisenbergDatum.Representation`. -/
def Rep.toTauCeti {H : Heisenberg W} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (R : H.Rep X) : H.toDatum.Representation X :=
  ⟨R.ρ, R.mul, R.norm_map, R.cont⟩

omit [MeasurableSpace W] in
lemma representation_ext {H : Heisenberg W} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {ϱ₁ ϱ₂ : H.toDatum.Representation X} (h : ∀ x v, ϱ₁ x v = ϱ₂ x v) : ϱ₁ = ϱ₂ := by
  cases ϱ₁; cases ϱ₂; congr; ext x v; exact h x v

/-- The function e: W → ℂ is a vacuum for β and μ: continuous, integrable, even, real-valued,
e(0) = 1, and ∫ e(z)e(x−y−z)β(z,y)β(z+y,x) dμ(z) = e(y)e(x). -/
class IsVacuum where
  /-- `e` is continuous. -/
  cont : Continuous e
  /-- `e` is normalized to take the value `1` at the origin. -/
  apply_zero : e 0 = 1
  /-- `e` is even. -/
  apply_neg (x : W) : e (-x) = e x
  /-- `e` is real-valued. -/
  conj_apply (x : W) : conj (e x) = e x
  /-- The key identity: the convolution of `e` with itself at `x - y`, twisted by
  `β z y * β (z + y) x`, is `e y * e x`. -/
  twisted_conv (y x : W) :
      ∫ z : W, e z * (β H z y * (β H (z + y) x * e (x - (z + y)))) ∂μ = e y * e x
  /-- `e` is integrable for `μ`. -/
  integrable : Integrable e μ

/-- View a `New.Heisenberg.IsVacuum` instance as a `TauCeti.HeisenbergDatum.IsVacuum` instance. -/
instance IsVacuum.toTauCeti {H : Heisenberg W} {μ : Measure W} {e : W → ℂ} [he : H.IsVacuum μ e] :
    H.toDatum.IsVacuum μ e :=
  ⟨he.cont, he.integrable, he.apply_zero, he.apply_neg, he.conj_apply, he.twisted_conv⟩

/-- The action of G on W preserves β and μ, and a continuous multiplier Δ: G → ℂ has Δ(1) = 1,
Δ(g⁻¹) = conj Δ(g), Δ(g)Δ(h)Δ((gh)⁻¹) ∬ e(hx)e(ghy)β(x,y)e(x+y) = c(g,h). -/
structure MultiplierAction (G : Type*) [Group G] [TopologicalSpace G] [DistribMulAction G W]
    (c : G → G → ℂ := 1) where
  /-- The action of `G` on `W` preserves `β`. -/
  beta_smul (g : G) (x y : W) : β H (g • x) (g • y) = β H x y
  /-- The action of `G` on `W` preserves the measure `μ`. -/
  measurePreserving (g : G) : MeasurePreserving (g • ·) μ μ
  /-- The multiplier `Δ`, a complex-valued function on `G`. -/
  Δ : G → ℂ
  /-- The multiplier is continuous. -/
  continuous_delta : Continuous Δ
  /-- The multiplier is `1` at the identity. -/
  Δ_one : Δ 1 = 1
  /-- The multiplier takes inverses to complex conjugates. -/
  Δ_inv (g : G) : Δ g⁻¹ = conj (Δ g)
  /-- The double integral of `e (h • x) * e ((g * h) • y) * β x y * e (x + y)` times
  `Δ g * Δ h * Δ (g * h)⁻¹` is the prescribed value `c g h` (by default `1`). -/
  cocycle (g h : G) :
      Δ g * Δ h * Δ (g * h)⁻¹ *
        ∫ x : W, ∫ y : W, e (h • x) * e ((g * h) • y) * β H x y * e (x + y) ∂μ ∂μ = c g h

/-- View a `New.Heisenberg.MultiplierAction` as a `TauCeti.HeisenbergDatum.Multiplier`. -/
def MultiplierAction.toTauCeti {H : Heisenberg W} {μ : Measure W} {e : W → ℂ}
    {G : Type*} [Group G] [TopologicalSpace G] [DistribMulAction G W] {c : G → G → ℂ}
    (A : H.MultiplierAction μ e G c) : H.toDatum.Multiplier μ G :=
  ⟨A.Δ, A.beta_smul, A.measurePreserving, A.continuous_delta, A.Δ_one, A.Δ_inv⟩

lemma MultiplierAction.cocycle_toTauCeti {H : Heisenberg W} {μ : Measure W} {e : W → ℂ}
    {G : Type*} [Group G] [TopologicalSpace G] [DistribMulAction G W] {c : G → G → ℂ}
    (A : H.MultiplierAction μ e G c) (g h : G) : A.toTauCeti.cocycle e g h = c g h :=
  (A.toTauCeti.cocycle_def e g h).trans (A.cocycle g h)

end New.Heisenberg

end Heisenberg

/-!
## First properties of cocycles, representations and vacua

* `New.Heisenberg.IsVacuum.integral_norm_sq_eq_one`, `New.Heisenberg.IsVacuum.norm_le_one`: a vacuum
  has `L²` norm one and is bounded by one.
-/

section HeisenbergBasic

open MeasureTheory Complex

namespace New.Heisenberg

variable {W : Type*} [AddCommGroup W] [TopologicalSpace W] {H : Heisenberg W}
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  (R : H.Rep X) (x y : W) (w : X) {mW : MeasurableSpace W} {μ : Measure W} {e : W → ℂ}

attribute [fun_prop] cont Rep.cont

@[simp]
lemma beta_ne_zero : H.β x y ≠ 0 := H.toDatum.apply_ne_zero x y

@[simp]
lemma beta_zero_left : H.β 0 y = 1 := H.toDatum.zero_apply y

@[simp]
lemma beta_mul_beta : H.β x y * H.β y x = 1 := H.toDatum.apply_mul_apply_swap x y

@[simp]
lemma beta_zero_right : H.β y 0 = 1 := H.toDatum.apply_zero y

@[simp]
lemma beta_neg_left : H.β (-x) y = H.β y x := H.toDatum.neg_apply x y

@[simp]
lemma beta_neg_right : H.β x (-y) = H.β y x := H.toDatum.apply_neg x y

@[simp]
lemma conj_beta : starRingEnd ℂ (H.β x y) = H.β y x := H.toDatum.conj_apply x y

/-- In a Heisenberg representation, `ρ 0` is the identity. -/
@[simp]
lemma Rep.rho_zero_apply : R.ρ 0 w = w := R.toTauCeti.zero_apply w

/-- A vacuum has `L²` norm one. -/
lemma IsVacuum.integral_norm_sq_eq_one (he : H.IsVacuum μ e) : ∫ x : W, ‖e x‖ ^ 2 ∂μ = 1 :=
  he.toTauCeti.integral_norm_sq_eq_one

/-- A vacuum is bounded by one in absolute value. -/
lemma IsVacuum.norm_le_one (he : H.IsVacuum μ e) : ‖e x‖ ≤ 1 :=
  he.toTauCeti.norm_le_one x

end New.Heisenberg

end HeisenbergBasic

/-!
## A Heisenberg representation twisted by a group element

A group `G` acting on `W` and preserving the bicharacter `β` (a part of
`New.Heisenberg.MultiplierAction`) twists any Heisenberg representation: `New.Heisenberg.Rep.moveBy`
is `x ↦ ρ (g • x)`.
-/

namespace New.Heisenberg.Rep

variable {W : Type*} [AddCommGroup W] [TopologicalSpace W]
  {H : Heisenberg W} [MeasurableSpace W]
  {μ : MeasureTheory.Measure W} {e : W → ℂ}
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (R : H.Rep X)
  {G : Type*} [Group G] [TopologicalSpace G] [DistribMulAction G W] [ContinuousSMul G W]
  {c : G → G → ℂ} (A : H.MultiplierAction μ e G c) (g : G)

/-- The representation `x ↦ R.ρ (g • x)`; it is again a representation of `H` because `g` preserves
`β`. -/
@[simps]
def moveBy : H.Rep X where
  ρ := (R.ρ <| g • ·)
  mul := by simp [A.beta_smul, mul]
  norm_map := by simp [norm_map]
  cont := by fun_prop

@[simp]
lemma moveBy_one : R.moveBy A 1 = R := by simp [moveBy]

end New.Heisenberg.Rep

/-!
## The L¹ reproducing model of a vacuum and Schur's lemma

* `New.Heisenberg.Rep.integrated`: the integrated action ∫ v y • R.ρ y f on any representation R.
* `New.Heisenberg.IsVacuum.map_eq_integral`, `New.Heisenberg.IsVacuum.hom_ext` (superposition):
  every v is the integral of the translates of the vacuum against v, so these translates determine
  bounded maps.
* `New.Heisenberg.IsVacuum.integrated_eq_smul`: in the model itself, the integrated action of v on
  w is w(0) • v.
-/

section Model

open MeasureTheory ComplexConjugate Subtype LinearMap DFunLike TauCeti

namespace New.Heisenberg

variable {W : Type*} [AddCommGroup W] [TopologicalSpace W]
  (H : Heisenberg W) [MeasurableSpace W] [IsTopologicalAddGroup W] [BorelSpace W]
  [SecondCountableTopology W] {μ : Measure W}
  {e : W → ℂ} [he : IsVacuum H μ e]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-! ### The space and its norm -/

variable {H} in
omit [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W] in
include he in
/-- The kernel β(y, x) e(x - y) of the reproducing identity of a vacuum e has norm at most one. -/
lemma IsVacuum.norm_beta_mul_le_one (x y : W) : ‖H.β y x * e (x - y)‖ ≤ 1 :=
  he.toTauCeti.norm_kernel_le_one x y

variable {H} in
include he in
omit [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W] in
/-- Multiplication by the kernel β(y, x) e(x - y) does not increase the absolute value. -/
lemma IsVacuum.norm_mul_beta_mul_le (x y : W) (a : ℂ) : ‖a * (H.β y x * e (x - y))‖ ≤ ‖a‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg a) (norm_beta_mul_le_one x y)

omit [SecondCountableTopology W] in
/-- For an integrable f, the function y ↦ f(y) β(y, x) e(x - y) (f times the kernel of the
reproducing identity) is integrable: the kernel is continuous and has norm at most one. -/
lemma IsVacuum.integrable_mul_kernel (x : W) {f : W → ℂ} (hf : Integrable f μ) :
    Integrable (fun y : W ↦ f y * (H.β y x * e (x - y))) μ :=
  he.toTauCeti.integrable_mul_kernel x hf

variable [μ.IsAddHaarMeasure]

/-- The complex subspace of integrable functions v on W satisfying the reproducing identity v(x) = ∫
v(y) β(y,x) e(x−y) dμ(y) for every x. -/
def IsVacuum.modelSubmodule : Submodule ℂ (W → ℂ) :=
  reproducingSubmodule H.toDatum μ e

/-- The space of integrable v with v(x) = ∫ v(y) β(y,x) e(x−y) dμ(y), as a type; it carries the
L¹ norm. -/
def IsVacuum.Model : Type _ := ↥he.modelSubmodule

deriving instance AddCommGroup, Module ℂ for (he.Model)

-- An element of the model is read as a function on `W`.
instance : CoeFun he.Model fun _ ↦ W → ℂ := ⟨val⟩

/-- The complex-linear map sending a function in the reproducing space to its class in L¹(W, μ). -/
def IsVacuum.toL1 : he.Model →ₗ[ℂ] W →₁[μ] ℂ :=
  ReproducingModel.toL1

instance : NormedAddCommGroup he.Model :=
  inferInstanceAs (NormedAddCommGroup (ReproducingModel H.toDatum μ e))

instance : NormedSpace ℂ he.Model :=
  inferInstanceAs (NormedSpace ℂ (ReproducingModel H.toDatum μ e))

namespace IsVacuum

variable {H} (x : W) (v w : Model H)

section

omit [μ.IsAddHaarMeasure] [SecondCountableTopology W]

@[simp]
lemma add_apply : (v + w) x = v x + w x := rfl

@[simp]
lemma smul_apply (c : ℂ) : (c • v) x = c * v x := rfl

@[simp]
lemma zero_apply : (0 : Model H) x = 0 := rfl

@[ext]
lemma ext {v w : Model H} : (∀ x : W, v x = w x) → v = w := Subtype.ext ∘ funext

/-- For a vacuum `e` of `H` and `μ`, the model `Model H` is the space of integrable `v` with
v(x) = ∫ v(y) β(y,x) e(x−y) dμ(y). The norm of the model is the L¹ norm ∫ ‖v x‖ dμ. -/
lemma norm_eq_integral_norm : ‖v‖ = ∫ x : W, ‖v x‖ ∂μ :=
  ReproducingModel.norm_eq_integral_norm v

lemma Model.integrable : Integrable (⇑v) μ :=
  ReproducingModel.integrable v

/-- The reproducing identity of an element v of the model: ∫ v(y) β(y, x) e(x - y) dμ(y) = v(x). -/
lemma Model.integral_mul_beta_mul_eq : ∫ y : W, v y * (H.β y x * e (x - y)) ∂μ = v x :=
  ReproducingModel.integral_mul_kernel v x

lemma mem_modelSubmodule_iff {f : W → ℂ} :
    f ∈ he.modelSubmodule ↔
      Integrable f μ ∧ ∀ x : W, ∫ y : W, f y * (H.β y x * e (x - y)) ∂μ = f x :=
  ⟨fun hf ↦ ⟨ReproducingModel.integrable ⟨f, hf⟩, ReproducingModel.integral_mul_kernel ⟨f, hf⟩⟩,
    fun ⟨h1, h2⟩ ↦
      (funext fun x ↦ ReproducingModel.mk_apply (β := H.toDatum) (e := e) x f h1 h2) ▸
        (ReproducingModel.mk (β := H.toDatum) (e := e) f h1 h2).property⟩

/-- Every function in the reproducing space is bounded by its L¹ norm. -/
lemma norm_apply_le : ‖v x‖ ≤ ‖v‖ :=
  ReproducingModel.norm_apply_le v x

end

omit [μ.IsAddHaarMeasure] in
/-- Every function in the reproducing space is continuous. -/
@[fun_prop]
lemma continuous : Continuous v :=
  ReproducingModel.continuous v

/-! ### The representation, the vacuum vector and the inner product -/

/-- The Heisenberg representation on the model: y acts by the L¹ isometry that sends v to
x ↦ β(y, x) v(x - y), see `New.Heisenberg.IsVacuum.heisenbergOp_apply`. -/
def heisenbergRep : H.Rep he.Model :=
  let R := ReproducingModel.heisenbergRep (β := H.toDatum) (μ := μ) (e := e)
  ⟨R.toFun, R.apply_apply, R.norm_apply, R.continuous_uncurry⟩

/-- For `x` in `W`, the bounded operator on the reproducing space sending `v` to the function
`z ↦ β x z * v (z - x)`. -/
abbrev heisenbergOp : Model H →L[ℂ] Model H := heisenbergRep.ρ x

/-- The function e itself, viewed as an element of the reproducing space it defines. -/
def vacElem : Model H :=
  ⟨e, (congrArg (· ∈ reproducingSubmodule H.toDatum μ e)
    (funext (ReproducingModel.vacuum_apply (β := H.toDatum) (μ := μ) (e := e)))).mp
    ReproducingModel.vacuum.property⟩

/-- The continuous linear functional on `Model H` that evaluates an element at the point `x`. -/
def valueAt : Model H →L[ℂ] ℂ :=
  mkContinuous ⟨⟨(· x), fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩ 1 fun v ↦
    (one_mul ‖v‖).symm ▸ norm_apply_le x v

/-- The bounded sesquilinear form on the reproducing space sending (v, w) to ∫ conj(v) w dμ,
conjugate-linear in the first argument. -/
def modelInner : Model H →L⋆[ℂ] Model H →L[ℂ] ℂ :=
  ReproducingModel.innerSL

section

omit [μ.IsAddHaarMeasure] [SecondCountableTopology W]

@[simp]
lemma valueAt_apply : valueAt x v = v x := rfl

@[simp]
lemma vacElem_apply : he.vacElem x = e x := rfl

lemma vacElem_eq_tauCeti :
    he.vacElem = (ReproducingModel.vacuum : ReproducingModel H.toDatum μ e) :=
  ext fun x ↦ (ReproducingModel.vacuum_apply (e := e) x).symm

end

@[simp]
lemma heisenbergOp_apply (y : W) : heisenbergOp y v x = H.β y x * v (x - y) :=
  ReproducingModel.heisenbergRep_apply v x y

omit [μ.IsAddHaarMeasure] in
/-- The function ‖v(·)‖² is integrable for v in the model: v is integrable and bounded by its
norm. -/
lemma integrable_norm_sq : Integrable (‖v ·‖ ^ 2) μ :=
  ReproducingModel.integrable_norm_sq v

omit [μ.IsAddHaarMeasure] in
@[local simp]
lemma modelInner_apply : modelInner v w = ∫ x : W, conj (v x) * w x ∂μ :=
  ReproducingModel.innerSL_apply v w

omit [μ.IsAddHaarMeasure] in
/-- The inner product is Hermitian: conj ⟨v, w⟩ = ⟨w, v⟩. -/
lemma conj_modelInner : conj (modelInner v w) = modelInner w v :=
  ReproducingModel.conj_innerSL v w

/-- The Heisenberg operators preserve the inner product of the model. -/
lemma modelInner_heisenbergOp :
    modelInner (heisenbergOp x v) (heisenbergOp x w) = modelInner v w :=
  ReproducingModel.innerSL_heisenbergRep v w x

/-- Reproducing property: for v in the reproducing space of a vacuum e and x in W, the inner
product ⟨ρ(x)vac, v⟩ equals v(x). -/
@[simp]
lemma modelInner_heisenbergOp_vacElem : modelInner (heisenbergOp x vacElem) v = v x := by
  rw [vacElem_eq_tauCeti]
  exact ReproducingModel.innerSL_heisenbergRep_vacuum v x

omit [μ.IsAddHaarMeasure] in
lemma modelInner_self : modelInner v v = ∫ x : W, ‖v x‖ ^ 2 ∂μ :=
  ReproducingModel.innerSL_self v

omit [μ.IsAddHaarMeasure] in
/-- The inner product of the model is definite: if ⟨v, v⟩ = 0, then v = 0. -/
lemma eq_zero_of_modelInner_self {v : he.Model} (h : he.modelInner v v = 0) : v = 0 :=
  ReproducingModel.eq_zero_of_innerSL_self h

end IsVacuum

/-- The model is complete, hence a Banach space. -/
instance : CompleteSpace he.Model :=
  inferInstanceAs (CompleteSpace (ReproducingModel H.toDatum μ e))

variable {H} [CompleteSpace X]
  (R : H.Rep X) (T : X →L[ℂ] Y) (x : W) (v w : IsVacuum.Model H) (f : X) [CompleteSpace Y]

/-! ### The integrated action -/

/-- The integrated action of the model on a representation R in a complex Banach space X: the
bounded bilinear map (v, f) ↦ ∫ v(y) • R.ρ y f dμ(y), see `New.Heisenberg.Rep.integrated_apply`. -/
def Rep.integrated : he.Model →L[ℂ] X →L[ℂ] X :=
  R.toTauCeti.integrated μ e

omit [μ.IsAddHaarMeasure] [CompleteSpace X] in
lemma Rep.integrated_apply : R.integrated v f = ∫ y : W, v y • R.ρ y f ∂μ :=
  R.toTauCeti.integrated_apply v f

omit [μ.IsAddHaarMeasure] [CompleteSpace X] in
lemma Rep.norm_integrated_le : ‖R.integrated v‖ ≤ ‖v‖ :=
  R.toTauCeti.norm_integrated_le v

omit [μ.IsAddHaarMeasure] in
/-- A bounded operator T passes under the integral that defines the integrated action. -/
lemma Rep.map_integrated_eq_integral : T (R.integrated v f) = ∫ y : W, v y • T (R.ρ y f) ∂μ :=
  R.toTauCeti.map_integrated T v f

/-- The integrated action turns the operator ρ(x) of the model into the operator R.ρ x. -/
@[simp]
lemma Rep.integrated_heisenbergOp :
    R.integrated (he.heisenbergOp x v) f = R.ρ x (R.integrated v f) :=
  R.toTauCeti.integrated_heisenbergRep v f x

omit [μ.IsAddHaarMeasure] in
/-- A bounded operator T from X to Y that intertwines the representations R and R' commutes with
their integrated actions. -/
lemma Rep.map_integrated {R' : H.Rep Y} (hT : ∀ (y : W) (f : X), T (R.ρ y f) = R'.ρ y (T f)) :
    T (R.integrated v f) = R'.integrated v (T f) :=
  R.toTauCeti.map_integrated_of_intertwines T v f (ϱ' := R'.toTauCeti) hT

namespace IsVacuum

/-! ### Bounded maps and invariant forms on the model -/

omit [μ.IsAddHaarMeasure] in
/-- For a representation R on the model itself, the value at x of the integrated action of v on w
is ∫ v(y) (R.ρ y w)(x) dμ(y). -/
lemma integrated_apply_eq_integral (R : H.Rep (Model H)) :
    R.integrated v w x = ∫ y : W, v y * R.ρ y w x ∂μ :=
  ReproducingModel.integrated_apply_apply v w x R.toTauCeti

/-- Integrating the translates ρ(y) vac of the vacuum against v gives back v: the reproducing
identity in operator form. -/
lemma integrated_vacElem : he.heisenbergRep.integrated v vacElem = v := by
  rw [vacElem_eq_tauCeti]
  exact ReproducingModel.integrated_vacuum v

/-- Superposition: for a bounded linear map T from the reproducing space to a complex Banach space
and any v in the reproducing space, Tv = ∫ v(y) T(ρ(y)vac) dμ(y). -/
lemma map_eq_integral (T : Model H →L[ℂ] Y) :
    T v = ∫ y : W, v y • T (heisenbergOp y vacElem) ∂μ := by
  rw [vacElem_eq_tauCeti]
  exact ReproducingModel.map_eq_integral v T

/-- Two bounded operators from the model to a Banach space that agree on the translates ρ(y) vac
of the vacuum are equal. -/
lemma hom_ext {L L' : Model H →L[ℂ] Y}
    (h : ∀ y : W, L (heisenbergOp y vacElem) = L' (heisenbergOp y vacElem)) : L = L' := by
  rw [vacElem_eq_tauCeti] at h
  exact ReproducingModel.hom_ext h

/-- For v, w in the reproducing space of a vacuum e, with its Heisenberg representation ρ, one
has ∫ v(y) ρ(y)w dμ(y) = w(0)·v.

A special case of the Moyal identity (orthogonality relations for the Heisenberg representation), in
operator form with one vector the vacuum. -/
@[simp]
lemma integrated_eq_smul : he.heisenbergRep.integrated v w = w 0 • v :=
  ReproducingModel.integrated_eq_smul v w

/-- Schur's lemma for the model: a bounded operator that commutes with the Heisenberg operators is a
scalar, namely the value at `0` of the image of the vacuum. -/
lemma eq_smul_one_of_commute (T : Model H →L[ℂ] Model H)
    (hT : ∀ y : W, Commute T (heisenbergOp y)) :
    T = T vacElem 0 • 1 := by
  rw [vacElem_eq_tauCeti]
  exact ReproducingModel.eq_smul_one_of_commute T hT

/-- A bounded continuous K from W to a Banach space X yields a bounded linear map L from the model
to X (in the proof, L v = ∫ v y • K y) that behaves as if it sent the translate
`heisenbergOp y vacElem` of the vacuum to K y: if bounded maps M, N into the Banach space Y satisfy
M (K y) = N (heisenbergOp y vacElem) for all y, then M ∘ L = N. -/
lemma exists_lift {K : W → X} (hK : Continuous K) {C : ℝ} (hC : ∀ y : W, ‖K y‖ ≤ C) :
    ∃ L : Model H →L[ℂ] X, ∀ (M : X →L[ℂ] Y) (N : Model H →L[ℂ] Y),
      (∀ y : W, M (K y) = N (heisenbergOp y vacElem)) → ∀ v : Model H, M (L v) = N v := by
  simp_rw [vacElem_eq_tauCeti]
  exact ReproducingModel.exists_lift hK hC

/-- Uniqueness of the invariant form, a form of Schur's lemma for the Heisenberg representation. Let
W be a locally compact, second countable abelian group with Haar measure μ, and let e be a vacuum
for the bicharacter β of `H` and μ. Let `Model H` be the space of integrable v with v(x) = ∫ v(y)
β(y,x) e(x−y) dμ(y), and let ρ(x) = `heisenbergOp x` send v to z ↦ β(x,z) v(z−x). If B_z (z ∈ Z) are
bounded sesquilinear forms on `Model H`, each z ↦ B_z(v,w) is ν-integrable, and ∫B_z dν is invariant
under all ρ(x), then ∫B_z(v,w) dν = (∫B_z(e,e) dν)·⟨v,w⟩, where ⟨v,w⟩ = ∫ conj(v) w dμ. -/
lemma integral_form_eq_mul_modelInner [LocallyCompactSpace W] {Z : Type*} {m : MeasurableSpace Z}
    {ν : Measure Z} (B : Z → Model H →L⋆[ℂ] Model H →L[ℂ] ℂ)
    (hB_int : ∀ v w : Model H, Integrable (fun z : Z ↦ B z v w) ν)
    (hB_inv : ∀ (x : W) (f g : Model H),
      ∫ z : Z, B z (heisenbergOp x f) (heisenbergOp x g) ∂ν = ∫ z : Z, B z f g ∂ν)
    (v w : Model H) :
    ∫ z : Z, B z v w ∂ν = (∫ z : Z, B z vacElem vacElem ∂ν) * modelInner v w := by
  rw [vacElem_eq_tauCeti]
  exact ReproducingModel.integral_form_eq_mul_innerSL B hB_int hB_inv v w

lemma heisenbergOp_eq_tauCeti (x : W) :
    he.heisenbergOp x = ReproducingModel.heisenbergRep (β := H.toDatum) (μ := μ) (e := e) x := rfl

attribute [irreducible] heisenbergRep

end IsVacuum

end New.Heisenberg

end Model

end
