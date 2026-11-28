module

import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import Lib.Adelic.Witt.IwasawaDecomposition
public import Lib.ClassField.HeckeCharacter.SplitTameCharacters
import Lib.Adelic.Unitary.WeakApproximation
import Lib.DiscreteSeries.Haar.TotalMass
import Lib.Weil.MixedModel.ZeroTerm

/-!
# Fourier coefficients along the centre of a unipotent radical and their partial means

This file studies the Fourier coefficients `New.Space.Splitting.centerCoeff` of a continuous
function f on the adelic unitary group of W that is left invariant under the rational points. The
coefficients are taken along the centre of the unipotent radical of the stabiliser of an isotropic
frame. The splitting `A` splits off a hyperbolic plane with isotropic vectors u, u', `B` splits off
a frame of p vectors from its complement, and `D` splits off the image k of that frame in W. The
shifts n₊(a), n₋(b) move u and u' along k. The file studies the partial mean f⁺ of the coefficient
along `D` at a p×p matrix T over the shifts n₋(b), and the function φ⁺_g(a) = f⁺(n₊(a) g).
Exchanging u and u' gives f⁻ and φ⁻_g; the functions φ⁺_g and φ⁻_g behave like a function and its
Fourier transform. The file also defines equivariant lifts of local data and representability at the
infinite places for comparing theta integrals.

## Main definitions and results

* `New.Exchange.IsEquivariantLift`: a linear map from local data at `𝔠.ramifiedPlaces` to functions
  on the unitary group of `X`, sending a given submodule of Schwartz–Bruhat functions to automorphic
  functions.
* `New.Space.Splitting.lineShift`, `New.Space.Splitting.partialMean`,
  `New.Space.Splitting.shiftedMean`: the shifts n₊(a), the partial mean f⁺ and the function φ⁺_g.
* `New.Space.Splitting.centreCoeff_eq_mul_of_shiftedMean_eq_smul`,
  `New.Space.Splitting.shiftedMean_symm_eq_smul`: for det T ≠ 0, a relation φ⁺_{g'} = c φ⁺_g passes
  to the coefficients along `D` at the points n₋(b) n₊(a) g and to φ⁻.
* `New.Space.Splitting.partialMean_radicalElement_mul`: singularity. Let f⁺ be invariant under the
  shears at a nonempty set of finite places (`New.Space.Splitting.ShearInvariant`) at all points
  that fix e·k for an adele e (`New.Space.Splitting.frameStabilizer`). Then f⁺(h g) = f⁺(g) for h in
  the adelic radical of the stabiliser of the line of u, whenever g and h g fix e·k. The proof
  compares f⁺ with `New.Space.Splitting.borderedCentreCoeff`.

Notions from other files:
* `New.Space`: A hermitian space with a point: a matrix J over E and x in GL_n(𝔸) with xᴴJx equal to
  diag(s) at the infinite places and 1 at the finite places; `W.Γ` is the group of rational points
  x⁻¹ U(J)(E) x in the adelic unitary group `New.G`.
* `New.Space.Splitting`: a decomposition W = (lE^p ⊕ kE^p) ⊥ iW₀ with dual isotropic frames l, k.
* `New.Space.Splitting.radicalCenter`: z(M) = 1 + k(M − M*)k*ε (ε the standard form), an element of
  the centre of the unipotent radical of the stabiliser of the frame k.
* `New.Exchange.SplitTameChar`: a character of [U(1)] of a given weight, positive at every infinite
  place, with tame part non-trivial exactly on a non-empty finite set S of places disjoint from its
  conjugate.
* `New.Space.Splitting.comp`: From splittings of V over V₀ (rank p) and V₀ over V₁ (rank q), the
  splitting of V over V₁ with frames (k, ik'), (l, il') and embedding ii'.
-/

@[expose] public section

/-!
## Laws of the Fourier coefficients along the centre of the radical

In this section `H` is the splitting and `D` the function.
-/

namespace New.Space.Splitting

open Matrix Exchange MeasureTheory QuotientAddGroup IsDualFamily

variable {E : Type*} [Field E] [CMType E] [WeilData E]
  {n p n₀ : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p] [Fintype n₀]
  [DecidableEq n₀] {s : n → ℤˣ}

/-- D is a continuous function on the adelic unitary group of W that is left invariant under the
rational points. -/
def _root_.New.Exchange.IsAutFunction (W : Space E n s) (D : G E s → ℂ) : Prop :=
  Continuous D ∧ W.Γ.FixesLeft D

variable {W : Space E n s} {D : G E s → ℂ} {s₀ : n₀ → ℤˣ} {W₀ : Space E n₀ s₀}
  (H : W.Splitting W₀ p)

/-- If D is continuous and left invariant under the rational points, then M ↦ D (z(M) g) is
continuous and periodic under rational matrices, z(M) being the element `H.radicalCenter M` of the
centre of the radical. -/
lemma isContPeriodic_radicalCentre (hD : IsAutFunction W D) (g : G E s) :
    IsContPeriodic (ratMatrices E p p) fun M : Matrix p p (𝔸 E) ↦ D (H.radicalCenter M * g) := by
  refine ⟨hD.1.comp (by fun_prop), fun γ hγ M ↦ ?_⟩
  simp [AddChar.map_add_eq_mul, mul_assoc, hD.2 (H.radicalCenter γ) (by simp [hγ])]

/-- Let D and D' be continuous and left invariant under the rational points. The coefficient at T
of D(· Y) − c D' at the point g is that of D at g Y minus c times that of D' at g. -/
lemma centreCoeff_mul_right_sub_smul {D' : G E s → ℂ} (hD : IsAutFunction W D)
    (hD' : IsAutFunction W D') (c : ℂ) (Y : G E s) (T : Matrix p p E) (g : G E s) :
    H.centerCoeff T ((fun x : G E s ↦ D (x * Y)) - c • D') g =
      H.centerCoeff T D (g * Y) - c * H.centerCoeff T D' g := by
  -- the mean is linear, both integrands being periodic and continuous, hence integrable
  simp only [centerCoeff, Pi.sub_apply, mul_assoc, Pi.smul_apply, smul_eq_mul, mul_sub,
    mul_left_comm _ c, ← quotMean_const_mul]
  exact integral_sub
    (isContPeriodic_mul (H.isContPeriodic_radicalCentre hD (g * Y)) T).integrable_out
    ((isContPeriodic_mul (H.isContPeriodic_radicalCentre hD' g) T).integrable_out.const_mul c)

/-- The coefficient at T is additive on functions that are continuous and left invariant under the
rational points. -/
lemma centreCoeff_add {D' : G E s → ℂ} (hD : IsAutFunction W D) (hD' : IsAutFunction W D')
    (T : Matrix p p E) (g : G E s) :
    H.centerCoeff T (D + D') g = H.centerCoeff T D g + H.centerCoeff T D' g := by
  simpa using H.centreCoeff_mul_right_sub_smul hD hD' (-1) 1 T g

variable (hD : IsAutFunction W D) {T : Matrix p p E}
include hD

/-- For D continuous and left invariant under the rational points, its Fourier coefficient at T
along the centre of the radical, the mean of ψ(tr TM) D(z(M) g) over M modulo rational matrices, is
a continuous function of g. -/
@[fun_prop]
lemma continuous_centreCoeff : Continuous (H.centerCoeff T D) := by
  -- The mean is an integral over a compact quotient, so it is enough that the integrand is jointly
  -- continuous; this can be tested before passing to the quotient.
  unfold centerCoeff quotMean
  refine (continuous_parametric_integral_of_continuous
    ((isQuotientMap_mk _).continuous_lift_prod_right ?_) isCompact_univ).congr
      fun _ ↦ setIntegral_univ
  -- by periodicity the choice of coset representatives does not matter
  simp only [Function.uncurry_apply_pair,
    (isContPeriodic_mul (H.isContPeriodic_radicalCentre hD _) T).apply_out_mk]
  exact (continuous_stdAddChar.subtypeVal.comp (by fun_prop)).mul (hD.1.comp (by fun_prop))

/-- For D continuous and left invariant under the rational points, left translation by
z(M) = `H.radicalCenter M` divides the coefficient at T by ψ(tr TM), ψ the standard additive
character. -/
lemma centreCoeff_radicalCentre_mul (M : Matrix p p (𝔸 E)) (g : G E s) :
    stdAddChar E (T.map toAdele * M).trace * H.centerCoeff T D (H.radicalCenter M * g) =
      H.centerCoeff T D g := by
  have h_translate : H.centerCoeff T D (H.radicalCenter M * g) =
      quotMean (ratMatrices E p p) fun N : Matrix p p (𝔸 E) ↦
        stdAddChar E (T.map toAdele * N).trace * D (H.radicalCenter (N + M) * g) := by
    simp [centerCoeff, AddChar.map_add_eq_mul, mul_assoc]
  rw [h_translate]
  exact mul_quotMean_translate (H.isContPeriodic_radicalCentre hD g) T M

/-- For D continuous and left invariant under the rational points, a rational point γ that acts on
the isotropic frame k of H through the rational matrix c (γ k = k c) carries the coefficient at T to
the coefficient at cᴴ T c. -/
lemma centreCoeff_rat_mul (T : Matrix p p E) {γ : G E s} (hγ : γ ∈ W.Γ) (c : Matrix p p E)
    (h_frame : H.ActsOnFrame γ (c.map toAdele)) (g : G E s) :
    H.centerCoeff T D (γ * g) = H.centerCoeff (cᴴ * T * c) D g := by
  obtain ⟨a, ha⟩ : IsUnit (c.map toAdele) := h_frame.isUnit
  -- The substitution M ↦ a M aᴴ is onto and keeps rational matrices, so it keeps the mean.
  let φ : Matrix p p (𝔸 E) →+ Matrix p p (𝔸 E) := .comp (.mulLeft ↑a) (.mulRight aᴴ)
  have hrat : ∀ M ∈ ratMatrices E p p, φ M ∈ ratMatrices E p p := by
    rintro M ⟨N, rfl⟩
    exact ⟨c * (N * cᴴ), by simp [φ, ha, Matrix.map_mul]⟩
  have hsurj : Function.Surjective φ := fun M ↦ ⟨(a⁻¹).val * M * aᴴ⁻¹, by simp [φ, mul_assoc]⟩
  -- Move γ to the left (z(a M aᴴ) γ = γ z(M)), absorb it in D, and cycle the trace.
  have h_move (M : Matrix p p (𝔸 E)) :
      D (H.radicalCenter (φ M) * (γ * g)) = D (H.radicalCenter M * g) := by
    have hφ : φ M = c.map toAdele * M * (c.map toAdele)ᴴ := by
      rw [← ha]; exact (Matrix.mul_assoc _ _ _).symm
    rw [hφ, ← mul_assoc, ← H.mul_radicalCenter h_frame, mul_assoc, hD.2 γ hγ]
  have h_trace (M : Matrix p p (𝔸 E)) :
      (T.map toAdele * φ M).trace = ((cᴴ * T * c).map toAdele * M).trace := by
    simp [φ, ha, Matrix.map_mul, Matrix.mul_assoc, (cᴴ.map toAdele).trace_mul_comm]
  rw [centerCoeff, ← quotMean_comp _ φ
    (isContPeriodic_mul (H.isContPeriodic_radicalCentre hD (γ * g)) T) hrat hsurj
    ((continuous_const_mul _).comp (continuous_mul_const _))]
  simp only [centerCoeff, h_move, h_trace]

/-- For D continuous and left invariant under the rational points, a rational point that fixes the
isotropic frame of H does not change the coefficient at T. -/
lemma centreCoeff_rat_mul_of_actsOnFrame_one {γ : G E s} (hγ : γ ∈ W.Γ)
    (h_frame : H.ActsOnFrame γ 1) (g : G E s) :
    H.centerCoeff T D (γ * g) = H.centerCoeff T D g := by
  simpa using H.centreCoeff_rat_mul hD T hγ 1 (by simpa using h_frame) g

end New.Space.Splitting

/-!
## Equivariant lifts of local data and forms represented at infinite places
Definitions for the comparison of theta integrals attached to a tamely ramified character `𝔠`, with
set of ramified places `𝔠.ramifiedPlaces`; `New.LocProd P` is the product of the completions of E at
the finite places in P.
-/

namespace New.Exchange

open Matrix NumberField

variable {E : Type} [Field E] [CMType E] [WeilData E]
  {n b m : Type} [Fintype n] [DecidableEq n] [Fintype b] [DecidableEq b] [Fintype m] [DecidableEq m]
  {s : n → ℤˣ} {r : m → ℤˣ} {μ : InfinitePlace E → ℤ} (𝔠 : SplitTameChar E μ) (x : Matrix n b (𝔸 E))

/-- The ring map sending an adele to its components at the ramified places S of 𝔠. -/
noncomputable def componentsAt : (InfinitePlace E → ℂ) × 𝔸f E →+* LocProd 𝔠.ramifiedPlaces :=
  (evalPlaces 𝔠.ramifiedPlaces).comp (RingHom.snd (InfinitePlace E → ℂ) (𝔸f E) : 𝔸 E →+* 𝔸f E)

/-- The homomorphism G_f → GL_n(∏_{w∈P} E_w) sending an element to its components at P. -/
noncomputable def _root_.New.atPlaces {E : Type} [Field E] [NumberField E] [IsCMField E]
    (P : Finset (FinPlace E)) : Gf E n →* GL n (LocProd P) :=
  (GeneralLinearGroup.map (evalPlaces P)).comp (U 1).subtype

/-- Let X be a hermitian space with index type m, let S = `𝔠.ramifiedPlaces` be the ramified places
of the character 𝔠, and let M be a space of functions of m × b matrices over the completions at S. A
linear map 𝒟 from such functions to functions on U(X) is an equivariant lift on M if M consists of
locally constant functions with compact support in the left invertible matrices, and on M the map 𝒟
has automorphic values, is equivariant at S up to a character of the determinant, and has values
right invariant under the elements of `stdLevel` with component 1 at S. -/
structure IsEquivariantLift (X : Space E m r)
  (M : Submodule ℂ (Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ))
    (𝒟 : (Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] G E r → ℂ) : Prop where
  /-- The data in `M` are locally constant, with compact support in the left invertible matrices. -/
  le_schwartzBruhat : M ≤ schwartzBruhat {x | HasLeftInv x}
  /-- `𝒟 Ψ` is continuous and left invariant under the rational points of `U(X)`. -/
  isAutFunction {Ψ : Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ} (hΨ : Ψ ∈ M) : IsAutFunction X (𝒟 Ψ)
  /-- For `g` supported on `S ∪ S̄`, the translate `Φ y = Ψ (g_S y)` lies in `M`, and `𝒟 Φ`,
  translated on the right by `g`, is `𝒟 Ψ` divided by `(υ |·|^(1/2)) (det g_S) ^ card b`. -/
  map_translate {Ψ : Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ} (hΨ : Ψ ∈ M) (g : Gf E m)
      (hg : g ∈ Gf.supportedOn m 𝔠.ramifiedPlaces) :
    let Φ (y : Matrix m b (LocProd 𝔠.ramifiedPlaces)) : ℂ :=
      Ψ ((atPlaces 𝔠.ramifiedPlaces g).val * y)
    Φ ∈ M ∧ ∀ x : G E r, 𝒟 Φ (x * (1, g)) =
      𝒟 Ψ x / localChar 𝔠.ramifiedPlaces WeilData.υ 1 (atPlaces 𝔠.ramifiedPlaces g).val.det ^
        Fintype.card b
  /-- `𝒟 Ψ` is right invariant under the elements of `stdLevel` that are `1` at `S`. -/
  invariant_off (Ψ : Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ) (hΨ : Ψ ∈ M) (k : Gf E m)
      (hk : k ∈ stdLevel E m ⊓ Gf.trivialOn m 𝔠.ramifiedPlaces) (x : G E r) :
        𝒟 Ψ (x * (1, k)) = 𝒟 Ψ x

section

variable {E : Type} [Field E] [NumberField E] (x : Matrix n b (𝔸 E))

/-- The complex matrix of components of the adelic matrix x at the infinite place v. -/
abbrev atRealPlace (v : InfinitePlace E) : Matrix n b ℂ := x.map fun a ↦ a.1 v

/-- An adelic b × b matrix T is represented by the signs t if at every infinite place its component
has the form cᴴ diag(t) c for some complex matrix c. -/
def RepresentedBy (t : b → ℤˣ) (T : Matrix b b (𝔸 E)) : Prop :=
  ∀ v : InfinitePlace E, ∃ c : Matrix b b ℂ, cᴴ * signMatrix t * c = atRealPlace T v

end

omit [WeilData E] [Fintype b] [DecidableEq b] in
/-- For an adelic matrix x and an infinite place v with component x_v (`atRealPlace x v`), the Gram
matrix x_vᴴ diag(s) x_v is the component at v of xᴴ ε x, where ε = `stdForm E s` is the standard
form with signs s. -/
lemma gram_atRealPlace (v : InfinitePlace E) :
    (atRealPlace x v)ᴴ * signMatrix s * atRealPlace x v = atRealPlace (xᴴ * stdForm E s * x) v := by
  ext i j
  simp [Matrix.mul_apply, stdForm, signMatrix, diagonal, Prod.fst_sum]

end New.Exchange

namespace New.Space.Splitting

/-!
## Coordinates of opposite and composite splittings

A splitting `H : W.Splitting W₂ p` consists of dual isotropic frames `k`, `l` of p vectors and an
embedding of the orthogonal complement `W₂`. Below, `A : W.Splitting W₀ Unit` splits off one line,
`B : W₀.Splitting W₂ p` splits `W₀`, and `A.comp B` is the splitting of `W` whose frame is the line
of `A` followed by the frame of `B`.
-/

section CompositeSplitting

open Matrix

variable {E n n₂ p : Type*} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  [Fintype n₂] [DecidableEq n₂] [Fintype p] [DecidableEq p] {s : n → ℤˣ} {s₂ : n₂ → ℤˣ}
  {W : Space E n s} {W₂ : Space E n₂ s₂} {W₀ : Space E ((p ⊕ p) ⊕ n₂) (hyperbolicSigns p ⊕ᵥ s₂)}
  (A : W.Splitting W₀ Unit) (B : W₀.Splitting W₂ p)

@[simp]
lemma symm_kAdelic (H : W.Splitting W₂ p) : H.symm.kAdelic = H.lAdelic := rfl

@[simp]
lemma symm_iAdelic (H : W.Splitting W₂ p) : H.symm.iAdelic = H.iAdelic := rfl

@[simp]
lemma symm_lCoord (H : W.Splitting W₂ p) : H.symm.lCoord = H.kCoord := rfl

@[simp]
lemma symm_iCoord (H : W.Splitting W₂ p) : H.symm.iCoord = H.iCoord := rfl

@[simp]
lemma symm_symm (H : W.Splitting W₂ p) : H.symm.symm = H := rfl

/-- For the composite of the splittings A of W and B of the complement W₀, the coordinate
`lCoord` (which reads off the coefficients of the dual frame l) has the block rows of A and of B,
the latter after the projection `A.iCoord` to W₀. -/
@[simp]
lemma comp_lCoord : (A.comp B).lCoord = fromRows A.lCoord (B.lCoord * A.iCoord) := by
  simp [lCoord, iCoord, comp_kAdelic, conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.mul_assoc]

end CompositeSplitting

/-!
## Shifts of an isotropic line and partial means

The splitting `A` splits off a hyperbolic plane with isotropic vectors u (its frame) and u' (the
frame of `A.symm`), and the frame k of `D` is the image in W of the frame of `B`. The shifts
n₊(a) = `A.lineShift B a` and n₋(b) = `A.symm.lineShift B b` move u and u' along k. Each statement
about `A` has a second form for `A.symm`, with the two signs exchanged.
-/

section PartialMeans

open Matrix Exchange WeilData IsDualFamily

variable {E n n₁ n₂ p : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] [Fintype p] [DecidableEq p]
  {s : n → ℤˣ} {s₁ : n₁ → ℤˣ} {s₂ : n₂ → ℤˣ} {W : Space E n s}
  {W₀ : Space E ((p ⊕ p) ⊕ n₂) (hyperbolicSigns p ⊕ᵥ s₂)} {W₁ : Space E n₁ s₁} {W₂ : Space E n₂ s₂}

/-- For an adele e, the group of the points g that fix e·k, where k is the frame of D. If e is an
idempotent, these are the points that fix the frame at the places where e is 1. -/
def frameStabilizer (D : W.Splitting W₁ p) (e : 𝔸 E) : Subgroup (G E s) where
  carrier := {g : G E s | g.adeleMatrix * e • D.kAdelic = e • D.kAdelic}
  mul_mem' {g h : G E s} hg hh := by
    change (g * h).adeleMatrix * e • D.kAdelic = e • D.kAdelic
    rw [G.adeleMatrix_mul, Matrix.mul_assoc, hh, hg]
  one_mem' := by
    change (1 : G E s).adeleMatrix * e • D.kAdelic = e • D.kAdelic
    rw [G.adeleMatrix_one, Matrix.one_mul]
  inv_mem' {g : G E s} hg := by
    change g⁻¹.adeleMatrix * e • D.kAdelic = e • D.kAdelic
    rw [← hg, ← Matrix.mul_assoc, ← G.adeleMatrix_mul, inv_mul_cancel, G.adeleMatrix_one,
      Matrix.one_mul, hg]

lemma mem_frameStabilizer {D : W.Splitting W₁ p} {e : 𝔸 E} {g : G E s} :
    g ∈ D.frameStabilizer e ↔ g.adeleMatrix * e • D.kAdelic = e • D.kAdelic :=
  Iff.rfl

lemma ActsOnFrame.mul {D : W.Splitting W₁ p} {g h : G E s} {a b : Matrix p p (𝔸 E)}
    (hg : D.ActsOnFrame g a) (hh : D.ActsOnFrame h b) : D.ActsOnFrame (g * h) (a * b) := by
  rw [ActsOnFrame, G.adeleMatrix_mul, Matrix.mul_assoc, hh, ← Matrix.mul_assoc, hg,
    Matrix.mul_assoc]

lemma ActsOnFrame.mem_frameStabilizer {D : W.Splitting W₁ p} {g : G E s}
    (hg : D.ActsOnFrame g 1) (e : 𝔸 E) : g ∈ D.frameStabilizer e := by
  rw [Splitting.mem_frameStabilizer, Matrix.mul_smul, hg, Matrix.mul_one]

variable [WeilData E] (A : W.Splitting W₀ Unit) (B : W₀.Splitting W₂ p)

/-- The shift n₊(a) : u ↦ u − k aᴴ of the isotropic vector u of A by the image k in W of the frame
of B. Here a is an adelic row. It is a central element of the radical for the splitting
`A.symm.comp B`. -/
noncomputable def lineShift (a : Matrix Unit p (𝔸 E)) : G E s :=
  (A.symm.comp B).radicalCenter (fromBlocks 0 a 0 0)

lemma lineShift_add (a b : Matrix Unit p (𝔸 E)) :
    A.lineShift B (a + b) = A.lineShift B a * A.lineShift B b := by
  simp [lineShift, ← AddChar.map_add_eq_mul, fromBlocks_add]

lemma lineShift_zero : A.lineShift B 0 = 1 := by simp [lineShift]

@[fun_prop]
lemma continuous_lineShift : Continuous (A.lineShift B) := by
  unfold lineShift
  fun_prop

lemma lineShift_mem {a : Matrix Unit p (𝔸 E)} (ha : a ∈ ratMatrices E Unit p) :
    A.lineShift B a ∈ W.Γ := by
  obtain ⟨a₀, rfl⟩ := ha
  simp [lineShift, mem_ratMatrices, ratAdeles]

private noncomputable abbrev lineShiftTerm (a : Matrix Unit p (𝔸 E)) : Matrix n n (𝔸 E) :=
  A.lAdelic * a * (B.lCoord * A.iCoord) - A.iAdelic * B.kAdelic * aᴴ * A.kCoord

private lemma adeleMatrix_lineShift (a : Matrix Unit p (𝔸 E)) :
    (A.lineShift B a).adeleMatrix =
      1 + (A.lAdelic * a * (B.lCoord * A.iCoord) - A.iAdelic * B.kAdelic * aᴴ * A.kCoord) := by
  rw [lineShift, adeleMatrix_radicalCenter, comp_kAdelic, comp_lCoord, symm_kAdelic,
    symm_iAdelic, symm_lCoord, symm_iCoord, fromBlocks_conjTranspose, sub_eq_add_neg,
    fromBlocks_neg, fromBlocks_add]
  simp only [conjTranspose_zero, neg_zero, zero_add, add_zero]
  rw [fromCols_mul_fromBlocks]
  simp only [Matrix.mul_zero, zero_add, add_zero]
  rw [fromCols_mul_fromRows, Matrix.mul_neg, Matrix.neg_mul, neg_add_eq_sub, Matrix.mul_assoc]

/-- The shift n₊(a) carries the frame (u, k) of the composite of A and B, k the image in W of the
frame of B, to (u − k aᴴ, k). -/
lemma actsOnFrame_lineShift (a : Matrix Unit p (𝔸 E)) :
    (A.comp B).ActsOnFrame (A.lineShift B a) (fromBlocks 1 0 (-aᴴ) 1) := by
  -- compare the two sides on the column of `u` and on those of the frame of B
  rw [ActsOnFrame, comp_kAdelic, Matrix.mul_fromCols, fromCols_mul_fromBlocks,
    adeleMatrix_lineShift]
  congr 1
  · simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc,
      A.iCoord_mul_kAdelic, A.kCoord_mul_kAdelic, Matrix.mul_zero, Matrix.mul_one,
      Matrix.mul_neg, Matrix.neg_mul, zero_add, sub_eq_add_neg]
  · simp only [Matrix.add_mul, Matrix.one_mul, Matrix.sub_mul, Matrix.mul_assoc,
      A.iCoord_mul_iAdelic_mul, B.lCoord_mul_kAdelic, A.kCoord_mul_iAdelic_mul,
      Matrix.mul_zero, Matrix.mul_one, sub_zero, add_zero, zero_add]

variable (D : W.Splitting W₁ p) (T : Matrix p p E) (f : G E s → ℂ)

/-- The partial mean f⁺(g): the mean, over the adelic rows b modulo the rational rows, of the
coefficient of f along D at T at the point n₋(b) g, where n₋(b) = `A.symm.lineShift B b`. The
partial mean for `A.symm` is f⁻. -/
noncomputable def partialMean (g : G E s) : ℂ :=
  quotMean (ratMatrices E Unit p) fun b : Matrix Unit p (𝔸 E) ↦
    D.centerCoeff T f (A.symm.lineShift B b * g)

/-- The function φ⁺_g(a) = f⁺(n₊(a) g) of an adelic row a, where f⁺ is the partial mean and
n₊(a) = `A.lineShift B a`. The function for `A.symm` is φ⁻_g. -/
noncomputable def shiftedMean (g : G E s) (a : Matrix Unit p (𝔸 E)) : ℂ :=
  A.partialMean B D T f (A.lineShift B a * g)

lemma shiftedMean_apply_zero (g : G E s) :
    A.shiftedMean B D T f g 0 = A.partialMean B D T f g := by
  rw [shiftedMean, lineShift_zero, one_mul]

variable {A B D T f}

/-- If the partial mean f⁺ is not zero at g, then the coefficient of f along D at T is not zero at
some point n₋(b) g. -/
lemma exists_centreCoeff_ne_zero {g : G E s} (h_ne : A.partialMean B D T f g ≠ 0) :
    ∃ b : Matrix Unit p (𝔸 E), D.centerCoeff T f (A.symm.lineShift B b * g) ≠ 0 := by
  by_contra! h_zero
  simp [partialMean, h_zero] at h_ne

omit [WeilData E] in
/-- If the frame of D is the image of the frame of B, the coordinate `D.lCoord` is that of B after
the projection to the complement W₀. -/
lemma lCoord_eq_lCoord_mul_iCoord (hD : D.kAdelic = A.iAdelic * B.kAdelic) :
    D.lCoord = B.lCoord * A.iCoord := by
  simp [lCoord, iCoord, hD, Matrix.mul_assoc]

/-- If the frame of D is the image of the frame of B, the shifts n₊(a) fix it. -/
lemma actsOnFrame_lineShift_one (hD : D.kAdelic = A.iAdelic * B.kAdelic)
    (a : Matrix Unit p (𝔸 E)) : D.ActsOnFrame (A.lineShift B a) 1 := by
  rw [ActsOnFrame, hD, adeleMatrix_lineShift]
  simp only [Matrix.add_mul, Matrix.one_mul, Matrix.sub_mul, Matrix.mul_assoc,
    A.iCoord_mul_iAdelic_mul, B.lCoord_mul_kAdelic, A.kCoord_mul_iAdelic_mul,
    Matrix.mul_zero, Matrix.mul_one, sub_zero, add_zero]

omit [WeilData E] in
private lemma lineShiftTerm_mul_symm (a b : Matrix Unit p (𝔸 E)) :
    A.lineShiftTerm B a * A.symm.lineShiftTerm B b =
      -(A.iAdelic * B.kAdelic * (aᴴ * b) * (B.lCoord * A.iCoord)) := by
  unfold lineShiftTerm
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp only [Matrix.mul_assoc, symm_iAdelic, symm_iCoord,
    show A.symm.lAdelic = A.kAdelic from rfl, show A.symm.kCoord = A.lCoord from rfl,
    A.iCoord_mul_kAdelic_mul, A.iCoord_mul_iAdelic_mul, B.lCoord_mul_kAdelic_mul,
    A.kCoord_mul_kAdelic_mul, A.kCoord_mul_iAdelic_mul, Matrix.mul_zero, sub_zero, zero_sub]

omit [WeilData E] in
private lemma radicalTerm_mul_lineShiftTerm (hD : D.kAdelic = A.iAdelic * B.kAdelic)
    (M : Matrix p p (𝔸 E)) (a : Matrix Unit p (𝔸 E)) :
    D.kAdelic * M * D.lCoord * A.lineShiftTerm B a = 0 := by
  rw [lineShiftTerm, lCoord_eq_lCoord_mul_iCoord hD, Matrix.mul_sub]
  simp only [Matrix.mul_assoc, A.iCoord_mul_lAdelic_mul, A.iCoord_mul_iAdelic_mul,
    B.lCoord_mul_kAdelic_mul, Matrix.mul_zero, sub_self]

/-- Let the frame of `D` be the image under `A` of the frame of `B` (`hD`), and for adelic rows a, b
let n₊(a) = `A.lineShift B a` and n₋(b) = `A.symm.lineShift B b` be the shifts of the two isotropic
vectors of `A` by the frame of `D`: n₊(a) is u ↦ u − k aᴴ on the vector u, and n₋(b) does the same
for the other vector. Then n₊(a) n₋(b) = z(−aᴴ b) n₋(b) n₊(a), where z = `D.radicalCenter`
parametrises the centre of the unipotent radical of the stabiliser of the frame of `D`. -/
lemma lineShift_mul_lineShift_symm (hD : D.kAdelic = A.iAdelic * B.kAdelic)
    (a b : Matrix Unit p (𝔸 E)) :
    A.lineShift B a * A.symm.lineShift B b =
      D.radicalCenter (-(aᴴ * b)) * (A.symm.lineShift B b * A.lineShift B a) := by
  refine G.ext_adeleMatrix ?_
  -- Both shifts are 1 plus terms of square zero; the cross terms differ by k (bᴴ a − aᴴ b) k*ε.
  have hDl : D.lCoord = B.lCoord * A.iCoord := lCoord_eq_lCoord_mul_iCoord hD
  have h_l : A.symm.lAdelic = A.kAdelic := rfl
  have h_k : A.symm.kCoord = A.lCoord := rfl
  let X := A.lineShiftTerm B a
  let Y := A.symm.lineShiftTerm B b
  set Z : Matrix n n (𝔸 E) := D.kAdelic * (-(aᴴ * b) - (-(aᴴ * b))ᴴ) * D.lCoord
  have h_prod (P Q : Matrix n n (𝔸 E)) : (1 + P) * (1 + Q) = 1 + (P + Q + P * Q) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
    abel
  have hXY := lineShiftTerm_mul_symm (A := A) (B := B) a b
  have hYX := lineShiftTerm_mul_symm (A := A.symm) (B := B) b a
  simp only [symm_symm, symm_iAdelic, symm_iCoord] at hYX
  have hZX : Z * X = 0 := radicalTerm_mul_lineShiftTerm hD _ a
  have hZY : Z * Y = 0 := radicalTerm_mul_lineShiftTerm (A := A.symm) hD _ b
  have hZ : Z = A.iAdelic * B.kAdelic * (bᴴ * a) * (B.lCoord * A.iCoord) -
      A.iAdelic * B.kAdelic * (aᴴ * b) * (B.lCoord * A.iCoord) := by
    dsimp only [Z]
    rw [hD, hDl, conjTranspose_neg, conjTranspose_mul, conjTranspose_conjTranspose,
      sub_neg_eq_add, neg_add_eq_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      Matrix.mul_assoc]
  rw [G.adeleMatrix_mul, G.adeleMatrix_mul, G.adeleMatrix_mul, adeleMatrix_radicalCenter,
    adeleMatrix_lineShift, adeleMatrix_lineShift, h_l, symm_iAdelic, h_k, symm_iCoord]
  change (1 + X) * (1 + Y) = (1 + Z) * ((1 + Y) * (1 + X))
  rw [h_prod X Y, h_prod Y X, h_prod Z (Y + X + Y * X)]
  have hZ_all : Z * (Y + X + Y * X) = 0 := by
    rw [Matrix.mul_add, Matrix.mul_add, hZY, hZX, ← Matrix.mul_assoc, hZY, Matrix.zero_mul,
      add_zero, add_zero]
  rw [hZ_all, add_zero, hXY, hYX, hZ]
  abel

/-- Let the frame of D be the image of the frame of B and let f be automorphic. The coefficient
along D at T at the point n₋(b) n₊(a) g is ψ(−tr T aᴴ b) times that at n₊(a) n₋(b) g. -/
lemma centreCoeff_lineShift_symm_mul_lineShift (hD : D.kAdelic = A.iAdelic * B.kAdelic)
    (hf : IsAutFunction W f) (a b : Matrix Unit p (𝔸 E)) (g : G E s) :
    D.centerCoeff T f (A.symm.lineShift B b * (A.lineShift B a * g)) =
      stdAddChar E (T.map toAdele * -(aᴴ * b)).trace *
        D.centerCoeff T f (A.lineShift B a * (A.symm.lineShift B b * g)) := by
  rw [← mul_assoc (A.lineShift B a), lineShift_mul_lineShift_symm hD, mul_assoc, mul_assoc,
    D.centreCoeff_radicalCentre_mul hf]

/-- If the frame of D is the image of the frame of B and f is automorphic, then the coefficient of f
along D at T at the point n₊(a) g is a continuous function of a, periodic under rational rows. -/
lemma isContPeriodic_centreCoeff_lineShift (hD : D.kAdelic = A.iAdelic * B.kAdelic)
    (hf : IsAutFunction W f) (g : G E s) :
    IsContPeriodic (ratMatrices E Unit p)
      fun a : Matrix Unit p (𝔸 E) ↦ D.centerCoeff T f (A.lineShift B a * g) := by
  refine ⟨by fun_prop (disch := exact hf), fun γ hγ a ↦ ?_⟩
  simp only [lineShift_add, mul_assoc]
  exact D.centreCoeff_rat_mul_of_actsOnFrame_one hf (A.lineShift_mem B hγ)
    (actsOnFrame_lineShift_one hD γ) _

/-- If the frame of D is the image of the frame of B and f is automorphic, the partial mean f⁺ is
continuous. -/
lemma continuous_partialMean (hD : D.kAdelic = A.iAdelic * B.kAdelic) (hf : IsAutFunction W f) :
    Continuous (A.partialMean B D T f) := by
  -- The mean is an integral over a compact quotient of a jointly continuous function.
  unfold partialMean quotMean
  refine (continuous_parametric_integral_of_continuous
    ((QuotientAddGroup.isQuotientMap_mk _).continuous_lift_prod_right ?_) isCompact_univ).congr
      fun _ ↦ MeasureTheory.setIntegral_univ
  simp only [Function.uncurry_apply_pair,
    (isContPeriodic_centreCoeff_lineShift (A := A.symm) hD hf _).apply_out_mk]
  exact (D.continuous_centreCoeff hf).comp (by fun_prop)

/-- If the frame of D is the image of the frame of B, the partial mean is additive on automorphic
functions. -/
lemma partialMean_add (hD : D.kAdelic = A.iAdelic * B.kAdelic) (hf : IsAutFunction W f)
    {f' : G E s → ℂ} (hf' : IsAutFunction W f') (g : G E s) :
    A.partialMean B D T (f + f') g = A.partialMean B D T f g + A.partialMean B D T f' g := by
  simp only [partialMean, D.centreCoeff_add hf hf']
  exact MeasureTheory.integral_add
    (isContPeriodic_centreCoeff_lineShift (A := A.symm) hD hf g).integrable_out
    (isContPeriodic_centreCoeff_lineShift (A := A.symm) hD hf' g).integrable_out

/-- If the frame of D is the image of the frame of B and f is automorphic, the partial mean f⁺ is
left invariant under all shifts n₋(b). -/
lemma partialMean_lineShift_symm_mul (hD : D.kAdelic = A.iAdelic * B.kAdelic)
    (hf : IsAutFunction W f) (b : Matrix Unit p (𝔸 E)) (g : G E s) :
    A.partialMean B D T f (A.symm.lineShift B b * g) = A.partialMean B D T f g := by
  simpa only [partialMean, lineShift_add, mul_assoc] using
    quotMean_translate (isContPeriodic_centreCoeff_lineShift (A := A.symm) hD hf g) b

/-- Let the frame of D be the image of the frame of B and let f be automorphic. Left translation by
the element z(M) of the centre of the radical for D divides the partial mean f⁺ by ψ(tr TM). -/
lemma partialMean_radicalCentre_mul (hD : D.kAdelic = A.iAdelic * B.kAdelic)
    (hf : IsAutFunction W f) (M : Matrix p p (𝔸 E)) (g : G E s) :
    stdAddChar E (T.map toAdele * M).trace * A.partialMean B D T f (D.radicalCenter M * g) =
      A.partialMean B D T f g := by
  have h_comm (b : Matrix Unit p (𝔸 E)) :
      A.symm.lineShift B b * D.radicalCenter M = D.radicalCenter M * A.symm.lineShift B b := by
    simpa using D.mul_radicalCenter (actsOnFrame_lineShift_one (A := A.symm) hD b) M
  simp only [partialMean, ← quotMean_const_mul, ← mul_assoc (A.symm.lineShift B _), h_comm]
  simp only [mul_assoc, D.centreCoeff_radicalCentre_mul hf]

/-- Replacing g by n₊(a) g translates φ⁺_g by a. -/
lemma shiftedMean_lineShift_mul (a x : Matrix Unit p (𝔸 E)) (g : G E s) :
    A.shiftedMean B D T f (A.lineShift B a * g) x = A.shiftedMean B D T f g (x + a) := by
  rw [shiftedMean, shiftedMean, lineShift_add, mul_assoc]

/-- Replacing g by n₊(a) g multiplies φ⁻_g(b) by ψ(−tr T aᴴ b), for f automorphic and the frame of D
the image of the frame of B. -/
lemma shiftedMean_symm_lineShift_mul (hD : D.kAdelic = A.iAdelic * B.kAdelic)
    (hf : IsAutFunction W f) (a b : Matrix Unit p (𝔸 E)) (g : G E s) :
    A.symm.shiftedMean B D T f (A.lineShift B a * g) b =
      stdAddChar E (T.map toAdele * -(aᴴ * b)).trace * A.symm.shiftedMean B D T f g b := by
  -- Move n₊(a) to the left, where it fixes f⁻.
  have h_fix : A.symm.partialMean B D T f (A.lineShift B a * (A.symm.lineShift B b * g)) =
      A.symm.partialMean B D T f (A.symm.lineShift B b * g) :=
    partialMean_lineShift_symm_mul (A := A.symm) hD hf a _
  rw [shiftedMean, shiftedMean, ← h_fix, ← mul_assoc (A.lineShift B a),
    lineShift_mul_lineShift_symm hD, mul_assoc, mul_assoc,
    partialMean_radicalCentre_mul (A := A.symm) hD hf]

/-- Let the frame of D be the image of the frame of B and let f be automorphic. For a rational row
a₀, the value φ⁺_g(a₀ + a) is the Fourier coefficient at −T a₀ᴴ of the function that sends b to the
coefficient of f along D at T at the point n₋(b) n₊(a) g. -/
lemma shiftedMean_rat_add (hD : D.kAdelic = A.iAdelic * B.kAdelic) (hf : IsAutFunction W f)
    (a₀ : Matrix Unit p E) (a : Matrix Unit p (𝔸 E)) (g : G E s) :
    A.shiftedMean B D T f g (a₀.map toAdele + a) =
      quotMean (ratMatrices E Unit p) fun b : Matrix Unit p (𝔸 E) ↦
        stdAddChar E ((-(T * a₀ᴴ)).map toAdele * b).trace *
          D.centerCoeff T f (A.symm.lineShift B b * (A.lineShift B a * g)) := by
  -- Move n₊(a₀) to the left, where it fixes the coefficient along D.
  have h_rat (x : G E s) :
      D.centerCoeff T f (A.lineShift B (a₀.map toAdele) * x) = D.centerCoeff T f x :=
    D.centreCoeff_rat_mul_of_actsOnFrame_one hf (A.lineShift_mem B ⟨a₀, rfl⟩)
      (actsOnFrame_lineShift_one hD _) x
  have h_index (b : Matrix Unit p (𝔸 E)) :
      T.map toAdele * -((a₀.map toAdele)ᴴ * b) = (-(T * a₀ᴴ)).map toAdele * b := by
    rw [Matrix.map_neg _ (map_neg toAdele), Matrix.map_mul, ← conjTranspose_map_toAdele,
      Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  simp only [shiftedMean, partialMean, lineShift_add, mul_assoc,
    centreCoeff_lineShift_symm_mul_lineShift hD hf (a₀.map toAdele), h_rat, h_index]

/-- Let the frame of D be the image of the frame of B, f automorphic and det T ≠ 0. If
φ⁺_{g'} = c φ⁺_g, then the coefficient of f along D at T at each point n₋(b) n₊(a) g' is c times
that at n₋(b) n₊(a) g. -/
lemma centreCoeff_eq_mul_of_shiftedMean_eq_smul (hD : D.kAdelic = A.iAdelic * B.kAdelic)
    (hf : IsAutFunction W f) (hT : T.det ≠ 0) {g g' : G E s} {c : ℂ}
    (h_eq : A.shiftedMean B D T f g' = c • A.shiftedMean B D T f g) (a b : Matrix Unit p (𝔸 E)) :
    D.centerCoeff T f (A.symm.lineShift B b * (A.lineShift B a * g')) =
      c * D.centerCoeff T f (A.symm.lineShift B b * (A.lineShift B a * g)) := by
  -- As T is invertible, the values φ⁺(a₀ + a) are all the Fourier coefficients in b.
  let F (x : G E s) (b : Matrix Unit p (𝔸 E)) : ℂ :=
    D.centerCoeff T f (A.symm.lineShift B b * (A.lineShift B a * x))
  have hF (x : G E s) : IsContPeriodic (ratMatrices E Unit p) (F x) :=
    isContPeriodic_centreCoeff_lineShift (A := A.symm) hD hf _
  have h_sub : IsContPeriodic (ratMatrices E Unit p) fun b ↦ F g' b - c * F g b :=
    ⟨(hF g').1.sub ((hF g).1.const_mul c), fun γ hγ b ↦ by simp [(hF g').2 γ hγ, (hF g).2 γ hγ]⟩
  refine sub_eq_zero.1 (eq_zero_of_quotMean_mul_eq_zero h_sub (fun (R : Matrix p Unit E) _ ↦ ?_) b)
  obtain ⟨a₀, rfl⟩ : ∃ a₀ : Matrix Unit p E, -(T * a₀ᴴ) = R := ⟨-(T⁻¹ * R)ᴴ, by simp [hT]⟩
  let χ (b : Matrix Unit p (𝔸 E)) : ℂ := stdAddChar E ((-(T * a₀ᴴ)).map toAdele * b).trace
  calc quotMean (ratMatrices E Unit p) (fun b ↦ χ b * (F g' b - c * F g b))
    _ = quotMean (ratMatrices E Unit p) (fun b ↦ χ b * F g' b) -
          c * quotMean (ratMatrices E Unit p) fun b ↦ χ b * F g b := by
      simp only [mul_sub, mul_left_comm _ c, ← quotMean_const_mul]
      exact MeasureTheory.integral_sub (isContPeriodic_mul (hF g') _).integrable_out
        ((isContPeriodic_mul (hF g) _).integrable_out.const_mul c)
    _ = A.shiftedMean B D T f g' (a₀.map toAdele + a) -
          c * A.shiftedMean B D T f g (a₀.map toAdele + a) := by
      rw [shiftedMean_rat_add hD hf, shiftedMean_rat_add hD hf]
    _ = 0 := by simp [h_eq]

/-- Let the frame of D be the image of the frame of B, f automorphic and det T ≠ 0. If
φ⁺_{g'} = c φ⁺_g, then φ⁻_{g'} = c φ⁻_g. -/
lemma shiftedMean_symm_eq_smul (hD : D.kAdelic = A.iAdelic * B.kAdelic)
    (hf : IsAutFunction W f) (hT : T.det ≠ 0) {g g' : G E s} {c : ℂ}
    (h_eq : A.shiftedMean B D T f g' = c • A.shiftedMean B D T f g) :
    A.symm.shiftedMean B D T f g' = c • A.symm.shiftedMean B D T f g := by
  -- The order of the two shifts matters only by a character that does not depend on the point.
  funext b
  have h_point (a : Matrix Unit p (𝔸 E)) :
      D.centerCoeff T f (A.lineShift B a * (A.symm.lineShift B b * g')) =
        c * D.centerCoeff T f (A.lineShift B a * (A.symm.lineShift B b * g)) := by
    have h_swap (x : G E s) : D.centerCoeff T f (A.lineShift B a * (A.symm.lineShift B b * x)) =
        stdAddChar E (T.map toAdele * -(bᴴ * a)).trace *
          D.centerCoeff T f (A.symm.lineShift B b * (A.lineShift B a * x)) :=
      centreCoeff_lineShift_symm_mul_lineShift (A := A.symm) hD hf b a x
    rw [h_swap, h_swap, centreCoeff_eq_mul_of_shiftedMean_eq_smul hD hf hT h_eq, mul_left_comm]
  simp [shiftedMean, partialMean, h_point]

/-- Let the frame of D be the image of the frame of B, f automorphic and det T ≠ 0. If φ⁺_g is zero,
then the coefficient of f along D at T is zero at g. -/
lemma centreCoeff_eq_zero_of_shiftedMean_eq_zero (hD : D.kAdelic = A.iAdelic * B.kAdelic)
    (hf : IsAutFunction W f) (hT : T.det ≠ 0) {g : G E s}
    (h_zero : A.shiftedMean B D T f g = 0) : D.centerCoeff T f g = 0 := by
  simpa [lineShift_zero] using
    centreCoeff_eq_mul_of_shiftedMean_eq_smul (c := 0) (g := g) hD hf hT (by simp [h_zero]) 0 0

/-- Let the frame of D be the image of the frame of B, f automorphic and det T ≠ 0. If φ⁺_g is zero,
then so is φ⁻_g. -/
lemma shiftedMean_symm_eq_zero (hD : D.kAdelic = A.iAdelic * B.kAdelic) (hf : IsAutFunction W f)
    (hT : T.det ≠ 0) {g : G E s} (h_zero : A.shiftedMean B D T f g = 0) :
    A.symm.shiftedMean B D T f g = 0 := by
  simpa using shiftedMean_symm_eq_smul (c := 0) (g := g) hD hf hT (by simp [h_zero])

end PartialMeans

/-!
## Singularity of the partial mean

Invariance under the shears at a nonempty set of places spreads, by strong approximation for the
additive group, first to the centre of the radical for `A` and then to the whole radical.
-/

section Singularity

open Matrix Exchange WeilData

variable {E n n₁ n₂ p : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
  [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] [Fintype p] [DecidableEq p]
  {s : n → ℤˣ} {s₁ : n₁ → ℤˣ} {s₂ : n₂ → ℤˣ} {W : Space E n s}
  {W₀ : Space E ((p ⊕ p) ⊕ n₂) (hyperbolicSigns p ⊕ᵥ s₂)} {W₁ : Space E n₁ s₁} {W₂ : Space E n₂ s₂}

/-- For an adele e and a point g, the condition that the partial mean f⁺ takes the same value at g
and ν g for every shear ν, that is, every ν with matrix 1 + ē·uc − e·a. Here u = `A.kAdelic` is the
isotropic vector of A, c is a row with cu = 0, and a is arbitrary. If e is the idempotent of a set
of places U disjoint from its conjugate, such a ν is 1 + uc on Ū and 1 outside U ∪ Ū. -/
def ShearInvariant (A : W.Splitting W₀ Unit) (B : W₀.Splitting W₂ p) (D : W.Splitting W₁ p)
    (T : Matrix p p E) (f : G E s → ℂ) (e : 𝔸 E) (g : G E s) : Prop :=
  ∀ ⦃ν : G E s⦄ (c : Matrix Unit n (𝔸 E)) (a : Matrix n n (𝔸 E)),
    c * A.kAdelic = 0 →
    ν.adeleMatrix = 1 + (star e • (A.kAdelic * c :) - e • a) →
    A.partialMean B D T f (ν * g) = A.partialMean B D T f g

/-- The Fourier coefficient of f along the composite of the splittings A (one line) and B, at the
block diagonal matrix 0 ⊕ T. -/
noncomputable abbrev borderedCentreCoeff (A : W.Splitting W₀ Unit) (B : W₀.Splitting W₂ p)
    (T : Matrix p p E) (f : G E s → ℂ) : G E s → ℂ :=
  (A.comp B).centerCoeff (fromBlocks 0 0 0 T) f

variable {A : W.Splitting W₀ Unit} {B : W₀.Splitting W₂ p} {D : W.Splitting W₁ p}

/-- If the frame of D is the image of the frame of B, the central element for the composite of A and
B with blocks z, b, c, N is the product of the central element for D at N, the shift n₋(b − cᴴ) and
the central element for A at z. -/
lemma radicalCentre_comp_fromBlocks (hD : D.kAdelic = A.iAdelic * B.kAdelic)
    (z : Matrix Unit Unit (𝔸 E)) (b : Matrix Unit p (𝔸 E)) (c : Matrix p Unit (𝔸 E))
    (N : Matrix p p (𝔸 E)) :
    (A.comp B).radicalCenter (fromBlocks z b c N) =
      D.radicalCenter N * (A.symm.lineShift B (b - cᴴ) * A.radicalCenter z) := by
  refine G.ext_adeleMatrix ?_
  have hDl : D.lCoord = B.lCoord * A.iCoord := lCoord_eq_lCoord_mul_iCoord hD
  have h_l : A.symm.lAdelic = A.kAdelic := rfl
  have h_k : A.symm.kCoord = A.lCoord := rfl
  set U : Matrix n n (𝔸 E) := D.kAdelic * (N - Nᴴ) * D.lCoord
  set V : Matrix n n (𝔸 E) :=
    A.kAdelic * (b - cᴴ) * (B.lCoord * A.iCoord) - A.iAdelic * B.kAdelic * (b - cᴴ)ᴴ * A.lCoord
  set Z : Matrix n n (𝔸 E) := A.kAdelic * (z - zᴴ) * A.lCoord
  have hVZ : V * Z = 0 := by
    dsimp only [V, Z]
    rw [Matrix.sub_mul]
    simp only [Matrix.mul_assoc, A.iCoord_mul_kAdelic_mul, A.lCoord_mul_kAdelic_mul,
      Matrix.mul_zero, sub_self]
  have hUV : U * V = 0 := radicalTerm_mul_lineShiftTerm (A := A.symm) hD _ _
  have hUZ : U * Z = 0 := by
    dsimp only [U, Z]
    rw [hDl]
    simp only [Matrix.mul_assoc, A.iCoord_mul_kAdelic_mul, Matrix.mul_zero]
  have h_rhs : (1 + U) * ((1 + V) * (1 + Z)) = 1 + U + V + Z := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hVZ, hUV, hUZ,
      add_zero]
  rw [G.adeleMatrix_mul, G.adeleMatrix_mul, adeleMatrix_radicalCenter, adeleMatrix_radicalCenter,
    adeleMatrix_radicalCenter, adeleMatrix_lineShift, h_l, symm_iAdelic, h_k, symm_iCoord]
  change 1 + (A.comp B).kAdelic * (fromBlocks z b c N - (fromBlocks z b c N)ᴴ) *
      (A.comp B).lCoord = (1 + U) * ((1 + V) * (1 + Z))
  rw [h_rhs, comp_kAdelic, comp_lCoord, fromBlocks_conjTranspose,
    sub_eq_add_neg (fromBlocks z b c N), fromBlocks_neg, fromBlocks_add,
    fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  dsimp only [U, V, Z]
  rw [hD, hDl]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, conjTranspose_sub,
    conjTranspose_conjTranspose, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  abel

/-- Let `A` split one hyperbolic plane off `W` over `W₀`, `B` split `p` planes off `W₀` over `W₂`,
and `D` split `p` planes off `W` over `W₁`. Let the frame of `D` be the image under `A` of the frame
of `B` (`hD`), and let `f` be automorphic. Then the coefficient of `f` along the composite of `A`
and `B` at `0 ⊕ T` is the mean, over the centre of the radical for `A`, of the partial mean f⁺. Here
f⁺(g) is the mean over adelic rows `b` modulo rational rows of the coefficient of `f` along `D` at
`T` at `n₋(b) g`. -/
lemma borderedCentreCoeff_eq_quotMean (hD : D.kAdelic = A.iAdelic * B.kAdelic) {f : G E s → ℂ}
    (hf : IsAutFunction W f) (T : Matrix p p E) (g : G E s) :
    A.borderedCentreCoeff B T f g =
      quotMean (ratMatrices E Unit Unit) fun z : Matrix Unit Unit (𝔸 E) ↦
        A.partialMean B D T f (A.radicalCenter z * g) := by
  -- The integrand `Φ M` depends only on M₁₁, on M₁₂ − M₂₁ᴴ and on M₂₂. Take the mean over M₂₂, then
  -- over M₁₂ and M₂₁, then over M₁₁.
  let Φ (M : Matrix (Unit ⊕ p) (Unit ⊕ p) (𝔸 E)) : ℂ :=
    stdAddChar E ((fromBlocks 0 0 0 T).map toAdele * M).trace * f ((A.comp B).radicalCenter M * g)
  have hΦ : IsContPeriodic (ratMatrices E (Unit ⊕ p) (Unit ⊕ p)) Φ :=
    isDualFamily_ratMatrices.isContPeriodic_mul (isContPeriodic_radicalCentre _ hf g) _
  have hΦ_eq (z : Matrix Unit Unit (𝔸 E)) (b : Matrix Unit p (𝔸 E)) (c : Matrix p Unit (𝔸 E))
      (N : Matrix p p (𝔸 E)) :
      Φ (fromBlocks z b c N) = stdAddChar E (T.map toAdele * N).trace *
        f (D.radicalCenter N * (A.symm.lineShift B (b - cᴴ) * (A.radicalCenter z * g))) := by
    dsimp only [Φ]
    rw [radicalCentre_comp_fromBlocks hD, mul_assoc, mul_assoc]
    simp only [fromBlocks_map, Matrix.map_zero _ (map_zero toAdele), fromBlocks_multiply,
      Matrix.zero_mul, zero_add, add_zero, trace_fromBlocks, trace_zero]
  let φ₁ : Matrix Unit Unit (𝔸 E) × Matrix (Unit ⊕ p) (Unit ⊕ p) (𝔸 E) →+
      Matrix (Unit ⊕ p) (Unit ⊕ p) (𝔸 E) :=
    .mk' (fun (z, M) ↦ fromBlocks z M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂)
      fun _ _ ↦ by rw [fromBlocks_add]; rfl
  let φ₂ : Matrix (Unit ⊕ p) (Unit ⊕ p) (𝔸 E) × Matrix p p (𝔸 E) →+
      Matrix (Unit ⊕ p) (Unit ⊕ p) (𝔸 E) :=
    .mk' (fun (M, N) ↦ fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ N)
      fun _ _ ↦ by rw [fromBlocks_add]; rfl
  let π : Matrix (Unit ⊕ p) (Unit ⊕ p) (𝔸 E) →+ Matrix Unit p (𝔸 E) :=
    .mk' (fun M ↦ M.toBlocks₁₂ - M.toBlocks₂₁ᴴ)
      fun _ _ ↦ by ext1; simp [toBlocks₁₂, toBlocks₂₁, add_sub_add_comm]
  obtain ⟨hφ₁, hφ₂, hπ⟩ : Continuous φ₁ ∧ Continuous φ₂ ∧ Continuous π := by
    simp only [φ₁, φ₂, π, AddMonoidHom.mk'_apply, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂]
    refine ⟨?_, ?_, ?_⟩ <;> fun_prop
  have hφ₁_rat : ∀ z ∈ ratMatrices E Unit Unit, ∀ M ∈ ratMatrices E (Unit ⊕ p) (Unit ⊕ p),
      φ₁ (z, M) ∈ ratMatrices E (Unit ⊕ p) (Unit ⊕ p) := by
    rintro _ ⟨z, rfl⟩ _ ⟨M, rfl⟩
    refine ⟨fromBlocks z M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂, ?_⟩
    refine Matrix.ext fun i j ↦ ?_
    rcases i with i | i <;> rcases j with j | j <;> rfl
  have hφ₂_rat : ∀ M ∈ ratMatrices E (Unit ⊕ p) (Unit ⊕ p), ∀ N ∈ ratMatrices E p p,
      φ₂ (M, N) ∈ ratMatrices E (Unit ⊕ p) (Unit ⊕ p) := by
    rintro _ ⟨M, rfl⟩ _ ⟨N, rfl⟩
    refine ⟨fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ N, ?_⟩
    refine Matrix.ext fun i j ↦ ?_
    rcases i with i | i <;> rcases j with j | j <;> rfl
  have h_inner (z : Matrix Unit Unit (𝔸 E)) :
      (quotMean (ratMatrices E (Unit ⊕ p) (Unit ⊕ p)) fun M ↦ Φ (φ₁ (z, M))) =
        A.partialMean B D T f (A.radicalCenter z * g) := by
    have hΦz : IsContPeriodic (ratMatrices E (Unit ⊕ p) (Unit ⊕ p)) fun M ↦ Φ (φ₁ (z, M)) :=
      ⟨hΦ.1.comp (hφ₁.comp (continuous_const.prodMk continuous_id)), fun γ hγ M ↦ by
        have h := hΦ.2 _ (hφ₁_rat 0 (zero_mem _) γ hγ) (φ₁ (z, M))
        rwa [← map_add, Prod.mk_add_mk, zero_add] at h⟩
    have hφ₁₂ (M : Matrix (Unit ⊕ p) (Unit ⊕ p) (𝔸 E)) (N : Matrix p p (𝔸 E)) :
        φ₁ (z, φ₂ (M, N)) = fromBlocks z M.toBlocks₁₂ M.toBlocks₂₁ N := by
      refine Matrix.ext fun i j ↦ ?_
      rcases i with i | i <;> rcases j with j | j <;> rfl
    calc (quotMean (ratMatrices E (Unit ⊕ p) (Unit ⊕ p)) fun M ↦ Φ (φ₁ (z, M)))
      _ = quotMean (ratMatrices E (Unit ⊕ p) (Unit ⊕ p)) fun M ↦
            quotMean (ratMatrices E p p) fun N ↦ Φ (φ₁ (z, φ₂ (M, N))) :=
        (quotMean_quotMean _ hΦz _ φ₂ hφ₂ hφ₂_rat
          fun M ↦ ⟨(M, M.toBlocks₂₂), M.fromBlocks_toBlocks⟩).symm
      _ = quotMean (ratMatrices E (Unit ⊕ p) (Unit ⊕ p)) fun M ↦
            D.centerCoeff T f (A.symm.lineShift B (π M) * (A.radicalCenter z * g)) := by
        simp only [hφ₁₂, hΦ_eq, centerCoeff, π, AddMonoidHom.mk'_apply]
      _ = A.partialMean B D T f (A.radicalCenter z * g) := by
        refine quotMean_comp _ π (isContPeriodic_centreCoeff_lineShift (A := A.symm) hD hf _) ?_
          (fun b ↦ ⟨fromBlocks 0 b 0 0, by simp [π]⟩) hπ
        rintro _ ⟨M, rfl⟩
        exact ⟨M.toBlocks₁₂ - M.toBlocks₂₁ᴴ, by ext1; simp [π, toBlocks₁₂, toBlocks₂₁]⟩
  simp only [← h_inner]
  exact (quotMean_quotMean _ hΦ _ φ₁ hφ₁ hφ₁_rat
    fun M ↦ ⟨(M.toBlocks₁₁, M), M.fromBlocks_toBlocks⟩).symm

/-- If the frame of D is the image of the frame of B, the centre of the radical for A fixes it. -/
lemma actsOnFrame_radicalCentre_one (hD : D.kAdelic = A.iAdelic * B.kAdelic)
    (z : Matrix Unit Unit (𝔸 E)) : D.ActsOnFrame (A.radicalCenter z) 1 := by
  simp [hD, Matrix.add_mul, Matrix.mul_assoc]

/-- Let the frame of `D` be the image under `A` of the frame of `B` (`hD`), let `f` be automorphic,
`T` a p×p matrix over E and `U` a nonempty set of finite places, and let f⁺(x) be the mean, over
adelic rows b modulo rational rows, of the Fourier coefficient of `f` along `D` at `T` at
`A.symm.lineShift B b * x`. If f⁺ takes the same value at `g` and at νg for every shear
ν = 1 + ē·uc − e·a (e the idempotent adele of `U`, u = `A.kAdelic`, cu = 0), then
f⁺(`A.radicalCenter z * g`) = f⁺(g) for every adelic 1×1 matrix `z`. -/
lemma ShearInvariant.partialMean_radicalCentre_mul (hD : D.kAdelic = A.iAdelic * B.kAdelic)
    {f : G E s → ℂ} (hf : IsAutFunction W f) {T : Matrix p p E} {U : Set (FinPlace E)}
    (hU : U.Nonempty) {g : G E s} (h_shear : A.ShearInvariant B D T f (idemAdele U) g) :
    ∀ z : Matrix Unit Unit (𝔸 E),
      A.partialMean B D T f (A.radicalCenter z * g) = A.partialMean B D T f g := by
  -- The function of z is continuous and invariant under rational z and under z supported on U; the
  -- sums of these are dense.
  let e : 𝔸 E := idemAdele U
  suffices h_dense : ∀ (Y : Matrix Unit Unit E) (y : Matrix Unit Unit (𝔸 E)),
      A.partialMean B D T f (A.radicalCenter (Y.map toAdele + e • y) * g) =
        A.partialMean B D T f g from
    (denseRange_rat_matrix_add hU 1).eq
      (fun ⟨Y, y⟩ ↦ by
        dsimp only [Function.comp_apply]
        rw [inv_one, Units.val_one, Matrix.one_mul]
        exact h_dense Y y)
      ((continuous_partialMean hD hf).comp (A.continuous_radicalCenter.mul continuous_const))
  intro Y y
  -- A rational point of the centre commutes with the shifts n₋(b) and fixes the frame of D.
  have h_rat (x : G E s) :
      A.partialMean B D T f (A.radicalCenter (Y.map toAdele) * x) = A.partialMean B D T f x := by
    have h_comm (b : Matrix Unit p (𝔸 E)) :
        A.symm.lineShift B b * A.radicalCenter (Y.map toAdele) =
          A.radicalCenter (Y.map toAdele) * A.symm.lineShift B b := by
      have h_frame : A.ActsOnFrame (A.symm.lineShift B b) 1 := by
        have h_l : A.symm.lAdelic = A.kAdelic := rfl
        have h_k : A.symm.kCoord = A.lCoord := rfl
        rw [ActsOnFrame, adeleMatrix_lineShift, h_l, symm_iAdelic, h_k, symm_iCoord]
        simp only [Matrix.add_mul, Matrix.one_mul, Matrix.sub_mul, Matrix.mul_assoc,
          A.iCoord_mul_kAdelic, A.lCoord_mul_kAdelic, Matrix.mul_zero, Matrix.mul_one,
          sub_zero, add_zero]
      have h := A.mul_radicalCenter h_frame (Y.map toAdele)
      rwa [Matrix.one_mul, conjTranspose_one, Matrix.mul_one] at h
    simp only [partialMean, ← mul_assoc (A.symm.lineShift B _), h_comm]
    have h_mem : A.radicalCenter (Y.map toAdele) ∈ W.Γ := A.radicalCenter_mem ⟨Y, rfl⟩
    simp only [mul_assoc, D.centreCoeff_rat_mul_of_actsOnFrame_one hf h_mem
      (actsOnFrame_radicalCentre_one hD _)]
  -- A point of the centre supported on U ∪ Ū is a shear.
  have h_mat : (A.radicalCenter (e • y)).adeleMatrix =
      1 + (star e • (A.kAdelic * -(yᴴ * A.lCoord) :) - e • -(A.kAdelic * y * A.lCoord)) := by
    rw [adeleMatrix_radicalCenter, conjTranspose_smul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_neg, smul_neg, smul_neg, Matrix.mul_assoc, Matrix.mul_assoc]
    abel
  rw [AddChar.map_add_eq_mul, mul_assoc, h_rat, h_shear _ _ (by simp [Matrix.mul_assoc]) h_mat]

/-- Let the frame of D be the image of the frame of B, let f be automorphic and U a nonempty set of
finite places. If the partial mean f⁺ is invariant at g under the shears for U, then f⁺(g) is the
coefficient of f along the composite of A and B at 0 ⊕ T. -/
lemma ShearInvariant.borderedCentreCoeff_eq (hD : D.kAdelic = A.iAdelic * B.kAdelic)
    {f : G E s → ℂ} (hf : IsAutFunction W f) {T : Matrix p p E} {U : Set (FinPlace E)}
    (hU : U.Nonempty) {g : G E s} (h_shear : A.ShearInvariant B D T f (idemAdele U) g) :
    A.borderedCentreCoeff B T f g = A.partialMean B D T f g := by
  simp [borderedCentreCoeff_eq_quotMean hD hf, h_shear.partialMean_radicalCentre_mul hD hf hU]

/-- Let the frame of D be the image of the frame of B, let f be automorphic, T a p×p matrix over E
and U a nonempty set of finite places. Let f⁺(g) be the mean over adelic rows b, modulo rational
ones, of the coefficient of f along D at T at n₋(b) g. Suppose f⁺ is invariant at all points z g,
for z in the adelic centre of the radical for A, under the shears for U: the ν with matrix
1 + ē·uc − e·a, where e is the idempotent of U, u the isotropic vector of A and cu = 0. Then the
coefficient of f along the composite of A and B at 0 ⊕ T is invariant at g under the elements
`A.radicalElement c z` of the adelic radical for A. -/
lemma borderedCentreCoeff_radicalElement_mul (hD : D.kAdelic = A.iAdelic * B.kAdelic)
  {f : G E s → ℂ}
    (hf : IsAutFunction W f) {T : Matrix p p E} {U : Set (FinPlace E)} (hU : U.Nonempty)
    {g : G E s} (h_shear : ∀ z : Matrix Unit Unit (𝔸 E),
      A.ShearInvariant B D T f (idemAdele U) (A.radicalCenter z * g))
    (z : Matrix Unit Unit (𝔸 E)) :
    ∀ c : Matrix ((p ⊕ p) ⊕ n₂) Unit (𝔸 E),
      A.borderedCentreCoeff B T f (A.radicalElement c z * g) = A.borderedCentreCoeff B T f g := by
  let e : 𝔸 E := idemAdele U
  -- By strong approximation it suffices to take `c = W₀.x⁻¹ Y + e • y` with `Y` rational.
  refine (denseRange_rat_matrix_add hU W₀.x).eq fun ⟨Y, y⟩ ↦ ?_
  -- The rational point `A.radicalElement (W₀.x⁻¹ Y) 0` acts on the frame of `A.comp B` by a
  -- unipotent matrix `u` with `uᴴ (0 ⊕ T) u = 0 ⊕ T`.
  let Y₀ : Matrix ((p ⊕ p) ⊕ n₂) Unit (𝔸 E) := W₀.x⁻¹.val * Y.map toAdele
  let u : Matrix (Unit ⊕ p) (Unit ⊕ p) E := fromBlocks 1 (Yᴴ * W₀.J * B.k) 0 1
  have h_frame : (A.comp B).ActsOnFrame (A.radicalElement Y₀ 0) (u.map toAdele) := by
    rw [ActsOnFrame, comp_kAdelic, Matrix.mul_fromCols]
    simp only [u, fromBlocks_map, Matrix.map_one _ (map_zero toAdele) (map_one toAdele),
      Matrix.map_zero _ (map_zero toAdele), fromCols_mul_fromBlocks,
      Matrix.mul_one, Matrix.mul_zero, add_zero]
    congr 1
    · exact (A.actsOnFrame_radicalElement Y₀ 0).trans (Matrix.mul_one _)
    · rw [← Matrix.mul_assoc, A.radicalElement_mul_iAdelic, Matrix.add_mul, add_comm]
      congr 1
      have hB : B.kAdelic = W₀.x⁻¹.val * B.k.map toAdele := rfl
      rw [Matrix.mul_assoc, Matrix.mul_assoc]
      congr 1
      dsimp only [Y₀]
      rw [hB, Matrix.map_mul, Matrix.map_mul, ← conjTranspose_map_toAdele, W₀.map_J,
        conjTranspose_mul]
      simp only [Matrix.mul_assoc]
  have h_rat (g' : G E s) :
      A.borderedCentreCoeff B T f (A.radicalElement Y₀ 0 * g') =
        A.borderedCentreCoeff B T f g' := by
    rw [borderedCentreCoeff,
      centreCoeff_rat_mul _ hf _ (A.radicalElement_mem_Gamma Y (by simp)) u h_frame]
    simp only [u, fromBlocks_conjTranspose, conjTranspose_one, conjTranspose_zero,
      fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one,
      add_zero, zero_add]
  -- The centre of the radical for `A` pairs trivially with `0 ⊕ T`.
  have h_centre (M : Matrix Unit Unit (𝔸 E)) (g' : G E s) :
      A.borderedCentreCoeff B T f (A.radicalCenter M * g') = A.borderedCentreCoeff B T f g' := by
    have h := centreCoeff_radicalCentre_mul (A.comp B) hf (T := fromBlocks 0 0 0 T)
      (fromBlocks M 0 0 0) g'
    rw [radicalCentre_comp_fromBlocks hD] at h
    simp only [conjTranspose_zero, sub_self, lineShift_zero, one_mul, AddChar.map_zero_eq_one,
      fromBlocks_map, Matrix.map_zero _ (map_zero toAdele), fromBlocks_multiply, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, trace_fromBlocks, trace_zero, Circle.coe_one] at h
    exact h
  -- The element `ν` of the radical is a shear, and it commutes with the centre.
  let ν : G E s := A.radicalElement (e • y) 0
  have h_local : A.borderedCentreCoeff B T f (ν * g) = A.borderedCentreCoeff B T f g := by
    let c₁ : Matrix Unit n (𝔸 E) := yᴴ * stdForm E (hyperbolicSigns p ⊕ᵥ s₂) *
      (A.iCoord - toAdele (2⁻¹ : E) • e • y * A.lCoord)
    have h_mat : ν.adeleMatrix = 1 + (star e • (A.kAdelic * c₁ :) - e •
      (A.iAdelic * y * A.lCoord)) := by
      dsimp only [ν, Splitting.radicalElement]
      rw [G.adeleMatrix_ofMatrix]
      simp only [c₁, conjTranspose_zero, add_zero, smul_zero, zero_add, conjTranspose_smul,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, smul_sub, Matrix.mul_assoc]
      have h_sc : toAdele (2⁻¹ : E) • e • star e •
          (A.kAdelic * (yᴴ * (stdForm E (hyperbolicSigns p ⊕ᵥ s₂) * (y * A.lCoord)))) =
          star e • toAdele (2⁻¹ : E) • e •
            (A.kAdelic * (yᴴ * (stdForm E (hyperbolicSigns p ⊕ᵥ s₂) * (y * A.lCoord)))) := by
        simp only [smul_smul]
        congr 1
        rw [mul_comm e, ← mul_assoc, mul_comm _ (star e), mul_assoc]
      rw [h_sc]
      abel
    have h_comm (w : Matrix Unit Unit (𝔸 E)) :
        A.radicalCenter w * (ν * g) = ν * (A.radicalCenter w * g) := by
      rw [← mul_assoc ν, A.mul_radicalCenter (A.actsOnFrame_radicalElement _ _), mul_assoc]
      simp [ν]
    simp only [borderedCentreCoeff_eq_quotMean hD hf, h_comm,
      h_shear _ c₁ _ (by simp [c₁, sub_eq_add_neg, Matrix.mul_assoc, Matrix.add_mul]) h_mat]
  -- The element is a product of a rational point, a point of the centre and the shear.
  let z' : Matrix Unit Unit (𝔸 E) :=
    z - toAdele (j : E) • Y₀ᴴ * stdForm E (hyperbolicSigns p ⊕ᵥ s₂) * (e • y)
  have h_central : A.radicalCenter (-toAdele (j * 2 : E)⁻¹ • z') = A.radicalElement 0 z' := by
    change A.radicalElement 0 (-toAdele (j * 2 : E) • -toAdele (j * 2 : E)⁻¹ • z') = _
    rw [smul_smul, neg_mul_neg, ← map_mul, mul_inv_cancel₀ (by simp [j_ne_zero]), map_one, one_smul]
  have h_split : A.radicalElement (Y₀ + e • y) z =
      A.radicalElement Y₀ 0 * (A.radicalElement 0 z' * ν) := by
    simp [ν, z', radicalElement_mul]
  rw [h_split, mul_assoc, mul_assoc, h_rat, ← h_central, h_centre, h_local]

/-- Singularity. Let the frame of D be the image of the frame of B, let f be automorphic, T a p×p
matrix over E, U a nonempty set of finite places and e an adele. Let f⁺(g) be the mean over adelic
rows b, modulo rational ones, of the coefficient of f along D at T at n₋(b) g. Suppose f⁺ is
invariant under the shears 1 + 1̄_U·uc − 1_U·a for U (1_U the idempotent of U, u the isotropic
vector of A, cu = 0) at all points that fix e·k, k the frame of D. If g and h g fix e·k, for
h = `A.radicalElement c z` in the adelic radical of the stabiliser of the line of A, then
f⁺(h g) = f⁺(g). -/
lemma partialMean_radicalElement_mul (hD : D.kAdelic = A.iAdelic * B.kAdelic) {f : G E s → ℂ}
    (hf : IsAutFunction W f) {T : Matrix p p E} {U : Set (FinPlace E)} (hU : U.Nonempty) {e : 𝔸 E}
    (h_shear : ∀ g ∈ D.frameStabilizer e, A.ShearInvariant B D T f (idemAdele U) g) {g : G E s}
    {c : Matrix ((p ⊕ p) ⊕ n₂) Unit (𝔸 E)} {z : Matrix Unit Unit (𝔸 E)}
    (hg : g ∈ D.frameStabilizer e) (h_mem : A.radicalElement c z * g ∈ D.frameStabilizer e) :
    A.partialMean B D T f (A.radicalElement c z * g) = A.partialMean B D T f g := by
  calc A.partialMean B D T f (A.radicalElement c z * g)
    _ = A.borderedCentreCoeff B T f (A.radicalElement c z * g) :=
      ((h_shear _ h_mem).borderedCentreCoeff_eq hD hf hU).symm
    _ = A.borderedCentreCoeff B T f g := borderedCentreCoeff_radicalElement_mul hD hf hU
      (fun w ↦ h_shear _ (mul_mem ((actsOnFrame_radicalCentre_one hD w).mem_frameStabilizer e) hg))
      z c
    _ = A.partialMean B D T f g := (h_shear g hg).borderedCentreCoeff_eq hD hf hU

end Singularity

end New.Space.Splitting
