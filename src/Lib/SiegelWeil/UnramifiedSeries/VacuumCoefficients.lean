module

public import Lib.Weil.DualPair.Defs
import Lib.Adelic.AutomorphicForms.PAdicGauge
import Lib.ClassField.HeckeCharacter.SplitTameCharacters

/-!
# Vacuum coefficients and coset representatives

This file defines the coefficients of the vacuum `New.SiegelWeil.vacuumCoeff`, the representatives
`New.SiegelWeil.cosetRep` of the cosets of `localLevel n A` and the series
`New.SiegelWeil.rallisSeries`. It shows that the coefficients and the cosets are multiplicative over
two sets of places with disjoint supports.

## Main definitions and results

* `New.SiegelWeil.vacuumCoeff`, `New.SiegelWeil.cosetRep`, `New.SiegelWeil.rallisSeries`: the
  coefficients, the representatives of the cosets and the series.

Notions from other files:
* `localLevel n A`: the points of `Gf E n` integral at the places of `A`; `stdLevel E n`: the points
  integral at all finite places.
* `supportedOn n A`: the points with component `1` outside `A` and its conjugate, whose union is
  `A.conjClosure`; `trivialOn n A`: the points with component `1` at `A`.
* `finMultiplier`: the multiplier of a finite point; its squared modulus is the index
  `[L : L ∩ γ⁻¹ L] = [γ L : L ∩ γ L]` at the point `γ`.
* `AutChar E`: the characters `b` of the norm-one adeles of `E` trivial on the norm-one elements of
  `E`; `detFin 1 g`: the determinant of the finite point `g`, as such an adele with component `1` at
  the infinite places.
* `HasLevel y K`: right translation by each point of `K` fixes the function `y` on the adelic points
  `G E s`, the products of a point of `GInf E s` (the real points, the only part that depends on the
  signs `s : n → ℤˣ`) and a point of `Gf E n`.

## Relation to the literature

Known; see `Lib.SiegelWeil.UnramifiedSeries.RallisSeries` for sources.
-/

@[expose] public section

noncomputable section

namespace New.SiegelWeil

open Matrix MeasureTheory Fintype Space Gf G WeilData NumberField Rows

variable {E n m : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] [Fintype m]
  {s : n → ℤˣ} {b : AutChar E} {A : Set (FinPlace E)} {y : G E s → ℂ}

/-! ### Vacuum coefficients and coset representatives -/

/-- For `g` in the finite adelic unitary group, the multiplier `finMultiplier g` is the
`glMultiplier` of its underlying matrix in GL_n(𝔸_f). It is unchanged by multiplying `g` on either
side by integral finite points: `finMultiplier (k * g * k') = finMultiplier g` for all `k, k'` in
`stdLevel E n` = G_f ∩ GL_n(Ô). -/
lemma finMultiplier_mul_mul_of_mem_stdLevel {k k' : Gf E n} (hk : k ∈ stdLevel E n)
    (hk' : k' ∈ stdLevel E n) (g : Gf E n) : finMultiplier (k * g * k') = finMultiplier g :=
  glMultiplier_mul_of_mem g.val hk hk'

/-- The multiplier of a product of two finite points of which, at each place, one has component
`1` is the product of their multipliers. -/
lemma finMultiplier_mul_of_forall_atPlace_eq_one_or {g g' : Gf E n}
    (h_atPlace : ∀ w : FinPlace E, g.atPlace w = 1 ∨ g'.atPlace w = 1) :
    finMultiplier (g * g') = finMultiplier g * finMultiplier g' :=
  glMultiplier_mul_of_map_evalAt_eq_one h_atPlace

/-- The number `(b(det g) * finMultiplier g ^ M)⁻¹` for a finite point `g`. For `M` the rank of
the second hermitian space of a pair it is the factor by which `g` changes the matrix coefficient
of a vacuum (`New.SiegelWeil.weilMatrixCoeff_mul`). -/
def vacuumCoeff (M : ℕ) (b : AutChar E) (g : Gf E n) : ℂ :=
  (b.val (detFin 1 g) * finMultiplier g ^ M)⁻¹

/-- For a coset `γ` of `localLevel n A`, the finite points integral at `A`, the component above
`A` and its conjugate of a chosen element of `γ`. It represents `γ` (`mk_cosetRep`) and is
supported on `A` and its conjugate. -/
def cosetRep (γ : Gf E n ⧸ localLevel n A) : supportedOn n A :=
  ⟨componentOn n A γ.out, componentOn_mem_supportedOn⟩

omit [WeilData E] in
lemma mk_cosetRep (q : Gf E n ⧸ localLevel n A) :
    ((cosetRep q).val : Gf E n ⧸ localLevel n A) = q := by
  conv_rhs => rw [← q.out_eq']
  rw [QuotientGroup.eq, mem_localLevel]
  exact fun w hw ↦ by simp [cosetRep, atPlace_componentOn, hw]

omit [WeilData E] in
lemma isOpen_coe_localLevel (A : Set (FinPlace E)) : IsOpen (localLevel n A : Set (Gf E n)) :=
  Subgroup.isOpen_mono stdLevel_le_localLevel isOpen_stdLevel

omit [WeilData E] in
lemma countable_quotient_localLevel (A : Set (FinPlace E)) :
    Countable (Gf E n ⧸ localLevel n A) := by
  have := QuotientGroup.discreteTopology (isOpen_coe_localLevel (n := n) A)
  exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance

omit [WeilData E] in
/-- For `A ⊆ B`, viewing the chosen representatives at `A` as cosets at `B` is injective:
the natural quotient map sends each representative back to its original coset. -/
lemma cosetRep_injective_of_subset {B : Set (FinPlace E)} (hAB : A ⊆ B) :
    Function.Injective fun q : Gf E n ⧸ localLevel n A ↦
      ((cosetRep q).val : Gf E n ⧸ localLevel n B) := by
  have h_level : localLevel n B ≤ localLevel n A := fun _ hg w hw ↦ hg w (hAB hw)
  refine Function.LeftInverse.injective (g := Subgroup.quotientMapOfLE h_level) fun q ↦ ?_
  rw [Subgroup.quotientMapOfLE_apply_mk, mk_cosetRep]

/-- The character `b ∘ det` is trivial on `stdLevel E n ⊓ supportedOn n A`, the integral finite
points whose component is `1` at every place outside `A` and its conjugate. -/
def IsUnramifiedOn (b : AutChar E) (n : Type) [Fintype n] [DecidableEq n]
    (A : Set (FinPlace E)) : Prop :=
  ∀ k ∈ stdLevel E n ⊓ supportedOn n A, b.val (detFin 1 k) = 1

omit [WeilData E] in
/-- If `b` has weight `γ` at the infinite places and a tame part `ψ` (the characters of the residue
fields through which `b` acts on integral units) that is trivial at `A` and its conjugate, then
`b ∘ det` is trivial on the integral finite points supported there. -/
lemma _root_.New.AutChar.HasWeight.isUnramifiedOn {γ : InfinitePlace E → ℤ}
    {ψ : ∀ w : FinPlace E, MulChar (ResField w) ℂ} (hb : b.HasWeight γ ψ)
    (hψ : ∀ w ∈ A.conjClosure, ψ w = 1) : IsUnramifiedOn b n A :=
  fun _k hk ↦ hb.apply_det_eq_one_of_supportedOn hψ hk

/-- Let `b ∘ det` be trivial on the integral points supported on `A` and its conjugate. The
coefficient of the vacuum is invariant on both sides under these points. -/
lemma vacuumCoeff_mul_mul_of_mem (hb : IsUnramifiedOn b n A) (M : ℕ) {k k' : Gf E n}
    (hk : k ∈ stdLevel E n ⊓ supportedOn n A) (hk' : k' ∈ stdLevel E n ⊓ supportedOn n A)
    (g : Gf E n) :
    vacuumCoeff M b (k * g * k') = vacuumCoeff M b g := by
  have h_det : detFin 1 (k * g * k') = detFin 1 k * detFin 1 g * detFin 1 k' := by simp [← map_mul]
  rw [vacuumCoeff, vacuumCoeff, h_det, finMultiplier_mul_mul_of_mem_stdLevel hk.1 hk'.1 g, map_mul,
    map_mul, hb _ hk, hb _ hk', one_mul, mul_one]

/-- Let `b ∘ det` be trivial on the integral finite points whose component is `1` outside `A` and
its conjugate (`IsUnramifiedOn`). Then for every `M : ℕ`, the coefficient of the vacuum `vacuumCoeff
M b k = (b(det k) · finMultiplier k ^ M)⁻¹` equals `1` at each such point `k`. -/
lemma vacuumCoeff_eq_one_of_mem (hb : IsUnramifiedOn b n A) (M : ℕ) {k : Gf E n}
    (hk : k ∈ stdLevel E n ⊓ supportedOn n A) : vacuumCoeff M b k = 1 := by
  simp [vacuumCoeff, hb _ hk, finMultiplier_eq_one_of_mem hk.1]

/-- The coefficient of the vacuum is multiplicative on two finite points of which, at each place,
one has component `1`. -/
lemma vacuumCoeff_mul_of_atPlace (M : ℕ) (b : AutChar E) {g g' : Gf E n}
    (h_atPlace : ∀ w : FinPlace E, g.atPlace w = 1 ∨ g'.atPlace w = 1) :
    vacuumCoeff M b (g * g') = vacuumCoeff M b g * vacuumCoeff M b g' := by
  have h_det : detFin 1 (g * g') = detFin 1 g * detFin 1 g' := by simp [← map_mul]
  rw [vacuumCoeff, vacuumCoeff, vacuumCoeff, h_det,
    finMultiplier_mul_of_forall_atPlace_eq_one_or h_atPlace,
    map_mul, Circle.coe_mul]
  ring

/-- The series `∑ mc(q) R(q) y` of right translates of a function `y` on the adelic points. The sum
is over the cosets `q`, in the finite points, of the subgroup of the points integral at `A`. The
coefficient of the vacuum `mc = vacuumCoeff M b` and the right translation `R` are taken at the
representative `cosetRep q`, which is supported on `A` and its conjugate; see
`mk_eq_mk_iff_of_supportedOn` for the cosets among such points and
`vacuumCoeff_mul_apply_cosetRep` for conditions under which the choice does not matter. The value
is `0` where the terms are not summable. -/
def rallisSeries (M : ℕ) (b : AutChar E) (A : Set (FinPlace E)) (y : G E s → ℂ) (g : G E s) : ℂ :=
  ∑' q : Gf E n ⧸ localLevel n A, vacuumCoeff M b (cosetRep q).val * y (g * (1, (cosetRep q).val))

omit [WeilData E] in
/-- Two finite points supported on `A` and its conjugate lie in the same coset of the points
integral at `A` exactly when they lie in the same coset of the integral points with such support. -/
lemma mk_eq_mk_iff_of_supportedOn {u u' : Gf E n} (hu : u ∈ supportedOn n A)
    (hu' : u' ∈ supportedOn n A) :
    (u : Gf E n ⧸ localLevel n A) = u' ↔ u⁻¹ * u' ∈ stdLevel E n ⊓ supportedOn n A := by
  rw [QuotientGroup.eq, Subgroup.mem_inf, and_iff_left (mul_mem (inv_mem hu) hu'),
    mem_stdLevel_iff_of_supportedOn (mul_mem (inv_mem hu) hu'), mem_localLevel]

omit [WeilData E] in
/-- The chosen representative of the coset of a point `u` supported on `A` and its conjugate differs
from `u` on the right by an integral point with such support. -/
lemma inv_mul_cosetRep_mem {u : Gf E n} (hu : u ∈ supportedOn n A) :
    u⁻¹ * (cosetRep (u : Gf E n ⧸ localLevel n A)).val ∈ stdLevel E n ⊓ supportedOn n A :=
  (mk_eq_mk_iff_of_supportedOn hu (cosetRep _).property).1 (mk_cosetRep _).symm

/-- The terms of `rallisSeries` do not depend on the representatives. Let `b ∘ det` be trivial on
the integral points supported on `A` and its conjugate, and let `y` be fixed by these points. The
term of the coset of a point `u` supported on `A` and its conjugate may be computed at `u`. -/
lemma vacuumCoeff_mul_apply_cosetRep (hb : IsUnramifiedOn b n A) (M : ℕ)
    (hy : HasLevel y (stdLevel E n ⊓ supportedOn n A)) {u : Gf E n} (hu : u ∈ supportedOn n A)
    (g : G E s) :
    vacuumCoeff M b (cosetRep (u : Gf E n ⧸ localLevel n A)).val *
        y (g * (1, (cosetRep (u : Gf E n ⧸ localLevel n A)).val)) =
      vacuumCoeff M b u * y (g * (1, u)) := by
  -- The representative is `u * j` with `j` integral and supported on `A` and its conjugate.
  let j : Gf E n := u⁻¹ * (cosetRep (u : Gf E n ⧸ localLevel n A)).val
  have hj : j ∈ stdLevel E n ⊓ supportedOn n A := inv_mul_cosetRep_mem hu
  have h_coeff : vacuumCoeff M b (u * j) = vacuumCoeff M b u := by
    simpa only [one_mul] using vacuumCoeff_mul_mul_of_mem hb M (one_mem _) hj u
  have h_assoc : g * (1, u * j) = g * (1, u) * (1, j) := by simp [mul_assoc]
  have h_rep : (cosetRep (u : Gf E n ⧸ localLevel n A)).val = u * j :=
    (mul_inv_cancel_left u _).symm
  rw [h_rep, h_coeff, h_assoc, hy j hj]

/-- The modulus of the coefficient of the vacuum at `g` is `‖finMultiplier g‖ ^ (-M)`; it does not
depend on the character. -/
lemma norm_vacuumCoeff (M : ℕ) (b : AutChar E) (g : Gf E n) :
    ‖vacuumCoeff M b g‖ = ‖finMultiplier g‖⁻¹ ^ M := by
  simp [vacuumCoeff, Circle.norm_coe]

/-- The multiplier of the chosen representative of the coset of a point `u` supported on `A` and its
conjugate is the multiplier of `u`. -/
lemma finMultiplier_cosetRep_mk {u : Gf E n} (hu : u ∈ supportedOn n A) :
    finMultiplier (cosetRep (u : Gf E n ⧸ localLevel n A)).val = finMultiplier u := by
  obtain ⟨h_int, -⟩ := Subgroup.mem_inf.1 (inv_mul_cosetRep_mem hu)
  have h_mult : finMultiplier (1 * u * (u⁻¹ * (cosetRep (u : Gf E n ⧸ localLevel n A)).val)) =
      finMultiplier u :=
    finMultiplier_mul_mul_of_mem_stdLevel (one_mem _) h_int u
  rwa [one_mul, mul_inv_cancel_left] at h_mult

/-! ### Two sets of places with disjoint supports -/

section Union

variable {A₁ A₂ : Set (FinPlace E)}

omit [WeilData E] in
/-- If `A₂` is disjoint from `A₁` and its conjugate, the points supported on `A₁` and its conjugate
are trivial at `A₂`. -/
lemma supportedOn_le_trivialOn_right (h_disj : Disjoint A₁.conjClosure A₂) :
    supportedOn n A₁ ≤ trivialOn n A₂ := fun _ hg ↦
  mem_trivialOn.2 fun w hw ↦ mem_supportedOn.1 hg w
    (fun hw₁ ↦ h_disj.notMem_of_mem_left (.inl hw₁) hw)
    (fun hw₁ ↦ h_disj.notMem_of_mem_left (.inr hw₁) hw)

omit [WeilData E] in
/-- If `A₂` is disjoint from `A₁` and its conjugate, the points supported on `A₂` and its conjugate
are trivial at `A₁`. -/
lemma supportedOn_le_trivialOn_left (h_disj : Disjoint A₁.conjClosure A₂) :
    supportedOn n A₂ ≤ trivialOn n A₁ := fun g hg ↦
  mem_trivialOn.2 fun w hw ↦ mem_supportedOn.1 hg w (h_disj.notMem_of_mem_left (.inl hw))
    (h_disj.notMem_of_mem_left (.inr (by simpa)))

omit [WeilData E] in
/-- Let `A₂` be disjoint from `A₁` and its conjugate, and let `u₁`, `u₂` be supported on `A₁`, `A₂`
and their conjugates. Then `u₁ * u₂` represents the coset of `g` at `A₁ ∪ A₂` exactly when `u₁`
represents it at `A₁` and `u₂` represents it at `A₂`. -/
lemma mk_mul_eq_mk_iff (h_disj : Disjoint A₁.conjClosure A₂) {u₁ u₂ : Gf E n}
    (hu₁ : u₁ ∈ supportedOn n A₁) (hu₂ : u₂ ∈ supportedOn n A₂) (g : Gf E n) :
    ((u₁ * u₂ : Gf E n) : Gf E n ⧸ localLevel n (A₁ ∪ A₂)) = g ↔
      (u₁ : Gf E n ⧸ localLevel n A₁) = g ∧ (u₂ : Gf E n ⧸ localLevel n A₂) = g := by
  have h_left : ∀ w ∈ A₁, u₂.atPlace w = 1 :=
    mem_trivialOn.1 (supportedOn_le_trivialOn_left h_disj hu₂)
  have h_right : ∀ w ∈ A₂, u₁.atPlace w = 1 :=
    mem_trivialOn.1 (supportedOn_le_trivialOn_right h_disj hu₁)
  have h_at₁ : ∀ w ∈ A₁, ((u₁ * u₂)⁻¹ * g).atPlace w = (u₁⁻¹ * g).atPlace w :=
    fun w hw ↦ by simp [h_left w hw]
  have h_at₂ : ∀ w ∈ A₂, ((u₁ * u₂)⁻¹ * g).atPlace w = (u₂⁻¹ * g).atPlace w :=
    fun w hw ↦ by simp [h_right w hw]
  simp +contextual only [QuotientGroup.eq, mem_localLevel, Set.mem_union, or_imp, forall_and,
    h_at₁, h_at₂]

omit [WeilData E] in
/-- Let `A₂` be disjoint from `A₁` and its conjugate. The cosets at `A₁ ∪ A₂` are the products of a
coset at `A₁` and a coset at `A₂`. -/
lemma bijective_mk_cosetRep_mul (h_disj : Disjoint A₁.conjClosure A₂) :
    Function.Bijective fun p : (Gf E n ⧸ localLevel n A₁) × (Gf E n ⧸ localLevel n A₂) ↦
      (((cosetRep p.1).val * (cosetRep p.2).val : Gf E n) : Gf E n ⧸ localLevel n (A₁ ∪ A₂)) := by
  -- The product represents the coset of `g` exactly when `p` is the pair of cosets of `g`.
  have h_iff (p : (Gf E n ⧸ localLevel n A₁) × (Gf E n ⧸ localLevel n A₂)) (g : Gf E n) :
      (((cosetRep p.1).val * (cosetRep p.2).val : Gf E n) : Gf E n ⧸ localLevel n (A₁ ∪ A₂)) = g ↔
        p = ((g : Gf E n ⧸ localLevel n A₁), (g : Gf E n ⧸ localLevel n A₂)) := by
    simp [mk_mul_eq_mk_iff h_disj (cosetRep _).property (cosetRep _).property, mk_cosetRep,
      Prod.ext_iff]
  refine ⟨fun p p' h_eq ↦ ((h_iff p _).1 h_eq).trans ((h_iff p' _).1 rfl).symm, fun q ↦ ?_⟩
  induction q using QuotientGroup.induction_on with
  | H g => exact ⟨_, (h_iff _ g).2 rfl⟩

/-- For `M : ℕ` and a character `b`, `vacuumCoeff M b g = (b(det g) · finMultiplier g ^ M)⁻¹` is the
factor by which a finite point `g` changes the matrix coefficient of a vacuum when `M` is the rank
of the second hermitian space. If `A₂` is disjoint from `A₁` and its conjugate, then `vacuumCoeff M
b (u₁ * u₂) = vacuumCoeff M b u₁ * vacuumCoeff M b u₂`. This holds whenever `u₁` is a finite point
supported on `A₁` and its conjugate, and `u₂` is one supported on `A₂` and its conjugate; supported
means having component `1` at every other place. -/
lemma vacuumCoeff_mul_of_disjoint (h_disj : Disjoint A₁.conjClosure A₂) (M : ℕ) (b : AutChar E)
    {u₁ u₂ : Gf E n} (hu₁ : u₁ ∈ supportedOn n A₁) (hu₂ : u₂ ∈ supportedOn n A₂) :
    vacuumCoeff M b (u₁ * u₂) = vacuumCoeff M b u₁ * vacuumCoeff M b u₂ :=
  vacuumCoeff_mul_of_atPlace M b
    (atPlace_eq_one_or hu₁ (supportedOn_le_trivialOn_left h_disj hu₂))

end Union

end New.SiegelWeil

end
