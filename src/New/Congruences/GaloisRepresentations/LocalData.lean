module

public import Lib.ClassField.Avatar.HeckeBaseChange
public import Lib.GaloisRep.Main.LocalConditions
public import Lib.GaloisRep.Main.SelmerModules
public import Lib.General.LinearAlgebra.MatrixPolynomials
public import Lib.PadicHodge.Characters
public import New.Reduction.Data.LevelAndTwists

/-!
# Galois data and local conditions for Selmer bounds

Fix admissible data `D` with CM field `D.E`. Its cyclotomic embedding specifies the absolute
Galois group on which the inverse avatar of a tame character and the representations below act.
`New.Selmer.badPlaces` records the places above the residual characteristic and the level.

## Main definitions and results

* `New.Selmer.IsConjSelfDual`: `R` is continuous, has a non-degenerate trace form on the span of
  its image, and is conjugate self-dual up to a twist.
* `New.Selmer.IsConjSelfDualOfLevel`: moreover `R` has given jumps and is of finite type at the
  places off a set `S` and at those above `ℓ p₀ p₁`, and has good reduction at those of them prime
  to `p₀ p₁`.
-/

@[expose] public section

noncomputable section

namespace New.Selmer

open GaloisRep Units

section

variable {P : Parameters} (D : Data P) (ℓ : ℕ) [ThePrime ℓ]

/-- `D.E` is a `New.CMFieldWithRoot5040`. Its embedding in `Ω` factors through the cyclotomic field
of conductor `D.cyclotomicConductor`. -/
noncomputable instance : CMFieldWithRoot5040 D.E :=
  {((cycloField _).val.comp P.toCycloField).toAlgebra with}

lemma _root_.New.Data.algebraMap_mem_cycloField (x : D.E) :
    algebraMap D.E Ω x ∈ cycloField D.cyclotomicConductor :=
  Subtype.prop (P.toCycloField x)

/-! ### The Galois group and the bad places -/

/-- The absolute Galois group of the field E of the data D: automorphisms of an algebraic
closure of E fixing E. -/
abbrev AbsGal : Type := Gal(Ω/D.E)

/-- The set of finite places of E above one of the two primes p₀, p₁ of the data. -/
def placesAboveM : Set (FinPlace D.E) :=
  {v : FinPlace D.E | ∃ i : Fin 2, ↑(D.levelPrime i) ∈ v.asIdeal}

/-- The finite set of places of E dividing `ℓ p₀ p₁ N`, with `N` the level of the data; these are
the bad places. -/
noncomputable def badPlaces : Finset (FinPlace D.E) :=
  (finite_natCast_mem (K := D.E) (ℓ * (D.M * D.N))).toFinset

/-- The places dividing `ℓ` and the places above `p₀` or `p₁` are bad places. -/
lemma placesDividing_union_subset_badPlaces :
    placesDividing D.E ℓ ∪ placesAboveM D ⊆ badPlaces D ℓ := by
  intro w hw
  -- A prime ideal contains `ℓ p₀ p₁ N` as soon as it contains one of the factors.
  suffices h_mem : ↑(ℓ * (D.M * D.N)) ∈ w.asIdeal by simpa [badPlaces] using h_mem
  obtain hℓ | ⟨i, hi⟩ := hw
  · simpa using w.asIdeal.mul_mem_right _ hℓ
  · have h_dvd : D.levelPrime i ∣ D.M := by fin_cases i <;> simp [Data.M]
    exact w.asIdeal.mem_of_dvd (Nat.cast_dvd_cast ((h_dvd.mul_right D.N).mul_left ℓ)) hi

variable {D ℓ}

/-- A chosen place (`New.Data.IsChosen`) lies above `p₀` or `p₁`. -/
lemma _root_.New.Data.IsChosen.mem_placesAboveM {v : FinPlace D.E} (hv : D.IsChosen v) :
    v ∈ placesAboveM D :=
  let ⟨i, _, h_above⟩ := D.isChosen_iff.1 hv
  ⟨i, h_above⟩

@[simp, grind =]
lemma star_mem_placesAboveM {v : FinPlace D.E} : star v ∈ placesAboveM D ↔ v ∈ placesAboveM D := by
  simp [placesAboveM]

/-- Two distinct `N`-th roots of unity in `ℚ̄_ℓ` have distance at least `‖N‖`. -/
lemma norm_natCast_le_norm_sub_of_pow_eq_one {x y : PadicAlgCl ℓ} {N : ℕ} :
    x ^ N = 1 → y ^ N = 1 → x ≠ y → ‖(N : PadicAlgCl ℓ)‖ ≤ ‖x - y‖ := by
  intro hx hy hxy
  by_contra! h_lt
  -- Roots of unity closer than `N` in the valuation are equal.
  have h_val : intQpBar ℓ (x - y) < intQpBar ℓ N :=
    lt_of_not_ge fun h_le ↦ h_lt.not_ge ((valuation_intQpBar_le_iff _ _).1 h_le)
  exact hxy (eq_of_pow_eq_one_of_val_sub_lt hx hy h_val)

@[fun_prop]
lemma continuous_cyclotomicInv : Continuous (cyclotomicInv ℓ D.E (PadicAlgCl ℓ)) :=
  continuous_coe_inv.comp continuous_cyclotomicCharIn

/-- For a Frobenius datum `x` whose place `x.place` does not divide `ℓ`, the inverse cyclotomic
character `cyclotomicInv ℓ D.E (PadicAlgCl ℓ)` takes the value `x.place.q`, the norm of `x.place`,
at `x.frob`, a geometric Frobenius at `x.place`. -/
lemma cyclotomicInv_frob (x : FrobeniusDatum D.E) (hℓ : ↑ℓ ∉ x.place.asIdeal) :
    cyclotomicInv ℓ D.E (PadicAlgCl ℓ) x.frob = x.place.q := by
  have h_unit : x.valuationSubring.valuation (ℓ : Ω) = 1 :=
    x.isPlaceOver.valuation_natCast_eq_one_iff.2 hℓ
  simp [cyclotomicInv, ← map_inv, x.isFrob_inv.cyclotomicChar_eq ℓ h_unit]

variable [PadicIso ℓ]

/-- The ℓ-adic avatar, through ι, of the base change to E of ϑ⁻¹: a character of the absolute
Galois group of E with values in ℚ̄_ℓ. Here ι is the isomorphism of ℂ with ℚ̄_ℓ that the instance
`New.PadicIso ℓ` fixes. -/
noncomputable def _root_.New.Data.TameChar.invAvatar (ϑ : D.TameChar) : AbsGal D →* PadicAlgCl ℓ :=
  (coeHom (PadicAlgCl ℓ)).comp (ϑ.hasWeight.inv.toAlgebraic 0 0).avatar

end

section

variable {ℓ : ℕ} [ThePrime ℓ] {P : Parameters} {D : Data P} [PadicIso ℓ]
  {n : Type} [Fintype n] [DecidableEq n]
  (t : ℕ) (J : (D.E →+* ℂ) → Multiset ℤ) (S : Set (FinPlace D.E)) (R : GalRep ℓ D.E n)

/-- `R` is continuous, has non-degenerate trace form, and is conjugate self-dual up to twist,
`R^c ≅ R^∨(1 − t)`. Self-duality is stated on traces: `tr R(g^c) = cyc(g)^{1−t} tr R(g⁻¹)` for all
`g`, where `t = 0` is read as `t = 1`. -/
structure IsConjSelfDual : Prop where
  /-- `R` is continuous. -/
  continuous : Continuous R
  /-- The trace form on the span of the image of `R` is non-degenerate. -/
  nondeg : IsTraceNondeg R
  /-- Conjugate self-duality on traces: `tr R(g^c) = cyc(g)^{1 - t} tr R(g⁻¹)`, where
  `cyclotomicInv` is the inverse of the cyclotomic character `cyc`; `t = 0` is read as `t = 1`. -/
  trace_conj (g : Gal(Ω/D.E)) :
      (R (conjGal g)).val.trace = cyclotomicInv ℓ D.E (PadicAlgCl ℓ) g ^ (t - 1) * (R g⁻¹).val.trace

variable (D)

/-- A conjugate self-dual representation of level `S`: `R` satisfies `IsConjSelfDual`, and three
local conditions hold at every place `v` that is outside `S` or divides `ℓ p₀ p₁`. -/
structure IsConjSelfDualOfLevel : Prop extends IsConjSelfDual t R where
  /-- At every place `v` off `S` or above `ℓ p₀ p₁`, and every `A` over `v`: `R` is trivial on
  inertia near `1` (potentially crystalline above `ℓ`), has jumps `J` (`HasJumpsAt R A J`, read
  through the isomorphism fixed by the instance `New.PadicIso ℓ`), and is unramified (crystalline
  above `ℓ`) if `v` is prime to `p₀ p₁`. -/
  local_conditions : ∀ v ∉ S \ (placesDividing D.E ℓ ∪ placesAboveM D), ∀ ⦃A : ClosurePlace⦄,
    IsPlaceOver A v →
    IsFiniteTypeAt R A ∧ HasJumpsAt R A J ∧ (v ∉ placesAboveM D → GaloisRep.IsGoodAt R A)

end

end New.Selmer
