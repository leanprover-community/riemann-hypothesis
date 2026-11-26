module

public import Lib.ClassField.Places.DecompositionCompletion
import Lib.ClassField.Global.Chebotarev

/-!
# The filter of most Frobenii and density by Chebotarev

A filter expressing that a property holds for most Frobenius elements of a number field `E`,
together with its density via the Chebotarev density theorem.

## Main definitions and results

* `New.FrobeniusDatum`: a finite place of prime norm, a valuation subring of `Ω` above it, and a
  geometric Frobenius element at that place.
* `New.mostFrobenii`: the filter on `FrobeniusDatum E`. `New.mostFrobeniiAt` adds that the
  Frobenius element `frob` tends to `g`.
* `New.dense_of_mostFrobenii`: a property of most Frobenius elements holds on a dense set; hence the
  filters `New.mostFrobeniiAt` are not trivial.

The cofinite condition in `mostFrobenii` applies only after shrinking each nonempty open set of
Galois elements. It is not a density-one condition on places. Chebotarev is used to show that any
such shrunk open set contains a Frobenius outside the exceptional set; this makes the localized
filters suitable for taking unique limits at every Galois element.

Notions from other files:
* `New.IsFrob`: `σ` stabilises the valuation subring `A` and `σ • x ≡ x ^ q` modulo the maximal
  ideal for all `x ∈ A`.
* `New.IsPlaceOver`: The valuation subring `A` of `Ω` lies over the prime `w` of `E`: an integer of
  `E` is in the maximal ideal of `A` exactly when it lies in `w`.

## Relation to the literature

Known; see `Lib.ClassField.Global.Chebotarev` for sources.
-/

@[expose] public section

noncomputable section

section FrobeniusFilter

open Filter Topology

namespace New

variable (E : Type) [Field E] [EmbeddedNumberField E]

/-- A finite place w = `place` of E of prime norm, a valuation subring A = `valuationSubring` of Ω
(a term of `ClosurePlace`) above w in the sense of `IsPlaceOver`, and a geometric Frobenius
s = `frob` in Gal(Ω/E) at A. -/
structure FrobeniusDatum where
  /-- The finite place of `E`. -/
  place : FinPlace E
  /-- The valuation subring of `Ω`. -/
  valuationSubring : ClosurePlace
  /-- The element of the Galois group of `Ω` over `E`. -/
  frob : Gal(Ω/E)
  /-- The norm of the place is a prime number. -/
  prime_q : place.q.Prime
  /-- The valuation subring lies over the place. -/
  isPlaceOver : IsPlaceOver valuationSubring place
  /-- The inverse of the element is an arithmetic Frobenius at the valuation subring. -/
  isFrob_inv : IsFrob valuationSubring place.q frob⁻¹

/-- The filter 'most Frobenii' on `New.FrobeniusDatum E`. A set `X` of data `(w, A, s)` belongs to
it if each nonempty open `V ⊆ Gal(Ω/E)` has a nonempty open part `O` such that, for almost all `w`,
`X` contains every datum `(w, A, s)` with `s ∈ O`. -/
def mostFrobenii : Filter (FrobeniusDatum E) where
  sets :=
    {X : Set (FrobeniusDatum E) |
      ∀ V : Set Gal(Ω/E), IsOpen V → V.Nonempty → ∃ O ⊆ V,
        IsOpen O ∧ O.Nonempty ∧
        ∀ᶠ w : FinPlace E in cofinite,
          ∀ (A : ClosurePlace) (s : Gal(Ω/E)) (hp : w.q.Prime) (hA : IsPlaceOver A w)
            (hs : IsFrob A w.q s⁻¹),
          s ∈ O →
          ⟨w, A, s, hp, hA, hs⟩ ∈ X}
  univ_sets V hV hV_ne := ⟨V, subset_rfl, hV, hV_ne, by simp⟩
  sets_of_superset hX hXY V hV hV_ne := by
    obtain ⟨O, hOV, hO, hO_ne, h_ev⟩ := hX V hV hV_ne
    exact ⟨O, hOV, hO, hO_ne, h_ev.mono fun w hw A s hp hA hs hsO ↦ hXY (hw A s hp hA hs hsO)⟩
  inter_sets hX hY V hV hV_ne := by
    -- shrink `V` twice: to `O` for the first set, then to `O'` inside `O` for the second
    obtain ⟨O, hOV, hO, hO_ne, hX_ev⟩ := hX V hV hV_ne
    obtain ⟨O', hO'O, hO', hO'_ne, hY_ev⟩ := hY O hO hO_ne
    refine ⟨O', hO'O.trans hOV, hO', hO'_ne, ?_⟩
    filter_upwards [hX_ev, hY_ev] with w hwX hwY A s hp hA hs hsO'
    exact ⟨hwX A s hp hA hs (hO'O hsO'), hwY A s hp hA hs hsO'⟩

/-- The filter of most Frobenii tending to `g`: `New.mostFrobenii` on data `(w, A, s)`, refined by
the condition that `s` lies near `g`. -/
noncomputable abbrev mostFrobeniiAt (g : Gal(Ω/E)) : Filter (FrobeniusDatum E) :=
  mostFrobenii E ⊓ comap (fun x : FrobeniusDatum E ↦ x.frob) (𝓝 g)

variable {E}

/-- For a continuous `f` on `Gal(Ω/E)`, the values of `f` at the Frobenius elements tend to `f g`
along the filter `mostFrobeniiAt E g` of most Frobenii tending to `g`. -/
lemma tendsto_mostFrobeniiAt {X : Type*} {g : Gal(Ω/E)} [TopologicalSpace X] (f : Gal(Ω/E) → X)
    (hf : Continuous f := by fun_prop) :
    Tendsto (fun x : FrobeniusDatum E ↦ f x.frob) (mostFrobeniiAt E g) (𝓝 (f g)) :=
  (hf.tendsto g).comp (tendsto_comap.mono_left inf_le_right)

/-- Along most Frobenius data the place leaves every finite set: a property of all but finitely
many places holds at the place of most Frobenius data. -/
lemma tendsto_place_mostFrobenii :
    Tendsto (fun x : FrobeniusDatum E ↦ x.place) (mostFrobenii E) cofinite := by
  -- any nonempty open set serves as its own small open set
  intro S hS V hV hV_ne
  refine ⟨V, subset_rfl, hV, hV_ne, ?_⟩
  filter_upwards [hS] with w hw A s hp hA hs _ using hw

/-- If `p` holds at all but finitely many places, and `p` at the place of a Frobenius datum
implies `q` of the datum, then `q` holds for most Frobenius data. When `q x` is `p x.place`, pass
`fun _ ↦ id` as `h_imp`. -/
lemma eventually_mostFrobenii {p : FinPlace E → Prop} {q : FrobeniusDatum E → Prop}
    (hp : ∀ᶠ w : FinPlace E in cofinite, p w) (h_imp : ∀ x : FrobeniusDatum E, p x.place → q x) :
    ∀ᶠ x : FrobeniusDatum E in mostFrobenii E, q x :=
  (tendsto_place_mostFrobenii.eventually hp).mono h_imp

/-- Let `φ` be an open embedding of `Gal(Ω/E)` in `Gal(Ω/F)`, `π` a map from the finite places of
`E` to those of `F`, and `X` a set that contains most Frobenius data over `E`. Then for most data
`y` over `F`, the set `X` contains every datum over `E` whose place and Frobenius element are sent
by `π` and `φ` to those of `y`. -/
lemma eventually_mostFrobenii_of_isOpenEmbedding {F : Type} [Field F] [EmbeddedNumberField F]
    {φ : Gal(Ω/E) → Gal(Ω/F)}
    (hφ : IsOpenEmbedding φ) (π : FinPlace E → FinPlace F) {X : Set (FrobeniusDatum E)}
    (hX : X ∈ mostFrobenii E) :
    ∀ᶠ y : FrobeniusDatum F in mostFrobenii F,
      ∀ x : FrobeniusDatum E, π x.place = y.place → φ x.frob = y.frob → x ∈ X := by
  intro V hV hV_ne
  by_cases h_meet : (φ ⁻¹' V).Nonempty
  · -- Push forward the open set `O` that `hX` gives in `φ ⁻¹' V`; the exceptional places of `F`
    -- lie in the image under `π` of the finitely many exceptional places of `E`.
    obtain ⟨O, hO_sub, hO_open, hO_ne, h_cofinite⟩ :
        ∃ O ⊆ φ ⁻¹' V, IsOpen O ∧ O.Nonempty ∧
          ∀ᶠ w : FinPlace E in cofinite,
            ∀ (A : ClosurePlace) (s : Gal(Ω/E)) (hp : w.q.Prime) (hA : IsPlaceOver A w)
              (hs : IsFrob A w.q s⁻¹), s ∈ O → (⟨w, A, s, hp, hA, hs⟩ : FrobeniusDatum E) ∈ X :=
      hX (φ ⁻¹' V) (hV.preimage hφ.continuous) h_meet
    refine ⟨φ '' O, Set.image_subset_iff.2 hO_sub, hφ.isOpenMap O hO_open, hO_ne.image φ, ?_⟩
    filter_upwards [(h_cofinite.image π).compl_mem_cofinite] with v hv A s hp hA hs hs_mem x hw hφx
    have h_frob_mem : x.frob ∈ O := hφ.injective.mem_set_image.1 (by rwa [hφx])
    -- were `x` outside `X`, its place would be exceptional and `v = π x.place` in the image
    by_contra hx_not_mem
    refine hv ⟨x.place, fun h_good ↦ hx_not_mem ?_, hw⟩
    exact h_good x.valuationSubring x.frob x.prime_q x.isPlaceOver x.isFrob_inv h_frob_mem
  · -- If `V` misses the range of `φ`, the condition is vacuous on `V` itself.
    refine ⟨V, subset_rfl, hV, hV_ne, .of_forall fun v A s hp hA hs hs_mem x hw hφx ↦ ?_⟩
    exact absurd ⟨x.frob, show φ x.frob ∈ V by rwa [hφx]⟩ h_meet

/-- If most Frobenius data `(w, A, s)` satisfy `p s`, then `p` holds on a dense subset of
`Gal(Ω/E)`. -/
lemma dense_of_mostFrobenii {p : Gal(Ω/E) → Prop}
    (h : ∀ᶠ x : FrobeniusDatum E in mostFrobenii E, p x.frob) :
    Dense {s : Gal(Ω/E) | p s} := by
  -- A nonempty open `V` contains an open set `O` as in the definition of `mostFrobenii`. By
  -- Chebotarev `O⁻¹` contains an arithmetic Frobenius `σ` at a place of prime norm that is not
  -- exceptional, so `p σ⁻¹` holds.
  refine dense_iff_inter_open.2 fun V hV hV_ne ↦ ?_
  obtain ⟨O, hOV, hO, hO_ne, h_cofinite⟩ :
      ∃ O ⊆ V, IsOpen O ∧ O.Nonempty ∧
        ∀ᶠ w : FinPlace E in cofinite,
          ∀ (A : ClosurePlace) (s : Gal(Ω/E)) (hp : w.q.Prime) (hA : IsPlaceOver A w)
            (hs : IsFrob A w.q s⁻¹), s ∈ O → p s :=
    h V hV hV_ne
  -- Chebotarev: a place `w` of prime norm outside the exceptional set of `h_cofinite`, a place
  -- `A` of `Ω` above it, and an arithmetic Frobenius `σ ∈ O⁻¹` at `A`.
  obtain ⟨w, hw_good, h_prime, A, hA, σ, hσ_inv, h_frob, -⟩ :=
    chebotarev hO.inv hO_ne.inv h_cofinite
  have h_frob_inv : IsFrob A w.q σ⁻¹⁻¹ := by rwa [inv_inv]
  exact ⟨σ⁻¹, hOV hσ_inv, not_not.mp hw_good A σ⁻¹ h_prime hA h_frob_inv hσ_inv⟩

instance {g : Gal(Ω/E)} : NeBot (mostFrobeniiAt E g) :=
  -- Chebotarev gives density for each set in the Frobenius filter, hence compatibility
  -- with every neighbourhood of `g`. This is the nontriviality used for uniqueness of limits.
  neBot_inf_comap_iff_map.mpr
    (inf_neBot_iff.mpr fun _ h_most _ ↦ (dense_of_mostFrobenii h_most).inter_nhds_nonempty)

end New

end FrobeniusFilter

end
