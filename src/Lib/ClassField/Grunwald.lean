module

import Mathlib.Algebra.Order.Star.Int
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.Group.Units
public import Lib.GaloisRep.BaseChange.CommutingHeckeFamilies
public import Lib.GaloisRep.Main.SelmerModules
public import Lib.Weil.Construction.WeilData
import Lib.Adelic.Adeles.LocalFactors
import Lib.Adelic.Adeles.StrongApproximation
import Lib.ClassField.Global.AlbertBrauerHasseNoether
import Lib.ClassField.Global.ArtinMap
import Lib.ClassField.Global.ArtinReciprocity
public import Lib.ClassField.Global.CMSplittingCharacters -- shake: keep (needed public by an exposed definition)
import Lib.ClassField.Global.Chebotarev
import Lib.ClassField.Global.ExistenceTheorem
import Lib.ClassField.Global.NormTheorems
import Lib.General.NumberTheory.CMFields
import Lib.General.NumberTheory.FrobeniusOrbits
import Lib.General.NumberTheory.SUnitsAndClassNumber

/-!
# Grunwald's theorem in prime degree and CM steps with prescribed local behaviour

The file studies continuous characters `χ : Γ → ℚ/ℤ` of absolute Galois groups `Γ = Gal(Ω/E)` (`Ω`
the algebraic closure; `New.EmbeddedNumberField E`: a number field with an embedding into `Ω`) of CM
fields `E` that are killed by a prime `p`, and the cyclic extensions of degree `p` they cut out.
Grunwald's theorem in prime degree produces such characters with prescribed local behaviour. If `E`
is stably unramified (here: `New.HasPrimitiveRoot5040 E`, a primitive 5040th root of unity lies in
`E`) and the symmetrised character is nonzero and kills inertia above `p`, the field cut out by the
symmetrised character is a step of degree `p` over `E`. Weil data lift to stably unramified CM
extensions `L` whose CM type restricts to that of `E` and whose relative different is prime to the
places fixed by conjugation. Together these results give a step of prime degree with Weil data and a
prescribed completion at a split place.

## Main definitions and results

* `New.grunwald`: a character of the finite ideles of a totally complex field, killed by `p`, agrees
  with a Galois character killed by `p` at finitely many given places, and on the units at every
  place whose norm is not prime.
* `New.QZChar.symmetrize`, `New.QZChar.abelianLift_symmetrize`: for a CM field, the character
  `g ↦ χ g + χ (gᶜ)`; on the Artin symbol of an idele `a` it is `χ a + χ (star a)`.
* `New.QZChar.stepField`: the fixed field of the kernel of `New.QZChar.symmetrize χ`. Instances show
  that it is CM, that a CM type of `E` extends to it (`New.CMTypeOver`) and that it inherits
  `New.HasPrimitiveRoot5040`.
* `New.isStep_stepField`: it is a step of degree `p` over `E` if `New.HasPrimitiveRoot5040 E` holds,
  `χ` is killed by a prime `p`, and `New.QZChar.symmetrize χ` is not zero and kills inertia above
  `p`.
* `New.nonempty_weilData_of_not_dvd_differentIdeal`: if `L` also satisfies
  `New.HasPrimitiveRoot5040`, then `L` has Weil data; in the construction `j` stays, `υ` is composed
  with the norm, and a new idele absorbs the relative different, which is assumed prime to the
  places fixed by conjugation.
* `New.GaloisRep.exists_isStepOfLocalChar`, `New.GaloisRep.exists_step_of_local_char`: given a split
  place `w` below `A` and a nontrivial tame character `χ` of `E_wˣ` killed by a prime `p`, a step
  `E' / E` of degree `p`, again with Weil data, cut out by the symmetrisation of a Galois character
  `ν` that is trivial at `w` and has symmetrisation `χ` there; the only place of `E'` above `w` is
  split and lies under `A`.

Notions from other files:
* `New.locIdele`: The homomorphism sending x ∈ K_v^× to the finite idele with component x at v and 1
  elsewhere; `New.ideleAt v` takes the component at v.
* `New.CMTypeOver`: a CM type of L that restricts to the given CM type of E; the embedding chosen at
  a place extends the one chosen at the place below.
* `New.WeilData`: Weil data on a stably unramified E. They consist of ȷ in E with ȷ = −ȷ̄, Im τȷ > 0
  for every τ in the CM type and (1 − ȷ⁻¹)/2 integral; a finite idele α for which the completed
  integers Ô are self-dual under (z, u) ↦ ψ_f(ȷαᾱzu); and a splitting character υ equal to −1 at
  uniformisers of the places w with w = w̄.

## Relation to the literature

Known result: Grunwald–Wang theorem in prime exponent. It is proved over a totally complex field,
and the character also agrees with the given one on units at all primes of degree above one. It
yields a CM extension of prime degree with prescribed tame completion at a split place. Source:
Artin–Tate, Class Field Theory (1968), ch. X; S. Wang, Grunwald–Wang theorem, an effective version,
arXiv 1401.0389 (2014).

See also `Lib.Weil.MixedModel.ZeroTerm`.
-/

@[expose] public section

namespace New

/-!
## Grunwald's theorem in prime degree and the symmetrised character

`New.QZChar Γ` is the group of continuous characters `Γ → ℚ/ℤ`, `New.QZChar.abelianLift χ` the
induced map on `Γ^ab` (written multiplicatively), `New.artinMap` the global Artin map on finite
ideles.
-/

section Grunwald

open NumberField QuotientGroup Subgroup QZChar Valued QZ Algebra Nat SUnit MonoidHom Fact

variable {E : Type} [Field E] [NumberField E] [Algebra E Ω]

/-- Grunwald's theorem in prime exponent. Let `E` be totally complex, `p` prime, `S` a finite set of
finite places, and `ψ` a character of the finite ideles with values in `ℚ/ℤ` (written
multiplicatively), with open kernel and killed by `p`; it need not be trivial on `Eˣ`. Then some
continuous character `χ` of the absolute Galois group, killed by `p`, has `χ ∘ Art = ψ` on the
ideles `New.locIdele u x` with single component `x` at `u`. This holds for all `x` if `u ∈ S`, and
for local units `x` (`v x = 1`) if the norm `u.q` of `u` (the size of its residue field) is not
prime. -/
lemma grunwald [IsTotallyComplex E] {p : ℕ} {S : Set (FinPlace E)} (hp : p.Prime)
    (hS : Set.Finite S) (ψ : (𝔸f E)ˣ →* Multiplicative QZ) (hψ_open : ψ.ker.IsOpen)
    (hψ_pow : ∀ a : (𝔸f E)ˣ, ψ a ^ p = 1) :
    ∃ χ : ↥(QZChar Gal(Ω/E)),
      -- (a) the Galois character `χ` is killed by `p`
      p • χ = 0 ∧
      -- (b) `χ` agrees with `ψ` at places of `S` and on units at places of non-prime norm
      ∀ (u : FinPlace E) (x : (LocField u)ˣ),
        u ∈ S ∨ ¬u.q.Prime ∧ v x.val = 1 →
        abelianLift χ (artinMap Gal(Ω/E) (locIdele u x)) = ψ (locIdele u x) := by
  -- Enlarge `S` to `T` so that principal ideles and units off `T` generate. For each class `q` of
  -- `T`-units mod `p`-th powers not killed by `ψ`, Chebotarev gives a place `w q` where `q` is not
  -- a local `p`-th power. Then `ψ` kills principal ideles in the open group `U` of units off `T`
  -- that are `p`-th powers at every `w q`, so `ψ|_U` extends to a global character.
  have h_fact : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, hT_fin, hST, h_sup⟩ := exists_superset_sup_idelesUnitOff_eq_top hS
  obtain ⟨h_fg, -⟩ := dirichlet_unit_theorem hT_fin
  let N : Subgroup (T.unit E) := (powMonoidHom p).range
  have h_N_fin : N.FiniteIndex := N.finiteIndex_iff.mpr
    (index_range_pow_eq (Y := T.unit E) (n := p) (mod_cast cokerKerIndex_eq_pow_finrank)).left
  let H : Subgroup Gal(Ω/E) := (cyclotomicCharMod Ω p).ker
  have h_coprime : (Module.finrank E (fixedFieldOf H)).Coprime p := by
    have h_dvd : Module.finrank E (fixedFieldOf H) ∣ p - 1 :=
      calc Module.finrank E (fixedFieldOf H)
        _ = Nat.card (cyclotomicCharMod Ω p).range := by rw [finrank_fixedFieldOf, index_ker]
        _ ∣ Nat.card (ZMod p)ˣ := card_subgroup_dvd_card _
        _ = p - 1 := by rw [card_units, Nat.card_zmod]
    exact .of_dvd_left h_dvd (by simp [hp.one_le])
  choose r hr using Variety.IsAbsIntegrallyClosed.exists_pow_eq (A := Ω) p
  -- An `x` not killed by `ψ` is no `p`-th power in `E`, so some element of `H` moves its root.
  have h_moves (x : Eˣ) (hx : ψ (principalIdele x) ≠ 1) :
      ((H : Set Gal(Ω/E)) \ {g | g • r (algebraMap E Ω x) = r (algebraMap E Ω x)}).Nonempty := by
    change ∃ g, g ∈ H ∧ g • r (algebraMap E Ω x) ≠ r (algebraMap E Ω x)
    by_contra! h_fix
    let root : fixedFieldOf H := ⟨r (algebraMap E Ω x), fun g ↦ h_fix g g.prop⟩
    have h_norm : norm E root ^ p = (x : E) ^ Module.finrank E (fixedFieldOf H) := by
      rw [← map_pow, show root ^ p = algebraMap E (fixedFieldOf H) x from Subtype.ext (hr _),
        Algebra.norm_algebraMap]
    obtain ⟨z, hz : z ^ p = (x : E)⟩ :=
      (pow_mem_range_pow_of_coprime h_coprime (x : E)).mp ⟨norm E root, h_norm⟩
    have h_eq : (x.ofPow z hp.ne_zero hz) ^ p = x := Units.ext hz
    exact hx (by rw [← h_eq, map_pow, map_pow, hψ_pow])
  let Q : Type := {q : T.unit E ⧸ N // ψ (principalIdele q.out) ≠ 1}
  let ρ (q : Q) : Ω := r (algebraMap E Ω (q.val.out : Eˣ))
  choose w hwT hw_prime A hA σ hσ h_frob using fun q : Q ↦
    chebotarev ((Fact.out : IsOpen (H : Set Gal(Ω/E))).sdiff
      (isClosed_setOf_smul (ρ q) fun y ↦ y = ρ q)) (h_moves _ q.prop) hT_fin
  let R (q : Q) : Subgroup (𝔸f E)ˣ := (powMonoidHom p).range.comap (ideleAt (w q))
  let U : Subgroup (𝔸f E)ˣ := idelesUnitOff T ⊓ iInf R
  have h_principal (x : Eˣ) (hx : principalIdele x ∈ U) : ψ (principalIdele x) = 1 := by
    by_contra h_ne
    obtain ⟨hx_units, hx_R⟩ := hx
    let xT : T.unit E := ⟨x, principalIdele_mem_idelesUnitOff.mp hx_units⟩
    obtain ⟨⟨_, y, rfl⟩, h_out⟩ := mk_out_eq_mul N xT
    let q : Q := ⟨xT, by simpa [h_out, hψ_pow] using h_ne⟩
    have h_loc_pow : principalIdele q.val.out ∈ R q := by
      rw [show (q.val.out : Eˣ) = x * y ^ p from congrArg Subtype.val h_out, map_mul]
      exact mul_mem (mem_iInf.mp hx_R q) (by simp [R])
    exact (hσ q).right ((hA q).smul_root_eq_of_local_pow h_loc_pow (hr _) (σ q)
      (h_frob q).left.left (mem_ker.mp (hσ q).left))
  have hR_open (q : Q) : (R q).IsOpen :=
    (isOpen_of_forall_pow_mem hp.ne_zero fun y ↦ mem_range.mpr ⟨y, rfl⟩).preimage_of_continuous
  have hU_open : U.IsOpen := by
    simpa [U, Subgroup.IsOpen] using
      (isOpen_idelesUnitOff T).inter (isOpen_iInter_of_finite hR_open)
  -- Extend `ψ|_U` to a continuous idele character `θ` killing `Eˣ`, hence a Galois character `μ`.
  obtain ⟨θ, hθ_rat, hθ⟩ := exists_monoidHom_extend (C := Multiplicative QZ)
    (d := instDivisibleByQZInt) U.subtype (ψ.domRestrict U) principalIdele.range
    fun a ⟨x, hx⟩ ↦ by change ψ a = 1; simpa [hx] using h_principal x (by simp [hx])
  have hθ_cont : Continuous θ := .of_isOpen_ker _
    ((ψ.ker ⊓ U).isOpen_mono (fun a ⟨ha_k, ha_U⟩ ↦ (hθ ⟨a, ha_U⟩).trans ha_k)
      (hψ_open.inter hU_open))
  obtain ⟨μ, hμ_cont, hμ⟩ := exists_comp_artinMap Gal(Ω/E) θ hθ_cont fun x ↦ hθ_rat ⟨x, rfl⟩
  have hθ_pow (a : (𝔸f E)ˣ) : θ a ^ p = 1 := by
    have h_units : idelesUnitOff T ≤ (θ ^ p).ker := fun b hb ↦ by
      simpa [hψ_pow] using hθ ⟨b ^ p, by simp [U, R, pow_mem hb]⟩
    simpa using sup_le (fun _ hb ↦ by simp [mem_ker.mp (hθ_rat hb)]) h_units (h_sup.ge (mem_top a))
  refine ⟨⟨μ, hμ_cont, μ.map_mul⟩, Subtype.ext (funext fun g ↦ ?_), fun u x hu ↦ ?_⟩
  · obtain ⟨a, ha⟩ := artinMap_surjective _ (g : TopologicalAbelianization Gal(Ω/E))
    change μ g ^ p = 1
    rw [hμ a g ha, hθ_pow]
  · have h_ne (q : Q) : w q ≠ u := by
      rintro rfl
      exact hu.elim (fun h ↦ hwT q (hST h)) fun h ↦ h.left (hw_prime q)
    have h_mem : locIdele u x ∈ U := ⟨hu.elim
      (fun hu_S ↦ mem_idelesUnitOff.mpr fun v hv ↦ by
        rw [locIdele_apply_of_ne (ne_of_mem_of_not_mem (hST hu_S) hv).symm x, map_one])
      (fun h ↦ locIdele_mem_idelesUnitOff h.right),
      mem_iInf.mpr fun q ↦ by
        change ideleAt (w q) (locIdele u x) ∈ (powMonoidHom p).range
        rw [ideleAt_locIdele_of_ne (h_ne q) x]
        exact one_mem _⟩
    obtain ⟨g, hg⟩ := mk_surjective (artinMap Gal(Ω/E) (locIdele u x))
    exact ((congrArg _ hg.symm).trans (abelianLift_mk _ g)).trans
      ((hμ _ g hg.symm).trans (hθ ⟨_, h_mem⟩))

variable [IsCMField E] (χ : QZChar Gal(Ω/E))

/-- For a character `χ` of the absolute Galois group of a CM field, the character
`g ↦ χ g + χ (gᶜ)`, where `gᶜ` is the conjugate of `g` by complex conjugation (`New.conjGal`). -/
noncomputable abbrev QZChar.symmetrize : ↥(QZChar Gal(Ω/E)) :=
  χ + comap ⟨conjGal, continuous_conjGal⟩ χ

/-- For a `ℚ/ℤ`-valued character `χ` of `Gal(Ω/E)`, the character `exp (2πi χ ∘ Art)` of the
finite ideles of `E`. -/
noncomputable abbrev QZChar.ideleChar : (𝔸f E)ˣ →* ℂˣ :=
  expUnit.comp ((abelianLift χ).comp (artinMap Gal(Ω/E)))

/-- On the Artin symbol of an idele `a`, the symmetrised character `New.QZChar.symmetrize χ` takes
the value of `χ` at `a` times the value of `χ` at the conjugate idele `star a`. -/
lemma QZChar.abelianLift_symmetrize (a : (𝔸f E)ˣ) :
    abelianLift (symmetrize χ) (artinMap Gal(Ω/E) a) =
      abelianLift χ (artinMap Gal(Ω/E) a) * abelianLift χ (artinMap Gal(Ω/E) (star a)) := by
  obtain ⟨g, hg⟩ := mk_surjective (artinMap Gal(Ω/E) a)
  -- the Artin symbol of `star a` is the class of `conjGal g`
  rw [← hg, artinMap_star g hg.symm]
  simp [symmetrize, ofAdd_add]
  rfl

end Grunwald

/-!
## The CM step cut out by a symmetrised Galois character

For a character `χ` of `Gal(Ω/E)`, the fixed field `stepField χ` of the kernel of `symmetrize χ` is
a CM field. If `p • χ = 0`, `symmetrize χ ≠ 0`, and `symmetrize χ` is unramified above `p`, then
`stepField χ` has degree `p` over `E` and is a step (`New.IsStep`) for `ideleChar χ`.
-/

section StepField

open NumberField Ideal Algebra ComplexEmbedding Cohomology Subgroup QZChar QZ FractionalIdeal
  RingOfIntegers

variable {E : Type} [Field E] [EmbeddedNumberField E]

section

variable [IsCMField E] (χ : QZChar Gal(Ω/E))

/-- The Galois extension of `E` cut out by `New.QZChar.symmetrize χ : g ↦ χ g + χ (gᶜ)`, that
is, the fixed field of its kernel. -/
noncomputable abbrev QZChar.stepField : IntermediateField E Ω := fixedFieldOf (ker (symmetrize χ))

/-- The field `New.QZChar.stepField χ` is a CM field: the complex conjugation `cmConj` of `Ω` maps
it to itself and restricts on it to complex conjugation under every embedding into `ℂ`. -/
instance : IsCMField (stepField χ) := by
  refine isCMField_of_forall_exists_conj E fun y ↦ ⟨⟨cmConj y, fun g ↦ ?_⟩, fun φ ↦ ?_⟩
  · -- `cmConj y` is fixed by `g`, since `y` is fixed by `conjGal g`, which is again in the kernel
    have h_conj : conjGal g.val ∈ ker (symmetrize χ) := by
      change χ.val (conjGal g.val) + χ.val (conjGal (conjGal g.val)) = 0
      rw [conjGal_conjGal, add_comm]
      exact g.prop
    change g.val • cmConj (y : Ω) = cmConj (y : Ω)
    rw [← cmConj_cmConj (g.val • cmConj (y : Ω))]
    exact congrArg cmConj (y.prop ⟨conjGal g.val, h_conj⟩)
  · -- Extend `φ` to `J` on `Ω`. Then `J ∘ cmConj` and `star J` agree on `E`, so they differ by
    -- some `g` with `conjGal g * g = 1`, which lies in the kernel and fixes `y`.
    rw [← lift_comp_algebraMap Ω φ]
    let J := lift Ω φ
    have h_agree : (J.comp cmConj).comp (algebraMap E Ω) = (star J).comp (algebraMap E Ω) := by
      ext e; simpa using map_star_complex (J.comp _) _
    obtain ⟨g, hg⟩ :=
      exists_apply_smul_eq_of_comp_algebraMap_eq Gal(Ω/E) (J.comp cmConj) (star J) h_agree
    have h_inv : conjGal g * g = 1 := by
      ext x
      have hg_x := hg x
      have hg_conj := hg (cmConj (g • x))
      simp_all [← J.injective.eq_iff, conjGal]
    have h_fix : g • (y : Ω) = y := y.prop ⟨g, map_mul_eq_one (toHom χ) (mul_eq_one_symm h_inv)⟩
    have h_conj_emb : J.comp cmConj (g • (y : Ω)) = star J (y : Ω) := hg y
    rwa [h_fix] at h_conj_emb

end

open scoped Classical in
open InfinitePlace in
/-- A CM type of `E` extends to `New.QZChar.stepField χ`: at each infinite place take the embedding
whose restriction to `E` is the embedding chosen at the place below. -/
noncomputable instance [CMType E] (χ : QZChar Gal(Ω/E)) : CMTypeOver E (stepField χ) where
  -- Of the two embeddings at `u`, take the one that restricts to the chosen embedding below.
  Φ u :=
    let e : stepField χ →+* ℂ := u.embedding
    if e.comp (algebraMap E (stepField χ)) = Φ (u.comap (algebraMap E (stepField χ))) then
      e
    else
      star e
  mk_Φ := by aesop
  eq_chosen_iff := by grind [embedding_mk_eq, Φ_mk_eq_or_star_eq, comap_mk, conjugate_comp,
    star_star]

variable [IsCMField E] (χ : QZChar Gal(Ω/E))

/-- `New.QZChar.stepField χ` contains the image of a primitive `5040`-th root of unity of `E`. -/
instance [h : HasPrimitiveRoot5040 E] : HasPrimitiveRoot5040 (stepField χ) where
  exists_primitive_root := by
    obtain ⟨ζ, hζ⟩ := h.exists_primitive_root
    exact ⟨algebraMap E (stepField χ) ζ, hζ.map_of_injective (algebraMap E _).injective⟩

/-- If `New.QZChar.symmetrize χ` kills the inertia groups at the places `A : ClosurePlace` of `Ω`
(valuation subrings) over (`IsPlaceOver`) the prime of `E` below `u`, then `u` does not divide the
different of `New.QZChar.stepField χ` over `E`. -/
lemma QZChar.not_dvd_differentIdeal_stepField {u : FinPlace (stepField χ)}
    (h_inertia : ∀ {A : ClosurePlace},
      IsPlaceOver A (u.below E) → inertiaGroup Gal(Ω/E) A ≤ ker (symmetrize χ)) :
    ¬u.asIdeal ∣ differentIdeal (𝓞 E) (𝓞 (stepField χ)) := by
  have h_below : IsPlaceOver (placeOver u) (u.below E) := u.isPlaceOver_placeOver.isPlaceOver_below
  obtain ⟨-, h_unram_of_le, -⟩ :=
    h_below.ramification_in_tower (ker (symmetrize χ)) u.isPlaceOver_placeOver
  exact not_dvd_differentIdeal_iff.mpr
    (ramificationIdx_eq_one_iff.mp (h_unram_of_le (h_inertia h_below)))

/-- Let `E` be a CM field containing a primitive 5040th root of unity (`New.HasPrimitiveRoot5040`),
and let `p` be prime. Write `New.QZChar.symmetrize χ` for the character `g ↦ χ g + χ gᶜ`, where `gᶜ`
is the conjugate of `g` by complex conjugation. Suppose that (a) `p • χ = 0`, (b)
`New.QZChar.symmetrize χ` is not zero, and (c) it kills the inertia groups at the places above `p`.
Then the field `New.QZChar.stepField χ`, the fixed field of the kernel of `symmetrize χ`, has degree
`p` over `E`. It is a step (`New.IsStep`: a CM field Galois of prime degree over `E`, with an
integer of trace `1`) for the Hecke character `New.QZChar.ideleChar χ = exp (2πi χ ∘ Art)`. This
character has open kernel, is trivial on `Eˣ`, and is `1` at `z z̄` exactly when `z` is a principal
idele times a norm from the field. -/
lemma isStep_stepField [HasPrimitiveRoot5040 E] {p : ℕ} (hp : Nat.Prime p) (hχ : p • χ = 0)
    (hχ_sym_ne : symmetrize χ ≠ 0)
    (h_unram : ∀ {A : ClosurePlace} {u : FinPlace E}, IsPlaceOver A u → ↑p ∈ u.asIdeal →
      inertiaGroup Gal(Ω/E) A ≤ ker (symmetrize χ)) :
    IsStep (stepField χ) (ideleChar χ) ∧ Module.finrank E (stepField χ) = p := by
  have h_fact : Fact p.Prime := ⟨hp⟩
  -- The degree is the order of the image of `symmetrize χ`, a nontrivial `p`-torsion subgroup.
  have h_rank : Module.finrank E (stepField χ) = p := by
    have hχ_apply (g : Gal(Ω/E)) : p • χ.val g = 0 := by
      simpa using congrFun (congrArg Subtype.val hχ) g
    have h_range : (toHom (symmetrize χ)).range ≤ (ofZMod p).toMultiplicative.range := by
      rintro _ ⟨g, rfl⟩
      exact exists_ofZMod (a := χ.val g + χ.val (conjGal g)) (by simp [hχ_apply])
    have h_dvd : (toHom (symmetrize χ)).ker.index ∣ p :=
      calc (toHom (symmetrize χ)).ker.index
        _ = Nat.card (toHom (symmetrize χ)).range := index_ker _
        _ ∣ Nat.card (ofZMod p).toMultiplicative.range := card_dvd_of_le h_range
        _ ∣ Nat.card (Multiplicative (ZMod p)) := card_range_dvd _
        _ = p := Nat.card_zmod p
    have h_ne_one : (toHom (symmetrize χ)).ker.index ≠ 1 := fun h_one ↦
      hχ_sym_ne (Subtype.ext (funext fun g ↦
        ofAdd_eq_one.mp (MonoidHom.mem_ker.mp ((index_eq_one.mp h_one).ge (mem_top g)))))
    rw [finrank_fixedFieldOf, (hp.dvd_iff_eq h_ne_one).mp h_dvd]
  -- The trace on integers is onto: otherwise it lands in a prime `u ∋ tr 1 = p`, so any prime `P`
  -- above `u` is unramified yet contains the different.
  have h_trace : (intTrace (𝓞 E) (𝓞 (stepField χ))).range = ⊤ := by
    by_contra h_ne
    obtain ⟨u, hu⟩ :=
      (IsDedekindDomain.HeightOneSpectrum.ideal_ne_top_iff_exists (not_isField E) _).mp h_ne
    have hp_mem : (p : 𝓞 E) ∈ u.asIdeal := hu ⟨1,
      ext (by simp [algebraMap_intTrace (L := stepField χ), trace_apply, map_one, h_rank])⟩
    obtain ⟨P, rfl⟩ := FinPlace.comap_surjective (algebraMap E (stepField χ)) u
    refine not_dvd_differentIdeal_stepField χ (fun h_place ↦ h_unram h_place hp_mem)
      (dvd_iff_le.mpr ?_)
    rw [differentialIdeal_le_iff (K := E) (L := stepField χ) P.ne_bot]
    rintro _ ⟨x, hx, rfl⟩
    let u : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := (P.below E).asIdeal
    have hu_ne : u ≠ 0 := coeIdeal_ne_zero.mpr (P.below E).ne_bot
    suffices h_div : trace E (stepField χ) x ∈ u / u by
      rw [div_self hu_ne] at h_div
      exact coeToSubmodule_one.le h_div
    refine (mem_div_iff_of_ne_zero hu_ne).mpr fun _ ⟨a, ha, h_eq⟩ ↦ ?_
    obtain ⟨z, -, hz : algebraMap (𝓞 (stepField χ)) (stepField χ) z =
        x * algebraMap (𝓞 (stepField χ)) (stepField χ)
          (algebraMap (𝓞 E) (𝓞 (stepField χ)) a)⟩ :=
      (mem_inv_iff (coeIdeal_ne_zero.mpr P.ne_bot)).mp hx _ ⟨_, ha, rfl⟩
    refine ⟨_, hu ⟨z, rfl⟩, ?_⟩
    rw [← h_eq]
    change algebraMap (𝓞 E) E (intTrace (𝓞 E) (𝓞 (stepField χ)) z) =
      trace E (stepField χ) x * algebraMap (𝓞 E) E a
    rw [algebraMap_intTrace (L := stepField χ), hz]
    simp [algebraMap_eq_smul_one]
  subst h_rank
  refine ⟨⟨?_, ?_, fun z ↦ ?_, ?_⟩, rfl⟩
  · exact isOpen_mono (expUnit.ker.ker_le_comap _)
      (continuous_iff_forall_isOpen_ker_comp.mp continuous_artinMap χ)
  · simp [artinMap_principalIdele_eq_one_of_isTotallyPositive,
      isTotallyPositive_of_isTotallyComplex]
  · rw [show ideleChar χ (z * star z) =
        expUnit (abelianLift (symmetrize χ) (artinMap Gal(Ω/E) z)) by
          simp [← abelianLift_symmetrize],
      expUnit_eq_one_iff, abelianLift_artinMap_eq_one_iff (symmetrize χ)]
    simp [isTotallyPositive_of_isTotallyComplex]
  · obtain ⟨c, hc⟩ := (eq_top_iff_one _).mp h_trace
    exact ⟨c, by simp [← algebraMap_intTrace (A := 𝓞 E), hc]⟩

end StepField

end New

/-!
## Lifting Weil data to CM extensions unramified at non-split places

Weil data (`New.WeilData E`) on a CM field `E` consist of an element `j = -j̄` with positive
imaginary part under the CM type `Φ` and with `(1 - j⁻¹) / 2` integral, a finite idele `α` such that
`j α ᾱ` generates the inverse different, and a splitting character `υ` (`New.SplittingChar`) that is
`-1` at the uniformisers of the places fixed by conjugation.
-/

section WeilDataExtension

open NumberField WithZero Valued Ideal IsDedekindDomain HeightOneSpectrum FiniteMultiplicity Finset
  New WeilData RingHom

/-- Let the CM type of `L` restrict to that of `E` (`New.CMTypeOver E L`). Then the embedding `Φ u`
of `L` into `ℂ` that the CM type chooses at the infinite place `u` extends the embedding chosen at
the place of `E` below `u`. -/
lemma New.Φ_algebraMap_eq_Φ_comap {E L : Type} [Field E] [CMType E] [Field L] [Algebra E L]
    [h : CMTypeOver E L] (u : InfinitePlace L) (r : E) :
    Φ u (algebraMap E L r) = Φ (u.comap (algebraMap E L)) r :=
  RingHom.congr_fun (by simpa only [mk_Φ] using (h.eq_chosen_iff (Φ u)).mp (by rw [mk_Φ])) r

/-- Let the CM type of `L` restrict to that of `E` (`New.CMTypeOver E L`), and let `w` be an
infinite place of `E`. The embeddings `Φ u` chosen at the places `u` of `L` above `w` are exactly
the embeddings of `L` that extend `Φ w`; so for `x` in `L` the product of the `Φ u x` is `Φ w` of
the norm of `x` from `L` to `E`. -/
lemma New.prod_Φ_eq_Φ_norm {E L : Type} [Field E] [CMType E] [Field L] [Algebra E L]
    [h : CMTypeOver E L] (w : InfinitePlace E) (x : L) :
    ∏ u : InfinitePlace L with u.comap (algebraMap E L) = w, Φ u x = Φ w (Algebra.norm E x) := by
  algebraize [Φ w]
  have h_norm : Φ w (Algebra.norm E x) = ∏ σ : L →ₐ[E] ℂ, σ x :=
    Algebra.norm_eq_prod_embeddings E ℂ x
  rw [h_norm]
  have h_chosen (σ : L →ₐ[E] ℂ) : Φ (InfinitePlace.mk σ) = (σ : L →+* ℂ) := by
    rw [eq_comm, h.eq_chosen_iff]
    simp [algebraMap_toAlgebra]
  refine prod_bij' (fun u hu ↦ ⟨Φ u, fun r ↦ ?_⟩) (fun σ _ ↦ .mk σ) (by simp)
    (by simp_all [algebraMap_toAlgebra]) (by simp)
    (fun σ _ ↦ AlgHom.toRingHom_injective (h_chosen σ)) (by simp)
  simp_all [algebraMap_toAlgebra, Φ_algebraMap_eq_Φ_comap]

/-- Let the CM type of `L` restrict to that of `E` (`New.CMTypeOver E L`), and let `E` carry a
splitting character `υ` (`New.SplittingChar`: a unitary Hecke character with `υ x̄ = (υ x)⁻¹` that
is `∏ x_τ / |x_τ|` on ideles whose finite part is a unit of `Ô`). Then `L` has a splitting
character: `υ` composed with the norm of ideles from `L` to `E`, which at an infinite place `w` of
`E` is the product of the components at the places of `L` above `w`. -/
lemma New.nonempty_splittingChar_of_cmTypeOver {E L : Type} [Field E] [CMType E] [Field L]
    [Algebra E L] [CMTypeOver E L] [SplittingChar E] :
    Nonempty (SplittingChar L) := by
  let Nm : 𝔸 L →* 𝔸 E :=
    .prodMap (.pi fun w ↦ ∏ u with u.comap (algebraMap E L) = w, Pi.evalMonoidHom _ u)
      (adeleNorm E L)
  have hNm : Continuous Nm := by
    simp only [Nm, MonoidHom.coe_prodMap, continuous_prodMap_iff, continuous_adeleNorm, and_true,
      MonoidHom.pi, MonoidHom.finsetProd_apply, Pi.evalMonoidHom_apply, MonoidHom.coe_mk,
      OneHom.coe_mk]
    fun_prop
  refine ⟨{ υ := ⟨υ.val.comp ⟨Units.map Nm, hNm.units_map _⟩, fun y ⟨x, hx⟩ ↦ ?_⟩
            υ_unit := fun y hy ↦ ?_
            υ_star := fun y ↦ ?_ }⟩
  · refine υ.prop _ ⟨Algebra.norm E x, .symm ?_⟩
    ext w <;> simp [Nm, ← hx, prod_Φ_eq_Φ_norm]
  · change (υ.val (Units.map Nm y) : ℂ) = _
    rw [υ_unit (Units.map Nm y) (by simp_all [Nm, adeleNorm_mem_Ô, Submonoid.mem_units_iff])]
    simp [Nm, prod_fiberwise]
  · exact (congrArg υ.val (by ext <;> simp [Nm, adeleNorm_star])).trans (υ_star _)

/-- The different of a CM field `L` is invariant under complex conjugation: a finite place `u`
and its conjugate `star u` have the same multiplicity in it. -/
lemma New.multiplicity_star_differentIdeal {L : Type} [Field L] [CMType L] (u : FinPlace L) :
    multiplicity (star u).asIdeal (differentIdeal ℤ (𝓞 L)) =
      multiplicity u.asIdeal (differentIdeal ℤ (𝓞 L)) := by
  -- Take an idele `g` with the order of the different at every place; `ψf`-invariance under `star`
  -- makes `g * star g⁻¹` integral, bounding `ord (star u)` by `ord u`.
  obtain ⟨-, -, -, g, -, hg_val, hg_dual⟩ :=
    exists_reduction_and_idele_generator (E := L) (differentIdeal_ne_bot (A := ℤ))
  have hg_star : g.val * star g⁻¹.val ∈ Ô L := by
    refine (hg_dual _).mp (forall_ψf_mul_eq_one_iff.mp fun a ha ↦ ?_)
    rw [← ψf_star, star_mul', star_star]
    exact forall_ψf_mul_eq_one_iff.mpr ((hg_dual g⁻¹.val).mpr (by simp)) (star a) (star_mem_Ô ha)
  have h_star_le (u' : FinPlace L) : multiplicity (star u').asIdeal (differentIdeal ℤ (𝓞 L)) ≤
      multiplicity u'.asIdeal (differentIdeal ℤ (𝓞 L)) := by
    simpa [hg_val, ← evalAt_apply _ g⁻¹.val, ← log_le_log] using mem_Ô.mp hg_star u'
  exact (h_star_le u).antisymm (by simpa only [star_star] using h_star_le (star u))

/-- Let `u` be a finite place of `L` that does not divide the relative different of `L / E`. Then
the multiplicity of `u` in the different of `L` is the ramification index of `u` over the place
`w` of `E` below it times the multiplicity of `w` in the different of `E`. -/
lemma New.multiplicity_differentIdeal_eq_ramificationIdx'_mul_of_not_dvd {E L : Type} [Field E]
    [NumberField E] [Field L] [NumberField L] [Algebra E L] (u : FinPlace L)
    (h_not_dvd : ¬u.asIdeal ∣ differentIdeal (𝓞 E) (𝓞 L)) :
    multiplicity u.asIdeal (differentIdeal ℤ (𝓞 L)) =
      (u.below E).asIdeal.ramificationIdx' u.asIdeal *
        multiplicity (u.below E).asIdeal (differentIdeal ℤ (𝓞 E)) := by
  -- the different of `L` is that of `E`, pushed to `L`, times the relative one, which is prime
  -- to `u`; the first factor has multiplicity `e * ord_w` at `u`
  apply multiplicity_eq_of_emultiplicity_eq_some
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 E) (𝓞 L),
    emultiplicity_mul u.prime, emultiplicity_eq_zero.mpr h_not_dvd]
  simp [emultiplicity_eq_multiplicity, ne_bot,
    emultiplicity_map_eq_ramificationIdx'_mul _ (u.below E).irreducible u.irreducible, prime,
    differentIdeal_ne_bot, of_prime_left]

/-- Let `E` carry Weil data and let the finite place `w` be fixed by complex conjugation. Then the
log of the valuation of `j` at `w` is the multiplicity of `w` in the different of `E` minus twice
the log of the valuation of `α` at `w` (this is the condition `self_dual` at `w`, where `α` and
`star α` have the same order). -/
lemma New.WeilData.log_valuation_j_of_star_eq {E : Type} [Field E] [CMType E] [WeilData E]
    (w : FinPlace E) (hw_fix : star w = w) :
    (w.valuation E j).log =
      multiplicity w.asIdeal (differentIdeal ℤ (𝓞 E)) - 2 * (v (α.val w)).log := by
  have h_ne : v ((algebraMap E (𝔸f E) j * α.val * star α.val : 𝔸f E) w) ≠ 0 := by
    rw [self_dual w]; exact exp_ne_zero
  have hα : v (α.val (star w)) = v (α.val w) := by rw [hw_fix]
  have hα_ne : v (α.val w) ≠ 0 := by simp_all
  have h_sum : (w.valuation E j).log + (v (α.val w)).log + (v (α.val w)).log =
      multiplicity w.asIdeal (differentIdeal ℤ (𝓞 E)) := by
    simpa [j_ne_zero, log_mul, hα, hα_ne] using congrArg log (self_dual w)
  linarith

/-- Let `L / E` be an extension of CM fields with compatible CM types, where `E` carries Weil data
and `L` contains a primitive 5040th root of unity. Weil data consist of such a root of unity, an
element `ȷ = −ȷ̄` with `Im τȷ > 0` and `(1 − ȷ⁻¹)/2` integral, a finite idele making the integers
self-dual for the standard additive character, and a splitting character equal to `−1` at
uniformisers of places fixed by conjugation. If no finite prime of `L` fixed by complex conjugation
divides the relative different ideal of `𝓞 L` over `𝓞 E`, then `L` also carries Weil data. -/
lemma New.nonempty_weilData_of_not_dvd_differentIdeal {E L : Type} [Field E] [CMType E] [Field L]
    [Algebra E L] [h : CMTypeOver E L] [WeilData E] [HasPrimitiveRoot5040 L]
    (h_unram : ∀ u : FinPlace L, star u = u → ¬u.asIdeal ∣ differentIdeal (𝓞 E) (𝓞 L)) :
    Nonempty (WeilData L) := by
  -- Keep `j`, compose the splitting character with the norm, and choose `β` cancelling half the
  -- order of `s = j * g` (`g` generating the different of `L`) at each pair `{u, star u}`.
  obtain ⟨-, -, -, g, -, hg_val, -⟩ :=
    exists_reduction_and_idele_generator (E := L) (differentIdeal_ne_bot (A := ℤ))
  obtain ⟨s, hs⟩ : IsUnit (algebraMap L (𝔸f L) (algebraMap E L j) * g.val) := by simp [j_ne_zero]
  have hs_ord (u : FinPlace L) : (v (s.val u)).log =
      (u.valuation L (algebraMap E L j)).log -
        multiplicity u.asIdeal (differentIdeal ℤ (𝓞 L)) := by
    simp [hs, hg_val, j_ne_zero, sub_eq_add_neg]
  have hs_star (u : FinPlace L) : (v (s.val (star u))).log = (v (s.val u)).log := by
    have hj : (star u).valuation L (algebraMap E L j) = u.valuation L (algebraMap E L j) := by
      simpa [← map_star_CM] using valuation_star u (algebraMap E L j)
    rw [hs_ord, hs_ord, hj, multiplicity_star_differentIdeal u]
  have hs_even (u : FinPlace L) (hu_fix : star u = u) : 2 ∣ (v (s.val u)).log := by
    let w : FinPlace E := u.below E
    refine ⟨-(w.asIdeal.ramificationIdx' u.asIdeal * (v (α.val w)).log), ?_⟩
    rw [hs_ord, multiplicity_differentIdeal_eq_ramificationIdx'_mul_of_not_dvd u (h_unram u hu_fix),
      ← w.valuation_liesOver L, log_pow,
      WeilData.log_valuation_j_of_star_eq w (by rw [← below_star, hu_fix]),
      ← w.asIdeal.ramificationIdx'_eq_ramificationIdx u.asIdeal w.ne_bot]
    push_cast
    ring
  obtain ⟨h_linearOrder, -⟩ := exists_wellFoundedLT (FinPlace L)
  let halfOrder (u : FinPlace L) : ℤ := ((if u < star u then 1 else 0) - (v (s.val u)).log) / 2
  have h_half_eq_zero (u : FinPlace L) (h_one : v (s.val u) = 1) : halfOrder u = 0 := by
    simp only [halfOrder, h_one, log_one, sub_zero]
    split_ifs <;> omega
  obtain ⟨β, hβ⟩ := exists_idele_eq_uniformizer_zpow halfOrder
    ((finite_setOf_valued_val_ne_one s).subset fun u h_ne h_one ↦ h_ne (h_half_eq_zero u h_one))
  obtain ⟨h_splittingChar⟩ := nonempty_splittingChar_of_cmTypeOver (E := E) (L := L)
  refine ⟨{ j := algebraMap E L j, α := β, self_dual u := ?_
            star_j := by simp [← map_star_CM]
            im_pos u := by simp [Φ_algebraMap_eq_Φ_comap, im_pos]
            isIntegral_traceOne := by
              simpa [map_ofNat] using map_isIntegral_int (algebraMap E L) isIntegral_traceOne
            υ_inert := Cohomology.upsilon_atUniformizer_eq_neg_one }⟩
  rw [← exp_log (x := v ((algebraMap L (𝔸f L) (algebraMap E L j) * β.val * star β.val) u))
    (by simp [j_ne_zero, hβ]), exp_inj]
  have h_halves : halfOrder u + halfOrder (star u) = -(v (s.val u)).log := by
    simp only [halfOrder, star_star, hs_star]
    rcases lt_trichotomy u (star u) with h | h | h
    · rw [ite_eq_left h, ite_eq_right (lt_asymm h)]; omega
    · have := hs_even u h.symm
      rw [← h, ite_eq_right (lt_irrefl u)]; omega
    · rw [ite_eq_right (lt_asymm h), ite_eq_left h]; omega
  rw [show (v ((algebraMap L (𝔸f L) (algebraMap E L j) * β.val * star β.val : 𝔸f L) u)).log =
      (u.valuation L (algebraMap E L j)).log + halfOrder u + halfOrder (star u) by
    simp [hβ, j_ne_zero]]
  linarith [h_halves, hs_ord u]

end WeilDataExtension

/-! ## A CM step of prime degree with prescribed completion at a split place -/

section GrunwaldStep

open New NumberField Valued QZChar

/-- Let `A` be a place of the algebraic closure `Ω` (a valuation subring), `w` a finite place of
`E`, `χ` a character of `E_wˣ` (`LocField w`) with values in `ℚ/ℤ`, `ν` a Galois character of `E`
with `E' = stepField ν` the fixed field of the kernel of `symmetrize ν`, and `u` a finite place of
`E'`. The predicate says that `E' / E` is a step (`New.IsStep`: CM, Galois of prime degree, an
integer of trace `1`, for `ideleChar ν = exp (2πi ν ∘ Art)`) of degree `p` and `E'` has Weil data,
that `u` is split, lies below `A` and is the only place of `E'` above `w`, and that under the local
Artin map at `w` the character `ν` is trivial and `symmetrize ν` is `χ`. -/
structure New.GaloisRep.IsStepOfLocalChar {E : Type} [Field E] [EmbeddedNumberField E] [CMType E]
    {w : FinPlace E} (A : ClosurePlace) (χ : (LocField w)ˣ →* Multiplicative QZ) (p : ℕ)
    (ν : QZChar Gal(Ω/E)) (u : FinPlace (stepField ν)) : Prop where
  /-- The field `E'` has Weil data. -/
  nonempty_weilData : Nonempty (WeilData (stepField ν))
  /-- The extension `E' / E`, with the idele character of `ν`, is a step. -/
  isStep : IsStep (stepField ν) (ideleChar ν)
  /-- The extension `E' / E` has degree `p`. -/
  finrank_eq : Module.finrank E (stepField ν) = p
  /-- The place `u` is split. -/
  isSplit : u.IsSplit
  /-- The place `u` is the only place of `E'` above `w`. -/
  below_eq_iff (u' : FinPlace (stepField ν)) : u'.below E = w ↔ u' = u
  /-- The place `u` lies below `A`. -/
  isPlaceOver : IsPlaceOver A u
  /-- Under the local Artin map at `w`, the character `ν` is trivial. -/
  abelianLift_artinAt (x : (LocField w)ˣ) : abelianLift ν (artinAt Gal(Ω/E) w x) = 1
  /-- Under the local Artin map at `w`, the character `symmetrize ν` is `χ`. -/
  abelianLift_symmetrize_artinAt (x : (LocField w)ˣ) :
    abelianLift (symmetrize ν) (artinAt Gal(Ω/E) w x) = χ x

/-- Let `χ` be a character of `E_wˣ` (`LocField w`) with values in `ℚ/ℤ` that is killed by `p` and
kills the `(q - 1)`-th powers of units, `q = w.q` being the norm of `w`. If `w` lies above `p`,
then `χ` kills the units of `E_w`, since `p` divides `q` and so is prime to `q - 1`. -/
lemma New.GaloisRep.apply_eq_one_of_natCast_mem_asIdeal {E : Type} [Field E] [NumberField E]
    {w : FinPlace E} {p : ℕ} (hp : p.Prime) (χ : (LocField w)ˣ →* Multiplicative QZ)
    (hχ_pow : ∀ x : (LocField w)ˣ, χ x ^ p = 1)
    (h_tame : ∀ x : (LocField w)ˣ, v x.val = 1 → χ (x ^ (w.q - 1)) = 1)
    (hpw : (p : 𝓞 E) ∈ w.asIdeal) (x : (LocField w)ˣ) (hx : v x.val = 1) : χ x = 1 := by
  have h_fact : Fact p.Prime := ⟨hp⟩
  have h_cop : p.Coprime (w.q - 1) :=
    .of_dvd_left ((w.natCast_mem_iff_dvd hpw).mp w.asIdeal.absNorm_mem) (by simp)
  exact (pow_eq_one_iff_of_coprime h_cop).mp ⟨hχ_pow x, by rw [← map_pow, h_tame x hx]⟩

/-- Grunwald's theorem for CM extensions of prime degree. Let `E` be a CM field with Weil data. Let
`w` be a split finite place of `E` (one that differs from its conjugate) lying below the place `A`
of `Ω`. Let `χ ≠ 1` be a character of `E_wˣ` that is killed by the prime `p` and kills the
`(q - 1)`-th powers of units, `q = w.q` being the norm of `w`. Then there are a Galois character `ν`
of `E` and a place `u` of `stepField ν` (the fixed field of the kernel of `g ↦ ν g + ν gᶜ`) forming
a step of degree `p` with local character `χ` at `w` (`New.GaloisRep.IsStepOfLocalChar`). This says
that `stepField ν / E` is a step of degree `p`, `stepField ν` has Weil data, and `u` is split. -/
lemma New.GaloisRep.exists_isStepOfLocalChar {E : Type} [Field E] [EmbeddedNumberField E]
    [CMType E] [WeilData E] {w : FinPlace E} {A : ClosurePlace} {p : ℕ} (hw : w.IsSplit)
    (hA : IsPlaceOver A w) (hp : p.Prime) (χ : (LocField w)ˣ →* Multiplicative QZ) (hχ_ne : χ ≠ 1)
    (hχ_pow : ∀ x : (LocField w)ˣ, χ x ^ p = 1)
    (h_tame : ∀ x : (LocField w)ˣ, v x.val = 1 → χ (x ^ (w.q - 1)) = 1) :
    ∃ (ν : QZChar Gal(Ω/E)) (u : FinPlace (stepField ν)), IsStepOfLocalChar A χ p ν u := by
  -- Stage 1: Grunwald's theorem for `ψ b := χ ((star b) w)` at `w`, `star w`, and places above `p`
  -- yields `ν` trivial at `w`, with `symmetrize ν = χ` at `w` and unramified at `u = star u` and
  -- above `p`.
  have h_neZero : NeZero p := ⟨hp.ne_zero⟩
  let ψ : (𝔸f E)ˣ →* Multiplicative QZ := .mk' (fun b ↦ χ (ideleAt w (star b))) (by simp)
  have hχ_open : χ.ker.IsOpen :=
    isOpen_of_forall_pow_mem hp.ne_zero fun x ↦ by simpa using hχ_pow x
  obtain ⟨ν, hν, h_grun⟩ := grunwald hp (((finite_natCast_mem p).insert w).insert (star w)) ψ
    hχ_open.preimage_of_continuous fun b ↦ hχ_pow (ideleAt w (star b))
  have hν_w (x : (LocField w)ˣ) : abelianLift ν (artinAt Gal(Ω/E) w x) = 1 := by
    simpa [ψ, star_locIdele, hw.symm] using h_grun w x (.inl (by simp))
  have h_sym_w (x : (LocField w)ˣ) :
      abelianLift (symmetrize ν) (artinAt Gal(Ω/E) w x) = χ x := by
    have h_conj :
        abelianLift ν (artinMap Gal(Ω/E) (star (locIdele w x))) = ψ (star (locIdele w x)) := by
      rw [star_locIdele, h_grun _ _ (.inl (by simp))]
    simpa [ψ, hν_w, h_conj] using abelianLift_symmetrize ν (locIdele w x)
  have hν_unit (u : FinPlace E) (x : (LocField u)ˣ) (hu : star u = u ∨ (p : 𝓞 E) ∈ u.asIdeal)
      (hx : v x.val = 1) : abelianLift ν (artinMap Gal(Ω/E) (locIdele u x)) = 1 := by
    rw [h_grun u x (hu.elim (fun h ↦ .inr ⟨fun hq ↦ isSplit_of_q_prime hq h, hx⟩)
      fun h ↦ .inl (by simp [h]))]
    change χ (ideleAt w (star (locIdele u x))) = 1
    rw [star_locIdele]
    by_cases hwu : w = star u
    · subst hwu
      have hpu : (p : 𝓞 E) ∈ u.asIdeal :=
        hu.resolve_left fun h_fixed ↦ hw (by rw [h_fixed, h_fixed])
      rw [ideleAt_locIdele]
      exact apply_eq_one_of_natCast_mem_asIdeal hp χ hχ_pow h_tame (by simpa using hpu) _
        ((v_conjLoc rfl x.val).trans hx)
    · rw [ideleAt_locIdele_of_ne hwu, map_one]
  -- Stage 2: `symmetrize ν` is unramified at `u = star u` and above `p` and nontrivial at `w`,
  -- giving the step of degree `p`, Weil data, and a unique split place above `w`.
  have h_unram {B : ClosurePlace} {u : FinPlace E} (hB : IsPlaceOver B u)
      (hu : star u = u ∨ (p : 𝓞 E) ∈ u.asIdeal) :
      inertiaGroup Gal(Ω/E) B ≤ ker (symmetrize ν) := by
    have hu_star : star (star u) = star u ∨ (p : 𝓞 E) ∈ (star u).asIdeal :=
      hu.imp (fun h ↦ by rw [h, h]) fun h ↦ by simpa using h
    refine (hB.artinAt_units_trivial_iff_inertiaGroup_le (symmetrize ν)).mp fun x hx ↦ ?_
    rw [← artinMap_locIdele, abelianLift_symmetrize, star_locIdele,
      hν_unit u x hu hx, hν_unit (star u) _ hu_star (by simpa using hx), one_mul]
  obtain ⟨x₀, hx₀⟩ := DFunLike.ne_iff.mp hχ_ne
  obtain ⟨g₀, hg₀, hg₀_eq⟩ :=
    (hA.range_abelianLift_comp_artinAt (symmetrize ν)).le ⟨x₀, h_sym_w x₀⟩
  have h_sym_ne : symmetrize ν ≠ 0 := fun h_zero ↦
    hg₀_eq.trans_ne hx₀ (congrArg (fun s : QZChar Gal(Ω/E) ↦ toHom s g₀) h_zero)
  obtain ⟨u, hAu, hu_below⟩ := hA.exists_above (L := stepField ν)
  obtain ⟨h_step, h_deg⟩ := isStep_stepField ν hp hν h_sym_ne fun hB hu ↦ h_unram hB (.inr hu)
  have h_index : (ker (symmetrize ν)).relIndex (decompGroup Gal(Ω/E) A) ≠ 1 := fun h_one ↦
    hx₀ (hg₀_eq.symm.trans (Subgroup.relIndex_eq_one.mp h_one hg₀))
  have h_count : {u' : FinPlace (stepField ν) | u'.below E = w}.ncard = 1 :=
    ((Nat.prime_mul_iff.mp (by
      rwa [hA.ncard_above_mul_relIndex_eq_finrank (ker (symmetrize ν)), h_deg])).resolve_left
      fun h ↦ h_index h.right).right
  obtain ⟨u₁, h_set_eq⟩ := Set.ncard_eq_one.mp h_count
  have h_unique (u' : FinPlace (stepField ν)) : u'.below E = w ↔ u' = u₁ := by
    simpa using Set.ext_iff.mp h_set_eq u'
  obtain rfl : u = u₁ := (h_unique u).mp hu_below
  exact ⟨ν, u,
    { nonempty_weilData := nonempty_weilData_of_not_dvd_differentIdeal fun u' hu'_fix ↦
        not_dvd_differentIdeal_stepField ν fun hB ↦
          h_unram hB (.inl (by rw [← below_star, hu'_fix]))
      isStep := h_step, finrank_eq := h_deg
      isSplit := fun hu_fix ↦ hw (by rw [← hu_below, ← below_star, hu_fix])
      below_eq_iff := h_unique, isPlaceOver := hAu
      abelianLift_artinAt := hν_w, abelianLift_symmetrize_artinAt := h_sym_w }⟩

/-- `New.GaloisRep.exists_isStepOfLocalChar` with `χ ≠ 1` given by a point `x₀` where `χ x₀ ≠ 1`. -/
lemma New.GaloisRep.exists_step_of_local_char {E : Type} [Field E] [EmbeddedNumberField E]
    [CMType E] {w : FinPlace E} {A : ClosurePlace} [WeilData E] {p : ℕ} (hw : w.IsSplit)
    (hA : IsPlaceOver A w) (hp : p.Prime) (χ : (LocField w)ˣ →* Multiplicative QZ)
    {x₀ : (LocField w)ˣ} (hx₀ : χ x₀ ≠ 1) (hχ_pow : ∀ x : (LocField w)ˣ, χ x ^ p = 1)
    (h_tame : ∀ x : (LocField w)ˣ, v x.val = 1 → χ (x ^ (w.q - 1)) = 1) :
    ∃ (ν : QZChar Gal(Ω/E)) (u : FinPlace (stepField ν)), IsStepOfLocalChar A χ p ν u :=
  exists_isStepOfLocalChar hw hA hp χ (DFunLike.ne_iff.mpr ⟨x₀, hx₀⟩) hχ_pow h_tame

end GrunwaldStep
