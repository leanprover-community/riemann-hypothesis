module

public import New.Congruences.Selmer.Line
public import New.Congruences.Selmer.TiedClasses
public import New.Congruences.Selmer.Descent

/-!
# The descent bounds for tied Selmer groups, stated for classes

The descent bounds the lengths of tied Selmer groups, which are modules of cocycles that vanish at
`γ_*`. By `New.Selmer.SelmerDatum.length_tiedSelmer_eq_length_map_π₁` such a group has the length
of the module of classes in `H¹(Gal(Ω/E), T / a)` of the cocycles with the same local conditions and
ties, without the normalisation at `γ_*`. This file states the descent bounds for those classes.

* `New.Selmer.exists_isTiedPrimes_length_classes_le`,
  `New.Selmer.exists_isTiedPrimes_card_le_and_length_classes_le`: sets of tied primes for which the
  tied Selmer classes of every datum are short.
* `New.Selmer.SelmerDatum.exists_boundsSelmer_ellVal_eval_le_of_length_classes_le`: the polynomial
  bound from a bound on the classes tied at the later primes.

Notions from other files:
* `New.Selmer.SelmerDatum.tiedCocyclesZ1`: the tied cocycles without the normalisation at `γ_*`,
  as continuous 1-cocycles of `T / a`; `New.DiscreteModule.π₁` sends them to their classes.

## Relation to the literature

See `New.Congruences.Selmer.Descent` for related work.
-/

@[expose] public section

noncomputable section

namespace New.Selmer

open Module Finset

open scoped NNReal

variable {ℓ : ℕ} [ThePrime ℓ] {E : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]
  {S₀ : Finset (FinPlace E)} {g₀ : Gal(Ω/E)} {O ι : Type} [CommRing O] [PadicIntegerRing O ℓ]
  {n : ι → Type} [∀ i : ι, Fintype (n i)] [∀ i : ι, DecidableEq (n i)]
  (T : ∀ i : ι, SelmerDatum ℓ S₀ g₀ O (n i))

/-- `New.Selmer.exists_isTiedPrimes_length_tiedSelmer_le` for classes: the tied primes it gives
make the module of tied Selmer classes modulo `ϖ ^ e` of every datum no longer than its global
and local terms. -/
theorem exists_isTiedPrimes_length_classes_le [Fintype ι] {M N : ℕ} {V : ι → Gal(Ω/E) → Prop}
    {W : Set Gal(Ω/E)} {P₀ : FinPlace E} {J : Finset (FinPlace E)}
    {x : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)} {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ}
    (h_room : ∀ i : ι, 2 * Fintype.card (n i) * e + 1 < Nat.card (IsLocalRing.ResidueField O))
    (hV : ∀ (i : ι) (g : Gal(Ω/E)), V i g ↔ reduceModPow ℓ M (T i).ρ g = 1) (hN : M < N)
    (he : ϖ ^ e ∣ ℓ ^ M) (hJ : IsTiedPrimes ℓ S₀ V W N P₀ J x) :
    ∃ (J' : Finset (FinPlace E)) (x' : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)),
      IsTiedPrimes ℓ S₀ V W N P₀ J' x' ∧
      (#J' : ℕ∞) ≤ #J + totalTiedLength T ϖ e J x ∧
      ∀ i : ι,
        length O (((T i).tiedCocyclesZ1 he J' J' x' i).map ((T i).reductionModule he).π₁) ≤
          (T i).globalTerm + (T i).placesTerm := by
  obtain ⟨J', x', hJ', h_card, h_len⟩ :=
    exists_isTiedPrimes_length_tiedSelmer_le T hϖ h_room hV hN he hJ
  refine ⟨J', x', hJ', h_card, fun i ↦ ?_⟩
  rw [← (T i).length_tiedSelmer_eq_length_map_π₁ he hJ' (fun g ↦ (hV i g).1) subset_rfl]
  exact h_len i

/-- `New.Selmer.exists_isTiedPrimes_card_le_and_length_le` for classes. Let `g₀` be inertial at a
place of `S₀` prime to `ℓ`, let the residue field of `O` be large, and let `W` be a neighbourhood of
`g₀`. There is `s` such that for every `N > M` there is a set `J` of at most `s` tied primes for
which, for every datum `T i`, the module of tied Selmer classes in `H¹(Gal(Ω/E), T i / ℓ ^ M)` is
no longer than the global term plus the local terms of `T i`. -/
theorem exists_isTiedPrimes_card_le_and_length_classes_le [Finite ι]
    (hg₀ : g₀ ∈ inertiaAbove (S₀ \ placesDividing E ℓ)) (M : ℕ)
    (h_room : ∀ i : ι, 2 * Fintype.card (n i) * IsDiscreteValuationRing.addVal O (ℓ ^ M) + 1 <
      Nat.card (IsLocalRing.ResidueField O))
    {W : Set Gal(Ω/E)} (hW : W ∈ nhds g₀) :
    ∃ s : ℕ, ∀ N > M, ∃ (P₀ : FinPlace E) (J : Finset (FinPlace E))
      (x : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)),
      IsTiedPrimes ℓ S₀ (fun (i : ι) (g : Gal(Ω/E)) ↦ reduceModPow ℓ M (T i).ρ g = 1) W N P₀ J x ∧
      #J ≤ s ∧
      ∀ i : ι,
        length O (((T i).tiedCocyclesZ1 (dvd_refl ((ℓ : O) ^ M)) J J x i).map
          ((T i).reductionModule (dvd_refl ((ℓ : O) ^ M))).π₁) ≤
          (T i).globalTerm + (T i).placesTerm := by
  obtain ⟨s, h⟩ := exists_isTiedPrimes_card_le_and_length_le T hg₀ M h_room hW
  refine ⟨s, fun N hN ↦ ?_⟩
  obtain ⟨P₀, J, x, hJ, h_card, h_len⟩ := h N hN
  refine ⟨P₀, J, x, hJ, h_card, fun i ↦ ?_⟩
  rw [← (T i).length_tiedSelmer_eq_length_map_π₁ dvd_rfl hJ (fun _ h ↦ h) subset_rfl]
  exact h_len i

namespace SelmerDatum

variable {ι n : Type} [Fintype n] [DecidableEq n] {V : ι → Gal(Ω/E) → Prop} {W : Set Gal(Ω/E)}
  {J : Finset (FinPlace E)} {M N s₀ : ℕ} {P₀ : FinPlace E} {r : ℚ≥0}

open scoped Classical in
/-- `New.Selmer.SelmerDatum.exists_boundsSelmer_ellVal_eval_le` with its hypothesis on classes: if
the tied Selmer classes modulo `ℓ ^ M` with the ties at the primes of `J` other than `P₀` have
length at most `β_T`, then some `P` bounds the length of the Selmer module of the characters at
all points (`BoundsSelmer`), and `v(P(x₀)) ≤ β_T + s₀ r` at a point `x₀` whose coordinates have
valuation at least `r`. -/
theorem exists_boundsSelmer_ellVal_eval_le_of_length_classes_le {O : CoeffRing ℓ}
    (T : SelmerDatum ℓ S₀ g₀ O.val n) {d : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O.val)}
    (h_primes : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hN₀ : N ≠ 0) (i : ι)
    (hV : ∀ g : Gal(Ω/E), V i g → reduceModPow ℓ M T.ρ g = 1)
    (h_tied : length O.val
      ((T.tiedCocyclesZ1 (dvd_refl ((ℓ : O.val) ^ M)) J (J.erase P₀) d i).map
        (T.reductionModule (dvd_refl ((ℓ : O.val) ^ M))).π₁) ≤ T.β)
    (hs₀ : 2 * Fintype.card n * #J ≤ s₀) (hr : r ≤ 1) (hN : M ≤ N * r) :
    ∃ (P : MvPolynomial J O.val) (x₀ : J → intQpBar ℓ),
      (∀ v : J, (r : ℝ≥0) ≤ ellVal (x₀ v).val) ∧
      ellVal (MvPolynomial.eval x₀ (P.map O.toIntQpBar)).val ≤
        O.normLength T.β + s₀ * (r : ℝ≥0) ∧
      BoundsSelmer ℓ M (fun v : J ↦ (d v).1.character) T.ρ (unionWithConj T.places J)
        T.classRelations P := by
  rw [← T.length_tiedSelmer_eq_length_map_π₁ dvd_rfl h_primes hV (erase_subset P₀ J)] at h_tied
  exact T.exists_boundsSelmer_ellVal_eval_le h_primes hN₀ i hV h_tied hs₀ hr hN

end SelmerDatum

end New.Selmer
