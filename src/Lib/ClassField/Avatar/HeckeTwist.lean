module

public import Lib.ClassField.HeckeCharacter.AlgebraicValues
public import Lib.PadicHodge.Limit.CrystallineLimit
public import Lib.GaloisRep.Main.Defs
public import Lib.GaloisRep.Main.LocalConditions
import Lib.ClassField.Places.TameInertia
import Lib.GaloisRep.Pseudocharacter.SemisimpleRepresentations
import Lib.PadicHodge.Characters
import Lib.PadicHodge.Crystalline.HodgeTateJumps
import Lib.PadicHodge.Crystalline.Regularity

/-!
# Twisting ℓ-adic Galois representations by algebraic Hecke characters

An element `ω` of `New.AlgHeckeChar E` is a pair `(θ, n)`, where `θ = ω.1.1` is a character of the
finite ideles with open kernel, `n = ω.1.2.toAdd` is its type, and `θ(x) = ∏_σ σ(x) ^ (-n_σ)` on
`Eˣ`. This file constructs the twist of a continuous `ℓ`-adic representation `ρ` by `ω`, controlled
at the finite places `w` where `ω` is unramified and its type takes a single natural-number value
`d` over `w`.

## Main definitions and results

* `New.scalarRep`: the one-dimensional representation of `Gal(Ω/E)` given by a character `μ`.
* `New.Variety.exists_twist_algHeckeChar`: twisting `ρ` by `ω`, controlled at places `w` where `ω`
  is unramified and its type is one natural number `d`. The twist is by `χ ^ d · μ`, with `χ` the
  cyclotomic character and `μ` the `ℓ`-adic avatar of `ω |·| ^ (-d)`, whose type vanishes over `w`.

Notions from other files:
* `New.AlgHeckeChar`: algebraic Hecke characters of a number field `E`.
* `New.GaloisRep.IsSphericalAbove ρ R J w P`: above `w`, `ρ` is unramified or crystalline, its jump
  multiplicities are `R`-related to `J`, and `P` kills every geometric Frobenius.
-/

@[expose] public section

noncomputable section

namespace New

section HeckeTwist

variable {E : Type _} {ℓ : ℕ} [Field E] [EmbeddedNumberField E] [ThePrime ℓ]

open Polynomial GaloisRep Units Fintype Period

@[fun_prop]
lemma Selmer.continuous_cyclotomicCharIn :
  Continuous (cyclotomicCharIn (Γ := Gal(Ω/E)) (PadicAlgCl ℓ) Ω ℓ) :=
  (continuous_algebraMap ℤ_[ℓ] (PadicAlgCl ℓ)).units_map.comp (continuous_cyclotomicChar ℓ)

/-- The one-dimensional representation of `Gal(Ω/E)` by the scalars `μ g`. -/
def scalarRep (μ : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ) : Gal(Ω/E) →* GL (Fin 1) (PadicAlgCl ℓ) :=
  (Matrix.GeneralLinearGroup.scalar (Fin 1)).comp μ

/-- In a chart `L : PadicPlaceEmbedding E A ℓ` at `A` above `ℓ` (`decompRep` restricts to the
decomposition group at `A`; `cyclotomicGp` is the cyclotomic character of its image `L.toGp g`),
twisting the scalar representation of `μ` by the `d`-th power of the cyclotomic character is its
Tate twist by `d`. -/
private lemma decompRep_scalarRep_cyclotomicCharIn_pow_mul
    (μ : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ)
    (A : ClosurePlace) (d : ℕ) [L : PadicPlaceEmbedding E A ℓ] (g : decompGroup Gal(Ω/E) A)
    (x : Fin 1 → PadicAlgCl ℓ) :
    decompRep (scalarRep (cyclotomicCharIn (PadicAlgCl ℓ) Ω ℓ ^ d * μ)) A g x =
      (cyclotomicGp (L.toGp g) ^ (d : ℤ)).val • decompRep (scalarRep μ) A g x := by
  simp [scalarRep, PadicPlaceEmbedding.cyclotomicGp_eq_cyclotomicChar, mul_smul, ← map_pow,
    ← smul_def]

/-- In a chart at `A` above `ℓ`, the scalar representation of `μ` is the Tate twist by `-d` of its
twist by the `d`-th power of the cyclotomic character. -/
private lemma decompRep_scalarRep_eq_cyclotomicCharIn_pow_mul
    (μ : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ) (A : ClosurePlace) (d : ℕ) [L : PadicPlaceEmbedding E A ℓ]
    (g : decompGroup Gal(Ω/E) A) (x : Fin 1 → PadicAlgCl ℓ) :
    decompRep (scalarRep μ) A g x =
      (cyclotomicGp (L.toGp g) ^ (-d : ℤ)).val •
        decompRep (scalarRep (cyclotomicCharIn (PadicAlgCl ℓ) Ω ℓ ^ d * μ)) A g x := by
  rw [decompRep_scalarRep_cyclotomicCharIn_pow_mul]
  simp [smul_smul, ← mul_pow]

/-- Twisting a character by the `d`-th power of the cyclotomic character keeps it unramified or
crystalline at `A`. -/
lemma isGoodAt_scalarRep_cyclotomicCharIn_pow_mul (μ : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ)
    (A : ClosurePlace) (d : ℕ) (h : IsGoodAt (scalarRep μ) A) :
    IsGoodAt (scalarRep (cyclotomicCharIn (PadicAlgCl ℓ) Ω ℓ ^ d * μ)) A := by
  obtain ⟨h_inertia, h_crys⟩ := h
  -- The cyclotomic character is trivial on inertia away from `ℓ`; the crystalline part passes to
  -- the Tate twist.
  refine ⟨?_, h_crys.tate_twist d (decompRep_scalarRep_cyclotomicCharIn_pow_mul μ A d)⟩
  simpa +contextual [scalarRep, cyclotomicChar_eq_one_of_mem_inertiaGroup (A := A)] using h_inertia

/-- Twisting a character by the `d`-th power of the cyclotomic character lowers its jumps at `A`
by `d`. -/
lemma hasJumpsAt_scalarRep_cyclotomicCharIn_pow_mul [PadicIso ℓ] (μ : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ)
    (A : ClosurePlace) (d : ℕ) (n : (E →+* ℂ) → ℤ)
    (h : HasJumpsAt (scalarRep μ) A fun τ : E →+* ℂ ↦ {n τ + d}) :
    HasJumpsAt (scalarRep (cyclotomicCharIn (PadicAlgCl ℓ) Ω ℓ ^ d * μ)) A fun τ : E →+* ℂ ↦
      {n τ} := by
  -- The jump `u` of the twist has the multiplicity of the jump `u + d` of `μ`.
  intro L γ τ hτ u
  simp [← jump_twist_cyclotomicGp (-d) (decompRep_scalarRep_eq_cyclotomicCharIn_pow_mul μ A d),
    ← h hτ,
    Multiset.count_singleton]

/-- Let μ be a character of Gal(Ω/E) with values in the algebraic closure of ℚ_ℓ, let A be a place
of Ω, and let s be such that s⁻¹ stabilises A and acts as x ↦ x^q modulo its maximal ideal, with
q ≠ 0. If X − q^d c kills s at A for the one-dimensional representation μ, then X − c kills s at A
for χ_ℓ^d · μ, where χ_ℓ is the ℓ-adic cyclotomic character. "P kills s at A" (`PolyKillsAt`) means
P(r(s)) = 0 when ℓ is a unit at A, and otherwise the Weil-pair condition `New.Period.IsKilledBy`
along every local datum at A. -/
lemma polyKillsAt_scalarRep_cyclotomicCharIn_pow_mul
    (μ : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ) (A : ClosurePlace) (d : ℕ) (s : Gal(Ω/E)) (q : ℕ)
    (c : PadicAlgCl ℓ) (hq : q ≠ 0) (hs : IsFrob A q s⁻¹)
    (h : PolyKillsAt (scalarRep μ) A s (X - C (q ^ d * c))) :
    PolyKillsAt (scalarRep (cyclotomicCharIn (PadicAlgCl ℓ) Ω ℓ ^ d * μ)) A s (X - C c) := by
  -- It suffices to show that `q ^ d * (X - c)` kills `s`.
  obtain ⟨h_away, h_above⟩ :
      (A.valuation ℓ = 1 → aeval (scalarRep μ s).val (X - C ((q : PadicAlgCl ℓ) ^ d * c)) = 0) ∧
        ∀ [L : PadicPlaceEmbedding E A ℓ] ⦃hs : s ∈ decompGroup Gal(Ω/E) A⦄ ⦃k : ℕ⦄,
          IsWeilPair (L.toGp ⟨s, hs⟩) k →
            IsKilledBy (decompRep (scalarRep μ) A) ⟨s, hs⟩ k (X - C ((q : PadicAlgCl ℓ) ^ d * c)) :=
    h
  have hq_ne : (q : PadicAlgCl ℓ) ^ d ≠ 0 := by simp [hq]
  -- (the second field binds the chart `L` implicitly, hence `@fun`)
  refine .of_dvd (P := C ((q : PadicAlgCl ℓ) ^ d) * (X - C c))
    ⟨fun hℓ ↦ ?_, @fun L hs_dec k hk ↦ ?_⟩ ((C_mul_dvd hq_ne).mpr dvd_rfl)
  · -- Away from `ℓ` the cyclotomic character takes the value `q` at `s⁻¹`.
    have h_cyc : (q : PadicAlgCl ℓ) = algebraMap ℤ_[ℓ] (PadicAlgCl ℓ) (cyclotomicChar Ω ℓ s⁻¹) := by
      rw [hs.cyclotomicChar_eq ℓ hℓ]
      simp
    -- `simp_all` unfolds the scalar representations and uses `h_cyc` and `h_val`.
    simp_all [sub_eq_zero, Matrix.algebraMap_eq_diagonal, scalarRep, Matrix.diagonal_pow,
      funext_iff]
  · -- Above `ℓ` we have `q = ℓ ^ k`, and the linear Frobenius of `μ` is `ℓ ^ (k * d)` times that
    -- of the twist.
    have h_frob : IsFrob (intQpBar ℓ) q (L.toGp ⟨s, hs_dec⟩)⁻¹ := by
      rwa [← map_inv, L.isFrob_iff]
    have hq_pow : q = ℓ ^ k := hk.eq_pow_of_isFrob h_frob
    obtain ⟨h_pcr, h_killed⟩ :
        IsKilledBy (decompRep (scalarRep μ) A) ⟨s, hs_dec⟩ k (X - C (q ^ d * c)) :=
      h_above hk
    have h_pcr_twist := h_pcr.tate_twist d (decompRep_scalarRep_cyclotomicCharIn_pow_mul μ A d)
    refine ⟨h_pcr_twist, ?_⟩
    rw [C_mul', eval₂_smul, ← h_killed, eq_comm, linearFrob_twist_cyclotomicGp h_pcr_twist hk d
      (decompRep_scalarRep_eq_cyclotomicCharIn_pow_mul μ A d)]
    rw [eval₂_sub, eval₂_C]
    simp [hq_pow, pow_mul, Algebra.smul_def, mul_sub]

/-- Mapping the Hecke polynomial of `t` by a ring homomorphism `f` gives the Hecke polynomial of
`f ∘ t`. -/
lemma map_heckePoly {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (q N : ℕ) (t : ℕ → R) :
    (heckePoly q N t).map f = heckePoly q N (f ∘ t) := by
  simp [heckePoly, Polynomial.map_sum]

/-- Let ω be an algebraic Hecke character of the CM field E of type n, and let ι = ιℓ be the fixed
isomorphism of ℂ with the algebraic closure of ℚ_ℓ. For continuous ρ there is a continuous ρ' (in
the proof, a twist of ρ) with the following property at every finite place w where ω is unramified
and n_σ = d for all σ with ισ inducing w. Put c = ω(ϖ_w), with ϖ_w the chosen uniformiser
`uniformizer w` at w. If `IsSphericalAbove` holds for ρ with jump data J and `heckePoly q a` of the
ι(t_j c^(−j)), it holds for ρ' with jump data J(τ) − n_τ and `heckePoly q a` of the ι(t_j). Here
`IsSphericalAbove ρ R J w P` means that at each place of Ω over w, ρ is good, its jump
multiplicities are R-related to J, and P kills geometric Frobenius. Also `heckePoly q a t = Σ_{j≤a}
(−1)^j q^{j(j−1)/2} t_j X^{a−j}`. -/
lemma Variety.exists_twist_algHeckeChar [PadicIso ℓ] [CMType E] (ω : AlgHeckeChar E) (d : ℕ)
    {ρ : PadicRep Gal(Ω/E) ℓ} (hρ : Continuous ρ.rep) :
    ∃ ρ' : PadicRep Gal(Ω/E) ℓ,
      Continuous ρ'.rep ∧
      -- at a place `w` where `ω` is unramified and of type `d` at all embeddings over `w`
      ∀ w : FinPlace E,
        (∀ σ : E →+* ℂ, inducedPrime σ = w → ω.val.2.toAdd σ = d) →
        CharUnramifiedAt ω.val.1 w →
        ∀ {R : ℕ → ℕ → Prop} {J : (E →+* ℂ) → Multiset ℤ} {q a : ℕ} {t : ℕ → ℂ},
          IsSphericalAbove ρ.rep R J w
            (heckePoly q a
              (ιℓ ∘ fun j : ℕ ↦ t j * (ω.val.1 (locIdele w (uniformizer w)) : ℂ)⁻¹ ^ j)) →
          IsSphericalAbove ρ'.rep R (fun τ : E →+* ℂ ↦ (J τ).map fun u : ℤ ↦ u - ω.val.2.toAdd τ) w
            (heckePoly q a (ιℓ ∘ t)) := by
  -- Twist by `ν = cyclotomicCharIn ^ d * μ`, with `μ` the avatar of `θ = ω |·| ^ (-d)`. The type of
  -- `θ` vanishes over `w`, so `avatarCompatAt_of_type_eq_zero` describes `μ` at `w`. The character
  -- `|·| ^ d`, of type `d`, is `IsHeckeOfType.toAlgebraic` of the trivial character with weight
  -- `k = 2 d`.
  have one_hecke : IsHeckeOfType (K := E) 1 fun _ ↦ (d - d : ℤ) := by
    simp [IsHeckeOfType, isOpen_iff_eventually]
  let θ : AlgHeckeChar E := ω / one_hecke.toAlgebraic (m := d) (k := d + d) (fun _ ↦ rfl)
  let μ : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ := θ.avatar
  let ν : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ := cyclotomicCharIn _ Ω ℓ ^ d * μ
  refine ⟨⟨twistByChar ν ρ.rep⟩, .of_coeHom_comp (.smul (by fun_prop) (by fun_prop)), ?_⟩
  intro w hd hω R J q a t hρ_sph A hA
  set c : ℂ := ((ω.val.1 (locIdele w (uniformizer w)) : ℂˣ) : ℂ) with hc
  have θ_val : heckeCoeff θ.val.fst ∅ w = w.q ^ d * c := by
    simp [heckeCoeff, θ, c, v_uniformizer, ← two_mul, zpow_mul, ← Complex.ofReal_pow, field]
  -- `θ` is unramified at `w`: `ω` is, and `|·| ^ d` is trivial on local units.
  have hθ_unr : ∀ x : (LocField w)ˣ, Valued.v x.val = 1 → θ.val.fst (locIdele w x) = 1 :=
    fun x hx ↦ by simp [θ, hω x hx, hx, Units.ext_iff]
  -- At `A`, `μ` is unramified or crystalline, has minus the type of `θ` as its jumps, and
  -- `X - ιℓ (θ ϖ_w)` kills every geometric Frobenius.
  obtain ⟨μ_unr, μ_jump, μ_frob⟩ :
      IsGoodAt (scalarRep μ) A ∧
        JumpsRelAt (scalarRep μ) A Eq (fun τ : E →+* ℂ ↦ {-θ.val.snd.toAdd τ}) ∧
        ∀ s : Gal(Ω/E), IsFrob A w.q s⁻¹ →
          PolyKillsAt (scalarRep μ) A s (X - C (ιℓ (heckeCoeff θ.val.fst ∅ w))) :=
    (avatarCompatAt_of_type_eq_zero θ
        fun σ hσ ↦ sub_eq_zero.mpr (hd σ hσ)).isSphericalAbove_of_unramified hθ_unr hA
  -- Being unramified or crystalline passes to the twist, jumps are shifted by the jump of `ν`, and
  -- `Q` kills `s` for the twist if `Q (c X)` kills it for `ρ` and `X - c` for `ν`.
  have h_twist (g : Gal(Ω/E)) : (twistByChar ν ρ.rep g).val = (ν g).val • (ρ.rep g).val := rfl
  obtain ⟨ρ_unr, ρ_jump, ρ_frob⟩ := hρ_sph hA
  refine ⟨ρ_unr.twist h_twist (isGoodAt_scalarRep_cyclotomicCharIn_pow_mul μ A d μ_unr),
    ρ_jump.twist h_twist (hasJumpsAt_scalarRep_cyclotomicCharIn_pow_mul μ A d _ ?_), fun s hs ↦ ?_⟩
  · simpa [θ, IsHeckeOfType.toAlgebraic, neg_add_eq_sub] using μ_jump
  refine .twist (c := ιℓ c) ((ρ_frob s hs).of_dvd ⟨C (ιℓ c ^ a), ?_⟩) h_twist
    (polyKillsAt_scalarRep_cyclotomicCharIn_pow_mul μ A d s w.q _ w.one_lt_q.ne_zero hs ?_)
  · -- Substituting `ιℓ c * X` multiplies the term of `t j` by `ιℓ c ^ a / ιℓ c ^ j`.
    ext
    rw [← map_pow, coeff_mul_C]
    simp +contextual [coeff_heckePoly, c, apply_ite, pow_sub₀, field]
  · simpa [θ_val] using μ_frob s hs

end HeckeTwist

end New

end
