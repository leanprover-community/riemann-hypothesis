module

import Mathlib.Algebra.Divisibility.Prod
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
public import TauCeti.RingTheory.Hilbert90.TameLevel
import TauCeti.Algebra.BigOperators.Finset.Periodic
public import Lib.GaloisRep.BaseChange.Defs
import Lib.Adelic.Adeles.AdditiveCharacter
import Lib.General.LinearAlgebra.MatrixPolynomials

/-!
# Hilbert 90 for GL_n and units under tame actions on Artinian, finite or profinite rings

This file gives versions of Hilbert's theorem 90, with congruence conditions, for a ring
endomorphism `σ` of finite order of a finite, Artinian or profinite ring. It proves Hilbert 90 for
`GL n` and for units at level `m`, and the surjectivity of the norm onto fixed units `≡ 1 mod m`.
`TauCeti.TameHilbert90.IsTameAtLevel σ p m` means: `σ ^ p = 1` with `0 < p`, `σ m = m`, some
element has trace `1` modulo `m`, and no `σ ^ i` with `0 < i < p` is trivial modulo a prime not
containing `m`. Tau Ceti proves Hilbert 90 over Artinian rings and the surjectivity of the norm over
finite rings; this file extends them to profinite rings.
`New.IsProfiniteRing R` means: every sequence `x` has a unique `L` with `x N ≡ L` modulo each
natural number `M ≠ 0`, for `N` in a set of the hyperfilter.
`New.twistedNorm τ p δ` is the twisted norm `δ · τ δ ⋯ τ^(p-1) δ` of `δ` in a monoid.

## Main definitions and results

* `TauCeti.TameHilbert90.IsTameAtLevel.hilbert90_gl`,
  `TauCeti.TameHilbert90.IsTameAtLevel.hilbert90_unit`: a cocycle `≡ 1 mod m` is a coboundary of an
  element `≡ 1 mod m`, for `GL n` and for units.
* `TauCeti.TameHilbert90.IsTameAtLevel.exists_prod_range_pow_apply_eq`: a fixed unit `≡ 1 mod m` is
  the norm of a unit `≡ 1 mod m`.
* `New.IsProfiniteRing.exists_algHom_semiconj`, `New.IsProfiniteRing.finite_quotient_natCast`,
  `New.isTameAtLevel_quotientNatMap`, bundled in
  `TauCeti.TameHilbert90.IsTameAtLevel.exists_algHom_semiconj_quotientNatMap`: a limit map from the
  finite quotients `R ⧸ (N !)` reduces the profinite case to the finite one.

## Relation to the literature

Known result: Hilbert 90 for GL_n and norm surjectivity on units, cyclic action, congruence level.
This is done over Artinian, finite or profinite rings, where the action need only be free away from
an invariant element m and have an element of trace one modulo m. Cocycles, coboundaries and units
are congruent to 1 modulo m. Source: A. Speiser 1919;
J.-P. Serre, Corps locaux, 1962, Ch. X §1 Prop. 3 and Ch. V §2; S. Chase, D. Harrison, A. Rosenberg,
Galois theory and Galois cohomology of commutative rings, Mem. AMS 52, 1965; for the norm on O[γ],
P. Scholze, The Langlands-Kottwitz approach for some simple Shimura varieties, 2013, Lemma 2.2.
-/

@[expose] public section

section TameDescent

open Matrix Finset Filter Subgroup Nat Function Ideal Quotient MulEquiv Algebra
open TauCeti.TameHilbert90

namespace New

variable {R n B V : Type*} [CommRing R] [CommRing B] [Fintype n] [DecidableEq n]
  {σ : R →+* R} {p : ℕ} {m x : R} {θ : B →+* B} [AddCommGroup V] [Module R V]

/-! ### Norms -/

/-- For a ring endomorphism `σ` of `R`, an element `m` and `p : ℕ`, the `p`-th iterate of
`y ↦ m * σ y` sends `x` to the norm `∏ i < p, (σ ^ i) m` times `(σ ^ p) x`. -/
lemma iterate_mul_apply :
    ∀ x : R, (fun y : R ↦ m * σ y)^[p] x = (∏ i ∈ range p, (σ ^ i) m) * (σ ^ p) x := by
  -- one more step multiplies by `m` and shifts every factor of the norm by `σ`
  induction p with
  | zero => simp
  | succ p ih =>
    intro x
    rw [iterate_succ_apply', ih, map_mul, map_prod, prod_range_succ', pow_zero, RingHom.coe_one,
      id_eq]
    simp only [RingHom.coe_pow, iterate_succ_apply']
    ring

/-! ### Profinite rings -/

/-- The ring of integral finite adeles of a number field E satisfies the profiniteness condition
`New.IsProfiniteRing`. -/
lemma isProfiniteRing_intAdeles {E : Type*} [Field E] [NumberField E] : IsProfiniteRing (Ô E) := by
  -- `Ô E` is compact Hausdorff, so `x` has a unique limit along `hyperfilter ℕ`; the sets
  -- `M • Ô E`, `M ≠ 0`, are a basis of neighbourhoods of `0`, so this is the limit in
  -- `IsProfiniteRing`.
  intro x
  have h_compact : CompactSpace (Ô E) := isCompact_iff_compactSpace.mp isCompact_Ô
  have h_basis :
      (nhds (0 : 𝔸f E)).HasBasis (fun M : ℕ ↦ M ≠ 0) fun M : ℕ ↦ (fun y : 𝔸f E ↦ M • y) '' Ô E :=
    ⟨fun U ↦ by aesop (add simp mem_nhds_zero_finAdele_iff)⟩
  have key (L : Ô E) :
      (∀ M : ℕ, M ≠ 0 → ∀ᶠ N : ℕ in hyperfilter ℕ, (M : Ô E) ∣ x N - L) ↔
        ((hyperfilter ℕ).map x).lim = L := by
    -- the limit along the ultrafilter is a limit in the sense of `Tendsto` in `𝔸f E`
    rw [Ultrafilter.lim_eq_iff_le_nhds, Ultrafilter.coe_map]
    change _ ↔ Tendsto x (hyperfilter ℕ) (nhds L)
    rw [tendsto_subtype_rng, ← tendsto_sub_nhds_zero_iff, h_basis.tendsto_right_iff]
    simp [dvd_def, Subtype.ext_iff, eq_comm]
  simpa only [key] using existsUnique_eq'

/-- If `R` is profinite (`New.IsProfiniteRing`) and `B` is an additive retract of `R`, through
additive maps `i : B → R` and `r : R → B` with `r (i x) = x`, then `B` is profinite. -/
lemma IsProfiniteRing.of_retract (hR : IsProfiniteRing R) (i : B →+ R) (r : R →+ B)
    (hri : ∀ x : B, r (i x) = x) : IsProfiniteRing B := by
  -- The limit of `x` in `B` is `r` of the limit of `i ∘ x` in `R`. Both maps are additive, so they
  -- preserve divisibility by a natural number.
  intro x
  obtain ⟨L, hL, h_unique⟩ := hR (i ∘ x)
  -- `r` carries `M ∣ i (x N) - L` to `M ∣ x N - r L`
  have h_dvd_r (M N : ℕ) (h_dvd : (M : R) ∣ i (x N) - L) : (M : B) ∣ x N - r L := by
    obtain ⟨c, hc⟩ := h_dvd
    refine ⟨r c, ?_⟩
    simpa [hri, ← nsmul_eq_mul] using congrArg r hc
  -- `i` carries `M ∣ x N - y` to `M ∣ i (x N) - i y`
  have h_dvd_i (M N : ℕ) (y : B) (h_dvd : (M : B) ∣ x N - y) : (M : R) ∣ i (x N) - i y := by
    obtain ⟨c, hc⟩ := h_dvd
    refine ⟨i c, ?_⟩
    simpa [← nsmul_eq_mul] using congrArg i hc
  refine ⟨r L, fun M hM ↦ (hL M hM).mono fun N ↦ h_dvd_r M N, fun y hy ↦ ?_⟩
  -- a limit `y` of `x` gives the limit `i y` of `i ∘ x`
  have hiy : i y = L := h_unique (i y) fun M hM ↦ (hy M hM).mono fun N ↦ h_dvd_i M N y
  rw [← hiy, hri y]

omit [DecidableEq n] in
/-- If `R` is profinite (`New.IsProfiniteRing`), so is every ring `B` that is isomorphic as an
additive group to `n → R`, through `coords`, for a finite type `n`. -/
lemma IsProfiniteRing.of_addEquiv_pi (hR : IsProfiniteRing R) (coords : B ≃+ (n → R)) :
    IsProfiniteRing B := by
  -- `n → R` is profinite, with limits taken coordinatewise, and `B` is a retract of it.
  have h_pi : IsProfiniteRing (n → R) := by
    intro x
    -- `L k` is the limit of the `k`-th coordinates, and `hL` says that it is the only one
    obtain ⟨L, hL⟩ : ∃ L : n → R, ∀ (k : n) (L' : R),
        (∀ M : ℕ, M ≠ 0 → ∀ᶠ N : ℕ in hyperfilter ℕ, (M : R) ∣ x N k - L') ↔ L k = L' :=
      forall_existsUnique_iff.mp fun k ↦ hR fun N ↦ x N k
    refine ⟨L, fun M hM ↦ ?_, fun L' hL' ↦ ?_⟩
    · -- each coordinate converges, and `n` is finite
      filter_upwards [eventually_all.mpr fun k ↦ (hL k (L k)).mpr rfl M hM] with N hN
      exact pi_dvd_iff.mpr fun k ↦ by simpa using hN k
    · funext k
      refine ((hL k (L' k)).mp fun M hM ↦ ?_).symm
      exact (hL' M hM).mono fun N hN ↦ by simpa using pi_dvd_iff.mp hN k
  exact h_pi.of_retract coords.toAddMonoidHom coords.symm coords.left_inv

/-- If `R` is profinite (`New.IsProfiniteRing`) and `σ` is tame at level `0`, so that `σ ^ p = 1`
and some element of `R` has trace `1`, then the subring `σ.eqLocus 1` of elements fixed by `σ` is
profinite. -/
lemma IsProfiniteRing.eqLocus (hR : IsProfiniteRing R) (h_tame : IsTameAtLevel σ p 0) :
    IsProfiniteRing (σ.eqLocus 1) := by
  -- With `e` of trace one, `x ↦ ∑ i < p, σ^[i] (e * x)` is an additive retraction of `R` onto the
  -- fixed ring.
  obtain ⟨e, he⟩ := h_tame.exists_dvd_sum_range_pow_sub_one
  have h_trace : ∑ i ∈ range p, σ^[i] e = 1 := by simpa [sub_eq_zero] using he
  have h_period (y : R) : σ^[p] y = y := by
    rw [← RingHom.coe_pow, h_tame.pow_eq_one, RingHom.coe_one, id_eq]
  have h_fixed (x : R) : IsFixedPt σ (∑ i ∈ range p, σ^[i] (e * x)) :=
    map_sum_range_eq_self_of_periodic (σ : R →+ R) (fun i ↦ σ^[i] (e * x)) (h_period (e * x))
      fun i ↦ iterate_succ_apply' σ i (e * x)
  let retract : R →+ σ.eqLocus 1 :=
    .mk' (fun x ↦ ⟨∑ i ∈ range p, σ^[i] (e * x), h_fixed x⟩) fun x y ↦
      Subtype.ext (by simp [mul_add, sum_add_distrib])
  refine hR.of_retract (σ.eqLocus 1).subtype.toAddMonoidHom retract fun x ↦ Subtype.ext ?_
  -- for a fixed `x` the sum is the trace of `e` times `x`
  change ∑ i ∈ range p, σ^[i] (e * x) = x
  have hx_iter (i : ℕ) : σ^[i] (x : R) = x := iterate_fixed x.prop i
  simp only [iterate_map_mul, hx_iter, ← sum_mul, h_trace, one_mul]

/-! ### Passing to finite quotients and descent at a prime -/

/-- Tameness passes along a ring homomorphism `f : R →+* B` that intertwines `σ` with an
endomorphism `θ` of `B`, provided `θ ^ p = 1`; the level becomes `f m`. -/
lemma _root_.TauCeti.TameHilbert90.IsTameAtLevel.of_semiconj (h_tame : IsTameAtLevel σ p m)
    (f : R →+* B) (hf : Semiconj f σ θ) (hθ : θ ^ p = 1) : IsTameAtLevel θ p (f m) := by
  obtain ⟨e, he⟩ : ∃ e : R, m ∣ ∑ i ∈ range p, (σ ^ i) e - 1 :=
    h_tame.exists_dvd_sum_range_pow_sub_one
  -- `f` intertwines the powers of `σ` with those of `θ`
  have h_pow (i : ℕ) (y : R) : (θ ^ i) (f y) = f ((σ ^ i) y) := by
    rw [RingHom.coe_pow, RingHom.coe_pow, (hf.iterate_right i).eq]
  have h_trace : f m ∣ ∑ i ∈ range p, (θ ^ i) (f e) - 1 := by simpa [h_pow] using map_dvd f he
  refine ⟨IsFixedPt.map h_tame.map_level hf, ⟨f e, h_trace⟩, hθ, h_tame.pos,
    fun i hi P _ h_triv ↦ ?_⟩
  have h_comap (y : R) : (σ ^ i) y - y ∈ P.comap f := by simpa [h_pow] using h_triv (f y)
  exact h_tame.mem_of_forall_sub_mem hi (P.comap f) h_comap

lemma span_natCast_le_comap (σ : R →+* R) (N : ℕ) : span {(N : R)} ≤ (span {(N : R)}).comap σ := by
  simp [span_le]

/-- The ring endomorphism of `R ⧸ (N)` induced by `σ`, for a natural number `N`. -/
def quotientNatMap (σ : R →+* R) (N : ℕ) : R ⧸ span {(N : R)} →+* R ⧸ span {(N : R)} :=
  quotientMap (span {(N : R)}) σ (span_natCast_le_comap σ N)

/-- Let `R` be profinite (`New.IsProfiniteRing`) and `σ` a ring endomorphism of `R`. Some
`R`-algebra map `Λ` from the families of residues modulo `N !` to `R` carries the maps
`quotientNatMap σ (N !)` to `σ`. -/
lemma IsProfiniteRing.exists_algHom_semiconj (hR : IsProfiniteRing R) (σ : R →+* R) :
    ∃ Λ : (∀ N : ℕ, R ⧸ span {((N ! : ℕ) : R)}) →ₐ[R] R,
      Semiconj Λ (Pi.map fun N : ℕ ↦ quotientNatMap σ N !) σ := by
  -- `Λ x` is the limit along the hyperfilter of lifts of the residues `x N`. Limits are unique and
  -- `M ∣ N !` for large `N`, so `Λ` commutes with every operation that passes to the quotients:
  -- sums, products, constants and `σ`.
  let I (N : ℕ) : Ideal R := span {(N : R)}
  replace hR (x : ℕ → R) :
      ∃! L : R, ∀ M : ℕ, M ≠ 0 → ∀ᶠ N : ℕ in hyperfilter ℕ, mk (I M) (x N) = mk (I M) L := by
    simpa [I, ← eq_zero_iff_dvd, sub_eq_zero] using hR x
  choose Λ hΛ_lim hΛ_uniq using fun x : ∀ N : ℕ, R ⧸ I N ! ↦ hR fun N ↦ (x N).out
  have hΛ_op {F : R → R → R} (G : ∀ M : ℕ, R ⧸ I M → R ⧸ I M → R ⧸ I M)
      (hG : ∀ {M : ℕ}, Semiconj₂ (mk (I M)) F (G M)) (x y : ∀ N : ℕ, R ⧸ I N !) :
      Λ (fun N ↦ G (N !) (x N) (y N)) = F (Λ x) (Λ y) := by
    -- By uniqueness it is enough that `F (Λ x) (Λ y)` is a limit of the lifts, modulo each `M`.
    refine (hΛ_uniq _ (F (Λ x) (Λ y)) fun M hM ↦ ?_).symm
    filter_upwards [hΛ_lim x M hM, hΛ_lim y M hM, hyperfilter_le_atTop (mem_atTop M)] with
      N hx hy hMN
    -- The lift of `G (x N) (y N)` and `F` of the lifts agree modulo `N !`, hence modulo `M`.
    have h_fact : mk (I N !) (G (N !) (x N) (y N)).out = mk (I N !) (F (x N).out (y N).out) := by
      simp [hG.eq]
    have h_dvd : (M : R) ∣ N ! := cast_dvd_cast (dvd_factorial (pos_of_ne_zero hM) hMN)
    calc
      mk (I M) (G (N !) (x N) (y N)).out = mk (I M) (F (x N).out (y N).out) :=
        mk_span_eq_iff_dvd_sub.mpr (h_dvd.trans (mk_span_eq_iff_dvd_sub.mp h_fact))
      _ = mk (I M) (F (Λ x) (Λ y)) := by rw [hG.eq, hx, hy, ← hG.eq]
  -- constants and `σ` are operations that ignore both or the first of their arguments
  have hΛ_const (a : R) : Λ (fun N ↦ mk (I N !) a) = a :=
    hΛ_op (fun M _ _ ↦ mk (I M) a) (fun _ _ ↦ rfl) (x := 0) (y := 0)
  have hΛ_mul (x y : ∀ N : ℕ, R ⧸ I N !) : Λ (x * y) = Λ x * Λ y := hΛ_op _ (map_mul _) x y
  have hΛ_add (x y : ∀ N : ℕ, R ⧸ I N !) : Λ (x + y) = Λ x + Λ y := hΛ_op _ (map_add _) x y
  have hΛ_σ (x : ∀ N : ℕ, R ⧸ I N !) : Λ (fun N ↦ quotientNatMap σ N ! (x N)) = σ (Λ x) :=
    hΛ_op (F := fun _ b ↦ σ b) (fun M _ b ↦ quotientNatMap σ M b) (fun _ _ ↦ rfl)
      (x := 0) (y := x)
  exact ⟨{ toFun := Λ, map_one' := hΛ_const 1, map_mul' := hΛ_mul, map_zero' := hΛ_const 0,
           map_add' := hΛ_add, commutes' := hΛ_const }, hΛ_σ⟩

/-- Each quotient `R ⧸ (N)` of a profinite ring `R` by a natural number `N ≠ 0` is finite. -/
lemma IsProfiniteRing.finite_quotient_natCast (hR : IsProfiniteRing R) {N : ℕ} (hN : N ≠ 0) :
    Finite (R ⧸ span {(N : R)}) := by
  -- A sequence of distinct residues would have a limit, so it would be constant on a set of the
  -- hyperfilter; but it takes each value at most once, and finite sets are not in it.
  refine .of_not_infinite fun h_inf ↦ ?_
  let x : ℕ ↪ R ⧸ span {(N : R)} := h_inf.natEmbedding _
  obtain ⟨L, hL, -⟩ := hR fun n ↦ (x n).out
  have h_ev : ∀ᶠ n : ℕ in hyperfilter ℕ, x n = mk (span {(N : R)}) L := by
    simpa [← eq_zero_iff_dvd, sub_eq_zero] using hL N hN
  exact ((Set.toFinite {mk (span {(N : R)}) L}).preimage_embedding x).notMem_hyperfilter h_ev

/-- If `σ` is tame at level `m`, the map `quotientNatMap σ N` it induces on `R ⧸ (N)` is tame at
the residue of `m`. -/
lemma isTameAtLevel_quotientNatMap (h_tame : IsTameAtLevel σ p m) (N : ℕ) :
    IsTameAtLevel (quotientNatMap σ N) p (mk (span {(N : R)}) m) := by
  have hq : Semiconj (mk (span {(N : R)})) σ (quotientNatMap σ N) := fun _ ↦ rfl
  have h_per (y : R) : IsPeriodicPt σ p y := by
    change σ^[p] y = y
    simp [← RingHom.coe_pow, h_tame.pow_eq_one]
  have hq_pow : quotientNatMap σ N ^ p = 1 :=
    ringHom_ext (RingHom.ext fun y ↦ (h_per y).map hq)
  exact h_tame.of_semiconj _ hq hq_pow

/-- Let `R` be profinite (`New.IsProfiniteRing`) and `σ` tame at level `m`. Then some
`R`-algebra map `Λ` from the families of residues modulo `N !` to `R` carries the maps
`quotientNatMap σ (N !)` to `σ`, and each quotient `R ⧸ (N !)` is finite, with
`quotientNatMap σ (N !)` tame at the residue of `m`. -/
lemma _root_.TauCeti.TameHilbert90.IsTameAtLevel.exists_algHom_semiconj_quotientNatMap
    (h_tame : IsTameAtLevel σ p m) (hR : IsProfiniteRing R) :
    ∃ Λ : (∀ N : ℕ, R ⧸ span {((N ! : ℕ) : R)}) →ₐ[R] R,
      Semiconj Λ (Pi.map fun N : ℕ ↦ quotientNatMap σ N !) σ ∧
      ∀ N : ℕ, Finite (R ⧸ span {((N ! : ℕ) : R)}) ∧
        IsTameAtLevel (quotientNatMap σ N !) p (mk (span {((N ! : ℕ) : R)}) m) := by
  obtain ⟨Λ, hΛ⟩ := hR.exists_algHom_semiconj σ
  exact ⟨Λ, hΛ, fun N ↦
    ⟨hR.finite_quotient_natCast (factorial_ne_zero N), isTameAtLevel_quotientNatMap h_tame _⟩⟩

/-! ### Hilbert 90 and norms at level `m` -/

/-- Hilbert 90 for `GL n` at level `m` over an Artinian ring `R`, the main case of
`TauCeti.TameHilbert90.IsTameAtLevel.hilbert90_gl`: if `c = 1 + m • Y` is invertible with
`c · σ c ⋯ σ^(p-1) c = 1` (`σ` applied entrywise), then `c · σ k = k` for an invertible
`k = 1 + m • W`. This is
`TauCeti.TameHilbert90.IsTameAtLevel.exists_mul_map_eq_of_twistedNorm_eq_one`. -/
lemma _root_.TauCeti.TameHilbert90.IsTameAtLevel.hilbert90_gl_of_isArtinianRing
    (h_tame : IsTameAtLevel σ p m) (hart : IsArtinianRing R) (c : GL n R) {Y : Matrix n n R}
    (hY : c.val = 1 + m • Y) (hc : twistedNorm (GeneralLinearGroup.map σ) p c = 1) :
    ∃ k : GL n R, ∃ W : Matrix n n R, c * k.val.map σ = k ∧ k.val = 1 + m • W := by
  -- the two twisted norms of `c` agree: both satisfy `N (i + 1) = c * σ (N i)`
  have h_norm (i : ℕ) : twistedNorm (GeneralLinearGroup.map σ) i c =
      MonoidHom.twistedNorm (GeneralLinearGroup.map σ) i c := by
    induction i with
    | zero => simp [twistedNorm]
    | succ i ih => rw [twistedNorm_succ', MonoidHom.twistedNorm_succ, ih]
  obtain ⟨k, W, hk, hW⟩ :=
    h_tame.exists_mul_map_eq_of_twistedNorm_eq_one c hY ((h_norm p).symm.trans hc)
  exact ⟨k, W, congrArg Units.val hk, hW⟩

/-- Hilbert 90 for `GL n` at level `m`. Let `R` be Artinian or profinite, and let `σ` be tame at
level `m`, meaning `σ m = m`, `σ ^ p = 1` with `0 < p`, some `e` has `∑ i < p, (σ ^ i) e ≡ 1 mod m`,
and for `0 < i < p` every prime ideal modulo which `σ ^ i` is the identity contains `m`. If
`c = 1 + m • Y` is invertible with `c · σ c ⋯ σ^(p-1) c = 1` (`σ` applied entrywise), then
`c = k · (σ k)⁻¹`, written `c · σ k = k`, for an invertible `k = 1 + m • W`. -/
lemma _root_.TauCeti.TameHilbert90.IsTameAtLevel.hilbert90_gl
    (h_tame : IsTameAtLevel σ p m) (hR : IsArtinianRing R ∨ IsProfiniteRing R) (c : GL n R)
    {Y : Matrix n n R} (hY : c.val = 1 + m • Y)
    (hc : twistedNorm (GeneralLinearGroup.map σ) p c = 1) :
    ∃ k : GL n R, ∃ W : Matrix n n R, c * k.val.map σ = k ∧ k.val = 1 + m • W := by
  rcases hR with hart | hR
  · exact h_tame.hilbert90_gl_of_isArtinianRing hart c hY hc
  -- Profinite case: solve in each finite quotient `R ⧸ N !` and apply the limit map entrywise.
  let q (N : ℕ) : R ⧸ span {(N : R)} →+* R ⧸ span {(N : R)} := quotientNatMap σ N
  have h_lim : ∃ Λ : (∀ N : ℕ, R ⧸ span {(N ! : R)}) →ₐ[R] R,
      Semiconj Λ (Pi.map fun N : ℕ ↦ q N !) σ ∧
      ∀ N : ℕ, Finite (R ⧸ span {(N ! : R)}) ∧ IsTameAtLevel (q N !) p m :=
    h_tame.exists_algHom_semiconj_quotientNatMap hR
  choose Λ hΛ hfin htame using h_lim
  let π (N : ℕ) : R →+* R ⧸ span {(N ! : R)} := mk (span {(N ! : R)})
  have hY_map (N : ℕ) : (GeneralLinearGroup.map (π N) c).val = 1 + π N m • Y.map (π N) := by
    ext
    simp_all [Matrix.one_apply]
  -- reduction modulo `N !` turns `σ` into `q N !`, so it keeps the twisted norm `1`
  have h_comm (N : ℕ) (δ : GL n R) : GeneralLinearGroup.map (π N) (GeneralLinearGroup.map σ δ) =
      GeneralLinearGroup.map (q N !) (GeneralLinearGroup.map (π N) δ) :=
    GeneralLinearGroup.ext fun _ _ ↦ rfl
  have hc_map (N : ℕ) :
      twistedNorm (GeneralLinearGroup.map (q N !)) p (GeneralLinearGroup.map (π N) c) = 1 := by
    rw [← map_twistedNorm _ (h_comm N), hc, map_one]
  choose k W hk hW using fun N ↦
    (htame N).hilbert90_gl_of_isArtinianRing inferInstance _ (hY_map N) (hc_map N)
  -- `L` is the `R`-algebra map from families of matrices over the quotients to matrices over `R`
  let L : (∀ N : ℕ, Matrix n n (R ⧸ span {(N ! : R)})) →ₐ[R] Matrix n n R :=
    Λ.mapMatrix.comp (piAlgEquiv (n := n) R).symm.toAlgHom
  refine ⟨(piUnits.symm k).map L, L W, ?_, ?_⟩
  · -- apply `L` to the equations `hk`: `L` fixes the constant `c` and commutes with `σ`
    have h_const : L (fun N ↦ (GeneralLinearGroup.map (π N) c).val) = c :=
      ext fun i j ↦ Λ.commutes (c i j)
    have h_σ : L (fun N ↦ (k N).val.map (q N !)) = (L fun N ↦ (k N).val).map σ :=
      ext fun i j ↦ hΛ _
    calc (c : Matrix n n R) * (L fun N ↦ (k N).val).map σ
        = L ((fun N ↦ (GeneralLinearGroup.map (π N) c).val) * fun N ↦ (k N).val.map (q N !)) := by
          rw [map_mul, h_const, h_σ]
      _ = L fun N ↦ (k N).val := congrArg L (funext hk)
  · -- apply `L` to the congruences `hW`
    calc _ = L (fun N ↦ (k N : Matrix n n (R ⧸ span {(N ! : R)}))) := rfl
      _ = L (1 + m • W) := congrArg L (funext hW)
      _ = 1 + m • L W := by rw [map_add, map_one, map_smul]

/-- Hilbert 90 for units at level `m`: let the commutative ring `R` be Artinian or profinite
(`IsProfiniteRing`: every sequence has a unique limit along the hyperfilter for the topology of the
ideals `(M)`). Let `σ` be tame at level `m` (`IsTameAtLevel σ p m`: `σ m = m`, `0 < p`, `σ ^ p = 1`,
some `e` has trace `∑ i < p, (σ ^ i) e ≡ 1 mod m`, and for `0 < i < p` every prime ideal modulo
which `σ ^ i` is the identity contains `m`). Then every unit `x ≡ 1 mod m` of norm
`x · σ x ⋯ σ^(p-1) x = 1` is `g / σ g`, i.e. `x * σ g = g`, for a unit `g ≡ 1 mod m`. -/
lemma _root_.TauCeti.TameHilbert90.IsTameAtLevel.hilbert90_unit
    (h_tame : IsTameAtLevel σ p m) (hR : IsArtinianRing R ∨ IsProfiniteRing R) (hx : IsUnit x)
    (hx_one : m ∣ x - 1) (hx_norm : ∏ i ∈ range p, (σ ^ i) x = 1) :
    ∃ g : Rˣ, m ∣ g - 1 ∧ x * σ g = g := by
  -- apply `hilbert90_gl` to the `1 × 1` matrix `x` and take the determinant of the solution
  obtain ⟨y, hy⟩ : ∃ y : R, x - 1 = m * y := hx_one
  let c : GL Unit R := diagGL fun _ : Unit ↦ hx.unit
  have hc_val : c.val = 1 + m • of fun _ _ ↦ y := by
    ext i j
    simpa [c] using eq_add_of_sub_eq' hy
  have hc_norm : twistedNorm (GeneralLinearGroup.map σ) p c = 1 := by aesop
  obtain ⟨k, W, hk, hW⟩ := h_tame.hilbert90_gl hR c hc_val hc_norm
  -- `k` is a `1 × 1` matrix, so its determinant is its only entry
  refine ⟨k.det, ?_, ?_⟩
  · have h_det : (k.det : R) = 1 + m * W () () := by simp [hW]
    rw [h_det, add_sub_cancel_left]
    exact dvd_mul_right m _
  · have h_entry : (c.val * k.val.map σ) () () = k.val () () := by rw [hk]
    simpa [c] using h_entry

/-- Norms for a tame action at level `m`, meaning that `σ m = m`, `σ ^ p = 1` with `0 < p`, some `e`
has trace `∑ i < p, (σ ^ i) e ≡ 1 mod m`, and for `0 < i < p` every prime modulo which `σ ^ i` is
the identity contains `m`. If the commutative ring `R` is finite or profinite, every `σ`-fixed unit
`x ≡ 1 mod m` is the norm `z · σ z ⋯ σ^(p-1) z` of a unit `z` with `z ≡ 1` and `z⁻¹ ≡ 1 mod m`. -/
lemma _root_.TauCeti.TameHilbert90.IsTameAtLevel.exists_prod_range_pow_apply_eq
    (h_tame : IsTameAtLevel σ p m) (hR : Finite R ∨ IsProfiniteRing R) (hx : IsUnit x)
    (hσx : σ x = x) (hx_one : m ∣ x - 1) :
    ∃ z : Rˣ, m ∣ z - 1 ∧ m ∣ z⁻¹ - 1 ∧ ∏ i ∈ range p, (σ ^ i) z = x := by
  obtain ⟨x, rfl⟩ := hx
  rcases hR with hfin | hR
  · exact h_tame.exists_prod_range_pow_eq_of_finite hσx hx_one
  -- Profinite case: solve in each finite quotient `R ⧸ N !` and apply the limit map `Λ`.
  let q (N : ℕ) : R ⧸ span {(N : R)} →+* R ⧸ span {(N : R)} := quotientNatMap σ N
  obtain ⟨Λ, hΛ, h_quotient⟩ : ∃ Λ : (∀ N : ℕ, R ⧸ span {(N ! : R)}) →ₐ[R] R,
      Semiconj Λ (Pi.map fun N : ℕ ↦ q N !) σ ∧
      ∀ N : ℕ, Finite (R ⧸ span {(N ! : R)}) ∧ IsTameAtLevel (q N !) p m :=
    h_tame.exists_algHom_semiconj_quotientNatMap hR
  choose h_finite h_tame_quotient using h_quotient
  have hx_fixed (N : ℕ) : q N ! (Ideal.Quotient.mk _ (x : R)) = Ideal.Quotient.mk _ (x : R) := by
    change Ideal.Quotient.mk _ (σ x) = Ideal.Quotient.mk _ (x : R)
    rw [hσx]
  choose z hz hz_inv hz_norm using fun N ↦
    (h_tame_quotient N).exists_prod_range_pow_eq_of_finite
      (x := Units.map (mk (span {(N ! : R)})).toMonoidHom x) (hx_fixed N) (map_dvd _ hx_one)
  -- `Λ` keeps congruences modulo `m`
  have h_cong (y : ∀ N : ℕ, R ⧸ span {(N ! : R)})
      (hy : ∀ N : ℕ, mk (span {(N ! : R)}) m ∣ y N - 1) : m ∣ Λ y - 1 := by
    simpa using map_dvd Λ (pi_dvd_iff.mpr hy : algebraMap R _ m ∣ y - 1)
  use (piUnits.symm z).map Λ, h_cong _ hz, h_cong _ hz_inv
  -- `Λ` intertwines the powers of `σ`, is multiplicative and sends the residues of `x` to `x`
  have h_iter (i : ℕ) (y : ∀ N : ℕ, R ⧸ span {(N ! : R)}) :
      (σ ^ i) (Λ y) = Λ (fun N ↦ (q N ! ^ i) (y N)) := by
    rw [RingHom.coe_pow, ← (hΛ.iterate_right i).eq y, Pi.map_iterate]
    rfl
  have h_norms : Λ (fun N ↦ ∏ i ∈ range p, (q N ! ^ i) (z N : R ⧸ span {(N ! : R)})) = x :=
    (congrArg Λ (funext hz_norm)).trans (Λ.commutes x)
  calc ∏ i ∈ range p, (σ ^ i) (Λ fun N ↦ (z N : R ⧸ span {(N ! : R)}))
      = ∏ i ∈ range p, Λ (fun N ↦ (q N ! ^ i) (z N : R ⧸ span {(N ! : R)})) :=
        prod_congr rfl fun i _ ↦ h_iter i _
    _ = x := by rw [← map_prod, prod_fn, h_norms]

end New

end TameDescent
