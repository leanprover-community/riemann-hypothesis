module

import TauCeti.NumberTheory.Padics.Complex.TateTwist
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.PicardGroup
import Mathlib.Topology.Separation.CompletelyRegular
public import Lib.PadicHodge.Crystalline.Basic
public import Lib.PadicHodge.PeriodRings.DeRhamPeriods
import Lib.ClassField.Places.DecompositionCompletion
import Lib.General.Groups.ProfiniteCharacters

/-!
# Tate's vanishing theorem, Hodge–Tate elimination and the filtration of B_dR

Let `χ` be the cyclotomic character `New.cyclotomicGp` of `New.Gp p = Gal(ℚ̄_p/ℚ_p)`, where the
class `[ThePrime p]` says that `p` is prime. The file also defines the filtration tⁿ B_dR⁺ of the de
Rham period field B_dR = `New.Period.BdR`.

## Main definitions and results

* `New.Period.tate_eq_zero_of_cyclotomicGp_twist`: the only `x` in `ℂ_p` with
  `χ(g) ^ u g x = χ(g) ^ v x` for all `g` near `1` is `0` when `u ≠ v`.
* `New.Period.le_of_hodgeTate_stable`: for a subspace of `ℂ_p ^ ι` stable under the Galois action
  twisted by `χ ^ u i` in the coordinate `i`, the vectors of minimal support can be taken algebraic,
  fixed and supported on one weight, by the theorems of Tate and Ax.
* `New.Period.hodgeFil`: the step tⁿ B_dR⁺, with t = `New.Period.tPeriod` a uniformiser of the
  discrete valuation ring B_dR⁺ = `New.Period.BdRPlus`, on which g acts by g t = χ(g) t
  (`New.Period.smul_tUnit_zpow`).
* `New.Period.exists_mem_localFieldOf_of_forall_smul_eq`: an element of ℂ_p fixed by an open subgroup lies in its fixed
  field K in Q̄_p.
* `New.Period.BdR.exists_sub_mem_of_smul_sub_mem`: an element of B_dR that is invariant modulo a
  B_dR⁺-submodule S is congruent modulo S to an element of K; S = 0 gives the invariants of B_dR.

Notions from other files:
* `New.Period.OverGp`, `New.Period.localFieldOf Γ`: a homomorphism j = `toGp` from a group `Γ` to
  `New.Gp p` with open image, and the subfield of Q̄_p fixed by that image.

## Relation to the literature

Known result: The Ax–Sen–Tate theorem and Tate's vanishing of the invariants of C_p(i). Ax's theorem
is not proved in this file; it comes from an imported file, as `ax_mem_closure_fixedField` and
`exists_algebraic_of_fixed_near_one`, without the constant. Tate's theorem for H⁰ on an open
subgroup follows from Tau Ceti's vanishing theorem over its finite fixed field. A consequence
is that invariants of B_dR modulo a submodule come from the base field. Source: J. Ax, Zeros of
polynomials over local fields: the Galois action, J. Algebra 15 (1970); J. Tate, p-divisible groups
(1967), §3; proofs in Fontaine–Ouyang 3.3-3.5 and Brinon–Conrad §14.

See also `Lib.PadicHodge.Crystalline.Regularity` and `Lib.PadicHodge.PeriodRings.DeRhamPeriods`.
-/

@[expose] public section

/-! ## Tate's vanishing theorem for cyclotomic twists of ℂ_p -/

/-- Tate's theorem: if `χ(g) ^ u • g • x = χ(g) ^ v • x` for all `g` near `1` in `Gal(ℚ̄_p/ℚ_p)`,
with `χ` the cyclotomic character and integers `u ≠ v`, then `x = 0` in `ℂ_p`. This is
`H⁰(U, ℂ_p(u - v)) = 0` for every open subgroup `U`, as the relation is asked only near `1`. -/
lemma New.Period.tate_eq_zero_of_cyclotomicGp_twist {p : ℕ} [ThePrime p] {x : ℂ_[p]} {u v : ℤ}
    (hu : u ≠ v)
    (hx : ∀ᶠ g : Gp p in nhds 1, (cyclotomicGp g ^ u).val • g • x = (cyclotomicGp g ^ v).val • x) :
    x = 0 := by
  -- An open subgroup `U` on which the relation holds.
  obtain ⟨U, hU⟩ : ∃ U : OpenSubgroup (Gp p), (U : Set (Gp p)) ⊆
      {g | (cyclotomicGp g ^ u).val • g • x = (cyclotomicGp g ^ v).val • x} :=
    NonarchimedeanGroup.is_nonarchimedean _ hx
  let K := fixedFieldOf (U : Subgroup (Gp p))
  apply PadicComplex.eq_zero_of_forall_cyclotomicCharacter_zpow_mul_smul_eq
    (K := K) (i := u - v) (sub_ne_zero.mpr hu)
  intro σ
  let g := σ.restrictScalars ℚ_[p]
  have hg : g ∈ U := by
    change g ∈ U.toSubgroup
    rw [← fixingSubgroup_fixedFieldOf U.toSubgroup]
    exact fun z ↦ σ.commutes z
  rw [← UniformSpace.Completion.algEquiv_restrictScalars_smul (R := ℚ_[p]), ← Algebra.smul_def]
  change algebraMap ℤ_[p] ℚ_[p] (cyclotomicGp g ^ (u - v)).val • g • x = x
  rw [IsScalarTower.algebraMap_smul]
  change cyclotomicGp g ^ (u - v) • g • x = x
  rw [zpow_sub, mul_comm, mul_smul, inv_smul_eq_iff]
  exact hU hg

/-!
## Elimination by vectors of minimal support

Elimination: a submodule `W` of a free module is contained in `W'` as soon as `W'` contains enough
vectors of `W` of minimal support.

* `New.Period.le_of_echelon`: the linear algebra, by induction on the support.
-/

section Elimination

open UniformSpace.Completion Submodule Units

/-- Let `b` give coordinates on `V`. Suppose that for each nonzero `v ∈ W` to which all vectors of
`W` supported within `v` are proportional, some `u ∈ W ⊓ W'` supported within `v` has a
coordinate equal to `1`. Then `W ≤ W'`. -/
lemma New.Period.le_of_echelon {A V ι : Type*} [CommRing A] [AddCommGroup V] [Module A V]
    (b : V ≃ₗ[A] ι →₀ A) {W W' : Submodule A V}
    (h_exists_pivot : ∀ v ∈ W, v ≠ 0 →
      (∀ y ∈ W, (∀ i : ι, b v i = 0 → b y i = 0) → ∀ k : ι, b v k • y = b y k • v) →
      ∃ u ∈ W ⊓ W', (∃ k : ι, b u k = 1) ∧ ∀ i : ι, b v i = 0 → b u i = 0) :
    W ≤ W' := by
  -- Both steps are inductions on the support. If `y` is supported within `w` and `b w k ≠ 0`,
  -- eliminating the `k`-th coordinate makes the support strictly smaller.
  have h_elim (w y : V) (k : ι) (hy : ∀ i : ι, b w i = 0 → b y i = 0) (hk : b w k ≠ 0) :
      (b (b y k • w - b w k • y)).support < (b w).support := by
    refine ⟨fun i ↦ not_imp_not.mp (by simp +contextual [hy]), fun h_sub ↦ ?_⟩
    -- the `k`-th coordinate of the combination vanishes, but that of `w` does not
    simpa [mul_comm] using h_sub (Finsupp.mem_support_iff.mpr hk)
  have wf := InvImage.wf (fun w : V ↦ (b w).support) (wellFounded_lt (α := Finset ι))
  -- Every nonzero `w ∈ W` has a vector `u` as in `h_exists_pivot`, without the proportionality
  -- assumption.
  have h_pivot (w : V) (hw : w ∈ W) (hw₀ : w ≠ 0) :
      ∃ u ∈ W ⊓ W', (∃ k : ι, b u k = 1) ∧ ∀ i : ι, b w i = 0 → b u i = 0 := by
    induction w using wf.induction with | _ w ih =>
      by_contra h_none
      -- Every `y ∈ W` supported within `w` is proportional to `w`: otherwise eliminating a
      -- coordinate gives a smaller nonzero vector of `W`, whose `u` would serve for `w`.
      have h_prop : ∀ y ∈ W, (∀ i : ι, b w i = 0 → b y i = 0) →
          ∀ k : ι, b w k • y = b y k • w := by
        intro y hy h_supp k
        by_contra h_ne
        apply h_none
        have hk : b w k ≠ 0 := fun hk_zero ↦ h_ne (by simp [hk_zero, h_supp k hk_zero])
        obtain ⟨u, hu, h_one, hu_supp⟩ := ih _ (h_elim w y k h_supp hk)
          (sub_mem (W.smul_mem _ hw) (W.smul_mem _ hy)) (sub_ne_zero.mpr (Ne.symm h_ne))
        exact ⟨u, hu, h_one, fun i hi ↦ hu_supp i (by simp [hi, h_supp i hi])⟩
      exact h_none (h_exists_pivot w hw hw₀ h_prop)
  -- Subtracting `b w k • u` from `w` gives an element of `W` of smaller support.
  intro w hw
  induction w using wf.induction with | _ w ih =>
    obtain rfl | hw₀ := eq_or_ne w 0
    · exact zero_mem _
    obtain ⟨u, ⟨huW, huW'⟩, ⟨k, hk⟩, h_supp⟩ := h_pivot w hw hw₀
    -- If `b w k = 0` then `1 = b u k = 0` in `A`, which would force `w = 0`.
    have hwk : b w k ≠ 0 := fun h_zero ↦
      hw₀ (by rw [← one_smul A w, ← hk, h_supp k h_zero, zero_smul])
    have h_diff : b u k • w - b w k • u ∈ W' :=
      ih _ (h_elim w u k h_supp hwk) (sub_mem (W.smul_mem _ hw) (W.smul_mem _ huW))
    rwa [hk, one_smul, sub_mem_iff_left _ (smul_mem _ _ huW')] at h_diff

/-- Let `ι` be finite and let `F` be a filter on `Gal(ℚ̄_p/ℚ_p)` with `nhds 1 ≤ F` (`hF`). Let the
subspace `W` of `ℂ_p ^ ι` be stable along `F` under `a ↦ (χ(g) ^ u i • g • a i)ᵢ` (`hW`). Suppose
that `W'` contains every vector `a` of `W` with coordinates in `ℚ̄_p` such that, for some `k`,
(a) `‖a i‖ ≤ 1`, (b) `a i = 0` whenever `u i ≠ u k`, (c) `a k = 1` and (d) each `a i` is fixed
along `F` (`h_pure`). Then `W ≤ W'`. -/
lemma New.Period.le_of_hodgeTate_stable {p : ℕ} [ThePrime p] {ι : Type*} [Finite ι]
    {F : Filter (Gp p)} (hF : nhds 1 ≤ F) (u : ι → ℤ) (W W' : Submodule ℂ_[p] (ι → ℂ_[p]))
    (hW : ∀ a ∈ W, ∀ᶠ g : Gp p in F, (fun i : ι ↦ (cyclotomicGp g ^ u i).val • g • a i) ∈ W)
    (h_pure : ∀ (a : ι → PadicAlgCl p) (k : ι), (↑) ∘ a ∈ W →
      -- (a) the coordinates are integral
      (∀ i : ι, ‖a i‖ ≤ 1) →
      -- (b) those of another weight than `u k` vanish
      (∀ i : ι, u i = u k ∨ a i = 0) →
      -- (c) the `k`-th one is `1`
      a k = 1 →
      -- (d) each is fixed by `g`, eventually along `F`
      (∀ i : ι, ∀ᶠ g : Gp p in F, g (a i) = a i) →
      (↑) ∘ a ∈ W') :
    W ≤ W' := by
  -- Apply `le_of_echelon`: for `v` as there, normalise by a coordinate `v k` of largest norm.
  refine le_of_echelon (Pi.basisFun ℂ_[p] ι).repr fun v hv hv₀ h_prop ↦ ?_
  have h_nonempty : Nonempty ι := (Function.ne_iff.mp hv₀).nonempty
  obtain ⟨k, h_max⟩ : ∃ k : ι, ∀ i : ι, ‖v i‖ ≤ ‖v k‖ := Finite.exists_max _
  have hk : v k ≠ 0 := fun hk_zero ↦ hv₀ <| funext fun i ↦ by simpa [hk_zero] using h_max i
  let w : ι → ℂ_[p] := fun i ↦ (v k)⁻¹ * v i
  have h_mem : w ∈ W := W.smul_mem _ hv
  -- The twisted conjugate of `w` lies in `W` with the same support, so is proportional to it; the
  -- factor is its `k`-th coordinate `χ(g) ^ u k`.
  have h_twist (i : ι) :
      ∀ᶠ g : Gp p in F,
        (cyclotomicGp g ^ u i).val • g • w i = (cyclotomicGp g ^ u k).val • w i := by
    filter_upwards [hW _ h_mem] with g hg
    -- `h_prop` for the twisted conjugate of `w`, at the coordinates `k` and `i`
    have h_supp (j : ι) : (Pi.basisFun ℂ_[p] ι).repr v j = 0 →
        (Pi.basisFun ℂ_[p] ι).repr (fun l ↦ (cyclotomicGp g ^ u l).val • g • w l) j = 0 := by
      simp +contextual [w]
    have h_coord : v k * ((cyclotomicGp g ^ u i).val • g • w i) =
        ((cyclotomicGp g ^ u k).val • g • w k) * v i := by
      simpa using congrFun (h_prop _ hg h_supp k) i
    rw [← mul_right_inj' hk, h_coord]
    simp [w, hk]
  -- By Tate's theorem the coordinates with `u i ≠ u k` vanish; the others are fixed, so
  -- algebraic by Ax's theorem.
  have h_zero (i : ι) (hi : u i ≠ u k) : w i = 0 :=
    tate_eq_zero_of_cyclotomicGp_twist hi (hF (h_twist i))
  have h_fixed (i : ι) : ∀ᶠ g : Gp p in F, g • w i = w i := by
    by_cases hi : u i = u k
    · exact (h_twist i).mono fun g hg ↦ isSMulRegular _ _ (by simpa only [hi] using hg)
    · simp [h_zero i hi]
  choose a ha using fun i ↦ exists_algebraic_of_fixed_near_one (hF (h_fixed i))
  -- Restate these facts for the algebraic vector `a`.
  have ha_mem : ((↑) ∘ a : ι → ℂ_[p]) ∈ W := by
    simpa only [funext ha, Function.comp_def] using h_mem
  have ha_fixed (i : ι) : ∀ᶠ g : Gp p in F, g (a i) = a i := by
    simpa only [ha, algEquiv_smul_coe, coe_inj] using h_fixed i
  have h_one : a k = 1 := coe_inj.mp (by simp [← ha, w, hk, coe_one])
  have h_norm (i : ι) : ‖a i‖ ≤ 1 := by simp [← norm_coe (a i), ← ha, w, field, h_max]
  have h_weight (i : ι) : u i = u k ∨ a i = 0 :=
    (eq_or_ne (u i) (u k)).imp_right fun hi ↦ by simpa only [ha, coe_eq_zero_iff] using h_zero i hi
  refine ⟨(↑) ∘ a, ⟨ha_mem, h_pure a k ha_mem h_norm h_weight h_one ha_fixed⟩, ⟨k, ?_⟩, ?_⟩
  · simp [h_one, coe_one]
  · simp +contextual [← ha, w]

end Elimination

/-!
## The filtration of B_dR and its Galois invariants

The relevant subgroup of `Gal(ℚ̄_p/ℚ_p)` is the image of `j = toGp : Γ → Gp p`, and K is
`New.Period.localFieldOf Γ`.
-/

namespace New.Period

variable {p : ℕ} [ThePrime p] (Γ : Type*) [Group Γ] [𝒥 : OverGp Γ p] {m n : ℤ} {x : BdR}
  {y : BdRPlus}

/-- Ax–Sen–Tate: if `j : Γ → G_p` has open image, an element of `ℂ_p` fixed by every `j(g)` lies
in the subfield `K` of `ℚ̄_p` fixed by that image. -/
lemma exists_mem_localFieldOf_of_forall_smul_eq {x : ℂ_[p]}
    (hx : ∀ g : Γ, 𝒥.toGp g • x = x) : ∃ a ∈ localFieldOf Γ, x = a := by
  -- by Ax's theorem `x` is algebraic
  have h_near : ∀ᶠ g : Gp p in Filter.map toGp (nearOne Γ), g • x = x := by simp [hx]
  obtain ⟨a, rfl⟩ := exists_algebraic_of_fixed_near_one (nhds_one_le_map_nearOne Γ h_near)
  exact ⟨a, by simpa using hx, rfl⟩

open BdRPlus Algebra IsDiscreteValuationRing IsFractionRing Submodule algebraMap

/-- The period `tPeriod` is a prime element of B_dR⁺: it is associated to the prime `ξ = xi` of
B_dR⁺, which divides exactly the `y` with `thetaBdR y = 0`. -/
lemma prime_tPeriod : Prime tPeriod := associated_xi_tPeriod.prime prime_xi

/-- The period `tPeriod` as a unit of the field `B_dR`. -/
noncomputable def tUnit : BdRˣ := Units.mk0 tPeriod (mod_cast prime_tPeriod.ne_zero)

/-- The step `tⁿ B_dR⁺` of the filtration of B_dR, a B_dR⁺-submodule, for any integer `n`. -/
noncomputable def hodgeFil (n : ℤ) : Submodule BdRPlus BdR := BdRPlus ∙ (tUnit ^ n).val

lemma mem_hodgeFil : x ∈ hodgeFil n ↔ ∃ y : BdRPlus, y * (tUnit ^ n).val = x := by
  simp [hodgeFil, mem_span_singleton, smul_def']

@[simp]
lemma algebraMap_mem_hodgeFil_zero : algebraMap BdRPlus BdR y ∈ hodgeFil 0 := by
  simp [hodgeFil, mem_span_singleton, smul_def']

/-- The filtration decreases: `tⁿ B_dR⁺ ≤ tᵐ B_dR⁺` for `m ≤ n`. -/
lemma hodgeFil_anti : Antitone hodgeFil := by
  refine antitone_int_of_succ_le fun k ↦ ?_
  -- `tᵏ⁺¹ = tᵏ · t` with `t` in B_dR⁺
  simp [← mul_self_zpow, hodgeFil, tUnit, mem_span_singleton, smul_def']

/-- The filtration is multiplicative: `tᵐ B_dR⁺ · tⁿ B_dR⁺ ⊆ tᵐ⁺ⁿ B_dR⁺`. -/
lemma mul_mem_hodgeFil {y : BdR} : x ∈ hodgeFil m → y ∈ hodgeFil n → x * y ∈ hodgeFil (m + n) := by
  intro hx hy
  simpa [span_mul_span, zpow_add, hodgeFil] using mul_mem_mul hx hy

/-- An element `y` of B_dR⁺ lies in `tᴹ B_dR⁺` if and only if `ξ ^ M` divides `y`, where `ξ = xi` is
the prime of B_dR⁺ dividing exactly the kernel of `thetaBdR`. -/
lemma algebraMap_mem_hodgeFil_iff_xi_pow_dvd {M : ℕ} :
    ↑y ∈ hodgeFil M ↔ (xi : BdRPlus) ^ M ∣ y := by
  -- `t = tPeriod` and `ξ` are associated, so their powers divide the same elements; an identity
  -- `y = c tᴹ` holds in B_dR⁺ if and only if it holds in B_dR.
  have h_cast (c : BdRPlus) :
      (y : BdR) = algebraMap BdRPlus BdR c * (tPeriod : BdR) ^ M ↔ y = c * tPeriod ^ M := by
    norm_cast
  simp [associated_xi_tPeriod.pow_pow.dvd_iff_dvd_left, dvd_def, eq_comm, mul_comm, hodgeFil, tUnit,
    mem_span_singleton, smul_def', h_cast]

/-- An element `y` of B_dR⁺ lies in `t B_dR⁺` if and only if its residue `θ(y)` vanishes. -/
lemma algebraMap_mem_hodgeFil_one_iff : ↑y ∈ hodgeFil 1 ↔ thetaBdR y = 0 := by
  simpa [thetaBdR_eq_zero_iff] using algebraMap_mem_hodgeFil_iff_xi_pow_dvd (y := y) (M := 1)

/-- An element of Q̄_p lies in every step `n ≤ 0` of the filtration, and in a step `n > 0` only if
it is zero. -/
lemma coe_mem_hodgeFil_iff {x : PadicAlgCl p} : ↑x ∈ hodgeFil n ↔ 0 < n → x = 0 := by
  refine ⟨fun hx hn ↦ ?_, fun hx ↦ ?_⟩
  · -- `x` lies in `hodgeFil 1`, so its residue `x` vanishes
    simpa using algebraMap_mem_hodgeFil_one_iff.mp (hodgeFil_anti hn hx)
  · by_cases! hn : 0 < n
    · simp [hx hn]
    · exact hodgeFil_anti hn algebraMap_mem_hodgeFil_zero

/-! ### Galois action and invariants -/

/-- An element `g` of `G_p` acts on `tᵏ` by `χ(g) ^ k`, for every integer `k`. -/
lemma smul_tUnit_zpow (g : Gp p) (k : ℤ) :
    g • ((tUnit ^ k : BdRˣ) : BdR) =
      ((cyclotomicGp g ^ k : ℤ_[p]ˣ) : ℤ_[p]) • ((tUnit ^ k : BdRˣ) : BdR) := by
  -- `g • t = χ(g) • t`, raised to a nonnegative or a negative power
  cases k <;>
    simp [smul_tPeriod, mul_pow, mul_comm, ← IsScalarTower.algebraMap_apply, tUnit, smul_def']

/-- Let `j = toGp : Γ → Gal(ℚ̄_p/ℚ_p)` have open image (`OverGp Γ p`, `p` prime) and let
`K = localFieldOf Γ` be the subfield of `ℚ̄_p` fixed by `j(Γ)`. If `x ∈ B_dR` and `j(g) • x - x`
lies in the B_dR⁺-submodule `S` of B_dR for every `g`, then `x - a ∈ S` for some `a ∈ K`. This is a
B_dR form of the Ax–Sen–Tate theorem; the case `S = 0` says that every element of B_dR fixed by
`j(Γ)` lies in `K`. -/
lemma BdR.exists_sub_mem_of_smul_sub_mem (S : Submodule BdRPlus BdR) {x : BdR}
    (hx : ∀ g : Γ, toGp g • x - x ∈ S) :
    ∃ a : localFieldOf Γ, x - a.val ∈ S := by
  -- Suppose no `x - a`, `a` in the fixed field, lies in `S`. Then each `x - a` is a unit of
  -- `BdRPlus` with residue in the fixed field (`h_sub_eq_unit`). Take `a = 0`, then `a` the
  -- residue of `x`: the unit `x - a` has residue `0`.
  by_contra! hS
  have h_smul_tPeriod_zpow (g : Gp p) (k : ℤ) :
      ((g • tPeriod : BdRPlus) : BdR) ^ k = (cyclotomicGp g ^ k).val • ↑tPeriod ^ k := by
    simpa [tUnit] using smul_tUnit_zpow g k
  have h_sub_eq_unit (a : localFieldOf Γ) :
      ∃ u : BdRPlusˣ, x - a.val = u.val ∧ ∃ b ∈ localFieldOf Γ, thetaBdR u = .coe' b := by
    have ha_fix : ∀ g : Γ, toGp g • (a.val : BdR) = a.val := by
      simpa using (mem_localFieldOf (Γ := Γ)).mp a.property
    -- `BdRPlus` is a discrete valuation ring with uniformiser `t = tPeriod`: `x - a = u tⁿ`.
    obtain ⟨n, u, hu⟩ : ∃ (n : ℤ) (u : BdRPlusˣ), x - a.val = u • (tPeriod : BdR) ^ n :=
      exists_units_eq_smul_zpow_of_irreducible prime_tPeriod.irreducible
        (S.zero_mem.ne_of_notMem (hS a)).symm
    -- As `g x - x = (χ(g)ⁿ g u - u) tⁿ` is in `S` and `u tⁿ` is not, the bracket is no unit.
    have h_nonunit (g : Γ) :
        ¬ IsUnit ((cyclotomicGp (toGp g) ^ n).val • toGp g • u.val - u) := by
      intro h_unit
      apply hS a
      rw [hu]
      refine S.smul_mem u ((S.smul_mem_iff_of_isUnit h_unit).mp ?_)
      have h_diff : toGp g • x - x =
          ((cyclotomicGp (toGp g) ^ n).val • toGp g • u.val - u) • (tPeriod : BdR) ^ n := by
        simp [h_smul_tPeriod_zpow, ha_fix, ← sub_smul, smul_distrib_smul,
          smul_algebra_smul_comm, eq_add_of_sub_eq hu, ← smul_assoc, Units.smul_def]
      simpa only [h_diff] using hx g
    have h_res (g : Γ) :
        (cyclotomicGp (toGp g) ^ n).val • toGp g • thetaBdR u = thetaBdR u := by
      simpa [sub_eq_zero, smul_def'] using h_nonunit g
    -- Tate: the residue of `u` is not zero, so `n = 0`. Ax: it then lies in the fixed field.
    have h_near : ∀ᶠ g : Gp p in Filter.map toGp (nearOne Γ),
        (cyclotomicGp g ^ n).val • g • thetaBdR u = (cyclotomicGp g ^ (0 : ℤ)).val • thetaBdR u :=
      Filter.eventually_map.mpr (.of_forall fun g ↦ by simpa using h_res g)
    obtain rfl : n = 0 := by
      by_contra hn
      exact isUnit_iff.mp u.isUnit
        (tate_eq_zero_of_cyclotomicGp_twist hn (nhds_one_le_map_nearOne Γ h_near))
    have h_res_fixed : ∀ g : Γ, toGp g • thetaBdR u = thetaBdR u := by simpa using h_res
    refine ⟨u, ?_, exists_mem_localFieldOf_of_forall_smul_eq Γ h_res_fixed⟩
    simpa [Units.smul_def, smul_def'] using hu
  obtain ⟨u, hu, a, ha, h_res⟩ := h_sub_eq_unit 0
  obtain ⟨v, hv, -⟩ := h_sub_eq_unit ⟨a, ha⟩
  have h_unit : IsUnit (u.val - algebraMap (PadicAlgCl p) BdRPlus a) :=
    ⟨v, IsFractionRing.injective _ BdR (by simp [← hu, ← hv, ← IsScalarTower.algebraMap_apply])⟩
  simpa [h_res] using isUnit_iff.mp h_unit

end New.Period
