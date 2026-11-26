module

public import Lib.SiegelWeil.RallisInner.Doubling

/-!
# Summability of the vacuum coefficients from the doubling formula

For `2 * card n < M`, the coefficients `New.SiegelWeil.vacuumCoeff M b` of the vacuum are absolutely
summable over the representatives `New.SiegelWeil.cosetRep` of the cosets of the points integral at
any set of places (`New.SiegelWeil.summable_norm_vacuumCoeff`).

The proof applies Rallis' inner product formula `New.SiegelWeil.inner_product_formula` to the
definite spaces `stdSpace E n`, `stdSpace E m` (with `card m = M`), the vacuum datum and the
constant function `1`: the matrix coefficient `g ↦ ⟨vac, ω(g) vac⟩` is integrable on the adelic
unitary group. Cutting the group into the cosets of the points integral at every place
(`New.hasSum_setIntegral_mul_of_existsUnique`), the integral of its modulus is the sum of the moduli
of the vacuum coefficients times a positive number.
-/

@[expose] public section

noncomputable section

open MeasureTheory Fintype

namespace New

/-- Cutting an integral over a group into cosets. Let `μ` be left invariant on `H`, let `L` be a
measurable subgroup, and let the points `r i`, for `i` in a countable type, meet every coset `g L`
exactly once. The integral of an integrable `Φ` is the sum over `i` of the integrals of
`g ↦ Φ (r i * g)` over `L`. -/
lemma hasSum_setIntegral_mul_of_existsUnique {H ι F : Type*} [Group H] [MeasurableSpace H]
    [MeasurableMul H] {μ : Measure H} [μ.IsMulLeftInvariant] {L : Subgroup H} [Countable ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hL : MeasurableSet (L : Set H)) {r : ι → H}
    (hr : ∀ g : H, ∃! i, (r i)⁻¹ * g ∈ L) {Φ : H → F} (hΦ : Integrable Φ μ) :
    HasSum (fun i ↦ ∫ g in (L : Set H), Φ (r i * g) ∂μ) (∫ g, Φ g ∂μ) := by
  -- The cosets `r i L` are disjoint, cover `H`, and each is the image of `L` under a measure
  -- preserving left translation.
  let coset (i : ι) : Set H := (fun g ↦ (r i)⁻¹ * g) ⁻¹' L
  have h_disjoint : Pairwise (Function.onFun Disjoint coset) := fun i j h_ne ↦
    Set.disjoint_left.2 fun g hi hj ↦ h_ne ((hr g).unique hi hj)
  have h_cover : ⋃ i, coset i = Set.univ :=
    Set.eq_univ_of_forall fun g ↦ Set.mem_iUnion.2 (hr g).exists
  have h_coset (i : ι) : ∫ g in coset i, Φ g ∂μ = ∫ g in (L : Set H), Φ (r i * g) ∂μ := by
    simpa using (measurePreserving_mul_left μ (r i)⁻¹).setIntegral_preimage_emb
      (measurableEmbedding_mulLeft _) (fun g ↦ Φ (r i * g)) L
  simpa only [h_coset, h_cover, Measure.restrict_univ] using
    hasSum_integral_iUnion (s := coset) (fun i ↦ measurable_const_mul _ hL) h_disjoint hΦ.restrict

namespace SiegelWeil

open Space

variable {E n m : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] [Fintype m]

/-- For `2 * card n < card m`, the vacuum coefficients `vacuumCoeff (card m) 1` are absolutely
summable over the cosets of the points integral at every place. -/
lemma summable_norm_vacuumCoeff_univ (h_rank : 2 * card n < card m) :
    Summable fun q : Gf E n ⧸ localLevel n Set.univ ↦
      ‖vacuumCoeff (card m) 1 (cosetRep q).val‖ := by
  classical
  -- The vacuum datum on `Hom(S, T)` for the definite spaces, paired with the constant `1`.
  let S : Space E n 1 := stdSpace E n
  let T : Space E m 1 := stdSpace E m
  let f : 𝒮 (S.hom T) := (S.hom T).vacElem
  have hf_clean : IsClean f := .inl fun _ _ ↦ rfl
  have h_one : (fun _ : G E (1 : n → ℤˣ) ↦ (1 : ℂ)) ∈ S.rapidFunctions :=
    (S.isAutomorphic_const 1).mem_rapidFunctions fun _ _ ↦ rfl
  obtain ⟨h_int, -⟩ :=
    inner_product_formula h_rank (1 : AutChar E) (1 : AutChar E) hf_clean h_one h_one
  -- The coefficient itself is integrable: the Petersson factor is the volume of `[U(S)]`.
  have h_const : S.petersson (fun _ ↦ (1 : ℂ)) (fun _ ↦ (1 : ℂ)) ≠ 0 := by
    simp [Space.petersson, measureReal_univ_ne_zero]
  have h_coeff : Integrable fun g : G E (1 : n → ℤˣ) ↦ weilMatrixCoeff 1 f f g := by
    refine (integrable_mul_const_iff (isUnit_iff_ne_zero.2 h_const) _).1 ?_
    convert h_int using 3
    rfl
  -- Cut the group into the cosets of `L`, the points whose finite part is integral everywhere.
  let L : Subgroup (G E (1 : n → ℤˣ)) :=
    (localLevel n Set.univ).comap (MonoidHom.snd (GInf E (1 : n → ℤˣ)) (Gf E n))
  let r (q : Gf E n ⧸ localLevel n Set.univ) : G E (1 : n → ℤˣ) := ((cosetRep q).val : G E 1)
  have hL_open : IsOpen (L : Set (G E (1 : n → ℤˣ))) :=
    (isOpen_coe_localLevel (E := E) (n := n) Set.univ).preimage continuous_snd
  have mem_L (q : Gf E n ⧸ localLevel n Set.univ) (g : G E (1 : n → ℤˣ)) :
      (r q)⁻¹ * g ∈ L ↔ q = (g.2 : Gf E n ⧸ localLevel n Set.univ) := by
    have h_snd : (r q)⁻¹ * g ∈ L ↔ ((cosetRep q).val)⁻¹ * g.2 ∈ localLevel n Set.univ := by
      simp [L, r]
    rw [h_snd, ← QuotientGroup.eq, mk_cosetRep]
  have hr (g : G E (1 : n → ℤˣ)) : ∃! q, (r q)⁻¹ * g ∈ L :=
    ⟨g.2, (mem_L _ g).2 rfl, fun q hq ↦ (mem_L q g).1 hq⟩
  have := countable_quotient_localLevel (E := E) (n := n) Set.univ
  have h_sum := hasSum_setIntegral_mul_of_existsUnique hL_open.measurableSet hr h_coeff.norm
  -- On `L` the vacuum coefficient comes out of the modulus.
  have hf_vac : projOn (S.hom T) Set.univ f = f := projOn_vacElem _
  set I : ℝ := ∫ g in (L : Set (G E (1 : n → ℤˣ))), ‖weilMatrixCoeff 1 f f g‖
  have h_terms (q : Gf E n ⧸ localLevel n Set.univ) :
      ∫ g in (L : Set (G E (1 : n → ℤˣ))), ‖weilMatrixCoeff 1 f f (r q * g)‖ =
        ‖vacuumCoeff (card m) 1 (cosetRep q).val‖ * I := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hL_open.measurableSet fun g (hg : g.2 ∈ localLevel n Set.univ) ↦ ?_
    simp only [r, weilMatrixCoeff_mul 1 hf_vac (by simp [Gf.mem_supportedOn]) hg, norm_mul]
  -- `I > 0`: the coefficient is continuous and equal to `1` at the identity.
  have h_cont : Continuous fun g : G E (1 : n → ℤˣ) ↦ weilMatrixCoeff 1 f f g := by
    unfold weilMatrixCoeff
    fun_prop
  have h_pos : 0 < I := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae (.of_forall fun _ ↦ norm_nonneg _)
      h_coeff.norm.integrableOn]
    let U : Set (G E (1 : n → ℤˣ)) := (L : Set _) ∩ {g | weilMatrixCoeff 1 f f g ≠ 0}
    have hU_open : IsOpen U := hL_open.inter (isOpen_ne_fun h_cont continuous_const)
    have h_mem : (1 : G E (1 : n → ℤˣ)) ∈ U :=
      ⟨one_mem L, by simp [weilMatrixCoeff, f, Prod.mk_one_one, dataInner_vacElem_vacElem]⟩
    refine (hU_open.measure_pos _ ⟨1, h_mem⟩).trans_le (measure_mono ?_)
    rintro g ⟨hg_L, hg⟩
    exact ⟨norm_ne_zero_iff.2 hg, hg_L⟩
  exact (summable_mul_right_iff h_pos.ne').1 (h_sum.congr_fun fun q ↦ (h_terms q).symm).summable

/-- For `2 * card n < card m`, consider the numbers `vacuumCoeff (card m) b g = (b(det g) *
finMultiplier g ^ card m)⁻¹`. This is the factor by which `g` changes the vacuum matrix coefficient
when the second space has rank `m`. These numbers are absolutely summable over the representatives
`cosetRep q` of the cosets `q` of `Gf E n` modulo `localLevel n A`, the points integral at `A`. -/
theorem summable_norm_vacuumCoeff (h_rank : 2 * card n < card m) (b : AutChar E)
    (A : Set (FinPlace E)) :
    Summable fun q : Gf E n ⧸ localLevel n A ↦ ‖vacuumCoeff (card m) b (cosetRep q).val‖ := by
  classical
  -- The norms do not see `b`, and the cosets at `A` inject into the cosets at all places.
  let ι (q : Gf E n ⧸ localLevel n A) : Gf E n ⧸ localLevel n Set.univ := ((cosetRep q).val : _)
  have hι : Function.Injective ι := by
    intro q₁ q₂ h
    rw [← mk_cosetRep q₁, ← mk_cosetRep q₂, QuotientGroup.eq]
    exact fun w _ ↦ QuotientGroup.eq.1 h w (Set.mem_univ w)
  refine ((summable_norm_vacuumCoeff_univ (E := E) h_rank).comp_injective hι).congr fun q ↦ ?_
  have h_supp : (cosetRep q).val ∈ Gf.supportedOn n Set.univ := by simp
  simp only [Function.comp_apply, ι, norm_vacuumCoeff]
  rw [finMultiplier_cosetRep_mk h_supp]

end SiegelWeil

end New
