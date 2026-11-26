module

public import Lib.SiegelWeil.RallisInner.Doubling

/-!
# The dual datum of a vacuum

For hermitian spaces `S`, `T` of ranks `n`, `m` with `2 n ≤ m`, a finite set `A` of places and a
datum `f` on `Hom(S, T)` that is a vacuum above `A` (fixed by `New.Space.projOn A`), this file
constructs a second datum `f'` whose matrix coefficient `g ↦ ⟨f', ω(g, 1) f⟩` is that of `f` on the
points integral at `A` and zero elsewhere (`New.SiegelWeil.exists_dualDatum`).

The datum is `ϱ(e) ω(κ) f` up to a scalar: `κ = 1 + z x xᴴ` (`New.SiegelWeil.isotropicShear`) is a
unitary of `T` along an integral isotropic frame `x`
(`New.SiegelWeil.exists_integral_isotropic_frame`), with `z̄ = -z` large at `A` and its conjugate
(`New.SiegelWeil.exists_skew_adele`), and `ϱ(e)` is the finite Heisenberg operator of the rows of
`x` that form the identity. Where the coefficient at `g` is not zero, the Heisenberg operators
fixing both `ω(κ) f` and `ω(g) f` act on `f'` by characters that must be trivial, and self-duality
of `Ô` (`New.stdLattice.forall_selfDualAddChar_mul_eq_one_iff`) then forces `g⁻¹` to be integral at
`A` and its conjugate.

## Main results

* `New.SiegelWeil.exists_dualDatum`: the dual datum.
-/

@[expose] public section

noncomputable section

open Matrix Kronecker

namespace New.SiegelWeil

open WeilData Fintype Space Prod G Gf stdLattice Valued

variable {E n m : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m] {s : n → ℤˣ} {t : m → ℤˣ} {S : Space E n s} {T : Space E m t}

omit [CMType E] in
/-- For a place `w` and `μ ≠ 0` in `E_w`, a finite adele `y` times the adele with component `μ⁻¹`
at `w` and `0` elsewhere is integral if and only if `v (y w) ≤ v μ`. -/
lemma mul_singleAdele_inv_mem_Ô [NumberField E] {w : FinPlace E} {μ : LocField w} (hμ : μ ≠ 0)
    (y : 𝔸f E) : y * singleAdele w μ⁻¹ ∈ Ô E ↔ v (y w) ≤ v μ := by
  rw [mem_Ô]
  refine ⟨fun h ↦ ?_, fun h u ↦ ?_⟩
  · have h_w := h w
    rwa [show (y * singleAdele w μ⁻¹) w = y w * μ⁻¹ from by simp, map_mul, map_inv₀,
      mul_inv_le_iff₀ (pos_iff_ne_zero.2 ((Valuation.ne_zero_iff _).2 hμ)), one_mul] at h_w
  · by_cases hu : u = w
    · subst hu
      rw [show (y * singleAdele u μ⁻¹) u = y u * μ⁻¹ from by simp, map_mul, map_inv₀,
        mul_inv_le_iff₀ (pos_iff_ne_zero.2 ((Valuation.ne_zero_iff _).2 hμ)), one_mul]
      exact h
    · simp [hu]

/-- Let `A` be a finite set of places. There is a finite adele `z` with `z̄ = -z`, zero outside `A`
and its conjugate, and with `v (z w) > 1` at every place `w` of `A` and its conjugate: `j / N`
there for a suitable natural number `N`, with `j` the imaginary element of the Weil data. -/
lemma exists_skew_adele {A : Set (FinPlace E)} (hA : A.Finite) :
    ∃ z : 𝔸f E, star z = -z ∧ idem A.conjClosure * z = z ∧
      ∀ w ∈ A.conjClosure, 1 < v (z w) := by
  classical
  have : Finite A.conjClosure := hA.conjClosure.to_subtype
  -- `N` carries the adeles `ϖ_w⁻¹ j⁻¹`, for `w` in `A` and its conjugate, into `Ô E`; then
  -- `v (N) ≤ v (ϖ_w j) < v (j)` at `w`, so `j / N` is large there.
  obtain ⟨N, hN, h_int⟩ := exists_forall_mul_mem_Ô fun w : A.conjClosure ↦
    singleAdele w.1 (uniformizer w.1).val⁻¹ * algebraMap E (𝔸f E) j⁻¹
  refine ⟨idem A.conjClosure * algebraMap E (𝔸f E) (j / N), ?_, ?_, fun w hw ↦ ?_⟩
  · rw [star_mul', star_idem_conjClosure, star_algebraMap_finAdele, star_div₀, WeilData.star_j,
      star_natCast, neg_div, map_neg, mul_neg]
  · rw [← mul_assoc, idem_mul_self]
  · -- Read everything in `E_w`, through `φ : E → E_w`.
    let φ : E →+* LocField w := algebraMap E (LocField w)
    have h_coe (y : E) : (algebraMap E (𝔸f E) y) w = φ y := rfl
    have h_w := mem_Ô.1 (h_int ⟨w, hw⟩) w
    rw [finAdele_mul_apply, finAdele_mul_apply, finAdele_natCast_apply, singleAdele_same, h_coe,
      map_inv₀, map_mul, map_mul, map_inv₀, map_inv₀, ← mul_inv] at h_w
    rw [finAdele_mul_apply, idem_of_mem hw, one_mul, h_coe, map_div₀, map_natCast]
    have hJ : v (φ j) ≠ 0 := (Valuation.ne_zero_iff _).2 ((map_ne_zero φ).2 j_ne_zero)
    have hN' : v (N : LocField w) ≠ 0 := (Valuation.ne_zero_iff _).2 (by
      rw [← map_natCast φ]; exact (map_ne_zero φ).2 (Nat.cast_ne_zero.2 hN))
    rw [mul_inv_le_iff₀ (pos_iff_ne_zero.2 (mul_ne_zero (by simp) hJ)), one_mul,
      v_uniformizer] at h_w
    rw [map_div₀, lt_div_iff₀ (pos_iff_ne_zero.2 hN'), one_mul]
    exact h_w.trans_lt (mul_lt_of_lt_one_left (pos_iff_ne_zero.2 hJ) (by decide))

omit [WeilData E] [DecidableEq n] in
/-- If `z̄ = -z` and `xᴴ x = 0`, the matrix `1 + z x xᴴ` is unitary: `x xᴴ` is hermitian with
square `x (xᴴ x) xᴴ = 0`. -/
lemma conjTranspose_mul_isotropicShear {z : 𝔸f E} (hz : star z = -z) {x : Matrix m n (𝔸f E)}
    (hx : xᴴ * x = 0) : (1 + z • (x * xᴴ))ᴴ * 1 * (1 + z • (x * xᴴ)) = 1 := by
  have h_sq : x * xᴴ * (x * xᴴ) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc xᴴ, hx, Matrix.zero_mul, Matrix.mul_zero]
  have h_adj : (1 + z • (x * xᴴ))ᴴ = 1 - z • (x * xᴴ) := by
    rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul, conjTranspose_mul,
      conjTranspose_conjTranspose, hz, neg_smul, sub_eq_add_neg]
  have h_sq' : z • (x * xᴴ) * (z • (x * xᴴ)) = 0 := by rw [smul_mul_smul_comm, h_sq, smul_zero]
  rw [h_adj, Matrix.mul_one]
  calc (1 - z • (x * xᴴ)) * (1 + z • (x * xᴴ)) = 1 - z • (x * xᴴ) * (z • (x * xᴴ)) := by
        rw [sub_mul, one_mul, mul_add, mul_one]
        abel
    _ = 1 := by rw [h_sq', sub_zero]

/-- The shear `1 + z x xᴴ` as an element of the finite unitary group, for `z̄ = -z` and an
isotropic frame `x` (`xᴴ x = 0`). -/
def isotropicShear {z : 𝔸f E} (hz : star z = -z) {x : Matrix m n (𝔸f E)} (hx : xᴴ * x = 0) :
    Gf E m :=
  U.of isUnit_one (1 + z • (x * xᴴ)) (conjTranspose_mul_isotropicShear hz hx)

omit [WeilData E] [DecidableEq n] in
/-- The matrix of `isotropicShear hz hx` is `1 + z x xᴴ`. -/
lemma coe_isotropicShear {z : 𝔸f E} (hz : star z = -z) {x : Matrix m n (𝔸f E)} (hx : xᴴ * x = 0) :
    ((isotropicShear hz hx : Gf E m) : Matrix m m (𝔸f E)) = 1 + z • (x * xᴴ) := rfl

omit [WeilData E] [DecidableEq n] in
/-- If `z` is zero outside `A` and its conjugate, the shear `1 + z x xᴴ` is supported there. -/
lemma isotropicShear_mem_supportedOn {A : Set (FinPlace E)} {z : 𝔸f E} (hz : star z = -z)
    (hz_supp : idem A.conjClosure * z = z) {x : Matrix m n (𝔸f E)} (hx : xᴴ * x = 0) :
    isotropicShear hz hx ∈ supportedOn m A := by
  classical
  rw [Gf.mem_supportedOn]
  intro w hw hw_star
  have hzw : z w = 0 := by
    rw [← hz_supp, finAdele_mul_apply, idem_apply,
      ite_eq_right (by simp [Set.conjClosure, hw, hw_star]), zero_mul]
  refine Units.ext (Matrix.ext fun i k ↦ ?_)
  simp [Gf.atPlace, coe_isotropicShear, hzw, Matrix.one_apply, apply_ite (fun y : 𝔸f E ↦ y w)]

omit [CMType E] [WeilData E] in
/-- For matrices over a commutative ring, the entry `(p, k)` of `M * E_{r i}(a) * N`, with
`E_{r i}(a)` the matrix with the single entry `a` at `(r, i)`, is `M p r * a * N i k`. -/
lemma mul_single_mul_apply {R : Type*} [CommRing R] (M : Matrix m m R) (r : m) (i : n) (a : R)
    (N : Matrix n n R) (p : m) (k : n) : (M * single r i a * N) p k = M p r * a * N i k := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [mul_single_apply_same]
  · intro c _ hc
    rw [mul_single_apply_of_ne (hbj := hc), zero_mul]
  · simp

omit [DecidableEq n] [CMType E] [WeilData E] in
/-- Let `u` embed `n` into `m`, and let `F` be the matrix with entry `1` at the places `(u k, k)`
and `0` elsewhere. The pairing of `F` with a matrix `M`, read as vectors, is `∑ k, M (u k) k`. -/
lemma star_frame_dotProduct {R : Type*} [CommRing R] [StarRing R] (u : n ↪ m)
    (M : Matrix m n R) :
    star (matrixToVec (of fun r k ↦ if r = u k then (1 : R) else 0)) ⬝ᵥ matrixToVec M =
      ∑ k, M (u k) k := by
  rw [dotProduct, Fintype.sum_prod_type, Finset.sum_comm]
  simp [matrixToVec, apply_ite star]

omit [WeilData E] in
/-- The points of `G_f` whose inverse has integral entries at every place of `A` and its conjugate
are integral at `A`: by unitarity `g` is the conjugate transpose of `g⁻¹`, and conjugation
exchanges a place with its conjugate. -/
lemma mem_localLevel_of_inv {A : Set (FinPlace E)} {g : Gf E n}
    (h : ∀ w ∈ A.conjClosure, ∀ i k : n, v (((g⁻¹ : Gf E n) : Matrix n n (𝔸f E)) i k w) ≤ 1) :
    g ∈ localLevel n A := by
  intro w hw
  have h_val : (g : Matrix n n (𝔸f E)) = ((g⁻¹ : Gf E n) : Matrix n n (𝔸f E))ᴴ := by
    simpa using U.inv_val_eq_conjTranspose g⁻¹
  refine mem_intGL.2 ⟨fun i k ↦ mem_LocInt.2 ?_, fun i k ↦ mem_LocInt.2 ?_⟩
  · change v ((g : Matrix n n (𝔸f E)) i k w) ≤ 1
    rw [h_val, conjTranspose_apply, finAdele_star_apply, v_conjLoc]
    exact h (star w) (Or.inr (by simpa using hw)) k i
  · rw [← map_inv]
    exact h w (Or.inl hw) i k

omit [WeilData E] in
/-- In `Hom(S, T)`, read as `m × n` matrices, the finite part of `onHom (g, h)` acts by
`X ↦ h X g⁻¹`. -/
lemma onHom_snd_mulVec_matrixToVec (p : G E s × G E t) (X : Matrix m n (𝔸f E)) :
    ((onHom p).2 : Matrix (m × n) (m × n) (𝔸f E)) *ᵥ matrixToVec X =
      matrixToVec ((p.2.2 : Matrix m m (𝔸f E)) * X * ((p.1.2⁻¹ : Gf E n) : Matrix n n (𝔸f E))) := by
  rw [onHom_snd, kronecker_mulVec_eq_matrixToVec, vecToMatrix_matrixToVec]

/-- Let `f` be a vacuum above `A` (fixed by `projOn A`) and `p` a point of the unitary group. Then
`ω(p) f` is fixed by the finite Heisenberg operator of `idem (A ∪ Ā) • p y` for every integral
vector `y`. -/
lemma finHeisenbergOp_omega_of_projOn {k : Type} [Fintype k] [DecidableEq k] {r : k → ℤˣ}
    {V : Space E k r} {A : Set (FinPlace E)} {f : 𝒮 V} (hf : V.projOn A f = f) (p : G E r)
    {y : k → 𝔸f E} (hy : y ∈ stdLattice E k) :
    V.finHeisenbergOp (idem A.conjClosure • ((p.2 : Matrix k k (𝔸f E)) *ᵥ y)) (V.ω p f) =
      V.ω p f := by
  have h_fix : V.finHeisenbergOp (idem A.conjClosure • y) f = f := by
    simpa [hf] using V.finHeisenbergOp_projOn (S := A) hy f
  conv_rhs => rw [← h_fix]
  rw [omega_finHeisenbergOp, Matrix.mulVec_smul]

/-- If finite Heisenberg operators `ϱ(e)` and `ϱ(Y)` are given, and `ϱ(Y)` fixes `f₀` and `u`, then
`ϱ(Y)` multiplies `ϱ(e) f₀` by `ψ(ē ⬝ Y)`; so if `⟨ϱ(e) f₀, u⟩ ≠ 0`, then `ψ(ē ⬝ Y) = 1`. Here
`ψ = selfDualAddChar E`. -/
lemma selfDualAddChar_eq_one_of_dataInner_ne_zero {k : Type} [Fintype k] [DecidableEq k]
    {r : k → ℤˣ} {V : Space E k r} {e Y : k → 𝔸f E} {f₀ u : 𝒮 V}
    (h₀ : V.finHeisenbergOp Y f₀ = f₀) (hu : V.finHeisenbergOp Y u = u)
    (h_ne : V.dataInner (V.finHeisenbergOp e f₀) u ≠ 0) :
    selfDualAddChar E (star e ⬝ᵥ Y) = 1 := by
  have h := V.dataInner_finHeisenbergOp Y (V.finHeisenbergOp e f₀) u
  rw [finHeisenbergOp_comm, h₀, hu, map_smulₛₗ, _root_.smul_apply, smul_eq_mul] at h
  have h_conj : (starRingEnd ℂ) (selfDualAddChar E (star e ⬝ᵥ Y) : ℂ) = 1 :=
    (mul_eq_right₀ h_ne).1 h
  simpa using congrArg (starRingEnd ℂ) h_conj

open scoped Classical in
/-- The dual datum. Let `2 rk S ≤ rk T`, let `A` be a finite set of places and let `f` be a vacuum
above `A` (fixed by `projOn A`). There is a datum `f'` whose matrix coefficient
`g ↦ ⟨f', ω(g, 1) f⟩` against `f` equals that of `f` at the points `g` integral at `A` and is zero
at the others.

The datum is `f' = ϱ(e) ω(κ) f`, up to a scalar: `κ = 1 + z x xᴴ` is a shear of `T` along an
integral isotropic frame `x`, with `z` large at `A` and its conjugate (`exists_skew_adele`), and
`ϱ(e)` is the finite Heisenberg operator of the rows of `x` that form the identity. If the
coefficient at `g` is not zero, the Heisenberg operators that fix both `ω(κ) f` and `ω(g) f` act on
`f'` by characters that must be trivial, and this forces `g⁻¹` to be integral at `A`. -/
theorem exists_dualDatum (b : AutChar E) (h_rank : 2 * card n ≤ card m) {f : 𝒮 (S.hom T)}
    {A : Set (FinPlace E)} (hf : projOn (S.hom T) A f = f) (hA : A.Finite) :
    ∃ f' : 𝒮 (S.hom T), ∀ g : G E s,
      weilMatrixCoeff b f f' g = if g.2 ∈ localLevel n A then weilMatrixCoeff b f f g else 0 := by
  obtain ⟨x, hx_int, hx_iso, u, hu⟩ := exists_integral_isotropic_frame (E := E) h_rank
  obtain ⟨z, hz_star, hz_supp, hz_big⟩ := exists_skew_adele hA
  let κ : Gf E m := isotropicShear hz_star hx_iso
  -- `K` acts on `Hom(S, T)` by `X ↦ κ X`; it is supported on `A` and its conjugate.
  let K : Gf E (m × n) := (onHom ((1 : G E s), ((1, κ) : G E t))).2
  have hK_supp : K ∈ supportedOn (m × n) A :=
    onHom_mem_supportedOn (one_mem _) (isotropicShear_mem_supportedOn hz_star hz_supp hx_iso)
  have hK_act (X : Matrix m n (𝔸f E)) :
      (K : Matrix (m × n) (m × n) (𝔸f E)) *ᵥ matrixToVec X =
        matrixToVec ((κ : Matrix m m (𝔸f E)) * X) := by
    simp [K, onHom_snd_mulVec_matrixToVec]
  let f₀ : 𝒮 (S.hom T) := finMultiplier K⁻¹ • (S.hom T).ω (K : G E (homSigns s t)) f
  have h_proj₀ : (S.hom T).projOn A f₀ = f := by
    rw [map_smul, projOn_omega (S.hom T) hK_supp hf, smul_smul,
      mul_inv_cancel₀ (finMultiplier_ne_zero _), one_smul]
  -- the frame vector: the matrix with `1` at the places `(u k, k)`, cut to `A` and its conjugate
  let F : Matrix m n (𝔸f E) := of fun r k ↦ if r = u k then 1 else 0
  have hF_int : matrixToVec F ∈ stdLattice E (m × n) := by
    rw [mem_stdLattice]
    rintro ⟨r, k⟩
    simp [F, matrixToVec, ite_mem]
  let e : m × n → 𝔸f E := idem A.conjClosure • matrixToVec F
  refine ⟨(S.hom T).finHeisenbergOp e f₀, fun g ↦ ?_⟩
  set w₀ : 𝒮 (S.hom T) := pairWeil S T 1 b (g, 1) f with hw₀
  split_ifs with hg
  · -- At `g` integral at `A`, `ω(g) f` is a vacuum above `A`, fixed by `ϱ(e)` and `projOn A`.
    have h_vac : (S.hom T).projOn A w₀ = w₀ :=
      projOn_pairWeil hf (g, 1) fun w hw ↦ onHom_atPlace_mem (hg w hw) (by simp)
    have h_e : (S.hom T).finHeisenbergOp e w₀ = w₀ := by
      conv_lhs => rw [← h_vac]
      rw [(S.hom T).finHeisenbergOp_projOn hF_int, h_vac]
    calc weilMatrixCoeff b f ((S.hom T).finHeisenbergOp e f₀) g
        = (S.hom T).dataInner ((S.hom T).finHeisenbergOp e f₀)
            ((S.hom T).finHeisenbergOp e w₀) := by rw [h_e]
      _ = (S.hom T).dataInner f₀ ((S.hom T).projOn A w₀) := by rw [dataInner_finHeisenbergOp, h_vac]
      _ = weilMatrixCoeff b f f g := by rw [← dataInner_projOn, h_proj₀]
  · -- Otherwise suppose the coefficient is not zero; then `g⁻¹` is integral at `A ∪ Ā`.
    by_contra h_ne
    apply hg
    have h_ne' : (S.hom T).dataInner ((S.hom T).finHeisenbergOp e f₀)
        ((S.hom T).ω (onHom (g, (1 : G E t))) f) ≠ 0 := by
      intro h_zero
      apply h_ne
      change (S.hom T).dataInner _ (pairWeil S T 1 b (g, 1) f) = 0
      rw [pairWeil_apply, map_smul, h_zero, smul_zero]
    have hP_act (X : Matrix m n (𝔸f E)) :
        ((onHom (g, (1 : G E t))).2 : Matrix (m × n) (m × n) (𝔸f E)) *ᵥ matrixToVec X =
          matrixToVec (X * ((g.2⁻¹ : Gf E n) : Matrix n n (𝔸f E))) := by
      simp [onHom_snd_mulVec_matrixToVec]
    refine mem_localLevel_of_inv fun w hw i k ↦ ?_
    set h : Matrix n n (𝔸f E) := ((g.2⁻¹ : Gf E n) : Matrix n n (𝔸f E))
    by_contra h_big
    rw [not_le] at h_big
    have : Nonempty n := ⟨i⟩
    -- a largest entry `h i l` of the row `i` at `w`, and `μ` with `v μ = max (v (z w)) (v (h i l))`
    obtain ⟨l, hl⟩ := Finite.exists_max fun l ↦ v (h i l w)
    have h_il : 1 < v (h i l w) := h_big.trans_le (hl k)
    have hz_w : 1 < v (z w) := hz_big w hw
    let μ : LocField w := if v (z w) ≤ v (h i l w) then h i l w else z w
    have hμ : v μ = max (v (z w)) (v (h i l w)) := by
      by_cases h_le : v (z w) ≤ v (h i l w)
      · simp [μ, h_le]
      · simp [μ, h_le, max_eq_left (le_of_not_ge h_le)]
    have hμ_one : 1 < v μ := hμ ▸ hz_w.trans_le (le_max_left _ _)
    have hμ_ne : μ ≠ 0 := (Valuation.ne_zero_iff _).1 (ne_of_gt (zero_lt_one.trans hμ_one))
    set σ : 𝔸f E := singleAdele w μ⁻¹
    have hσ (y : 𝔸f E) : y * σ ∈ Ô E ↔ v (y w) ≤ v μ := mul_singleAdele_inv_mem_Ô hμ_ne y
    have hσ_idem : idem A.conjClosure * σ = σ := by
      ext u'
      by_cases hu' : u' = w
      · subst hu'; simp [σ, hw]
      · simp [σ, hu']
    -- the integrality of the vectors used below
    have hσ_int : σ ∈ Ô E := by simpa using (hσ 1).2 (by simpa using hμ_one.le)
    have hzσ_int : z * σ ∈ Ô E := (hσ z).2 (hμ ▸ le_max_left _ _)
    have hhσ_int (k' : n) : h i k' * σ ∈ Ô E := (hσ _).2 (hμ ▸ (hl k').trans (le_max_right _ _))
    -- `κ` applied to the single entry `d σ` at `(u l, i)`
    have hκ_entry (r : m) :
        (κ : Matrix m m (𝔸f E)) r (u l) = (if r = u l then 1 else 0) + z * x r l := by
      simp [κ, coe_isotropicShear, Matrix.one_apply, Matrix.mul_apply, conjTranspose_apply, hu,
        Pi.single_apply, apply_ite star]
    -- For every integral `d`, the character of `ē ⬝ Y` is trivial, `Y = κ E_{u l, i}(d σ) h`.
    have h_char (d : 𝔸f E) (hd : d ∈ Ô E) :
        selfDualAddChar E (idem A.conjClosure * ((1 + z) * (d * σ) * h i l)) = 1 := by
      let D : Matrix m n (𝔸f E) := single (u l) i (d * σ)
      let Y : m × n → 𝔸f E := idem A.conjClosure •
        matrixToVec ((κ : Matrix m m (𝔸f E)) * D * h)
      have hY₀ : (S.hom T).finHeisenbergOp Y f₀ = f₀ := by
        have h_lat : matrixToVec (D * h) ∈ stdLattice E (m × n) := by
          rw [mem_stdLattice]
          rintro ⟨r, k'⟩
          by_cases hr : r = u l
          · subst hr
            simpa [D, matrixToVec, Matrix.single_mul_apply_same, mul_assoc, mul_comm σ] using
              mul_mem hd (hhσ_int k')
          · simp [D, matrixToVec, Matrix.single_mul_apply_of_ne (h := hr)]
        have := finHeisenbergOp_omega_of_projOn hf ((1, K) : G E (homSigns s t)) h_lat
        rw [map_smul]
        simp only [hK_act] at this
        simp only [Y, Matrix.mul_assoc, this]
        rfl
      have hYu : (S.hom T).finHeisenbergOp Y ((S.hom T).ω (onHom (g, (1 : G E t))) f) =
          (S.hom T).ω (onHom (g, (1 : G E t))) f := by
        have h_lat : matrixToVec ((κ : Matrix m m (𝔸f E)) * D) ∈ stdLattice E (m × n) := by
          rw [mem_stdLattice]
          rintro ⟨r, k'⟩
          by_cases hk' : k' = i
          · subst hk'
            simp only [D, matrixToVec, mul_single_apply_same, hκ_entry, add_mul]
            refine add_mem (mul_mem (by simp [ite_mem]) (mul_mem hd hσ_int)) ?_
            rw [show z * x r l * (d * σ) = x r l * d * (z * σ) by ring]
            exact mul_mem (mul_mem (hx_int r l) hd) hzσ_int
          · simp [D, matrixToVec, mul_single_apply_of_ne (hbj := hk')]
        simpa [hP_act] using finHeisenbergOp_omega_of_projOn hf (onHom (g, (1 : G E t))) h_lat
      have h_one := selfDualAddChar_eq_one_of_dataInner_ne_zero hY₀ hYu h_ne'
      have h_dot : star e ⬝ᵥ Y = idem A.conjClosure * ((1 + z) * (d * σ) * h i l) := by
        change star (idem A.conjClosure •
            matrixToVec (of fun r k ↦ if r = u k then (1 : 𝔸f E) else 0)) ⬝ᵥ
          (idem A.conjClosure •
            matrixToVec ((κ : Matrix m m (𝔸f E)) * single (u l) i (d * σ) * h)) = _
        rw [star_smul, smul_dotProduct, dotProduct_smul, star_frame_dotProduct,
          star_idem_conjClosure, smul_eq_mul, smul_eq_mul, ← mul_assoc, idem_mul_self]
        congr 1
        simp only [mul_single_mul_apply, hκ_entry, hu, Pi.single_apply, u.injective.eq_iff,
          add_mul, Finset.sum_add_distrib]
        simp
      rwa [h_dot] at h_one
    -- so `z σ h i l` is integral, against the choice of `μ`
    have h_mem : z * h i l * σ ∈ Ô E := by
      refine (forall_selfDualAddChar_mul_eq_one_iff _).1 fun d hd ↦ ?_
      have h_split := h_char d hd
      rw [show idem A.conjClosure * ((1 + z) * (d * σ) * h i l) =
          d * (h i l * σ) + z * h i l * σ * d by
        rw [show idem A.conjClosure * ((1 + z) * (d * σ) * h i l) =
          (1 + z) * d * h i l * (idem A.conjClosure * σ) by ring, hσ_idem]
        ring,
        AddChar.map_add_eq_mul, selfDualAddChar_eq_one_of_mem (mul_mem hd (hhσ_int l)), one_mul]
        at h_split
      exact h_split
    have h_le := (hσ _).1 h_mem
    rw [finAdele_mul_apply, map_mul, hμ] at h_le
    exact (max_lt (lt_mul_of_one_lt_right (zero_lt_one.trans hz_w) h_il)
      (lt_mul_of_one_lt_left (zero_lt_one.trans h_il) hz_w)).not_ge h_le

end New.SiegelWeil
