module

public import Mathlib.GroupTheory.Transfer
public import Lib.Weil.Unramified.HeckeGL
public import Lib.LocalGL.Iwahori.ParahoricStructure

/-!
# The first entry on the stabiliser of a line

Part of the algebra behind the family of operators at the auxiliary places: the first entry on the
stabiliser of a line in `GL_N`, its transfer, and the logarithm on the residue units. The norms, the
first-order deformations of the norm and the logarithms built from them are Tau Ceti's
(`TauCeti.RepresentationTheory.NormDeformation.Basic` and `.Logarithm`).

## Main definitions and results

* `New.Patching.firstEntry`: the character `g ↦ g 0 0` of the stabiliser of the line of the first
  basis vector.
* `New.Patching.transfer_firstEntry`: over a finite field, the transfer to `GL_N` of the first entry
  on the stabiliser of a line is the determinant.
* `New.Patching.exists_residue_log`: a logarithm modulo `m` on the residue units.

Notions from other files:
* `New.LocField w`, `New.LocInt w`, `New.ResField w`: for a finite place `w` of a number field, the
  completion `E_w`, its ring of integers `O_w` and its residue field, which has `w.q` elements.
* `New.localIntGL n w`: the subgroup `GL_n(O_w)` of `GL_n(E_w)`.
-/

@[expose] public section

section LineStabiliserLog

open Valued Finset IsLocalRing Matrix GeneralLinearGroup SpecialLinearGroup

namespace New.Patching

section FiniteField

variable (F : Type) [Field F] (N : ℕ) [NeZero N]

/-- The stabiliser in `GL_N(F)` of the line of the first basis vector. -/
def residueLineStabilizer : Subgroup (GL (Fin N) F) := parabolic fun i : Fin N ↦ min 1 i.val

variable {F N}

/-- A matrix stabilises the line of the first basis vector if and only if its first column
vanishes below the first entry. -/
lemma mem_residueLineStabilizer {g : GL (Fin N) F} :
    g ∈ residueLineStabilizer F N ↔ ∀ i ≠ 0, g i 0 = 0 := by
  change (∀ i j : Fin N, min 1 j.val < min 1 i.val → g i j = 0) ↔ ∀ i ≠ 0, g i 0 = 0
  refine ⟨fun hg i hi ↦ hg i 0 (by grind), fun hg i j hij ↦ ?_⟩
  obtain ⟨rfl, hi⟩ : j = 0 ∧ i ≠ 0 := by grind
  exact hg i hi

/-- If `p` stabilises the line of the first basis vector, then the first column of `h p` is the
first column of `h` times the first entry of `p`. -/
lemma mul_apply_zero_of_mem_residueLineStabilizer (h : GL (Fin N) F) {p : GL (Fin N) F}
    (hp : p ∈ residueLineStabilizer F N) (i : Fin N) : (h * p) i 0 = h i 0 * p 0 0 :=
  calc (h * p) i 0 = ∑ j : Fin N, h i j * p j 0 := Matrix.mul_apply
    _ = h i 0 * p 0 0 := Fintype.sum_eq_single 0 fun j hj ↦ by
        rw [mem_residueLineStabilizer.1 hp j hj, mul_zero]

/-- The first entry `g ↦ g 0 0`, a character of the stabiliser of the line of the first basis
vector: the scalar by which `g` acts on that line. -/
noncomputable def firstEntry : residueLineStabilizer F N →* Fˣ :=
  MonoidHom.toHomUnits
    { toFun g := (g : GL (Fin N) F) 0 0
      map_one' := by simp
      map_mul' g h := mul_apply_zero_of_mem_residueLineStabilizer (g : GL (Fin N) F) h.property 0 }


/-- Let `d = diagGL t` be the diagonal matrix with entries `t i`. If `h⁻¹ d h` stabilises the line
of the first basis vector, then the first column of `h` is an eigenvector of `d`, so the first entry
of `h⁻¹ d h` is `t i` whenever the `i`-th entry of that column is nonzero. -/
lemma firstEntry_conj_diagGL {t : Fin N → Fˣ} {h d : GL (Fin N) F} (hd : d = diagGL t)
    (h_mem : h⁻¹ * d * h ∈ residueLineStabilizer F N) {i : Fin N} (hi : h i 0 ≠ 0) :
    firstEntry ⟨h⁻¹ * d * h, h_mem⟩ = t i := by
  refine Units.ext (mul_left_cancel₀ hi ?_)
  calc h i 0 * firstEntry ⟨h⁻¹ * d * h, h_mem⟩ = (h * (h⁻¹ * d * h)) i 0 :=
        (mul_apply_zero_of_mem_residueLineStabilizer h h_mem i).symm
    _ = (diagGL t * h) i 0 := by rw [mul_assoc, mul_inv_cancel_left, hd]
    _ = h i 0 * t i := by simp [mul_comm]

variable [Finite F]

/-- Let `F` be a finite field, and let `firstEntry` be the character `g ↦ g 0 0` of the stabiliser
in `GL_N(F)` of the line of the first basis vector. Its transfer to `GL_N(F)` takes the value `x` at
the diagonal matrix `diag (x, 1, …, 1)`. -/
lemma transfer_firstEntry_diagGL (x : Fˣ) :
    (firstEntry (F := F) (N := N)).transfer (diagGL (Pi.mulSingle 0 x)) = x := by
  -- The transfer is a product over the orbits of `g = diag (x, 1, …, 1)` on the lines: an orbit of
  -- length `f` through the line of `v` contributes the factor by which `g ^ f` multiplies `v`. The
  -- line of the first basis vector contributes `x`; every other `v` has a nonzero entry that `g`
  -- fixes.
  let H : Subgroup (GL (Fin N) F) := residueLineStabilizer F N
  set g : GL (Fin N) F := diagGL (Pi.mulSingle 0 x) with hg
  let Ω : Type := Quotient (MulAction.orbitRel (Subgroup.zpowers g) (GL (Fin N) F ⧸ H))
  let : Fintype Ω := Fintype.ofFinite Ω
  have g_pow (f : ℕ) : g ^ f = diagGL (Pi.mulSingle 0 (x ^ f)) := by simp [hg, Pi.mulSingle_pow]
  have g_mem : g ∈ H := mem_residueLineStabilizer.2 fun i hi ↦ by simp [g, hi]
  let η₀ : GL (Fin N) F ⧸ H := ↑(1 : GL (Fin N) F)
  have eq_iff (η : GL (Fin N) F ⧸ H) : η₀ = η ↔ η.out ∈ H := by
    conv_lhs => rw [← η.out_eq', QuotientGroup.eq, inv_one, one_mul]
  have fixed (k : GL (Fin N) F) (hk : k ∈ H) : k • η₀ = η₀ := by
    simpa [η₀, QuotientGroup.eq] using hk
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    Fintype.prod_eq_single (⟦η₀⟧ : Ω)]
  · -- The orbit of `η₀` is the single point `η₀`.
    have out_eq : η₀ = (⟦η₀⟧ : Ω).out := by
      obtain ⟨k, hk⟩ :=
        Quotient.mk_out (s := MulAction.orbitRel (Subgroup.zpowers g) (GL (Fin N) F ⧸ H)) η₀
      change (k : GL (Fin N) F) • η₀ = (⟦η₀⟧ : Ω).out at hk
      rw [← hk, fixed k (Subgroup.zpowers_le.2 g_mem k.property)]
    have out_mem : (⟦η₀⟧ : Ω).out.out ∈ H := (eq_iff _).1 out_eq
    have entry_ne : (⟦η₀⟧ : Ω).out.out 0 0 ≠ 0 := (firstEntry ⟨_, out_mem⟩).ne_zero
    have period : Function.minimalPeriod (g • ·) (⟦η₀⟧ : Ω).out = 1 :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.2 (by rw [← out_eq]; exact fixed g g_mem)
    rw [firstEntry_conj_diagGL (g_pow _) _ entry_ne, period, pow_one, Pi.mulSingle_eq_same]
  · intro q hq
    have not_mem : q.out.out ∉ H := fun h ↦ hq (by rw [(eq_iff q.out).2 h, q.out_eq])
    obtain ⟨i, hi, entry_ne⟩ : ∃ i ≠ 0, q.out.out i 0 ≠ 0 := by
      simpa using mt mem_residueLineStabilizer.2 not_mem
    rw [firstEntry_conj_diagGL (g_pow _) _ entry_ne, Pi.mulSingle_eq_of_ne hi]

/-- A character `τ` of `GL n F` with values in `Fˣ`, for a finite field `F`, is trivial on
transvections: `τ` sends the image of each transvection `t` to `1`. -/
lemma map_toGL_transvection_eq_one {n : Type*} [Fintype n] [DecidableEq n] (τ : GL n F →* Fˣ)
    (t : TransvectionStruct n F) : τ (toGL t.toSpecialLinearGroup) = 1 := by
  -- `c ↦ τ (transvection c)` is a homomorphism from a group of order `q` to one of order `q - 1`.
  let : Fintype F := Fintype.ofFinite F
  let ψ : F →+ Additive Fˣ :=
    .mk' (fun c ↦ .ofMul (τ (toGL (transvection t.hij c)))) (by simp [transvection_add])
  have pow_card : τ (toGL t.toSpecialLinearGroup) ^ Fintype.card F = 1 :=
    congrArg Additive.toMul (show Fintype.card F • ψ t.c = 0 by
      rw [← map_nsmul, card_nsmul_eq_zero, map_zero])
  exact Units.ext (by rw [← FiniteField.pow_card (τ (toGL t.toSpecialLinearGroup) : F),
    ← Units.val_pow_eq_pow_val, pow_card])

/-- Let `F` be a finite field, and let `firstEntry` be the character `g ↦ g 0 0` of the stabiliser
in `GL_N(F)` of the line of the first basis vector. Its transfer to `GL_N(F)` takes the value `x` at
the diagonal matrix with `x` in place `i` and `1` elsewhere. -/
lemma transfer_firstEntry_diagGL_mulSingle (i : Fin N) (x : Fˣ) :
    (firstEntry (F := F) (N := N)).transfer (diagGL (Pi.mulSingle i x)) = x := by
  -- Conjugate by the permutation matrix `s` of the transposition of `0` and `i`.
  set τ : GL (Fin N) F →* Fˣ := (firstEntry (F := F) (N := N)).transfer
  let s : GL (Fin N) F := permGL (.swap 0 i)
  have conj : diagGL (Pi.mulSingle i x) * s = s * diagGL (Pi.mulSingle 0 x) := by
    rw [diagGL_mul_permGL, Pi.mulSingle_comp_equiv, Equiv.symm_swap, Equiv.swap_apply_right]
  have τ_conj : τ (diagGL (Pi.mulSingle i x)) = τ (diagGL (Pi.mulSingle 0 x)) :=
    mul_right_cancel (b := τ s) (by rw [← map_mul, conj, map_mul, mul_comm])
  rw [τ_conj, transfer_firstEntry_diagGL]

/-- Let `F` be a finite field, and let `firstEntry` be the character `g ↦ g 0 0` of the stabiliser
in `GL_N(F)` of the line of the first basis vector, the scalar by which `g` acts on that line. Its
transfer to `GL_N(F)` is the determinant. -/
lemma transfer_firstEntry (g : GL (Fin N) F) :
    (firstEntry (F := F) (N := N)).transfer g = GeneralLinearGroup.det g := by
  -- Both sides are characters of `GL_N(F)`, and they agree on diagonal matrices and transvections.
  set τ := (firstEntry (F := F) (N := N)).transfer
  have τ_diag : τ.comp diagGL = GeneralLinearGroup.det.comp diagGL := MonoidHom.pi_ext fun i x ↦
    (transfer_firstEntry_diagGL_mulSingle i x).trans <| Units.ext (by simp [← Units.coe_prod])
  let ⟨g', h, h'⟩ := diagonal_transvection_induction_of_det_ne_zero
    (fun M ↦ ∃ g' : GL (Fin N) F, (g' : Matrix _ _ F) = M ∧ τ g' = GeneralLinearGroup.det g')
    g g.det_ne_zero
    (fun D hD ↦ ⟨diagGL fun i ↦ .mk0 (D i) (by simp_all [prod_ne_zero_iff]), rfl,
      DFunLike.congr_fun τ_diag _⟩)
    (fun t ↦ ⟨toGL t.toSpecialLinearGroup, rfl, by simp [map_toGL_transvection_eq_one]⟩)
    (fun _ _ _ _ ⟨g₁, h₁, e₁⟩ ⟨g₂, h₂, e₂⟩ ↦ ⟨g₁ * g₂, by simp [h₁, h₂], by simp [e₁, e₂]⟩)
  simpa [Units.val_inj.mp h] using h'

/-- Let `F` be a finite field, `l` a homomorphism from `Fˣ` to a commutative group, and `firstEntry`
the character `g ↦ g 0 0` of the stabiliser in `GL_N(F)` of the line of the first basis vector. The
transfer of `l ∘ firstEntry` to `GL_N(F)` is `l ∘ det`. -/
lemma transfer_comp_firstEntry {A : Type*} [CommGroup A] (l : Fˣ →* A) :
    (l.comp (firstEntry (N := N))).transfer = l.comp GeneralLinearGroup.det := by
  -- The transfer is a product over the cosets, and `l` commutes with products.
  ext g
  rw [MonoidHom.comp_apply, ← transfer_firstEntry, MonoidHom.transfer_def _ default,
    MonoidHom.transfer_def _ default]
  simp [Subgroup.leftTransversals.diff, map_prod]

end FiniteField

section Residue

variable {E : Type} [Field E] [NumberField E] {w : FinPlace E}

open scoped Classical in
/-- The reduction of a unit of `O_w` as a unit of the residue field, and `1` for the other elements
of `E_w`. -/
noncomputable def residueUnit (x : LocField w) : (ResField w)ˣ :=
  if h : IsUnit (residueOrZero x) then h.unit else 1

/-- A unit `x` of the residue field `ResField w` that is the reduction of a local integer
`y : LocInt w` equals `residueUnit z`, where `z : LocField w` is `y` seen in `E_w`. -/
lemma eq_residueUnit {x : (ResField w)ˣ} {y : LocInt w} {z : LocField w}
    (hx : x = residue (LocInt w) y) (hy : (y : LocField w) = z) : x = residueUnit z := by
  have x_eq : (x : ResField w) = residueOrZero z := by rw [hx, ← hy, residueOrZero_coe]
  rw [residueUnit, dite_eq_left (by simp [← x_eq])]
  exact Units.ext x_eq

/-- The reduction of `g ∈ GL_N(O_w)` lies in a subgroup `H` if and only if `g` lies in the open
subgroup `residuePreimage P H hP`, for any property `P` that describes the preimage of `H`. -/
lemma reduceGL_mem_iff_mem_residuePreimage {N : ℕ} {P : GL (Fin N) (LocField w) → Prop}
    {H : Subgroup (GL (Fin N) (ResField w))}
    {hP : ∀ k : localIntGL (Fin N) w, reduceGL k ∈ H ↔ P k} {g : localIntGL (Fin N) w} :
    reduceGL g ∈ H ↔ (g : GL (Fin N) (LocField w)) ∈ residuePreimage P H hP :=
  (hP g).trans (and_iff_right g.property).symm

/-- The reduction of `g ∈ GL_N(O_w)` belongs to the residue line stabiliser if and only if
`g` belongs to the corresponding block parahoric. For positive `N`, the blocks have sizes
`1` and `N - 1`. -/
lemma reduceGL_mem_residueLineStabilizer_iff {N : ℕ} {g : localIntGL (Fin N) w} :
    reduceGL g ∈ residueLineStabilizer (ResField w) N ↔
      (g : GL (Fin N) (LocField w)) ∈ blockParahoric (min 1) := by
  unfold residueLineStabilizer blockParahoric
  exact reduceGL_mem_iff_mem_residuePreimage

/-- If the reduction of `g ∈ GL_N(O_w)` stabilises the line of the first basis vector, then its
first entry is the reduction of the first entry of `g`. -/
lemma firstEntry_reduceGL {N : ℕ} [NeZero N] {g : localIntGL (Fin N) w}
    (hg : reduceGL g ∈ residueLineStabilizer (ResField w) N) :
    firstEntry ⟨reduceGL g, hg⟩ = residueUnit ((g : GL (Fin N) (LocField w)) 0 0) :=
  eq_residueUnit rfl rfl

/-- The determinant of the reduction of `g ∈ GL_N(O_w)` is the reduction `residueUnit` of the
determinant of `g`, a unit of `O_w`. -/
lemma det_reduceGL {N : ℕ} (g : localIntGL (Fin N) w) :
    GeneralLinearGroup.det (reduceGL g) =
      residueUnit (g : GL (Fin N) (LocField w)).val.det :=
  eq_residueUnit (RingHom.map_det ..).symm (𝒪[LocField w].subtype.map_det _)

/-- If `g ∈ GL_N(O_w)` lies in the pro-`p` Iwahori subgroup (its reduction is upper triangular with
ones on the diagonal), then the reduction has determinant `1` and first entry `1`. -/
lemma det_firstEntry_reduceGL_eq_one_of_mem_proIwahori {N : ℕ} [NeZero N] {g : localIntGL (Fin N) w}
    (hg : (g : GL (Fin N) (LocField w)) ∈ proIwahori) :
    GeneralLinearGroup.det (reduceGL g) = 1 ∧
      ∀ h_mem : reduceGL g ∈ residueLineStabilizer (ResField w) N,
        firstEntry ⟨reduceGL g, h_mem⟩ = 1 := by
  have entries : ∀ i j : Fin N, j ≤ i →
      reduceGL g i j = (1 : Matrix (Fin N) (Fin N) (ResField w)) i j :=
    (reduceGL_mem_iff_mem_residuePreimage.2 hg : reduceGL g ∈ unitriangular id (ResField w))
  exact ⟨Units.ext (det_eq_one_of_unitriangular entries),
    fun _ ↦ Units.ext ((entries 0 0 le_rfl).trans (one_apply_eq 0))⟩

/-- Let `q = w.q` be the order of the residue field at `w`, let `m ∣ q - 1`, and let `z` generate
the residue units. There is a logarithm modulo `m` to the base `z`: a homomorphism from the residue
units to `ℤ/m` that sends `z` to `1`. -/
lemma exists_residue_log {m : ℕ} (hm : m ∣ w.q - 1) {z : (ResField w)ˣ}
    (hz : ∀ x : (ResField w)ˣ, x ∈ Subgroup.zpowers z) :
    ∃ ind : (ResField w)ˣ →* Multiplicative (ZMod m), ind z = .ofAdd 1 := by
  have order_z : orderOf z = w.q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hz, Nat.card_units, card_ResField]
  have order_dvd : orderOf (Multiplicative.ofAdd (1 : ZMod m)) ∣ orderOf z := by
    rwa [order_z, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  exact ⟨monoidHomOfForallMemZpowers hz order_dvd,
    monoidHomOfForallMemZpowers_apply_gen hz order_dvd⟩

end Residue

end New.Patching

end LineStabiliserLog
