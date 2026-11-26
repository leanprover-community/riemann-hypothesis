module

public import Lib.Weil.Unramified.HeckeGL
public import Lib.LocalGL.Iwahori.ParahoricStructure
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.LineHyperplane.Transfer

/-!
# The first entry on the stabiliser of a line, at a finite place

Part of the algebra behind the family of operators at the auxiliary places. Tau Ceti provides the
stabiliser `TauCeti.lineStabilizer K 0` in `GL_N(K)` of the line of the first basis vector, its
character `TauCeti.lineStabilizerChar K 0 : g ↦ g 0 0`, and the transfer of that character, which is
the determinant over a finite field (`TauCeti.transfer_lineStabilizerChar`). The norms, the
first-order deformations of the norm and the logarithms built from them are also Tau Ceti's
(`TauCeti.RepresentationTheory.NormDeformation.Basic` and `.Logarithm`). This file relates the line
stabiliser over the residue field at a finite place `w` to the block parahoric of `GL_N(E_w)`.

## Main definitions and results

* `New.Patching.reduceGL_mem_lineStabilizer_iff`: the reduction of `g ∈ GL_N(O_w)` stabilises the
  line if and only if `g` lies in the block parahoric with blocks of sizes `1` and `N - 1`.
* `New.Patching.lineStabilizerChar_reduceGL`: on such `g`, the character is the reduction of the
  first entry of `g`.
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

/-- The reduction of `g ∈ GL_N(O_w)` stabilises the line of the first basis vector if and only if
`g` belongs to the corresponding block parahoric, with blocks of sizes `1` and `N - 1`. -/
lemma reduceGL_mem_lineStabilizer_iff {N : ℕ} [NeZero N] {g : localIntGL (Fin N) w} :
    reduceGL g ∈ TauCeti.lineStabilizer (ResField w) (0 : Fin N) ↔
      (g : GL (Fin N) (LocField w)) ∈ blockParahoric (min 1) := by
  -- Both say that the first column of the reduction vanishes below the first entry.
  unfold blockParahoric
  refine Iff.trans ?_ reduceGL_mem_iff_mem_residuePreimage
  change _ ↔ ∀ i j : Fin N, min 1 j.val < min 1 i.val → reduceGL g i j = 0
  rw [TauCeti.mem_lineStabilizer_iff]
  refine ⟨fun hg i j hij ↦ ?_, fun hg i hi ↦ hg i 0 (by grind)⟩
  obtain ⟨rfl, hi⟩ : j = 0 ∧ i ≠ 0 := by grind
  exact hg i hi

/-- If the reduction of `g ∈ GL_N(O_w)` stabilises the line of the first basis vector, then the
scalar by which it acts on that line is the reduction of the first entry of `g`. -/
lemma lineStabilizerChar_reduceGL {N : ℕ} [NeZero N] {g : localIntGL (Fin N) w}
    (hg : reduceGL g ∈ TauCeti.lineStabilizer (ResField w) (0 : Fin N)) :
    TauCeti.lineStabilizerChar (ResField w) 0 ⟨reduceGL g, hg⟩ =
      residueUnit ((g : GL (Fin N) (LocField w)) 0 0) :=
  eq_residueUnit ((TauCeti.coe_lineStabilizerChar_apply _).trans rfl) rfl

/-- The determinant of the reduction of `g ∈ GL_N(O_w)` is the reduction `residueUnit` of the
determinant of `g`, a unit of `O_w`. -/
lemma det_reduceGL {N : ℕ} (g : localIntGL (Fin N) w) :
    GeneralLinearGroup.det (reduceGL g) =
      residueUnit (g : GL (Fin N) (LocField w)).val.det :=
  eq_residueUnit (RingHom.map_det ..).symm (𝒪[LocField w].subtype.map_det _)

/-- If `g ∈ GL_N(O_w)` lies in the pro-`p` Iwahori subgroup (its reduction is upper triangular with
ones on the diagonal), then the reduction has determinant `1` and acts trivially on the line of the
first basis vector. -/
lemma det_lineStabilizerChar_reduceGL_eq_one_of_mem_proIwahori {N : ℕ} [NeZero N]
    {g : localIntGL (Fin N) w} (hg : (g : GL (Fin N) (LocField w)) ∈ proIwahori) :
    GeneralLinearGroup.det (reduceGL g) = 1 ∧
      ∀ h_mem : reduceGL g ∈ TauCeti.lineStabilizer (ResField w) (0 : Fin N),
        TauCeti.lineStabilizerChar (ResField w) 0 ⟨reduceGL g, h_mem⟩ = 1 := by
  have entries : ∀ i j : Fin N, j ≤ i →
      reduceGL g i j = (1 : Matrix (Fin N) (Fin N) (ResField w)) i j :=
    (reduceGL_mem_iff_mem_residuePreimage.2 hg : reduceGL g ∈ unitriangular id (ResField w))
  exact ⟨Units.ext (det_eq_one_of_unitriangular entries),
    fun _ ↦ Units.ext ((TauCeti.coe_lineStabilizerChar_apply _).trans
      ((entries 0 0 le_rfl).trans (one_apply_eq 0)))⟩

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
