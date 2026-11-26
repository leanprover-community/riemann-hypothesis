module

public import Lib.Adelic.Adeles.AdditiveCharacter

/-!
# Principal ideles and a majorant on the complex torus

* `New.principalAdeleUnits`: the principal ideles, a discrete subgroup of the units of the adele
  ring.
* `New.integrable_prod_inv_one_add_log_sq`: `∏ x, (1 + (log |a x|) ^ 2)⁻¹` is integrable for Haar
  measure on `(ι → ℂ)ˣ`; it serves as a majorant at the infinite places.

Notions from other files:

* `New.CMType E`: E is a CM number field with, for each infinite place, a chosen complex embedding
  inducing it.
* `New.toAdele`: the diagonal embedding of E in its adeles, given at the infinite places by the
  chosen embeddings.
* `New.ratAdeles E`: the image of E under `New.toAdele`, a lattice in the adeles.
-/

@[expose] public section

namespace New

open MeasureTheory Measure Complex

variable (E : Type*) {ι : Type*} [Field E] [CMType E]

/-- The principal ideles: the image of E^× in the unit group of the adeles. -/
noncomputable def principalAdeleUnits : Subgroup (𝔸 E)ˣ :=
  (Units.map (toAdele (E := E)).toMonoidHom).range

/-- For a CM field E, the principal ideles, that is the image of E^× in the units of the adele ring,
form a discrete subgroup: they map into the discrete set `New.ratAdeles E`, the image of E in the
adeles. -/
instance : DiscreteTopology (principalAdeleUnits E) := by
  -- The principal ideles lie in the preimage of the discrete set of rational adeles.
  have h_rat : IsDiscrete (ratAdeles E : Set (𝔸 E)) :=
    ⟨isCovolOneLattice_ratAdeles.toDiscreteTopology⟩
  have h_subset :
      (principalAdeleUnits E : Set (𝔸 E)ˣ) ⊆ Units.val ⁻¹' (ratAdeles E : Set (𝔸 E)) := by
    simp [principalAdeleUnits, ratAdeles, Set.range_subset_iff]
  have h_discrete : IsDiscrete (Units.val ⁻¹' (ratAdeles E : Set (𝔸 E))) :=
    h_rat.preimage (by fun_prop) Units.val_injective
  exact (h_discrete.mono h_subset).to_subtype

@[simp]
lemma piUnits_val_apply_ne_zero (a : (ι → ℂ)ˣ) (x : ι) : a.val x ≠ 0 := (a.isUnit.apply x).ne_zero

/-- For a finite index type `ι`, the function `a ↦ ∏ x, (1 + (log |a x|) ^ 2)⁻¹` on the group
`(ι → ℂ)ˣ` is integrable for Haar measure. -/
lemma integrable_prod_inv_one_add_log_sq [Fintype ι] :
    Integrable (fun a : (ι → ℂ)ˣ ↦ ∏ x : ι, (1 + Real.log ‖a.val x‖ ^ 2)⁻¹) haar := by
  -- Push Haar measure forward along `L : a ↦ (x ↦ log |a x|)`. The image is translation invariant
  -- and finite on compact sets, hence a multiple of Lebesgue measure on `ι → ℝ`.
  let L (a : (ι → ℂ)ˣ) (x : ι) : ℝ := Real.log ‖a.val x‖
  -- polar coordinates: the unit with moduli `exp (p.1 x)` and phases `p.2 x`
  let polar (p : (ι → ℝ) × (ι → Circle)) : (ι → ℂ)ˣ :=
    (by simp [Pi.isUnit_iff] : IsUnit fun x : ι ↦ exp (p.1 x : ℝ) * (p.2 x : Circle)).unit
  have hL : Measurable L := measurable_pi_iff.2 fun _ ↦ .log (.norm (.eval (by fun_prop)))
  have h_polar : Continuous polar := by
    rw [Units.isOpenEmbedding_val.isInducing.continuous_iff]
    simp only [polar, Function.comp_def, IsUnit.unit_spec]
    fun_prop
  -- `L` turns multiplication by `polar (t, 1)` into translation by `t`
  have h_inv : (haar.map L).IsAddLeftInvariant := ⟨fun t ↦
    ((hL.measurePreserving haar).of_semiconj (measurePreserving_mul_left haar (polar (t, 1)))
      (by simp [Function.Semiconj, funext_iff, L, polar, Real.log_mul])
      (by fun_prop)).map_eq⟩
  -- the preimage of a compact `K` lies in the image under `polar` of `K × (ι → Circle)`
  have h_fin : IsFiniteMeasureOnCompacts (haar.map L) := ⟨fun K hK ↦ by
    rw [map_apply hL hK.measurableSet]
    refine (measure_mono fun a ha ↦ ?_).trans_lt
      ((hK.prod isCompact_univ).image h_polar).measure_lt_top
    refine ⟨(L a, fun x ↦ Circle.exp (arg (a.val x))), ⟨ha, trivial⟩, ?_⟩
    ext x
    simp [polar, L, exp_log, ofReal_log]⟩
  refine (?_ : Integrable (fun t : ι → ℝ ↦ ∏ x : ι, (1 + t x ^ 2)⁻¹)
    (haar.map L)).comp_measurable hL
  rw [(haar.map L).isAddLeftInvariant_eq_smul volume]
  exact (Integrable.fintype_prod fun _ ↦ integrable_inv_one_add_sq).smul_measure_nnreal

end New
