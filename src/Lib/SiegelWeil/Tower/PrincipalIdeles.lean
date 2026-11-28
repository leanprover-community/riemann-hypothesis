module

public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import Lib.Adelic.Adeles.Basic
public import Lib.General.Groups.CongruenceSubgroups
import Lib.Adelic.Adeles.AdditiveCharacter

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

/-- The coordinatewise logarithmic moduli send Haar measure on the complex torus to
an additive Haar measure. -/
lemma isAddHaarMeasure_map_log_norm [Fintype ι] (μ : Measure (ι → ℂ)ˣ) [IsHaarMeasure μ] :
    IsAddHaarMeasure (μ.map fun a : (ι → ℂ)ˣ ↦ fun x ↦ Real.log ‖a.val x‖) := by
  let L : Additive (ι → ℂ)ˣ →+ (ι → ℝ) :=
    { toFun := fun a x ↦ Real.log ‖a.toMul.val x‖
      map_zero' := by ext x; simp
      map_add' := fun a b ↦ by ext x; simp [Real.log_mul] }
  have h_apply (a : (ι → ℂ)ˣ) (x : ι) : L a x = Real.log ‖a.val x‖ := rfl
  -- The polar coordinates allow all phases, a compact space at fixed moduli.
  let polar (p : (ι → ℝ) × (ι → Circle)) : (ι → ℂ)ˣ :=
    (by simp [Pi.isUnit_iff] : IsUnit fun x : ι ↦ exp (p.1 x : ℝ) * (p.2 x : Circle)).unit
  have h_polar : Continuous polar := by
    rw [Units.isOpenEmbedding_val.isInducing.continuous_iff]
    simp only [polar, Function.comp_def, IsUnit.unit_spec]
    fun_prop
  have hL : Continuous L := continuous_pi fun x ↦
    (continuous_apply x |>.comp Units.continuous_val).norm.log fun a ↦ by simp
  have h_section (p : (ι → ℝ) × (ι → Circle)) : L (polar p) = p.1 := by
    ext x
    change Real.log ‖(polar p).val x‖ = p.1 x
    simp [polar]
  have h_proper : IsProperMap L := by
    refine isProperMap_iff_isCompact_preimage.2 ⟨hL, fun K hK ↦ ?_⟩
    refine ((hK.prod (isCompact_univ (X := ι → Circle))).image h_polar).of_isClosed_subset
      (hK.isClosed.preimage hL) fun a ha ↦ ?_
    refine ⟨(L a, fun x ↦ Circle.exp (arg (a.val x))), ⟨ha, trivial⟩, ?_⟩
    ext x
    simp [polar, h_apply, exp_log, ofReal_log]
  let μAdd : Measure (Additive (ι → ℂ)ˣ) := μ
  let _ : IsAddHaarMeasure μAdd :=
    { map_add_left_eq_self := fun a ↦ map_mul_left_eq_self μ a.toMul
      lt_top_of_isCompact := fun _ hK ↦ hK.measure_lt_top (μ := μ)
      open_pos := fun _ hU hne ↦ (hU.measure_pos μ hne).ne' }
  exact isAddHaarMeasure_map μAdd L hL (fun t ↦ ⟨polar (t, 1), h_section _⟩)
    (isProperMap_iff_tendsto_cocompact.1 h_proper).2

/-- For a finite index type `ι`, the function `a ↦ ∏ x, (1 + (log |a x|) ^ 2)⁻¹` on the group
`(ι → ℂ)ˣ` is integrable for Haar measure. -/
lemma integrable_prod_inv_one_add_log_sq [Fintype ι] :
    Integrable (fun a : (ι → ℂ)ˣ ↦ ∏ x : ι, (1 + Real.log ‖a.val x‖ ^ 2)⁻¹) haar := by
  let L (a : (ι → ℂ)ˣ) (x : ι) : ℝ := Real.log ‖a.val x‖
  have hL : Measurable L := measurable_pi_iff.2 fun _ ↦ .log (.norm (.eval (by fun_prop)))
  let _ : IsAddHaarMeasure (haar.map L) := isAddHaarMeasure_map_log_norm haar
  refine (?_ : Integrable (fun t : ι → ℝ ↦ ∏ x, (1 + t x ^ 2)⁻¹)
    (haar.map L)).comp_measurable hL
  rw [(haar.map L).isAddLeftInvariant_eq_smul volume]
  exact (Integrable.fintype_prod fun _ ↦ integrable_inv_one_add_sq).smul_measure_nnreal

end New
