module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.Topology.Connected.Separation
public import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
public import Mathlib.FieldTheory.Galois.Infinite

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

scoped instance isGalois_GB : IsGalois K (PadicAlgCl p) := by
  have : IsGalois ℚ_[p] (PadicAlgCl p) := inferInstance
  infer_instance

scoped instance : CompactSpace (GK p K) := inferInstance

scoped instance : T2Space (GK p K) := inferInstance

scoped instance : TotallyDisconnectedSpace (GK p K) := inferInstance

variable {p K L}

theorem subG_eq_fixingSubgroup (h : K ≤ L) :
    subG p K L = (IntermediateField.extendScalars h).fixingSubgroup := by
  ext σ
  rw [IntermediateField.mem_fixingSubgroup_iff]
  rfl

theorem mem_iff_fixed (h : K ≤ L) (x : PadicAlgCl p) : x ∈ L ↔ ∀ σ ∈ subG p K L, σ x = x := by
  rw [subG_eq_fixingSubgroup h, ← IntermediateField.mem_fixedField_iff,
    InfiniteGalois.fixedField_fixingSubgroup]
  rfl

theorem isOpen_subG (hL : FiniteDimensional ℚ_[p] L) : IsOpen (subG p K L : Set (GK p K)) := by
  have hint : Algebra.IsIntegral K (PadicAlgCl p) := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  let b := Module.finBasis ℚ_[p] L
  have hopen : IsOpen (⋂ i, {σ : GK p K | σ (b i : PadicAlgCl p) = b i}) :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral (K := K) (b i : PadicAlgCl p)
  have heq : (subG p K L : Set (GK p K)) = ⋂ i, {σ : GK p K | σ (b i : PadicAlgCl p) = b i} := by
    ext σ
    rw [Set.mem_iInter]
    constructor
    · intro hσ i
      exact hσ _ (b i).2
    · intro hσ x hx
      have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : PadicAlgCl p) := by
        have := congrArg L.val (b.sum_repr ⟨x, hx⟩)

        rw [map_sum] at this
        exact this.symm

      rw [hx', map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul]
      exact congrArg₂ _ ((σ.restrictScalars ℚ_[p]).commutes _) (hσ i)
  rw [heq]
  exact hopen

theorem finiteIndex_subG (hL : FiniteDimensional ℚ_[p] L) : (subG p K L).FiniteIndex := by
  have : Finite (GK p K ⧸ subG p K L) := Subgroup.quotient_finite_of_isOpen _ (isOpen_subG hL)
  exact Subgroup.finiteIndex_of_finite_quotient

theorem degLK_eq_finrank (h : K ≤ L) :
    degLK p K L = Module.finrank K (IntermediateField.extendScalars h) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, ← subG_eq_fixingSubgroup h]
  rfl

theorem finrank_eq_degLK_mul (h : K ≤ L) (hL : FiniteDimensional ℚ_[p] L) :
    Module.finrank ℚ_[p] L = degLK p K L * Module.finrank ℚ_[p] K := by
  rw [degLK_eq_finrank h, mul_comm]
  set_option synthInstance.maxHeartbeats 200000 in
    exact (Module.finrank_mul_finrank ℚ_[p] K (IntermediateField.extendScalars h)).symm

theorem degLK_pos (hL : FiniteDimensional ℚ_[p] L) : 0 < degLK p K L :=
  Nat.pos_of_ne_zero (finiteIndex_subG hL).index_ne_zero

variable (p K L) in
theorem totallySeparatedSpace_GalLK : TotallySeparatedSpace (GalLK p K L) := by
  have hint : Algebra.IsIntegral K (PadicAlgCl p) := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro x y hxy
  induction x using QuotientGroup.induction_on with
  | H a =>
  induction y using QuotientGroup.induction_on with
  | H b =>
  have hab : a⁻¹ * b ∉ subG p K L := fun hh => hxy (QuotientGroup.eq.2 hh)
  rw [mem_subG_iff] at hab
  push Not at hab
  obtain ⟨z, hz, hne⟩ := hab
  have hpre : (QuotientGroup.mk : GK p K → GalLK p K L) ⁻¹' (QuotientGroup.mk '' {g : GK p K | g z = a z}) =
      (fun g : GK p K => a⁻¹ * g) ⁻¹' (MulAction.stabilizer (GK p K) z : Set (GK p K)) := by
    ext g
    have key : ∀ g : GK p K, (a⁻¹ * g) z = z ↔ g z = a z := fun g => by
      rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
    constructor
    · rintro ⟨g', hg', he⟩
      have hn : g'⁻¹ * g ∈ subG p K L := QuotientGroup.eq.1 he
      have h1 : (g'⁻¹ * g) z = z := hn z hz
      rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at h1
      exact (key g).2 (h1.trans hg')
    · intro hg
      exact ⟨g, (key g).1 hg, rfl⟩
  have hop : IsOpen (MulAction.stabilizer (GK p K) z : Set (GK p K)) :=
    stabilizer_isOpen_of_isIntegral (K := K) z
  have hcl : IsClopen (MulAction.stabilizer (GK p K) z : Set (GK p K)) :=
    ⟨Subgroup.isClosed_of_isOpen _ hop, hop⟩
  refine ⟨QuotientGroup.mk '' {g : GK p K | g z = a z}, ?_, ⟨a, rfl, rfl⟩, ?_⟩
  · rw [← QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.isClopen_preimage, hpre]
    exact hcl.preimage (continuous_const.mul continuous_id)
  · rintro ⟨g', hg', he⟩
    have hn : g'⁻¹ * b ∈ subG p K L := QuotientGroup.eq.1 he
    have h1 : (g'⁻¹ * b) z = z := hn z hz
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at h1
    apply hne
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
    exact h1.trans hg'

scoped instance [(subG p K L).Normal] : T2Space (GalLK p K L) :=
  have := totallySeparatedSpace_GalLK p K L
  TotallySeparatedSpace.t2Space

scoped instance [(subG p K L).Normal] : TotallyDisconnectedSpace (GalLK p K L) :=
  have := totallySeparatedSpace_GalLK p K L
  TotallySeparatedSpace.totallyDisconnectedSpace _

end ReciprocityTheory.DiscreteGroups.LocalClassField
