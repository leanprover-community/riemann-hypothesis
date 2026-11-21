import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNormOneOrthTriple
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruenceSubgroupLatticeStabilizer
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqNormSumRepsMulIndexLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLocalCharacterSum

section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.UnramOrder

section Abstract

open IsLocalRing Polynomial

variable {R₀ R : Type*} [CommRing R₀] [CommRing R] [Algebra R₀ R]

end Abstract

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
private lemma algebraMap_integer_mem_O' (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (a : 𝒪[F]) :
    algebraMap F E (a : F) ∈ L.O :=
  (_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L a).2 a.2

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
private lemma exists_inv_of_isUnit_norm (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {x : E} (hx : x ∈ L.O) {c : 𝒪[F]}
    (hc : x * L.cj x = algebraMap F E (c : F)) (hu : IsUnit c) : ∃ y ∈ L.O, x * y = 1 := by
  obtain ⟨u, rfl⟩ := hu
  refine ⟨L.cj x * algebraMap F E ((↑u⁻¹ : 𝒪[F]) : F),
    mul_mem (_root_.GlobalTheory.UnramOrder.cj_mem L hx) (algebraMap_integer_mem_O' L _), ?_⟩
  have h : ((u : 𝒪[F]) : F) * ((↑u⁻¹ : 𝒪[F]) : F) = 1 := by
    exact_mod_cast congrArg Subtype.val u.mul_inv
  rw [← mul_assoc, hc, ← map_mul, h, map_one]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
private lemma uniformizer_dvd_of_not_isUnit {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {c : 𝒪[F]}
    (hc : ¬ IsUnit c) : ∃ d, c = ϖ * d := by
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hmem : c ∈ IsLocalRing.maximalIdeal 𝒪[F] := (IsLocalRing.mem_maximalIdeal c).2 hc
  rw [hmax, Ideal.mem_span_singleton'] at hmem
  obtain ⟨d, hd⟩ := hmem
  exact ⟨d, by rw [← hd, mul_comm]⟩

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
private lemma exists_norm_eq_uniformizer_mul_of_nonunit (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {ϖ : 𝒪[F]}
    (hϖ : Irreducible ϖ) {x : E} (hx : x ∈ L.O) (hnu : ∀ z ∈ L.O, x * z ≠ 1) :
    ∃ d : 𝒪[F], x * L.cj x = algebraMap F E (ϖ : F) * algebraMap F E (d : F) := by
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.UnramOrder.exists_norm L hx
  have hcu : ¬ IsUnit c := fun hu => by
    obtain ⟨y, hy, hxy⟩ := exists_inv_of_isUnit_norm L hx hc hu
    exact hnu y hy hxy
  obtain ⟨d, rfl⟩ := uniformizer_dvd_of_not_isUnit hϖ hcu
  exact ⟨d, by rw [hc, MulMemClass.coe_mul, map_mul]⟩

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
private lemma cj_algebraMap' (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (a : F) :
    L.cj (algebraMap F E a) = algebraMap F E a :=
  L.cj.commutes a

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
private lemma exists_norm_eq_uniformizer' (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    (hPID : IsPrincipalIdealRing L.O)
    (hnorm : ∀ u : 𝒪[F]ˣ, ∃ x ∈ L.O, x * L.cj x = algebraMap F E ((u : 𝒪[F]) : F))
    {y : E} (hy : y ∈ L.O) (hyu : ∀ z ∈ L.O, y * z ≠ 1)
    (hyϖ : ∀ c ∈ L.O, y ≠ algebraMap F E (ϖ : F) * c) :
    ∃ π ∈ L.O, π * L.cj π = algebraMap F E (ϖ : F) := by
  haveI := hPID
  let y₁ : L.O := ⟨y, hy⟩
  let ϖ₁ : L.O := ⟨algebraMap F E (ϖ : F), algebraMap_integer_mem_O' L ϖ⟩
  let J : Ideal L.O := Ideal.span {y₁, ϖ₁}
  obtain ⟨p, hp⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator J).1
    (Ideal.subset_span (by simp) : y₁ ∈ J)
  obtain ⟨t, ht⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator J).1
    (Ideal.subset_span (by simp) : ϖ₁ ∈ J)
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 (Submodule.IsPrincipal.generator_mem J)
  set g := Submodule.IsPrincipal.generator J
  have hpE : y = (p : E) * g := by simpa [y₁, smul_eq_mul] using congrArg Subtype.val hp
  have htE : algebraMap F E (ϖ : F) = (t : E) * g := by
    simpa [ϖ₁, smul_eq_mul] using congrArg Subtype.val ht
  have habE : (a : E) * y + b * algebraMap F E (ϖ : F) = g := by
    simpa [y₁, ϖ₁] using congrArg Subtype.val hab
  have hg : ∀ z ∈ L.O, (g : E) * z ≠ 1 := by
    intro z hz hgz
    obtain ⟨d, hd⟩ := exists_norm_eq_uniformizer_mul_of_nonunit L hϖ hy hyu
    have hmem : algebraMap F E (d : F) * a * z + b * z * L.cj y ∈ L.O :=
      add_mem (mul_mem (mul_mem (algebraMap_integer_mem_O' L d) a.2) hz)
        (mul_mem (mul_mem b.2 hz) (_root_.GlobalTheory.UnramOrder.cj_mem L hy))
    have hσy : L.cj y = algebraMap F E (ϖ : F) *
        (algebraMap F E (d : F) * a * z + b * z * L.cj y) := by
      linear_combination (-L.cj y) * hgz + (-(L.cj y) * z) * habE + ((a : E) * z) * hd
    refine hyϖ _ (_root_.GlobalTheory.UnramOrder.cj_mem L hmem) ?_
    have := congrArg L.cj hσy
    rwa [L.cj_cj, map_mul, cj_algebraMap'] at this
  have ht' : ∀ z ∈ L.O, (t : E) * z ≠ 1 := by
    intro z hz htz
    refine hyϖ ((p : E) * z) (mul_mem p.2 hz) ?_
    linear_combination hpE - ((p : E) * z) * htE - ((p : E) * g) * htz
  obtain ⟨d₁, hd₁⟩ := exists_norm_eq_uniformizer_mul_of_nonunit L hϖ g.2 hg
  obtain ⟨d₂, hd₂⟩ := exists_norm_eq_uniformizer_mul_of_nonunit L hϖ t.2 ht'
  have hE : algebraMap F E ((ϖ : F) * ϖ * 1) = algebraMap F E ((ϖ : F) * ϖ * (d₁ * d₂)) := by
    simp only [map_mul, map_one]
    calc algebraMap F E (ϖ : F) * algebraMap F E (ϖ : F) * 1
        = ((t : E) * g) * L.cj ((t : E) * g) := by rw [← htE, cj_algebraMap', mul_one]
      _ = ((t : E) * L.cj t) * ((g : E) * L.cj g) := by rw [map_mul]; ring
      _ = _ := by rw [hd₁, hd₂]; ring
  have hϖ0 : (ϖ : F) * ϖ ≠ 0 := by
    have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    exact mul_ne_zero h0 h0
  have hdF : (1 : F) = d₁ * d₂ := mul_left_cancel₀ hϖ0 (_root_.GlobalTheory.UnramOrder.algebraMap_inj L hE)
  have hd : d₁ * d₂ = 1 := Subtype.ext (by rw [MulMemClass.coe_mul]; exact hdF.symm)
  obtain ⟨z, hz, hzN⟩ := hnorm ⟨d₂, d₁, by rw [mul_comm]; exact hd, hd⟩
  refine ⟨g * z, mul_mem g.2 hz, ?_⟩
  have hdd : algebraMap F E (d₁ : F) * algebraMap F E (d₂ : F) = 1 := by
    rw [← map_mul, ← hdF, map_one]
  calc (g * z : E) * L.cj (g * z) = ((g : E) * L.cj g) * (z * L.cj z) := by rw [map_mul]; ring
    _ = _ := by
      rw [hd₁, hzN]
      linear_combination (algebraMap F E (ϖ : F)) * hdd

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
private lemma isUnit_algebraMap_uniformizer (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) :
    IsUnit (algebraMap F E (ϖ : F)) := by
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  exact (IsUnit.mk0 _ h0).map _

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
private lemma exists_coprime_combination_pi_cj (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    (hPID : IsPrincipalIdealRing L.O) {π : E} (hπ : π ∈ L.O)
    (hN : π * L.cj π = algebraMap F E (ϖ : F)) :
    ∃ r ∈ L.O, ∃ s ∈ L.O, π * r + L.cj π * s = 1 := by
  haveI := hPID
  let π₁ : L.O := ⟨π, hπ⟩
  let π₂ : L.O := ⟨L.cj π, _root_.GlobalTheory.UnramOrder.cj_mem L hπ⟩
  let K : Ideal L.O := Ideal.span {π₁, π₂}
  obtain ⟨p, hp⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator K).1
    (Ideal.subset_span (by simp) : π₁ ∈ K)
  obtain ⟨q, hq⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator K).1
    (Ideal.subset_span (by simp) : π₂ ∈ K)
  set δ := Submodule.IsPrincipal.generator K
  have hp' : π = (p : E) * δ := by simpa [π₁, smul_eq_mul] using congrArg Subtype.val hp
  have hq' : L.cj π = (q : E) * δ := by simpa [π₂, smul_eq_mul] using congrArg Subtype.val hq
  have hsq : ((δ : E) * p * q) * ((δ : E) * p * q) = algebraMap F E (ϖ : F) * ((p : E) * q) := by
    rw [← hN, hq', hp']; ring
  have hspan : ((p * q : L.O) : E) • algebraMap F E (ϖ : F) = (δ : E) * p * q * ((δ : E) * p * q) := by
    rw [hsq, smul_eq_mul, Subring.coe_mul, mul_comm]
  have hmem := L.unram ϖ hϖ _ (mul_mem (mul_mem δ.2 p.2) q.2)
    (Submodule.mem_span_singleton.2 ⟨p * q, by rw [Subring.smul_def]; exact hspan⟩)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  rw [Subring.smul_def, smul_eq_mul] at ha
  have hu : IsUnit ((δ : E) * p * q) := by
    apply isUnit_of_mul_isUnit_left (y := (δ : E))
    rw [show (δ : E) * p * q * δ = algebraMap F E (ϖ : F) by rw [← hN, hq', hp']; ring]
    exact isUnit_algebraMap_uniformizer L hϖ
  have h1 : (a : E) * δ = 1 := by
    have : ((δ : E) * p * q) * ((a : E) * δ) = ((δ : E) * p * q) * 1 := by
      rw [mul_one]
      calc ((δ : E) * p * q) * ((a : E) * δ) = (a : E) * (((p : E) * δ) * ((q : E) * δ)) := by ring
        _ = _ := by rw [← hp', ← hq', hN, ha]
    exact hu.mul_left_cancel this
  have hδ : IsUnit δ := isUnit_iff_exists_inv'.2 ⟨a, Subtype.ext (by simpa using h1)⟩
  have hK : K = ⊤ := by
    rw [← Submodule.IsPrincipal.span_singleton_generator K]
    exact Ideal.span_singleton_eq_top.2 hδ
  have h1K : (1 : L.O) ∈ K := hK ▸ Submodule.mem_top
  obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.1 h1K
  refine ⟨r, r.2, s, s.2, ?_⟩
  have := congrArg Subtype.val hrs
  simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_one, π₁, π₂] at this
  linear_combination this

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
private lemma exists_mul_eq_one_add_pi_mul_of_not_dvd (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    (hPID : IsPrincipalIdealRing L.O) {π : E} (hπ : π ∈ L.O)
    (hN : π * L.cj π = algebraMap F E (ϖ : F)) {x : E} (hx : x ∈ L.O)
    (hnot : ¬ ∃ c ∈ L.O, x = π * c) : ∃ u ∈ L.O, ∃ w ∈ L.O, x * u = 1 + π * w := by
  obtain ⟨r, hr, s, hs, hrs⟩ := exists_coprime_combination_pi_cj L hϖ hPID hπ hN
  have hσπ := _root_.GlobalTheory.UnramOrder.cj_mem L hπ
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.UnramOrder.exists_trace L (mul_mem hx (mul_mem hσπ hs))
  have hcj : L.cj (x * (L.cj π * s)) = L.cj x * π * L.cj s := by
    rw [map_mul, map_mul, L.cj_cj]; ring
  have hwO : x * r - L.cj x * L.cj s ∈ L.O :=
    sub_mem (mul_mem hx hr)
      (mul_mem (_root_.GlobalTheory.UnramOrder.cj_mem L hx) (_root_.GlobalTheory.UnramOrder.cj_mem L hs))
  have hxa : x = algebraMap F E (a : F) + π * (x * r - L.cj x * L.cj s) := by
    rw [← ha, hcj]; linear_combination (-x) * hrs
  have hau : IsUnit a := by
    by_contra hna
    obtain ⟨d, rfl⟩ := uniformizer_dvd_of_not_isUnit hϖ hna
    refine hnot ⟨L.cj π * algebraMap F E (d : F) + (x * r - L.cj x * L.cj s),
      add_mem (mul_mem hσπ (algebraMap_integer_mem_O' L d)) hwO, ?_⟩
    calc x = _ := hxa
      _ = _ := by rw [MulMemClass.coe_mul, map_mul, ← hN]; ring
  obtain ⟨v, rfl⟩ := hau
  have hv : algebraMap F E ((v : 𝒪[F]) : F) * algebraMap F E ((↑v⁻¹ : 𝒪[F]) : F) = 1 := by
    rw [← map_mul, show ((v : 𝒪[F]) : F) * ((↑v⁻¹ : 𝒪[F]) : F) = 1 by
      exact_mod_cast congrArg Subtype.val v.mul_inv, map_one]
  refine ⟨algebraMap F E ((↑v⁻¹ : 𝒪[F]) : F), algebraMap_integer_mem_O' L _,
    (x * r - L.cj x * L.cj s) * algebraMap F E ((↑v⁻¹ : 𝒪[F]) : F),
    mul_mem hwO (algebraMap_integer_mem_O' L _), ?_⟩
  conv_lhs => rw [hxa]
  linear_combination hv

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
private lemma exists_inv_one_sub_uniformizer_mul (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {ϖ : 𝒪[F]}
    (hϖ : Irreducible ϖ) {w : E} (hw : w ∈ L.O) :
    ∃ y ∈ L.O, (1 - algebraMap F E (ϖ : F) * w) * y = 1 := by
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.UnramOrder.exists_trace L hw
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.UnramOrder.exists_norm L hw
  apply exists_inv_of_isUnit_norm L
    (sub_mem (one_mem _) (mul_mem (algebraMap_integer_mem_O' L ϖ) hw)) (c := 1 - ϖ * (t - ϖ * n))
  · rw [map_sub, map_mul, cj_algebraMap', map_one,
      show ((1 - ϖ * (t - ϖ * n) : 𝒪[F]) : F) = 1 - (ϖ : F) * ((t : F) - ϖ * n) by push_cast; ring]
    simp only [map_sub, map_mul, map_one]
    linear_combination (-algebraMap F E (ϖ : F)) * ht + (algebraMap F E (ϖ : F)) ^ 2 * hn
  · rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (ϖ * (t - ϖ * n)) with h | h
    · exact absurd (isUnit_of_mul_isUnit_left h) hϖ.not_isUnit
    · exact h

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
private lemma ideal_le_pi_or_le_cj_pi_of_proper (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    (hPID : IsPrincipalIdealRing L.O) {π : E} (hπ : π ∈ L.O)
    (hN : π * L.cj π = algebraMap F E (ϖ : F)) (I : Ideal L.O) (hI : I ≠ ⊤) :
    (∀ x ∈ I, ∃ c ∈ L.O, (x : E) = π * c) ∨ ∀ x ∈ I, ∃ c ∈ L.O, (x : E) = L.cj π * c := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨x₁, hx₁I, hx₁⟩, ⟨x₂, hx₂I, hx₂⟩⟩ := hcon
  have hN' : L.cj π * L.cj (L.cj π) = algebraMap F E (ϖ : F) := by rw [L.cj_cj, mul_comm, hN]
  obtain ⟨u₁, hu₁, w₁, hw₁, h₁⟩ := exists_mul_eq_one_add_pi_mul_of_not_dvd L hϖ hPID hπ hN x₁.2
    (by rintro ⟨c, hc, h⟩; exact hx₁ c hc h)
  obtain ⟨u₂, hu₂, w₂, hw₂, h₂⟩ := exists_mul_eq_one_add_pi_mul_of_not_dvd L hϖ hPID
    (_root_.GlobalTheory.UnramOrder.cj_mem L hπ) hN' x₂.2 (by rintro ⟨c, hc, h⟩; exact hx₂ c hc h)
  obtain ⟨y, hy, hy1⟩ := exists_inv_one_sub_uniformizer_mul L hϖ (mul_mem hw₁ hw₂)
  let z : L.O := x₁ * ⟨u₁, hu₁⟩ + x₂ * ⟨u₂, hu₂⟩ - x₁ * ⟨u₁, hu₁⟩ * x₂ * ⟨u₂, hu₂⟩
  have hz : z ∈ I := sub_mem (add_mem (I.mul_mem_right _ hx₁I) (I.mul_mem_right _ hx₂I))
    (I.mul_mem_right _ (I.mul_mem_left _ hx₂I))
  have hzE : (z : E) = 1 - algebraMap F E (ϖ : F) * (w₁ * w₂) := by
    rw [show (z : E) = (x₁ : E) * u₁ + x₂ * u₂ - x₁ * u₁ * x₂ * u₂ from rfl]
    linear_combination (1 - (x₂ : E) * u₂) * h₁ + (-(π * w₁)) * h₂ + (-(w₁ * w₂)) * hN
  apply hI
  refine Ideal.eq_top_of_isUnit_mem I hz (isUnit_iff_exists_inv.2 ⟨⟨y, hy⟩, Subtype.ext ?_⟩)
  show (z : E) * y = 1
  rw [hzE, hy1]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in

theorem _root_.GlobalTheory.UnramOrder.proper_ideals : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ →
    (∀ I : Ideal L.O, I ≠ ⊤ → ∀ x ∈ I, ∃ c ∈ L.O, (x : E) = algebraMap F E ϖ * c) ∨
    ∃ π ∈ L.O, π * L.cj π = algebraMap F E ϖ ∧ ∀ I : Ideal L.O, I ≠ ⊤ →
      (∀ x ∈ I, ∃ c ∈ L.O, (x : E) = π * c) ∨ ∀ x ∈ I, ∃ c ∈ L.O, (x : E) = L.cj π * c := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ
  obtain ⟨-, -, -, hPID, -, -, -, hnorm⟩ := _root_.GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  by_cases h : ∃ y ∈ L.O, (∀ z ∈ L.O, y * z ≠ 1) ∧ ∀ c ∈ L.O, y ≠ algebraMap F E ϖ * c
  · right
    obtain ⟨y, hy, hyu, hyϖ⟩ := h
    obtain ⟨π, hπ, hN⟩ := exists_norm_eq_uniformizer' L hϖ hPID hnorm hy hyu hyϖ
    exact ⟨π, hπ, hN, fun I hI => ideal_le_pi_or_le_cj_pi_of_proper L hϖ hPID hπ hN I hI⟩
  · left
    push_neg at h
    intro I hI x hx
    apply h x x.2
    intro z hz hxz
    exact hI (Ideal.eq_top_of_isUnit_mem I hx (isUnit_iff_exists_inv.2 ⟨⟨z, hz⟩, Subtype.ext hxz⟩))

end GlobalTheory.UnramOrder
end

section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.TraceChar

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem psi0_eq_one_of_conj_eq_neg {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {z : E} (hz : L.cj z = -z) : L.psi0 z = 1 := by
  set w := algebraMap F E (1 / 2) * z with hw
  have hcw : L.cj w = -w := by
    rw [hw, map_mul, AlgEquiv.commutes, hz, mul_neg]
  have hzw : z = w + w := by
    rw [hw, ← add_mul, ← map_add]
    norm_num
  have h1 : L.psi0 w = L.psi0 (-w) := by rw [← hcw, _root_.Formalism.MainNotions.S.Loc.LocE.local_additive_char_conj]
  rw [hzw, AddChar.map_add_eq_mul]
  nth_rewrite 2 [h1]
  rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem ker_mkQ_comp_mulLeft_pow_eq_span' {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n k : ℕ) :
    ((Submodule.mkQ (Ideal.span {ϖ ^ (n + k)})).comp (LinearMap.mulLeft 𝒪[F] (ϖ ^ k))).ker =
      Ideal.span {ϖ ^ n} := by
  ext y
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
  rw [pow_add, mul_comm (ϖ ^ n), mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem card_quotient_span_pow_succ_eq_resQ_mul {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n : ℕ) :
    Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ (n + 1)}) =
      _root_.GlobalTheory.HL.resQ ϖ * Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) := by
  rw [add_comm n 1]
  set f := (Submodule.mkQ (Ideal.span {ϖ ^ (1 + n)})).comp (LinearMap.mulLeft 𝒪[F] (ϖ ^ n))
  have hS : Nat.card (LinearMap.range f) = _root_.GlobalTheory.HL.resQ ϖ := by
    unfold _root_.GlobalTheory.HL.resQ
    have hk := ker_mkQ_comp_mulLeft_pow_eq_span' hϖ 1 n
    rw [pow_one] at hk
    rw [← hk]
    exact (Nat.card_congr (f.quotKerEquivRange).toEquiv).symm
  set g := (Submodule.mkQ (LinearMap.range f)).comp (Submodule.mkQ (Ideal.span {ϖ ^ (1 + n)}))
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
  have hker : g.ker = Ideal.span {ϖ ^ n} := by
    ext y
    simp only [g, f, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range,
      LinearMap.mulLeft_apply, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨z, hz⟩
      rw [Submodule.Quotient.eq, Ideal.mem_span_singleton] at hz
      have h2 : ϖ ^ n ∣ ϖ ^ (1 + n) := pow_dvd_pow _ (by omega)
      have h4 : ϖ ^ n ∣ ϖ ^ n * z := dvd_mul_right _ _
      simpa using (dvd_sub h4 (h2.trans hz))
    · rintro ⟨z, rfl⟩
      exact ⟨z, rfl⟩
  have e := (g.quotKerEquivOfSurjective hg).toEquiv
  rw [hker] at e
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.range f), hS, Nat.card_congr e]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem card_quotient_span_pow_eq_resQ_pow {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n : ℕ) :
    Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) = _root_.GlobalTheory.HL.resQ ϖ ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, Ideal.span_singleton_one]
    exact Nat.card_unique
  | succ n ih => rw [card_quotient_span_pow_succ_eq_resQ_mul hϖ, ih, pow_succ, mul_comm]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem resQ_pos' {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) :
    0 < _root_.GlobalTheory.HL.resQ ϖ := by
  unfold _root_.GlobalTheory.HL.resQ
  have h := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  rw [← h]
  exact Nat.card_pos (α := 𝓀[F])

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem finite_quotient_span_pow_flag_measures {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n : ℕ) :
    Finite (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) :=
  Nat.finite_of_card_ne_zero (by rw [card_quotient_span_pow_eq_resQ_pow hϖ]; exact pow_ne_zero _ (resQ_pos' hϖ).ne')

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem exists_nat_mul_mem_integer (x : F) : ∃ N : ℕ, 0 < N ∧ (N : F) * x ∈ 𝒪[F] := by
  by_cases hx : x ∈ 𝒪[F]
  · exact ⟨1, one_pos, by simpa using hx⟩
  have hx0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
  have hinv : x⁻¹ ∈ 𝒪[F] := by
    rw [Valuation.mem_integer_iff] at hx ⊢
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hx))
  set b : 𝒪[F] := ⟨x⁻¹, hinv⟩ with hbdef
  have hb0 : b ≠ 0 := by
    intro h
    have : (b : F) = 0 := by rw [h]; rfl
    exact inv_ne_zero hx0 this
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨n, u, hb⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}), ?_, ?_⟩
  · haveI := finite_quotient_span_pow_flag_measures hϖ n
    exact Nat.card_pos
  have hmem : ((Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) : ℕ) : 𝒪[F]) ∈ Ideal.span {ϖ ^ n} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← nsmul_one]
    exact card_nsmul_eq_zero'
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hmem
  have hxb : x * (b : F) = 1 := mul_inv_cancel₀ hx0
  rw [hb] at hxb
  have hu : ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * (u : 𝒪[F]) = 1 := Units.inv_mul u
  have hu' : (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) * ((u : 𝒪[F]) : F) = 1 := by
    rw [← Subring.coe_mul, hu]; rfl
  have hN : ((Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) : ℕ) : F) = ((w : 𝒪[F]) : F) * ((ϖ : 𝒪[F]) : F) ^ n := by
    rw [← map_natCast (𝒪[F]).subtype, ← hw]; push_cast; rfl
  have : (Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) : F) * x = ((w * ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : 𝒪[F]) : F) := by
    rw [hN]
    push_cast at hxb ⊢
    linear_combination ((w : F) * (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F)) * hxb - ((w : F) * ((ϖ : 𝒪[F]) : F) ^ n * x) * hu'
  rw [this]
  exact (w * ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F])).2

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in

theorem _root_.GlobalTheory.TraceChar.exists_trace_char : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∃ ψ : AddChar F ℂ, (∀ x : F, ‖ψ x‖ = 1) ∧ (∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) ∧ ∀ (y : E) (c : F), y + L.cj y = algebraMap F E c → L.psi0 y = ψ c := by
  intro F _ _ _ _ _ E _ _ _ L
  let ψ : AddChar F ℂ := L.psi0.compAddMonoidHom
    ((algebraMap F E).toAddMonoidHom.comp (AddMonoidHom.mulLeft (1 / 2 : F)))
  have hψ : ∀ c, ψ c = L.psi0 (algebraMap F E (1 / 2 * c)) := fun c => rfl
  have hcomp : ∀ (y : E) (c : F), y + L.cj y = algebraMap F E c → L.psi0 y = ψ c := by
    intro y c h
    have hz : L.cj (y - algebraMap F E (1 / 2 * c)) = -(y - algebraMap F E (1 / 2 * c)) := by
      rw [map_sub, AlgEquiv.commutes]
      have : L.cj y = algebraMap F E c - y := by rw [← h]; ring
      rw [this]
      have : algebraMap F E c = algebraMap F E (1 / 2 * c) + algebraMap F E (1 / 2 * c) := by
        rw [← map_add]; congr 1; ring
      rw [this]; ring
    have := psi0_eq_one_of_conj_eq_neg L hz
    rw [hψ, ← one_mul (L.psi0 (algebraMap F E _)), ← this, ← AddChar.map_add_eq_mul, sub_add_cancel]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hint : ∀ c : 𝒪[F], ψ c = 1 := by
    intro c
    obtain ⟨e, he, htr⟩ := (_root_.GlobalTheory.UnramOrder.order_facts L ϖ hϖ).1 c
    rw [← hcomp e c htr, ← one_mul e]
    exact (_root_.Formalism.MainNotions.S.Loc.LocE.additive_character_dual_ring L 1).2 (one_mem _) e he
  refine ⟨ψ, ?_, ?_, hcomp⟩
  · intro x
    obtain ⟨N, hN, hNx⟩ := exists_nat_mul_mem_integer x
    have h1 : ψ x ^ N = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
      exact hint ⟨_, hNx⟩
    have h2 : ‖ψ x‖ ^ N = 1 := by rw [← norm_pow, h1, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h2
  · intro x
    constructor
    · intro hx
      rw [← _root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L]
      refine (_root_.Formalism.MainNotions.S.Loc.LocE.additive_character_dual_ring L _).1 fun e he => ?_
      obtain ⟨c, hc⟩ := _root_.GlobalTheory.UnramOrder.exists_trace L he
      have htr : algebraMap F E x * e + L.cj (algebraMap F E x * e) = algebraMap F E (x * c) := by
        rw [map_mul, AlgEquiv.commutes, ← mul_add, hc, map_mul]
      rw [hcomp _ _ htr]
      exact hx c
    · intro hx y
      exact hint ⟨x * y, mul_mem hx y.2⟩

end GlobalTheory.TraceChar
end

section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CharCond

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

noncomputable def rep (ϖ : 𝒪[F]) (j : ℕ) (x : 𝒪[F] ⧸ Ideal.span {ϖ ^ j}) : 𝒪[F] :=
  (Ideal.Quotient.mk_surjective x).choose

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem ker_mkQ_comp_mulLeft_pow_eq_span {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n k : ℕ) :
    ((Submodule.mkQ (Ideal.span {ϖ ^ (n + k)})).comp (LinearMap.mulLeft 𝒪[F] (ϖ ^ k))).ker =
      Ideal.span {ϖ ^ n} := by
  ext y
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
  rw [pow_add, mul_comm (ϖ ^ n), mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem card_quotient_pow_succ_eq_resQ_mul {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n : ℕ) :
    Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ (n + 1)}) =
      _root_.GlobalTheory.HL.resQ ϖ * Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) := by
  rw [add_comm n 1]
  set f := (Submodule.mkQ (Ideal.span {ϖ ^ (1 + n)})).comp (LinearMap.mulLeft 𝒪[F] (ϖ ^ n))
  have hS : Nat.card (LinearMap.range f) = _root_.GlobalTheory.HL.resQ ϖ := by
    unfold _root_.GlobalTheory.HL.resQ
    have hk := ker_mkQ_comp_mulLeft_pow_eq_span hϖ 1 n
    rw [pow_one] at hk
    rw [← hk]
    exact (Nat.card_congr (f.quotKerEquivRange).toEquiv).symm
  set g := (Submodule.mkQ (LinearMap.range f)).comp (Submodule.mkQ (Ideal.span {ϖ ^ (1 + n)}))
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
  have hker : g.ker = Ideal.span {ϖ ^ n} := by
    ext y
    simp only [g, f, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range,
      LinearMap.mulLeft_apply, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨z, hz⟩
      rw [Submodule.Quotient.eq, Ideal.mem_span_singleton] at hz
      have h2 : ϖ ^ n ∣ ϖ ^ (1 + n) := pow_dvd_pow _ (by omega)
      have h4 : ϖ ^ n ∣ ϖ ^ n * z := dvd_mul_right _ _
      simpa using (dvd_sub h4 (h2.trans hz))
    · rintro ⟨z, rfl⟩
      exact ⟨z, rfl⟩
  have e := (g.quotKerEquivOfSurjective hg).toEquiv
  rw [hker] at e
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.range f), hS, Nat.card_congr e]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem card_quotient_pow_eq_resQ_pow {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n : ℕ) :
    Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) = _root_.GlobalTheory.HL.resQ ϖ ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, Ideal.span_singleton_one]
    exact Nat.card_unique
  | succ n ih => rw [card_quotient_pow_succ_eq_resQ_mul hϖ, ih, pow_succ, mul_comm]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem resQ_pos_flag_measures {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) :
    0 < _root_.GlobalTheory.HL.resQ ϖ := by
  unfold _root_.GlobalTheory.HL.resQ
  have h := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  rw [← h]
  exact Nat.card_pos (α := 𝓀[F])

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem finite_quotient_span_pow' {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n : ℕ) :
    Finite (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) :=
  Nat.finite_of_card_ne_zero (by rw [card_quotient_pow_eq_resQ_pow hϖ]; exact pow_ne_zero _ (resQ_pos_flag_measures hϖ).ne')

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem addChar_mul_eq_of_quotient_eq {ϖ : 𝒪[F]} {ψ : AddChar F ℂ}
    (hψ : ∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) {a : ℕ} {c : F}
    (hc : c * (ϖ : F) ^ a ∈ 𝒪[F]) {y y' : 𝒪[F]}
    (h : Ideal.Quotient.mk (Ideal.span {ϖ ^ a}) y = Ideal.Quotient.mk _ y') :
    ψ (y * c) = ψ (y' * c) := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h
  obtain ⟨w, hw⟩ := h
  have hy : (y : F) = y' + w * (ϖ : F) ^ a := by
    have := congrArg (fun z : 𝒪[F] => (z : F)) hw
    push_cast at this
    linear_combination -this
  have h1 : ψ (c * (ϖ : F) ^ a * w) = 1 := (hψ _).2 hc w
  rw [hy, show ((y' : F) + w * (ϖ : F) ^ a) * c = y' * c + c * (ϖ : F) ^ a * w by ring,
    AddChar.map_add_eq_mul, h1, mul_one]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem mk_rep_eq (ϖ : 𝒪[F]) (a : ℕ)
    (r : 𝒪[F] ⧸ Ideal.span {ϖ ^ a}) :
    Ideal.Quotient.mk _ (_root_.GlobalTheory.HL.CharCond.rep ϖ a r) = r :=
  (Ideal.Quotient.mk_surjective r).choose_spec

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem addChar_eq_one_of_mem_integer {ψ : AddChar F ℂ}
    (hψ : ∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) {c : F} (hc : c ∈ 𝒪[F]) :
    ψ c = 1 := by
  simpa using (hψ c).2 hc 1

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem sum_addChar_rep_mul_eq_ite {ϖ : 𝒪[F]} {ψ : AddChar F ℂ}
    (hψ : ∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) (a : ℕ)
    [Fintype (𝒪[F] ⧸ Ideal.span {ϖ ^ a})] {c : F} (hc : c * (ϖ : F) ^ a ∈ 𝒪[F]) :
    ∑ r, ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a r * c) =
      if c ∈ 𝒪[F] then (Fintype.card (𝒪[F] ⧸ Ideal.span {ϖ ^ a}) : ℂ) else 0 := by
  have hadd : ∀ r s, ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a (r + s) * c) =
      ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a r * c) *
        ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a s * c) := by
    intro r s
    rw [← AddChar.map_add_eq_mul, ← add_mul]
    have := addChar_mul_eq_of_quotient_eq hψ hc (y := _root_.GlobalTheory.HL.CharCond.rep ϖ a (r + s))
      (y' := _root_.GlobalTheory.HL.CharCond.rep ϖ a r + _root_.GlobalTheory.HL.CharCond.rep ϖ a s)
      (by rw [map_add, mk_rep_eq,
        mk_rep_eq, mk_rep_eq])
    rw [this]
    push_cast
    rfl
  split_ifs with hcO
  · have : ∀ r, ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a r * c) = 1 := fun r =>
      addChar_eq_one_of_mem_integer hψ (mul_mem (_root_.GlobalTheory.HL.CharCond.rep ϖ a r).2 hcO)
    simp [this]
  · have hne : ¬ ∀ y : 𝒪[F], ψ (c * y) = 1 := fun h => hcO ((hψ c).1 h)
    push_neg at hne
    obtain ⟨y, hy⟩ := hne
    set m : 𝒪[F] ⧸ Ideal.span {ϖ ^ a} := Ideal.Quotient.mk _ y
    have hm : ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a m * c) ≠ 1 := by
      rw [addChar_mul_eq_of_quotient_eq hψ hc (y' := y) (mk_rep_eq ϖ a m), mul_comm]
      exact hy
    have hshift : ∑ r, ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a r * c) =
        (∑ r, ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a r * c)) *
          ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a m * c) := by
      rw [Finset.sum_mul]
      simp_rw [← hadd]
      exact (Fintype.sum_equiv (Equiv.addRight m) _ _ (fun r => rfl)).symm
    have h2 : (∑ r, ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a r * c)) *
        (1 - ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a m * c)) = 0 := by
      rw [mul_sub, mul_one, ← hshift, sub_self]
    exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 (Ne.symm hm))

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem exists_unit_of_exact_valuation_level {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {k i a : ℕ}
    (hi : a = k + i) {y : 𝒪[F]} (h1 : ϖ ^ k ∣ y) (h2 : ¬ ϖ ^ (k + 1) ∣ y) :
    ∃ u₀ : (𝒪[F])ˣ, (y : F) / (ϖ : F) ^ a * (ϖ : F) ^ i = ((u₀ : 𝒪[F]) : F) := by
  obtain ⟨w, rfl⟩ := h1
  have hw : ¬ ϖ ∣ w := fun h => h2 (by rw [pow_succ]; exact mul_dvd_mul_left _ h)
  have hu : IsUnit w := by
    by_contra hn
    apply hw
    have hmax : w ∈ IsLocalRing.maximalIdeal 𝒪[F] := (IsLocalRing.mem_maximalIdeal _).2 hn
    rwa [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
      Ideal.mem_span_singleton] at hmax
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, hi]
  push_cast
  field_simp
  ring

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem card_filter_pow_dvd_rep_eq_resQ_pow {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {k a : ℕ} (hk : k ≤ a)
    [Fintype (𝒪[F] ⧸ Ideal.span {ϖ ^ a})] :
    (Finset.univ.filter (fun r => ϖ ^ k ∣ _root_.GlobalTheory.HL.CharCond.rep ϖ a r)).card =
      _root_.GlobalTheory.HL.resQ ϖ ^ (a - k) := by
  obtain ⟨n, rfl⟩ : ∃ n, a = n + k := ⟨a - k, by omega⟩
  set f := (Submodule.mkQ (Ideal.span {ϖ ^ (n + k)})).comp (LinearMap.mulLeft 𝒪[F] (ϖ ^ k))
  have hmem : ∀ r, ϖ ^ k ∣ _root_.GlobalTheory.HL.CharCond.rep ϖ (n + k) r ↔
      r ∈ LinearMap.range f := by
    intro r
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      simp only [f, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
        Submodule.mkQ_apply]
      rw [← hy]
      exact mk_rep_eq ϖ (n + k) r
    · rintro ⟨y, rfl⟩
      have h := mk_rep_eq ϖ (n + k) (f y)
      have hfy : f y = Ideal.Quotient.mk (Ideal.span {ϖ ^ (n + k)}) (ϖ ^ k * y) := rfl
      rw [hfy, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
      have h3 : ϖ ^ k ∣ _ := (pow_dvd_pow ϖ (Nat.le_add_left k n)).trans h
      have h4 : ϖ ^ k ∣ ϖ ^ k * y := dvd_mul_right _ _
      have h5 := dvd_add h3 h4
      rw [sub_add_cancel] at h5
      exact h5
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    Nat.card_congr (Equiv.subtypeEquivRight hmem), Nat.add_sub_cancel]
  change Nat.card (LinearMap.range f) = _
  rw [← Nat.card_congr (f.quotKerEquivRange).toEquiv, ker_mkQ_comp_mulLeft_pow_eq_span hϖ n k, card_quotient_pow_eq_resQ_pow hϖ]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem _root_.GlobalTheory.HL.CharCond.expand_by_conductor : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]), Irreducible ϖ → ∀ ψ : AddChar F ℂ, (∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) → ∀ {U : Type} (R : Finset U) (Q : U → 𝒪[F]) (χ : U → ℂ) (a : ℕ) (B : ℕ → ℝ), (∀ i, 1 ≤ i → i ≤ a → ∀ (t : F) (u₀ : (𝒪[F])ˣ), t * (ϖ : F) ^ i = ((u₀ : 𝒪[F]) : F) → ‖∑ u ∈ R, ψ (t * Q u) * χ u‖ ≤ B i) → ‖(∑ u ∈ R.filter (fun u => ϖ ^ a ∣ Q u), χ u) * (_root_.GlobalTheory.HL.resQ ϖ : ℂ) ^ a - ∑ u ∈ R, χ u‖ ≤ ∑ i ∈ Finset.Icc 1 a, ((_root_.GlobalTheory.HL.resQ ϖ : ℝ) ^ i - (_root_.GlobalTheory.HL.resQ ϖ : ℝ) ^ (i - 1)) * B i := by
  intro F _ _ _ _ ϖ hϖ ψ hψ U R Q χ a B hB
  haveI := finite_quotient_span_pow' hϖ a
  letI : Fintype (𝒪[F] ⧸ Ideal.span {ϖ ^ a}) := Fintype.ofFinite _
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  set q := _root_.GlobalTheory.HL.resQ ϖ with hqdef
  set rep := _root_.GlobalTheory.HL.CharCond.rep ϖ a with hrep
  set g : (𝒪[F] ⧸ Ideal.span {ϖ ^ a}) → ℂ :=
    fun r => ∑ u ∈ R, ψ ((rep r : F) / (ϖ : F) ^ a * Q u) * χ u with hg
  have hcard : Fintype.card (𝒪[F] ⧸ Ideal.span {ϖ ^ a}) = q ^ a := by
    rw [← Nat.card_eq_fintype_card, card_quotient_pow_eq_resQ_pow hϖ]
  have hsumall : ∑ r, g r = (∑ u ∈ R.filter (fun u => ϖ ^ a ∣ Q u), χ u) * (q : ℂ) ^ a := by
    have hinner : ∀ u, ∑ r, ψ ((rep r : F) / (ϖ : F) ^ a * Q u) =
        if ϖ ^ a ∣ Q u then (q : ℂ) ^ a else 0 := by
      intro u
      have hc : ((Q u : F) / (ϖ : F) ^ a) * (ϖ : F) ^ a ∈ 𝒪[F] := by
        rw [div_mul_cancel₀ _ (pow_ne_zero _ hϖ0)]; exact (Q u).2
      have e := sum_addChar_rep_mul_eq_ite hψ a hc
      have hiff : ((Q u : F) / (ϖ : F) ^ a ∈ 𝒪[F]) ↔ ϖ ^ a ∣ Q u := by
        constructor
        · intro h
          refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
          push_cast
          field_simp
        · rintro ⟨w, hw⟩
          rw [hw]
          push_cast
          rw [mul_div_cancel_left₀ _ (pow_ne_zero _ hϖ0)]
          exact w.2
      calc ∑ r, ψ ((rep r : F) / (ϖ : F) ^ a * Q u)
          = ∑ r, ψ ((rep r : F) * ((Q u : F) / (ϖ : F) ^ a)) :=
            Finset.sum_congr rfl (fun r _ => by rw [div_mul_eq_mul_div, mul_div_assoc])
        _ = _ := by
            rw [e, hcard]
            by_cases h : ϖ ^ a ∣ Q u
            · rw [if_pos (hiff.2 h), if_pos h]; push_cast; rfl
            · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
    simp only [hg]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hinner]
    rw [Finset.sum_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    split_ifs <;> ring
  have hzero : g 0 = ∑ u ∈ R, χ u := by
    refine Finset.sum_congr rfl (fun u _ => ?_)
    have h0 := mk_rep_eq ϖ a 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h0
    obtain ⟨w, hw⟩ := h0
    have : (rep 0 : F) / (ϖ : F) ^ a * Q u = ((w * Q u : 𝒪[F]) : F) := by
      rw [hrep, ← hw]; push_cast; field_simp
    rw [this, addChar_eq_one_of_mem_integer hψ (w * Q u).2, one_mul]
  set D : ℕ → Finset (𝒪[F] ⧸ Ideal.span {ϖ ^ a}) :=
    fun k => Finset.univ.filter (fun r => ϖ ^ k ∣ rep r) with hD
  have hDa : D a = {0} := by
    ext r
    simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, hrep,
      mk_rep_eq]
  have hD0 : D 0 = Finset.univ := by
    ext r; simp [hD]
  have key : ∀ j, j ≤ a → ‖∑ r ∈ D (a - j), g r - g 0‖ ≤
      ∑ i ∈ Finset.Icc 1 j, ((q : ℝ) ^ i - (q : ℝ) ^ (i - 1)) * B i := by
    intro j
    induction j with
    | zero => intro _; simp [hDa]
    | succ j ih =>
      intro hj
      set k := a - (j + 1) with hk
      have hkj : a - j = k + 1 := by omega
      have hsub : D (k + 1) ⊆ D k := by
        intro r hr
        simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
        exact (pow_dvd_pow ϖ (Nat.le_succ k)).trans hr
      rw [hkj] at ih
      have ih' := ih (by omega)
      rw [← Finset.sum_sdiff hsub, add_sub_assoc, Finset.sum_Icc_succ_top (by omega)]
      have hlev : ∀ r ∈ D k \ D (k + 1), ‖g r‖ ≤ B (j + 1) := by
        intro r hr
        simp only [hD, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hr
        obtain ⟨u₀, hu₀⟩ := exists_unit_of_exact_valuation_level hϖ (k := k) (i := j + 1) (a := a)
          (by omega) hr.1 hr.2
        exact hB (j + 1) (by omega) hj _ u₀ hu₀
      have hcd : ((D k \ D (k + 1)).card : ℝ) = (q : ℝ) ^ (j + 1) - (q : ℝ) ^ (j + 1 - 1) := by
        rw [Finset.card_sdiff_of_subset hsub]
        have c1 : (D k).card = q ^ (j + 1) := by
          rw [hD]; simp only; rw [card_filter_pow_dvd_rep_eq_resQ_pow hϖ (by omega)]; congr 1; omega
        have c2 : (D (k + 1)).card = q ^ j := by
          rw [hD]; simp only; rw [card_filter_pow_dvd_rep_eq_resQ_pow hϖ (by omega)]; congr 1; omega
        rw [c1, c2, Nat.add_sub_cancel]
        have : q ^ j ≤ q ^ (j + 1) :=
          Nat.pow_le_pow_right (resQ_pos_flag_measures hϖ) (Nat.le_succ j)
        push_cast [this]
        ring
      have hbound : ‖∑ r ∈ D k \ D (k + 1), g r‖ ≤
          ((q : ℝ) ^ (j + 1) - (q : ℝ) ^ (j + 1 - 1)) * B (j + 1) := by
        rw [← hcd]
        refine (norm_sum_le _ _).trans ?_
        have := Finset.sum_le_card_nsmul _ _ _ hlev
        rwa [nsmul_eq_mul] at this
      calc ‖∑ r ∈ D k \ D (k + 1), g r + (∑ r ∈ D (k + 1), g r - g 0)‖
          ≤ ‖∑ r ∈ D k \ D (k + 1), g r‖ + ‖∑ r ∈ D (k + 1), g r - g 0‖ := norm_add_le _ _
        _ ≤ _ := by linarith
  have := key a le_rfl
  rw [Nat.sub_self, hD0, hzero, hsumall] at this
  exact this

end GlobalTheory.HL.CharCond
end

section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory

theorem two_geometric_sums_index_bound :
    ∀ (q ρ a : ℕ), 2 ≤ q → 4 ≤ ρ →
      (∑ i ∈ Finset.Icc 1 a, ((q : ℝ) ^ i - (q : ℝ) ^ (i - 1)) * (q : ℝ) ^ (-(i * ρ : ℤ))
        ≤ 8 / 7 * (q : ℝ) ^ (1 - (ρ : ℤ))) ∧
      ∀ j : ℕ, 1 + ∑ i ∈ Finset.Icc 1 a,
        ((q : ℝ) ^ i - (q : ℝ) ^ (i - 1)) * (q : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ))
          ≤ 8 / 7 * (q : ℝ) ^ j := by
  intro q ρ a hq hρ
  have hQ : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hQ0 : (0:ℝ) < q := by linarith
  have hQ1 : (1:ℝ) ≤ q := by linarith
  set r : ℝ := (q:ℝ) ^ (1 - (ρ:ℤ)) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr8 : r ≤ 1 / 8 := by
    have h1 : r ≤ (q:ℝ) ^ (-3:ℤ) := zpow_le_zpow_right₀ hQ1 (by omega)
    have h2 : (q:ℝ) ^ (-3:ℤ) = ((q:ℝ) ^ 3)⁻¹ := by norm_num [zpow_neg]
    have h3 : (8:ℝ) ≤ (q:ℝ) ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num) hQ 3
      norm_num at this
      linarith
    have h4 : ((q:ℝ) ^ 3)⁻¹ ≤ (8:ℝ)⁻¹ := inv_anti₀ (by norm_num) h3
    rw [h2] at h1
    linarith [show (8:ℝ)⁻¹ = 1 / 8 by norm_num]
  have key : ∀ i : ℕ, (q:ℝ) ^ i * (q:ℝ) ^ (-(i * ρ : ℤ)) = r ^ i := by
    intro i
    rw [hr, ← zpow_natCast ((q:ℝ)) i, ← zpow_natCast ((q:ℝ) ^ (1 - (ρ:ℤ))) i, ← zpow_mul,
      ← zpow_add₀ hQ0.ne']
    congr 1
    ring
  refine ⟨?_, ?_⟩
  · have hterm : ∀ i ∈ Finset.Icc 1 a,
        ((q:ℝ) ^ i - (q:ℝ) ^ (i - 1)) * (q:ℝ) ^ (-(i * ρ : ℤ)) ≤ r ^ i := by
      intro i _
      rw [← key i]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have : (0:ℝ) ≤ (q:ℝ) ^ (i - 1) := by positivity
      linarith
    have hgeom : ∑ i ∈ Finset.Icc 1 a, r ^ i ≤ r ^ 1 / (1 - r) := by
      have hIcc : Finset.Icc 1 a = Finset.Ico 1 (a + 1) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hIcc]
      exact geom_sum_Ico_le_of_lt_one hr0 (by linarith)
    have hfrac : r ^ 1 / (1 - r) ≤ 8 / 7 * r := by
      rw [pow_one, div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg hr0 (show (0:ℝ) ≤ 1 / 8 - r by linarith)]
    linarith [Finset.sum_le_sum hterm]
  · intro j
    have main : ∀ n : ℕ, 1 + ∑ i ∈ Finset.Icc 1 n,
          ((q : ℝ) ^ i - (q : ℝ) ^ (i - 1)) * (q : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ))
          ≤ (q:ℝ) ^ (min n j) + 1 / 7 * (q:ℝ) ^ j * (1 - (1 / 8 : ℝ) ^ (n - j)) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc]
        rcases Nat.lt_or_ge n j with h | h
        · have e1 : n + 1 - j = 0 := by omega
          have e2 : n - j = 0 := by omega
          have e3 : min (n + 1) j = n + 1 := by omega
          have e4 : min n j = n := by omega
          rw [e1, e3, Nat.add_sub_cancel]
          rw [e2, e4] at ih
          simp only [Nat.cast_zero, zero_mul, neg_zero, zpow_zero, mul_one, pow_zero, sub_self,
            mul_zero, add_zero] at ih ⊢
          linarith
        · have e1 : n + 1 - j = (n - j) + 1 := by omega
          have e3 : min (n + 1) j = j := by omega
          have e4 : min n j = j := by omega
          rw [e4] at ih
          rw [e3, Nat.add_sub_cancel]
          have hterm : ((q:ℝ) ^ (n + 1) - (q:ℝ) ^ n) * (q:ℝ) ^ (-(((n + 1 - j : ℕ) : ℤ) * ρ))
              ≤ (q:ℝ) ^ j * ((1 / 8 : ℝ) ^ (n - j) * (1 / 8)) := by
            have hk := key ((n - j) + 1)
            rw [← e1] at hk
            calc ((q:ℝ) ^ (n + 1) - (q:ℝ) ^ n) * (q:ℝ) ^ (-(((n + 1 - j : ℕ) : ℤ) * ρ))
                ≤ (q:ℝ) ^ (n + 1) * (q:ℝ) ^ (-(((n + 1 - j : ℕ) : ℤ) * ρ)) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  have : (0:ℝ) ≤ (q:ℝ) ^ n := by positivity
                  linarith
              _ = (q:ℝ) ^ j * ((q:ℝ) ^ (n + 1 - j) * (q:ℝ) ^ (-(((n + 1 - j : ℕ) : ℤ) * ρ))) := by
                  rw [← mul_assoc, ← pow_add]
                  congr 2
                  omega
              _ = (q:ℝ) ^ j * r ^ (n + 1 - j) := by rw [hk]
              _ ≤ (q:ℝ) ^ j * ((1 / 8 : ℝ) ^ (n - j) * (1 / 8)) := by
                  rw [e1, ← pow_succ]
                  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr8 _) (by positivity)
          have h8 : (1 / 8 : ℝ) ^ (n + 1 - j) = (1 / 8) ^ (n - j) * (1 / 8) := by
            rw [e1, pow_succ]
          rw [h8]
          linarith
    have hmin : (q:ℝ) ^ (min a j) ≤ (q:ℝ) ^ j := pow_le_pow_right₀ hQ1 (min_le_right _ _)
    have hX : (0:ℝ) ≤ (q:ℝ) ^ j := by positivity
    have hY : (0:ℝ) ≤ (1 / 8 : ℝ) ^ (a - j) := by positivity
    nlinarith [main a, mul_nonneg hX hY]

end GlobalTheory
end

section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical ComplexConjugate

namespace GlobalTheory.HL.GaussSummand

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem hf_add_left (x y z : Fin n → E) : hf L Hm (x + y) z = hf L Hm x z + hf L Hm y z := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_add_right (x y z : Fin n → E) : hf L Hm x (y + z) = hf L Hm x y + hf L Hm x z := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_left (c : E) (x z : Fin n → E) : hf L Hm (c • x) z = c * hf L Hm x z := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_smul_right (c : E) (x z : Fin n → E) : hf L Hm x (c • z) = L.cj c * hf L Hm x z := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hf_zero_left (z : Fin n → E) : hf L Hm 0 z = 0 := by
  simp [hf]

theorem hf_sum_left {ι : Type*} (s : Finset ι) (x : ι → Fin n → E) (z : Fin n → E) :
    hf L Hm (∑ a ∈ s, x a) z = ∑ a ∈ s, hf L Hm (x a) z := by
  induction s using Finset.induction_on with
  | empty => simp [hf_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_add_left, ih]

theorem cj_hf (h : IsHerm L Hm) (x y : Fin n → E) : L.cj (hf L Hm x y) = hf L Hm y x := by
  have h' : ∀ i j, L.cj (Hm j i) = Hm i j := fun i j => congrFun (congrFun h i) j
  simp only [hf, map_sum, map_mul, L.cj_cj, h']
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end

theorem norm_gauss_sum_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (ψ : AddChar F ℂ), (∀ x : F, ‖ψ x‖ = 1) → (∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) → ∀ (UU : Submodule L.O (Fin n → E)), (∀ x ∈ UU, ∀ y ∈ UU, hf L Hm x y ∈ L.O) → ∀ (ρ : ℕ) (e : Fin ρ → Fin n → E), (∀ a, e a ∈ UU) → (∀ a b, hf L Hm (e a) (e b) = if a = b then 1 else 0) → ∀ (i N : ℕ), 1 ≤ i → i ≤ N → ∀ (t : F) (u₀ : (𝒪[F])ˣ), t * (ϖ : F) ^ i = ((u₀ : 𝒪[F]) : F) → ∀ (χ : AddChar (Fin n → E) ℂ), (∀ u, ‖χ u‖ = 1) → (∀ u ∈ UU, χ (algebraMap F E ((ϖ : F) ^ N) • u) = 1) → ∀ (R : Finset (Fin n → E)) (nrm : (Fin n → E) → F), (∀ u, algebraMap F E (nrm u) = hf L Hm u u) → (∀ u ∈ R, u ∈ UU) → (∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((ϖ : F) ^ N) • y) → ‖∑ u ∈ R, ψ (t * nrm u) * χ u‖ ≤ (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(i * ρ : ℤ)) := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH ϖ hϖ ψ hψ1 hψ UU hUU d e heU hee i N _ hiN t u₀ ht χ hχ1 hχ
    R nrm hnrm hRO hR
  obtain ⟨-, -, hdual, -, hint, hcard, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  have hO : ∀ c : 𝒪[F], algebraMap F E c ∈ L.O := fun c => (hint c).2 c.2
  have hsm : ∀ c ∈ L.O, ∀ x ∈ UU, c • x ∈ UU := fun c hc x hx =>
    UU.smul_mem (⟨c, hc⟩ : L.O) hx
  let I : ℕ → Ideal L.O := fun j => Ideal.span {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)}
  have hI : ∀ j (x : L.O), x ∈ I j ↔ ∃ c ∈ L.O, (x : E) = algebraMap F E ((ϖ : F) ^ j) * c := by
    intro j x
    have hset : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)}
        = {⟨algebraMap F E ((ϖ : F) ^ j), hO (ϖ ^ j)⟩} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Subtype.ext_iff]
    simp only [I]
    rw [hset, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, c.2, congrArg Subtype.val hc⟩
    · rintro ⟨c, hc, h⟩
      exact ⟨⟨c, hc⟩, Subtype.ext h⟩
  let P₀ : AddSubgroup (Fin d → L.O) := AddSubgroup.pi Set.univ fun _ => (I i).toAddSubgroup
  have hP₀ : ∀ x, x ∈ P₀ ↔ ∀ a, ∃ c ∈ L.O, (x a : E) = algebraMap F E ((ϖ : F) ^ i) * c := by
    intro x
    simp only [P₀, AddSubgroup.mem_pi, Set.mem_univ, true_implies, Submodule.mem_toAddSubgroup, hI]
  have hidx₀ : P₀.index = (resQ ϖ ^ (i * d)) ^ 2 := by
    have : (I i).toAddSubgroup.index = resQ ϖ ^ (2 * i) := hcard i
    simp only [P₀]
    rw [AddSubgroup.index_pi, Finset.prod_const, this, Finset.card_univ, Fintype.card_fin]
    ring
  let φ : UU →+ (Fin d → L.O) :=
    { toFun := fun m a => ⟨hf L Hm m (e a), hUU _ m.2 _ (heU a)⟩
      map_zero' := funext fun a => Subtype.ext (hf_zero_left L Hm _)
      map_add' := fun x y => funext fun a => Subtype.ext (hf_add_left L Hm _ _ _) }
  have hφ : Function.Surjective φ := fun c => by
    refine ⟨⟨∑ b, (c b : E) • e b, UU.sum_mem fun b _ => hsm _ (c b).2 _ (heU b)⟩,
      funext fun a => Subtype.ext ?_⟩
    show hf L Hm (∑ b, (c b : E) • e b) (e a) = c a
    simp [hf_sum_left, hf_smul_left, hee]
  let Q : AddSubgroup UU := P₀.comap φ
  have hQ : ∀ x : UU, x ∈ Q ↔
      ∀ a, ∃ c ∈ L.O, hf L Hm x (e a) = algebraMap F E ((ϖ : F) ^ i) * c := fun x => hP₀ (φ x)
  have hidx : Q.index = (resQ ϖ ^ (i * d)) ^ 2 := by
    rw [← hidx₀]; exact AddSubgroup.index_comap_of_surjective P₀ hφ
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hiN
  let P : AddSubgroup UU :=
    { carrier := {x | ∃ y ∈ UU, (x : Fin n → E) = algebraMap F E ((ϖ : F) ^ (i + k)) • y}
      zero_mem' := ⟨0, UU.zero_mem, by simp⟩
      add_mem' := by
        rintro x y ⟨x', hx', hx⟩ ⟨y', hy', hy⟩
        exact ⟨x' + y', UU.add_mem hx' hy', by rw [Submodule.coe_add, hx, hy, smul_add]⟩
      neg_mem' := by
        rintro x ⟨x', hx', hx⟩
        exact ⟨-x', UU.neg_mem hx', by rw [Submodule.coe_neg, hx, smul_neg]⟩ }
  have hP : ∀ x : UU, x ∈ P ↔
      ∃ y ∈ UU, (x : Fin n → E) = algebraMap F E ((ϖ : F) ^ (i + k)) • y := fun _ => Iff.rfl
  have hPQ : P ≤ Q := fun x hx => (hQ x).2 fun a => by
    obtain ⟨y, hy, h⟩ := (hP x).1 hx
    refine ⟨algebraMap F E ((ϖ : F) ^ k) * hf L Hm y (e a),
      L.O.mul_mem (hO (ϖ ^ k)) (hUU _ hy _ (heU a)), ?_⟩
    rw [h, hf_smul_left, pow_add, map_mul, mul_assoc]
  have hιinj : Function.Injective (Subtype.val : UU → Fin n → E) := Subtype.val_injective
  have hrange : ∀ u ∈ R, u ∈ Set.range (Subtype.val : UU → Fin n → E) :=
    fun u hu => ⟨⟨u, hRO u hu⟩, rfl⟩
  let R' := R.preimage (Subtype.val : UU → Fin n → E) hιinj.injOn
  have hτ : algebraMap F E t * algebraMap F E ((ϖ : F) ^ i)
      = algebraMap F E ((u₀ : 𝒪[F]) : F) := by rw [← map_mul, ht]
  have key := GaussSum.sq_norm_sum_reps_mul_index_le P Q hPQ R' ?_
    (fun m => ψ (t * nrm m) * χ m) (fun m => by rw [norm_mul, hψ1, hχ1, mul_one]) ?_ ?_
  · rw [Finset.sum_preimage Subtype.val R hιinj.injOn (fun u => ψ (t * nrm u) * χ u)
      (fun u hu h => (h (hrange u hu)).elim), Finset.card_preimage, hidx,
      Finset.filter_true_of_mem hrange, Nat.cast_pow, ← mul_pow] at key
    have hq0 : (0 : ℝ) < resQ ϖ := by exact_mod_cast (by omega : 0 < resQ ϖ)
    have h := (sq_le_sq₀ (by positivity) (by positivity)).1 key
    rw [zpow_neg, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact_mod_cast h
  · intro u
    obtain ⟨w, ⟨hw, hw'⟩, huniq⟩ := hR u u.2
    obtain ⟨w, rfl⟩ := hrange w hw
    refine ⟨w, ⟨Finset.mem_preimage.2 hw, (hP _).2 hw'⟩, fun y hy => hιinj ?_⟩
    exact huniq _ ⟨Finset.mem_preimage.1 hy.1, (hP _).1 hy.2⟩
  · intro u p hp
    obtain ⟨c, hc, hpc⟩ := (hP p).1 hp
    have h1 : χ p = 1 := by rw [hpc, hχ c hc]
    have h3 : t * (nrm (u + p) - nrm u) ∈ 𝒪[F] := by
      rw [← hint, map_mul, map_sub, hnrm, hnrm]
      have : algebraMap F E t * (hf L Hm (u + p) (u + p) - hf L Hm u u)
          = algebraMap F E ((u₀ : 𝒪[F]) : F) * algebraMap F E ((ϖ : F) ^ k)
            * (hf L Hm c (u + p) + hf L Hm u c) := by
        have e1 : hf L Hm p (u + p) = algebraMap F E ((ϖ : F) ^ (i + k)) * hf L Hm c (u + p) := by
          rw [← hf_smul_left, ← hpc]
        have e2 : hf L Hm u p = algebraMap F E ((ϖ : F) ^ (i + k)) * hf L Hm u c := by
          rw [hpc, hf_smul_right, AlgEquiv.commutes]
        rw [hf_add_left, e1, hf_add_right L Hm u u p, e2, ← hτ, pow_add, map_mul]
        ring
      rw [this]
      exact L.O.mul_mem (L.O.mul_mem (hO _) (hO (ϖ ^ k)))
        (L.O.add_mem (hUU _ hc _ (UU.add_mem u.2 p.2)) (hUU _ u.2 _ hc))
    have h4 := (hψ _).2 h3 1
    have h5 : t * nrm (u + p) = t * nrm u
        + t * (nrm (u + p) - nrm u) * ((1 : 𝒪[F]) : F) := by
      push_cast; ring
    show ψ (t * nrm (u + p)) * χ (u + p) = _
    rw [h5, AddChar.map_add_eq_mul, h4, mul_one, AddChar.map_add_eq_mul, h1, mul_one]
  · intro h hh
    obtain ⟨a, ha⟩ := not_forall.1 fun h' => hh ((hQ h).2 h')
    obtain ⟨z, hz⟩ : ∃ z, z = hf L Hm h (e a) := ⟨_, rfl⟩
    rw [← hz] at ha
    have h1 : algebraMap F E t * z ∉ L.O := fun h' => ha
      ⟨algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * (algebraMap F E t * z),
        L.O.mul_mem (hO _) h', by
          have h2 : algebraMap F E ((u₀ : 𝒪[F]) : F)
              * algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) = 1 := by
            rw [← map_mul, ← Subring.coe_mul, Units.mul_inv]; simp
          linear_combination (-z) * h2
            - algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * z * hτ⟩
    obtain ⟨b, hb⟩ := not_forall.1 fun h' => h1 (hdual _ h')
    obtain ⟨hb, hb'⟩ := Classical.not_imp.1 hb
    obtain ⟨s, hs⟩ := (L.cj_fix (algebraMap F E t * z * L.cj b
      + L.cj (algebraMap F E t * z * L.cj b))).1 (by rw [map_add, L.cj_cj, add_comm])
    have hs' : s ∉ 𝒪[F] := fun h' => hb' ⟨⟨s, h'⟩, hs.symm⟩
    obtain ⟨y, hy⟩ := not_forall.1 fun h' => hs' ((hψ s).1 h')
    let v : UU := ⟨(algebraMap F E y * b) • e a, hsm _ (L.O.mul_mem (hO y) hb) _ (heU a)⟩
    refine ⟨v, ψ (s * y), hy, fun u => ?_⟩
    have h2 : t * nrm (u + v + h) - t * nrm (u + v)
        = s * y + (t * nrm (u + h) - t * nrm u) := by
      apply hinj
      have h3 : hf L Hm v h = algebraMap F E y * b * L.cj z := by
        rw [hz, cj_hf L Hm hH.1]
        exact hf_smul_left L Hm _ _ _
      have h3' : hf L Hm h v = algebraMap F E y * L.cj b * z := by
        rw [← cj_hf L Hm hH.1, h3]
        simp only [map_mul, AlgEquiv.commutes, L.cj_cj]
      simp only [map_mul, AlgEquiv.commutes, L.cj_cj] at hs
      simp only [map_sub, map_add (algebraMap F E), map_mul, hnrm, hs, hf_add_left, hf_add_right,
        h3, h3']
      ring
    have h4 : (u : Fin n → E) + v + h - (u + v) = u + h - u := by abel
    simp only [map_mul, Submodule.coe_add]
    rw [mul_mul_mul_comm, GaussSum.mul_conj_eq ψ hψ1, GaussSum.mul_conj_eq χ hχ1,
      mul_mul_mul_comm, GaussSum.mul_conj_eq ψ hψ1, GaussSum.mul_conj_eq χ hχ1, h2, h4,
      AddChar.map_add_eq_mul, mul_assoc]

end GlobalTheory.HL.GaussSummand
end

section
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.QuadricShare

open GlobalTheory.HL.GaussSummand

theorem sum_char_eq_zero {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {O : Subring E}
    (UU : Submodule O V) (p : E) (R : Finset V) (hRU : ∀ u ∈ R, u ∈ UU)
    (hR : ∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = p • y) (χ : AddChar V ℂ)
    (hχ : ∀ u ∈ UU, χ (p • u) = 1) (u₀ : V) (hu₀ : u₀ ∈ R) (hne : χ u₀ ≠ 1) :
    ∑ u ∈ R, χ u = 0 := by
  have hex : ∀ w ∈ R, ∃ w', w' ∈ R ∧ ∃ y ∈ UU, (w + u₀) - w' = p • y := fun w hw =>
    (hR _ (UU.add_mem (hRU w hw) (hRU u₀ hu₀))).exists
  choose! σ hσR hσ using hex
  have hinj : Set.InjOn σ R := by
    intro w hw w' hw' h
    obtain ⟨y, hy, e⟩ := hσ w hw
    obtain ⟨y', hy', e'⟩ := hσ w' hw'
    refine (hR w (hRU w hw)).unique ⟨hw, 0, UU.zero_mem, by simp⟩ ⟨hw', y - y', UU.sub_mem hy hy', ?_⟩
    rw [smul_sub, ← e, ← e', h]; abel
  have himg : R.image σ = R := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
      exact hσR w hw
    · rw [Finset.card_image_of_injOn hinj]
  have h1 : ∑ u ∈ R, χ u = ∑ u ∈ R, χ u * χ u₀ := by
    conv_lhs => rw [← himg, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun w hw => ?_
    obtain ⟨y, hy, e⟩ := hσ w hw
    have : w + u₀ = σ w + p • y := by rw [← e]; abel
    rw [← AddChar.map_add_eq_mul, this, AddChar.map_add_eq_mul, hχ y hy, mul_one]
  rw [← Finset.sum_mul] at h1
  have h2 : (∑ u ∈ R, χ u) * (1 - χ u₀) = 0 := by rw [mul_sub, mul_one, ← h1, sub_self]
  exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hne.symm)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
  {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem exists_norm (hH : IsHermND L Hm) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    (UU : Submodule L.O (Fin n → E)) (hUU : ∀ x ∈ UU, ∀ y ∈ UU, hf L Hm x y ∈ L.O) :
    ∃ (nrm : (Fin n → E) → F) (Q : (Fin n → E) → 𝒪[F]), (∀ u, algebraMap F E (nrm u) = hf L Hm u u) ∧
      (∀ u ∈ UU, (Q u : F) = nrm u) ∧
      ∀ (a : ℕ), ∀ u ∈ UU, (ϖ ^ a ∣ Q u ↔ ∃ c : 𝒪[F], hf L Hm u u = algebraMap F E ((ϖ : F) ^ a * c)) := by
  obtain ⟨-, -, -, -, hint, -, -, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  choose nrm hnrm using fun u : Fin n → E => (L.cj_fix _).1 (cj_hf L Hm hH.1 u u)
  have hQ : ∀ u ∈ UU, nrm u ∈ 𝒪[F] := fun u hu => (hint _).1 (by rw [hnrm]; exact hUU u hu u hu)
  refine ⟨nrm, fun u => if h : nrm u ∈ 𝒪[F] then ⟨nrm u, h⟩ else 0, hnrm, fun u hu => ?_,
    fun a u hu => ?_⟩
  · simp only [dif_pos (hQ u hu)]
  · simp only [dif_pos (hQ u hu)]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have := congrArg (fun x : 𝒪[F] => (x : F)) hc
      simp only [Subring.coe_mul, SubmonoidClass.coe_pow] at this
      rw [← hnrm, this]
    · rintro ⟨c, hc⟩
      rw [← hnrm] at hc
      exact ⟨c, Subtype.ext (by simpa using hinj hc)⟩

theorem char_share (hH : IsHermND L Hm) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    (UU : Submodule L.O (Fin n → E)) (hUU : ∀ x ∈ UU, ∀ y ∈ UU, hf L Hm x y ∈ L.O)
    (ρ : ℕ) (hρ : 4 ≤ ρ) (e : Fin ρ → Fin n → E) (he : ∀ a, e a ∈ UU)
    (hee : ∀ a b, hf L Hm (e a) (e b) = if a = b then 1 else 0) (a N : ℕ) (haN : a ≤ N)
    (R : Finset (Fin n → E)) (hRU : ∀ u ∈ R, u ∈ UU)
    (hR : ∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((ϖ : F) ^ N) • y)
    (Z : (Fin n → E) → Prop)
    (hZ : ∀ u, Z u ↔ ∃ c : 𝒪[F], hf L Hm u u = algebraMap F E ((ϖ : F) ^ a * c))
    (χ : AddChar (Fin n → E) ℂ) (hχ1 : ∀ u, ‖χ u‖ = 1)
    (hχ : ∀ u ∈ UU, χ (algebraMap F E ((ϖ : F) ^ N) • u) = 1) :
    ‖(∑ u ∈ R.filter Z, χ u) * (resQ ϖ : ℂ) ^ a - ∑ u ∈ R, χ u‖ ≤
      8 / 7 * (resQ ϖ : ℝ) ^ (1 - (ρ : ℤ)) * R.card := by
  obtain ⟨-, -, -, -, -, -, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨ψ, hψ1, hψ, -⟩ := GlobalTheory.TraceChar.exists_trace_char L
  obtain ⟨nrm, Q, hnrm, hQ, hdvd⟩ := exists_norm L Hm hH ϖ hϖ UU hUU
  have hfil : R.filter Z = R.filter (fun u => ϖ ^ a ∣ Q u) :=
    Finset.filter_congr fun u hu => by rw [hZ, hdvd a u (hRU u hu)]
  have h := GlobalTheory.HL.CharCond.expand_by_conductor ϖ hϖ ψ hψ R Q χ a
    (fun i => (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(i * ρ : ℤ))) (fun i hi hia t u₀ ht => by
      rw [Finset.sum_congr rfl fun u hu => by rw [hQ u (hRU u hu)]]
      exact norm_gauss_sum_le L Hm hH ϖ hϖ ψ hψ1 hψ UU hUU ρ e he hee i N hi (hia.trans haN) t u₀ ht
        χ hχ1 hχ R nrm hnrm hRU hR)
  rw [hfil]
  refine h.trans ?_
  have h2 := (GlobalTheory.two_geometric_sums_index_bound (resQ ϖ) ρ a hq hρ).1
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _))
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem prime_share (hH : IsHermND L Hm) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    (UU : Submodule L.O (Fin n → E)) (hUU : ∀ x ∈ UU, ∀ y ∈ UU, hf L Hm x y ∈ L.O)
    (ρ : ℕ) (hρ : 4 ≤ ρ) (e : Fin ρ → Fin n → E) (he : ∀ a, e a ∈ UU)
    (hee : ∀ a b, hf L Hm (e a) (e b) = if a = b then 1 else 0) (a N : ℕ) (haN : a ≤ N)
    (R : Finset (Fin n → E)) (hRU : ∀ u ∈ R, u ∈ UU)
    (hR : ∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((ϖ : F) ^ N) • y)
    (Z : (Fin n → E) → Prop)
    (hZ : ∀ u, Z u ↔ ∃ c : 𝒪[F], hf L Hm u u = algebraMap F E ((ϖ : F) ^ a * c))
    (π : E) (j : ℕ) (hπ : π ∈ L.O) (hπj : π * L.cj π = algebraMap F E ((ϖ : F) ^ j))
    (hπN : ∃ c ∈ L.O, algebraMap F E ((ϖ : F) ^ N) = π * c) :
    ((R.filter fun u => Z u ∧ ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c).card : ℝ) * (resQ ϖ : ℝ) ^ a ≤
      8 / 7 * (resQ ϖ : ℝ) ^ ((j : ℤ) - j * ρ) * R.card := by
  obtain ⟨-, -, -, -, -, -, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨ψ, hψ1, hψ, -⟩ := GlobalTheory.TraceChar.exists_trace_char L
  obtain ⟨nrm, Q, hnrm, hQ, hdvd⟩ := exists_norm L Hm hH ϖ hϖ UU hUU
  obtain ⟨hc, hg⟩ := GlobalTheory.T.hermitian_local_character_sum L Hm hH ϖ hϖ ψ hψ1 hψ UU hUU ρ e he hee π j N hπ hπj hπN R nrm hnrm
    hRU hR
  set R' := R.filter fun u => ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c with hR'
  have hfil : (R.filter fun u => Z u ∧ ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c)
      = R'.filter (fun u => ϖ ^ a ∣ Q u) := by
    rw [hR', Finset.filter_filter]
    exact Finset.filter_congr fun u hu => by rw [hZ, hdvd a u (hRU u hu), and_comm]
  have h := GlobalTheory.HL.CharCond.expand_by_conductor ϖ hϖ ψ hψ R' Q (fun _ => 1) a
    (fun i => (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) * (resQ ϖ : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ)))
    (fun i hi hia t u₀ ht => by
      rw [Finset.sum_congr rfl fun u hu => by
        rw [hQ u (hRU u (Finset.mem_filter.1 hu).1), mul_one]]
      exact hg i (hia.trans haN) t u₀ ht)
  rw [hfil]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have h1 : ((R'.filter (fun u => ϖ ^ a ∣ Q u)).card : ℝ) * (resQ ϖ : ℝ) ^ a - R'.card ≤
      ‖((R'.filter (fun u => ϖ ^ a ∣ Q u)).card : ℂ) * (resQ ϖ : ℂ) ^ a - R'.card‖ := by
    refine (le_abs_self _).trans (le_of_eq ?_)
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    push_cast; rfl
  have h2 := (GlobalTheory.two_geometric_sums_index_bound (resQ ϖ) ρ a hq hρ).2 j
  have hq0 : (0 : ℝ) < resQ ϖ := by exact_mod_cast (by omega : 0 < resQ ϖ)
  have h3 := mul_le_mul_of_nonneg_left h2
    (by positivity : (0 : ℝ) ≤ (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)))
  rw [mul_add, mul_one, Finset.mul_sum] at h3
  have h4 : ∑ i ∈ Finset.Icc 1 a, ((resQ ϖ : ℝ) ^ i - (resQ ϖ : ℝ) ^ (i - 1)) *
      ((R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) * (resQ ϖ : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ))) =
      ∑ i ∈ Finset.Icc 1 a, (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) *
      (((resQ ϖ : ℝ) ^ i - (resQ ϖ : ℝ) ^ (i - 1)) * (resQ ϖ : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ))) :=
    Finset.sum_congr rfl fun i _ => by ring
  have h5 : 8 / 7 * (resQ ϖ : ℝ) ^ ((j : ℤ) - j * ρ) * R.card =
      (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) * (8 / 7 * (resQ ϖ : ℝ) ^ j) := by
    rw [sub_eq_add_neg, zpow_add₀ hq0.ne', zpow_natCast]; ring
  rw [h5]
  rw [h4] at h
  linarith

theorem leak_share (hH : IsHermND L Hm) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    (UU : Submodule L.O (Fin n → E)) (hUU : ∀ x ∈ UU, ∀ y ∈ UU, hf L Hm x y ∈ L.O)
    (ρ : ℕ) (hρ : 4 ≤ ρ) (e : Fin ρ → Fin n → E) (W : Submodule L.O (Fin n → E)) (hW : W ≤ UU)
    (he : ∀ a, e a ∈ W)
    (hee : ∀ a b, hf L Hm (e a) (e b) = if a = b then 1 else 0) (a N : ℕ) (haN : a + 1 ≤ N)
    (R : Finset (Fin n → E)) (hRU : ∀ u ∈ R, u ∈ UU)
    (hR : ∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((ϖ : F) ^ N) • y)
    (Z : (Fin n → E) → Prop)
    (hZ : ∀ u, Z u ↔ ∃ c : 𝒪[F], hf L Hm u u = algebraMap F E ((ϖ : F) ^ a * c)) :
    ((R.filter fun u => Z u ∧ ¬ ∃ y ∈ W, hf L Hm u y = 1).card : ℝ) * (resQ ϖ : ℝ) ^ a ≤
      16 / 7 * (resQ ϖ : ℝ) ^ (1 - (ρ : ℤ)) * R.card := by
  obtain ⟨-, hcj, -, -, hint, -, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hq1 : (1 : ℝ) ≤ resQ ϖ := by exact_mod_cast (by omega : 1 ≤ resQ ϖ)
  have hp : algebraMap F E ϖ ∈ L.O := (hint _).2 ϖ.2
  have hps := prime_share L Hm hH ϖ hϖ UU hUU ρ hρ e (fun a => hW (he a)) hee a N (by omega) R hRU hR
    Z hZ
  have hI : ∀ u ∈ R, (¬ ∃ y ∈ W, hf L Hm u y = 1) → ∃ I : Ideal L.O, I ≠ ⊤ ∧
      ∀ a, ∃ x ∈ I, (x : E) = hf L Hm u (e a) := by
    intro u hu hne
    let I : Ideal L.O :=
      { carrier := {x | ∃ y ∈ W, hf L Hm u y = x}
        zero_mem' := ⟨0, W.zero_mem, by simp [hf]⟩
        add_mem' := by
          rintro x x' ⟨y, hy, e⟩ ⟨y', hy', e'⟩
          exact ⟨y + y', W.add_mem hy hy', by rw [hf_add_right, e, e']; rfl⟩
        smul_mem' := by
          rintro c x ⟨y, hy, e⟩
          refine ⟨L.cj c • y, CongFin.smul_mem_of W (hcj c c.2).1 hy, ?_⟩
          rw [hf_smul_right, L.cj_cj, e]; rfl }
    refine ⟨I, fun h => hne ((Ideal.eq_top_iff_one I).1 h), fun a => ?_⟩
    exact ⟨⟨_, hUU u (hRU u hu) _ (hW (he a))⟩, ⟨e a, he a, rfl⟩, rfl⟩
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hM : algebraMap F E ((ϖ : F) ^ M) ∈ L.O := by rw [map_pow]; exact L.O.pow_mem hp M
  have hqa : (0 : ℝ) ≤ (resQ ϖ : ℝ) ^ a := by positivity
  have hR0 : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  rcases GlobalTheory.UnramOrder.proper_ideals L ϖ hϖ with h | ⟨π, hπ, hππ, h⟩
  · have h1 := hps (algebraMap F E ϖ) 2 hp (by rw [AlgEquiv.commutes, ← map_mul, sq])
      ⟨_, hM, by rw [← map_mul, pow_succ']⟩
    have hsub : (R.filter fun u => Z u ∧ ¬ ∃ y ∈ W, hf L Hm u y = 1) ⊆
        R.filter fun u => Z u ∧ ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = algebraMap F E ϖ * c := by
      intro u hu
      obtain ⟨hu, hz, hne⟩ := Finset.mem_filter.1 hu
      obtain ⟨I, hI, hIe⟩ := hI u hu hne
      refine Finset.mem_filter.2 ⟨hu, hz, fun a => ?_⟩
      obtain ⟨x, hx, e⟩ := hIe a
      exact e ▸ h I hI x hx
    have h2 : ((R.filter fun u => Z u ∧ ¬ ∃ y ∈ W, hf L Hm u y = 1).card : ℝ) ≤ _ :=
      Nat.cast_le.2 (Finset.card_le_card hsub)
    have h3 : (resQ ϖ : ℝ) ^ (((2 : ℕ) : ℤ) - (2 : ℕ) * ρ) ≤ (resQ ϖ : ℝ) ^ (1 - (ρ : ℤ)) :=
      zpow_le_zpow_right₀ hq1 (by push_cast; omega)
    have h4 : (0 : ℝ) ≤ (resQ ϖ : ℝ) ^ (1 - (ρ : ℤ)) := by positivity
    refine (mul_le_mul_of_nonneg_right h2 hqa).trans (h1.trans ?_)
    exact mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_left h3 (by norm_num)).trans (by linarith only [h4])) hR0
  · have h1 := hps π 1 hπ (by rw [hππ, pow_one])
      ⟨L.cj π * algebraMap F E ((ϖ : F) ^ M), L.O.mul_mem (hcj π hπ).1 hM, by
        rw [← mul_assoc, hππ, ← map_mul, pow_succ']⟩
    have h1' := hps (L.cj π) 1 (hcj π hπ).1 (by rw [L.cj_cj, mul_comm, hππ, pow_one])
      ⟨π * algebraMap F E ((ϖ : F) ^ M), L.O.mul_mem hπ hM, by
        rw [← mul_assoc, mul_comm _ π, hππ, ← map_mul, pow_succ']⟩
    have hsub : (R.filter fun u => Z u ∧ ¬ ∃ y ∈ W, hf L Hm u y = 1) ⊆
        (R.filter fun u => Z u ∧ ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c) ∪
        (R.filter fun u => Z u ∧ ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = L.cj π * c) := by
      intro u hu
      obtain ⟨hu, hz, hne⟩ := Finset.mem_filter.1 hu
      obtain ⟨I, hI, hIe⟩ := hI u hu hne
      rcases h I hI with h | h
      · refine Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hu, hz, fun a => ?_⟩)
        obtain ⟨x, hx, e⟩ := hIe a
        exact e ▸ h x hx
      · refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hu, hz, fun a => ?_⟩)
        obtain ⟨x, hx, e⟩ := hIe a
        exact e ▸ h x hx
    have h2 : ((R.filter fun u => Z u ∧ ¬ ∃ y ∈ W, hf L Hm u y = 1).card : ℝ) ≤ _ :=
      Nat.cast_le.2 ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
    rw [Nat.cast_add] at h2
    have h3 := mul_le_mul_of_nonneg_right h2 hqa
    simp only [Nat.cast_one, one_mul] at h1 h1'
    rw [add_mul] at h3
    linarith

theorem integral_of_reps (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (Λ : Submodule L.O (Fin n → E))
    (hΛ : IsSD L Hm Λ) (UU : Submodule L.O (Fin n → E)) (hUΛ : UU ≤ Λ) (N : ℕ) (hN : 1 ≤ N)
    (R : Finset (Fin n → E))
    (hR : ∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((ϖ : F) ^ N) • y)
    (y : Fin n → E) (hy : ∀ u ∈ R, algebraMap F E ((ϖ : F) ^ N) * hf L Hm y u ∈ L.O) :
    ∀ u ∈ UU, algebraMap F E ((ϖ : F) ^ N) * hf L Hm y u ∈ L.O := by
  obtain ⟨-, -, -, -, hint, -, -, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hp : algebraMap F E ϖ ∈ L.O := (hint _).2 ϖ.2
  obtain ⟨M, hM⟩ := CongFin.exists_pow_smul_mem hp (CongFin.exists_pow_mul_mem L ϖ hϖ)
    (Submodule.span L.O {y}) Λ (Submodule.fg_span_singleton y) hΛ.1.2
  have hMy := hM y (Submodule.mem_span_singleton_self y)
  simp only [map_pow] at hR hy ⊢
  have hcp : L.cj (algebraMap F E ϖ ^ N) = algebraMap F E ϖ ^ N := by
    rw [map_pow, AlgEquiv.commutes]
  set p := algebraMap F E ϖ with hpdef
  have key : ∀ m : ℕ, (∀ u ∈ UU, p ^ m * (p ^ N * hf L Hm y u) ∈ L.O) →
      ∀ u ∈ UU, p ^ N * hf L Hm y u ∈ L.O := by
    intro m
    induction m with
    | zero => intro h u hu; simpa using h u hu
    | succ m ih =>
      intro h
      refine ih fun u hu => ?_
      obtain ⟨w, ⟨hw, z, hz, e⟩, -⟩ := hR u hu
      have e' : u = w + p ^ N • z := by rw [← e]; abel
      obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
      rw [e', hf_add_right, hf_smul_right, hcp]
      have := L.O.add_mem (L.O.mul_mem (L.O.pow_mem hp m) (hy w hw))
        (L.O.mul_mem (L.O.pow_mem hp K) (h z hz))
      convert this using 1
      ring
  refine key M fun u hu => ?_
  have h1 := (hΛ.2 u).2 (hUΛ hu) _ hMy
  rw [hf_smul_left] at h1
  rw [mul_left_comm]
  exact L.O.mul_mem (L.O.pow_mem hp N) h1

omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem perp_anti {A B : Submodule E (Fin n → E)} (h : A ≤ B) : perp L Hm B ≤ perp L Hm A :=
  fun _ hx y hy => hx y (h hy)

theorem shares : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (J : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (N : ℕ) (R : Finset S.V) (Z : S.V → Prop), S.a + 1 ≤ N → (∀ u, Z u ↔ ∃ c : 𝒪[F], S.h u u = algebraMap F E ((S.ϖ : F) ^ S.a * c)) → (∀ u ∈ R, u ∈ Λ ∧ u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)) → (∀ u ∈ Λ, u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J) → ∃! w, w ∈ R ∧ ∃ y ∈ Λ, u - w = algebraMap F E ((S.ϖ : F) ^ N) • y) → |((R.filter Z).card : ℝ) - R.card / (S.q : ℝ) ^ S.a| ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a) ∧ (((R.filter fun u => Z u ∧ ¬ ∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1).card : ℝ) ≤ 16 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a)) ∧ ∀ y : S.V, (∀ u ∈ R, algebraMap F E ((S.ϖ : F) ^ N) * S.h y u ∈ L.O) → (∃ u ∈ R, L.psi0 (S.h y u) ≠ 1) → ‖∑ u ∈ R.filter Z, L.psi0 (S.h y u)‖ ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk J d Λ hT N R Z haN hZ hRU hR
  obtain ⟨-, hcj, -, -, hint, -, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr
  have hSD := (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).1
  have hli := (GlobalTheory.FrameBasic.main L r k S).1
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).1
  rw [ha] at haN hZ ⊢
  simp only [zpow_natCast] at hZ ⊢
  have haN' : a + 1 ≤ N := by omega
  obtain ⟨e, he, hee⟩ := GlobalTheory.HL.OrthCompl.exists_orthonormal_perp L S.Hm S.herm Λ hSD _ _
    (hli.comp finSumFinEquiv.symm finSumFinEquiv.symm.injective)
  have hsp : ∀ j, S.spanTo S.f j ⊔ S.spanTo S.f' j ≤
      Submodule.span E (Set.range (Sum.elim S.f S.f' ∘ finSumFinEquiv.symm)) := by
    intro j
    rw [finSumFinEquiv.symm.surjective.range_comp]
    refine sup_le (Submodule.span_mono ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨i, -, rfl⟩; exact ⟨Sum.inl i, rfl⟩
    · rintro _ ⟨i, -, rfl⟩; exact ⟨Sum.inr i, rfl⟩
  let ρ := k + 2 * r + 1 - 2 * (r + 1 + (r + 1))
  have hρdef : ρ = k + 2 * r + 1 - 2 * (r + 1 + (r + 1)) := rfl
  have hρ : 4 ≤ ρ := by omega
  have hρ' : (k : ℤ) - 2 * r - 3 = ρ := by omega
  rw [hρ']
  let UU : Submodule L.O S.V :=
    Λ ⊓ (perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)).restrictScalars L.O
  let W : Submodule L.O S.V := Λ ⊓ S.W0.restrictScalars L.O
  have hJ : S.spanTo S.f J ⊔ S.spanTo S.f' J ≤ S.ME :=
    sup_le_sup (Submodule.span_mono (Set.image_mono fun i _ => i.2))
      (Submodule.span_mono (Set.image_mono fun i _ => i.2))
  have hW : W ≤ UU := fun x hx => ⟨hx.1, perp_anti L S.Hm hJ hx.2⟩
  have heW : ∀ i, e i ∈ W := fun i => ⟨(he i).1, perp_anti L S.Hm (hsp (r + 1)) (he i).2⟩
  have hUU : ∀ x ∈ UU, ∀ y ∈ UU, hf L S.Hm x y ∈ L.O := fun x hx y hy => (hSD.2 y).2 hy.1 x hx.1
  have hRU' : ∀ u ∈ R, u ∈ UU := hRU
  have hu : IsUnit (algebraMap F E ((S.ϖ : F) ^ N)) :=
    ((IsUnit.mk0 (S.ϖ : F) (fun h => S.ϖ_irr.ne_zero (Subtype.ext h))).pow N).map _
  have hR' : ∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((S.ϖ : F) ^ N) • y := by
    intro u hu'
    refine (existsUnique_congr fun w => and_congr_right fun hw => ?_).1 (hR u hu'.1 hu'.2)
    constructor
    · rintro ⟨y, hy, e⟩
      refine ⟨y, ⟨hy, ?_⟩, e⟩
      have h1 : algebraMap F E ((S.ϖ : F) ^ N) • y ∈
          perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J) :=
        e ▸ Submodule.sub_mem _ hu'.2 (hRU w hw).2
      exact (Submodule.smul_mem_iff_of_isUnit _ hu).1 h1
    · rintro ⟨y, hy, e⟩
      exact ⟨y, hy.1, e⟩
  have hcs := char_share L S.Hm S.herm S.ϖ S.ϖ_irr UU hUU ρ hρ e (fun i => hW (heW i)) hee a N
    (by omega) R hRU' hR' Z hZ
  have hqa : (0 : ℝ) < (S.q : ℝ) ^ a := by
    have : (0 : ℝ) < S.q := by exact_mod_cast (by omega : 0 < resQ S.ϖ)
    positivity
  refine ⟨?_, ?_, fun y hy ⟨u₀, hu₀, hne⟩ => ?_⟩
  · have h := hcs 1 (by simp) (by simp)
    simp only [AddChar.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    have h1 : ‖((R.filter Z).card : ℂ) * (resQ S.ϖ : ℂ) ^ a - R.card‖ =
        |((R.filter Z).card : ℝ) * (S.q : ℝ) ^ a - R.card| := by
      rw [← Real.norm_eq_abs, ← Complex.norm_real]
      push_cast; rfl
    rw [h1] at h
    rw [← mul_div_assoc, le_div_iff₀ hqa, ← abs_of_pos hqa, ← abs_mul, abs_of_pos hqa, sub_mul,
      div_mul_cancel₀ _ hqa.ne']
    exact h
  · have h := leak_share L S.Hm S.herm S.ϖ S.ϖ_irr UU hUU ρ hρ e W hW heW hee a N haN' R hRU' hR' Z hZ
    rw [← mul_div_assoc, le_div_iff₀ hqa]
    refine le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Finset.card_le_card ?_)) hqa.le) h
    intro u hu'
    simp only [Finset.mem_filter] at hu' ⊢
    refine ⟨hu'.1, hu'.2.1, ?_⟩
    rintro ⟨y, ⟨h1, h2⟩, h3⟩
    exact hu'.2.2 ⟨y, h1, h2, h3⟩
  · obtain ⟨ψ, hψ1, -, hψ⟩ := GlobalTheory.TraceChar.exists_trace_char L
    let φ : S.V →+ E := AddMonoidHom.mk' (fun u => hf L S.Hm y u) (hf_add_right L S.Hm y)
    let χ : AddChar S.V ℂ := L.psi0.compAddMonoidHom φ
    have hχ1 : ∀ u, ‖χ u‖ = 1 := fun u => by
      obtain ⟨c, hc⟩ := (L.cj_fix (φ u + L.cj (φ u))).1 (by rw [map_add, L.cj_cj, add_comm])
      change ‖L.psi0 (φ u)‖ = 1
      rw [hψ _ c hc.symm, hψ1]
    have hint' := integral_of_reps L S.Hm S.ϖ S.ϖ_irr Λ hSD UU inf_le_left N (by omega) R hR' y hy
    have hχ : ∀ u ∈ UU, χ (algebraMap F E ((S.ϖ : F) ^ N) • u) = 1 := fun u hu' => by
      change L.psi0 (hf L S.Hm y _) = 1
      rw [hf_smul_right, AlgEquiv.commutes]
      simpa using (L.additive_character_dual_ring _).2 (hint' u hu') 1 L.O.one_mem
    have h := hcs χ hχ1 hχ
    rw [sum_char_eq_zero UU _ R hRU' hR' χ hχ u₀ hu₀ hne, sub_zero, norm_mul, norm_pow,
      Complex.norm_natCast] at h
    rw [← mul_div_assoc, le_div_iff₀ hqa]
    exact h

end GlobalTheory.HL.QuadricShare
end

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadric_character_leak_shares_finite : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (J : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (N : ℕ) (R : Finset S.V) (Z : S.V → Prop), S.a + 1 ≤ N → (∀ u, Z u ↔ ∃ c : 𝒪[F], S.h u u = algebraMap F E ((S.ϖ : F) ^ S.a * c)) → (∀ u ∈ R, u ∈ Λ ∧ u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)) → (∀ u ∈ Λ, u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J) → ∃! w, w ∈ R ∧ ∃ y ∈ Λ, u - w = algebraMap F E ((S.ϖ : F) ^ N) • y) → |((R.filter Z).card : ℝ) - R.card / (S.q : ℝ) ^ S.a| ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a) ∧ (((R.filter fun u => Z u ∧ ¬ ∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1).card : ℝ) ≤ 16 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a)) ∧ ∀ y : S.V, (∀ u ∈ R, algebraMap F E ((S.ϖ : F) ^ N) * S.h y u ∈ L.O) → (∃ u ∈ R, L.psi0 (S.h y u) ≠ 1) → ‖∑ u ∈ R.filter Z, L.psi0 (S.h y u)‖ ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a) := by
  atlas_forward_decl GlobalTheory.HL.QuadricShare.shares
end
