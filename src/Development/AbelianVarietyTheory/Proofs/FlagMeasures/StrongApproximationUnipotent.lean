import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationAdditiveQuadraticExtensionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLatticesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemFlagUnipotentIffOrderedEichlerProduct
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemCoord
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import BuildAid.ForwardExisting

section
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.EichCont

section Abstract

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ}

def IntV (v : Fin N → E) : Prop := ∀ j, v j ∈ O

def Bd (A : Module.End E (Fin N → E)) (t : F) : Prop :=
  ∀ m, IntV O m → ∃ m', IntV O m' ∧ A m = algebraMap F E t • m'

def Cont {Q : Type} (near : F → Q → Prop) (G : Q → Module.End E (Fin N → E))
    (A : Module.End E (Fin N → E)) : Prop :=
  ∀ c : F, c ≠ 0 → ∃ d : F, d ≠ 0 ∧ ∀ q, near d q → Bd O (G q - A) c

variable {O}

theorem IntV.add {v w : Fin N → E} (hv : IntV O v) (hw : IntV O w) : IntV O (v + w) :=
  fun j => O.add_mem (hv j) (hw j)

theorem IntV.smul {z : E} (hz : z ∈ O) {v : Fin N → E} (hv : IntV O v) : IntV O (z • v) :=
  fun j => O.mul_mem hz (hv j)

theorem IntV.zero : IntV O (0 : Fin N → E) := fun _ => O.zero_mem

theorem Bd.mono {A : Module.End E (Fin N → E)} {t o : F} (h : Bd O A (t * o))
    (ho : algebraMap F E o ∈ O) : Bd O A t := by
  intro m hm
  obtain ⟨m', hm', e⟩ := h m hm
  exact ⟨algebraMap F E o • m', hm'.smul ho, by rw [e, map_mul, mul_smul]⟩

theorem Bd.add {A B : Module.End E (Fin N → E)} {t : F} (hA : Bd O A t) (hB : Bd O B t) :
    Bd O (A + B) t := by
  intro m hm
  obtain ⟨a, ha, ea⟩ := hA m hm
  obtain ⟨b, hb, eb⟩ := hB m hm
  exact ⟨a + b, ha.add hb, by rw [LinearMap.add_apply, ea, eb, smul_add]⟩

theorem Bd.mul {A B : Module.End E (Fin N → E)} {t s : F} (hA : Bd O A t) (hB : Bd O B s) :
    Bd O (A * B) (t * s) := by
  intro m hm
  obtain ⟨b, hb, eb⟩ := hB m hm
  obtain ⟨a, ha, ea⟩ := hA b hb
  exact ⟨a, ha, by rw [Module.End.mul_apply, eb, map_smul, ea, smul_smul, ← map_mul, mul_comm]⟩

theorem Bd.zero (t : F) : Bd O (0 : Module.End E (Fin N → E)) t :=
  fun _ _ => ⟨0, IntV.zero, by simp⟩

variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O)
include hden

theorem exists_den {ι : Type} [Fintype ι] (z : ι → E) :
    ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ ∀ i, algebraMap F E a * z i ∈ O := by
  choose a ha0 haO haz using fun i => hden (z i)
  have hP : ∀ s : Finset ι, algebraMap F E (∏ i ∈ s, a i) ∈ O := fun s => by
    rw [map_prod]; exact prod_mem fun i _ => haO i
  refine ⟨∏ i, a i, Finset.prod_ne_zero_iff.2 fun i _ => ha0 i, hP _, fun i => ?_⟩
  have e : algebraMap F E (∏ j, a j) * z i =
      algebraMap F E (∏ j ∈ Finset.univ.erase i, a j) * (algebraMap F E (a i) * z i) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul]; ring
  rw [e]
  exact O.mul_mem (hP _) (haz i)

theorem Bd.exists (A : Module.End E (Fin N → E)) :
    ∃ w : F, w ≠ 0 ∧ algebraMap F E w ∈ O ∧ Bd O A w⁻¹ := by
  obtain ⟨w, hw0, hwO, hw⟩ := exists_den hden
    (fun p : Fin N × Fin N => A (fun j => if p.1 = j then 1 else 0) p.2)
  refine ⟨w, hw0, hwO, fun m hm =>
    ⟨∑ i, m i • (algebraMap F E w • A (fun j => if i = j then 1 else 0)), fun j => ?_, ?_⟩⟩
  · rw [Finset.sum_apply]
    exact sum_mem fun i _ => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact O.mul_mem (hm i) (hw (i, j))
  · rw [LinearMap.pi_apply_eq_sum_univ A m, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm (m i) (algebraMap F E w), smul_smul, ← map_mul, inv_mul_cancel₀ hw0, map_one,
      one_smul]

theorem Cont.mul {Q : Type} {near : F → Q → Prop}
    (hnear : ∀ a b : F, a ≠ 0 → b ≠ 0 → ∃ d : F, d ≠ 0 ∧ ∀ q, near d q → near a q ∧ near b q)
    {G H : Q → Module.End E (Fin N → E)} {A B : Module.End E (Fin N → E)}
    (hG : Cont O near G A) (hH : Cont O near H B) : Cont O near (fun q => G q * H q) (A * B) := by
  intro c hc
  obtain ⟨w₁, hw₁, hw₁O, hA⟩ := Bd.exists hden A
  obtain ⟨w₂, hw₂, hw₂O, hB⟩ := Bd.exists hden B
  obtain ⟨ε, hε, hεO, hεc⟩ := hden (algebraMap F E c⁻¹)
  have hεc' : algebraMap F E (ε * c⁻¹) ∈ O := by rw [map_mul]; exact hεc
  have hwO : algebraMap F E (w₁ * w₂) ∈ O := by rw [map_mul]; exact O.mul_mem hw₁O hw₂O
  have hA' : Bd O A (w₁ * w₂)⁻¹ :=
    Bd.mono (o := w₂) (by rwa [show (w₁ * w₂)⁻¹ * w₂ = w₁⁻¹ by field_simp]) hw₂O
  have hB' : Bd O B (w₁ * w₂)⁻¹ :=
    Bd.mono (o := w₁) (by rwa [show (w₁ * w₂)⁻¹ * w₁ = w₂⁻¹ by field_simp]) hw₁O
  have hα : ε * (w₁ * w₂) ≠ 0 := mul_ne_zero hε (mul_ne_zero hw₁ hw₂)
  obtain ⟨d₁, hd₁, h1⟩ := hG _ hα
  obtain ⟨d₂, hd₂, h2⟩ := hH _ hα
  obtain ⟨d, hd, hn⟩ := hnear d₁ d₂ hd₁ hd₂
  refine ⟨d, hd, fun q hq => ?_⟩
  have hGq := h1 q (hn q hq).1
  have hHq := h2 q (hn q hq).2
  have e : G q * H q - A * B = (G q - A) * (H q - B) + ((G q - A) * B + A * (H q - B)) := by
    noncomm_ring
  show Bd O (G q * H q - A * B) c
  rw [e]
  refine Bd.add ?_ (Bd.add ?_ ?_)
  · refine Bd.mono (o := (ε * c⁻¹) * (ε * (w₁ * w₂) * (w₁ * w₂))) ?_ ?_
    · rw [show c * ((ε * c⁻¹) * (ε * (w₁ * w₂) * (w₁ * w₂))) = (ε * (w₁ * w₂)) * (ε * (w₁ * w₂)) by
        field_simp]
      exact hGq.mul hHq
    · have hwO' : algebraMap F E w₁ * algebraMap F E w₂ ∈ O := O.mul_mem hw₁O hw₂O
      simp only [map_mul]
      exact O.mul_mem hεc (O.mul_mem (O.mul_mem hεO hwO') hwO')
  · refine Bd.mono (o := ε * c⁻¹) ?_ hεc'
    rw [show c * (ε * c⁻¹) = (ε * (w₁ * w₂)) * (w₁ * w₂)⁻¹ by field_simp]
    exact hGq.mul hB'
  · refine Bd.mono (o := ε * c⁻¹) ?_ hεc'
    rw [show c * (ε * c⁻¹) = (w₁ * w₂)⁻¹ * (ε * (w₁ * w₂)) by field_simp]
    exact hA'.mul hHq

theorem Cont.prod {Q : Type} {near : F → Q → Prop}
    (hnear : ∀ a b : F, a ≠ 0 → b ≠ 0 → ∃ d : F, d ≠ 0 ∧ ∀ q, near d q → near a q ∧ near b q) :
    ∀ (r : ℕ) (G : Fin r → Q → Module.End E (Fin N → E)) (A : Fin r → Module.End E (Fin N → E)),
      (∀ i, Cont O near (G i) (A i)) →
      Cont O near (fun q => (List.ofFn fun i => G i q).prod) (List.ofFn A).prod
  | 0, G, A, _ => fun c _ => ⟨1, one_ne_zero, fun q _ => by simpa using Bd.zero (O := O) (N := N) c⟩
  | r + 1, G, A, h => by
    simp only [List.ofFn_succ, List.prod_cons]
    exact Cont.mul hden hnear (h 0)
      (Cont.prod hnear r (fun i => G i.succ) (fun i => A i.succ) fun i => h i.succ)

end Abstract

section Eich

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)

end Eich

section Lat

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {O : Subring E} {N : ℕ}
variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O)
include hden

end Lat

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
private lemma exists_algebraMap_mul_mem_O {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (z : E) :
    ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ L.O ∧ algebraMap F E a * z ∈ L.O := by
  have hint : ∀ t : F, ∃ s : F, s ≠ 0 ∧ s ∈ (valuation F).integer ∧
      s * t ∈ (valuation F).integer := by
    intro t
    by_cases ht : valuation F t ≤ 1
    · exact ⟨1, one_ne_zero, (valuation F).integer.one_mem, by
        rw [one_mul, Valuation.mem_integer_iff]; exact ht⟩
    · have ht0 : t ≠ 0 := by rintro rfl; exact ht (by simp)
      refine ⟨t⁻¹, inv_ne_zero ht0, ?_, by
        rw [inv_mul_cancel₀ ht0]; exact (valuation F).integer.one_mem⟩
      rw [Valuation.mem_integer_iff, map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 ht))
  obtain ⟨ω, hωO, e, -, hωe⟩ := _root_.GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  obtain ⟨x, y, hxy⟩ := _root_.GlobalTheory.UnramOrder.exists_eq_add_mul (R₀ := F) (L.cj : E →+* E)
    (fun x => L.cj_cj x) (fun r => L.cj.commutes r)
    (fun x hx => by obtain ⟨a, ha⟩ := (L.cj_fix x).1 hx; exact ⟨a, ha⟩)
    ⟨⟨_, e, hωe, by rw [mul_comm]; exact hωe⟩, rfl⟩ z
  obtain ⟨s₁, hs₁0, hs₁, hs₁x⟩ := hint x
  obtain ⟨s₂, hs₂0, hs₂, hs₂y⟩ := hint y
  have hO : ∀ t ∈ (valuation F).integer, algebraMap F E t ∈ L.O :=
    fun t ht => (_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L t).2 ht
  refine ⟨s₁ * s₂, mul_ne_zero hs₁0 hs₂0, hO _ ((valuation F).integer.mul_mem hs₁ hs₂), ?_⟩
  rw [hxy]
  have : algebraMap F E (s₁ * s₂) * (algebraMap F E x + algebraMap F E y * ω) =
      algebraMap F E s₂ * algebraMap F E (s₁ * x) +
        algebraMap F E s₁ * algebraMap F E (s₂ * y) * ω := by
    simp only [map_mul]; ring
  rw [this]
  exact L.O.add_mem (L.O.mul_mem (hO _ hs₂) (hO _ hs₁x))
    (L.O.mul_mem (L.O.mul_mem (hO _ hs₁) (hO _ hs₂y)) hωO)

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O) in
include hden in
private lemma exists_algebraMap_mul_mem_O_forall {κ : Type} [Fintype κ] (z : κ → E) :
    ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ ∀ k, algebraMap F E a * z k ∈ O := by
  choose a ha0 haO haz using fun k => hden (z k)
  refine ⟨∏ k, a k, Finset.prod_ne_zero_iff.2 fun k _ => ha0 k, ?_, fun k => ?_⟩
  · rw [map_prod]
    exact O.prod_mem fun k _ => haO k
  · rw [map_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ k), mul_assoc]
    exact O.mul_mem (O.prod_mem fun k' _ => haO k') (haz k)

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O) in
include hden in
private lemma exists_algebraMap_mem_O_Bd_inv (A : Module.End E (Fin N → E)) :
    ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ _root_.GlobalTheory.HL.EichCont.Bd O A a⁻¹ := by
  obtain ⟨a, ha0, haO, haz⟩ := exists_algebraMap_mul_mem_O_forall hden
    (fun p : Fin N × Fin N => A (fun k => if p.1 = k then 1 else 0) p.2)
  refine ⟨a, ha0, haO, fun m hm => ⟨algebraMap F E a • A m, fun i => ?_, ?_⟩⟩
  · rw [LinearMap.pi_apply_eq_sum_univ A m]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
    exact O.sum_mem fun j _ => by
      rw [mul_left_comm]
      exact O.mul_mem (hm j) (haz (j, i))
  · rw [smul_smul, ← map_mul, inv_mul_cancel₀ ha0, map_one, one_smul]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
private lemma Bd_zero' (t : F) : _root_.GlobalTheory.HL.EichCont.Bd O (0 : Module.End E (Fin N → E)) t :=
  fun _ _ => ⟨0, fun _ => O.zero_mem, by simp⟩

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
private lemma IntV_smul_of_mem {o : E} (ho : o ∈ O) {m : Fin N → E}
    (hm : _root_.GlobalTheory.HL.EichCont.IntV O m) : _root_.GlobalTheory.HL.EichCont.IntV O (o • m) :=
  fun j => by simpa using O.mul_mem ho (hm j)

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
private lemma Bd_of_Bd_mul_of_mem_O {A : Module.End E (Fin N → E)} {s o : F}
    (hA : _root_.GlobalTheory.HL.EichCont.Bd O A (s * o)) (ho : algebraMap F E o ∈ O) :
    _root_.GlobalTheory.HL.EichCont.Bd O A s := by
  intro m hm
  obtain ⟨m₁, hm₁, e₁⟩ := hA m hm
  exact ⟨algebraMap F E o • m₁, IntV_smul_of_mem ho hm₁, by rw [e₁, map_mul, mul_smul]⟩

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
private lemma Bd_of_eq {A : Module.End E (Fin N → E)} {s t : F} (h : s = t)
    (hA : _root_.GlobalTheory.HL.EichCont.Bd O A s) : _root_.GlobalTheory.HL.EichCont.Bd O A t := h ▸ hA

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
private lemma IntV_add' {m m' : Fin N → E} (hm : _root_.GlobalTheory.HL.EichCont.IntV O m)
    (hm' : _root_.GlobalTheory.HL.EichCont.IntV O m') : _root_.GlobalTheory.HL.EichCont.IntV O (m + m') :=
  fun j => O.add_mem (hm j) (hm' j)

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
private lemma Bd_add' {A B : Module.End E (Fin N → E)} {t : F}
    (hA : _root_.GlobalTheory.HL.EichCont.Bd O A t) (hB : _root_.GlobalTheory.HL.EichCont.Bd O B t) :
    _root_.GlobalTheory.HL.EichCont.Bd O (A + B) t := by
  intro m hm
  obtain ⟨m₁, hm₁, e₁⟩ := hA m hm
  obtain ⟨m₂, hm₂, e₂⟩ := hB m hm
  exact ⟨m₁ + m₂, IntV_add' hm₁ hm₂, by rw [LinearMap.add_apply, e₁, e₂, smul_add]⟩

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
private lemma Bd_mul' {A B : Module.End E (Fin N → E)} {s t : F}
    (hA : _root_.GlobalTheory.HL.EichCont.Bd O A s) (hB : _root_.GlobalTheory.HL.EichCont.Bd O B t) :
    _root_.GlobalTheory.HL.EichCont.Bd O (A * B) (s * t) := by
  intro m hm
  obtain ⟨m₁, hm₁, e₁⟩ := hB m hm
  obtain ⟨m₂, hm₂, e₂⟩ := hA m₁ hm₁
  refine ⟨m₂, hm₂, ?_⟩
  rw [Module.End.mul_apply, e₁, map_smul, e₂, smul_smul, ← map_mul, mul_comm t s]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O) in
include hden in
private lemma exists_Bd_prod_sub_of_Bd_sub : ∀ (r : ℕ) (A : Fin r → Module.End E (Fin N → E)) (c : F),
    c ≠ 0 → ∃ d : F, d ≠ 0 ∧ ∀ G : Fin r → Module.End E (Fin N → E),
      (∀ i, _root_.GlobalTheory.HL.EichCont.Bd O (G i - A i) d) →
        _root_.GlobalTheory.HL.EichCont.Bd O ((List.ofFn G).prod - (List.ofFn A).prod) c := by
  intro r
  induction r with
  | zero =>
    intro A c _
    exact ⟨1, one_ne_zero, fun G _ => by
      simp only [List.ofFn_zero, List.prod_nil, sub_self]
      exact Bd_zero' c⟩
  | succ r ih =>
    intro A c hc
    obtain ⟨a, ha0, haO, hA0⟩ := exists_algebraMap_mem_O_Bd_inv hden (A 0)
    obtain ⟨b, hb0, hbO, hAs⟩ := exists_algebraMap_mem_O_Bd_inv hden (List.ofFn fun i => A i.succ).prod
    obtain ⟨w, hw0, hwO, hwc⟩ := hden (algebraMap F E c)
    obtain ⟨d₁, hd₁0, hd₁⟩ := ih (fun i => A i.succ) (c * a * b * w) (by simp [hc, ha0, hb0, hw0])
    obtain ⟨z, hz0, hzO, hz⟩ := exists_algebraMap_mul_mem_O_forall hden
      ![algebraMap F E (c * b), algebraMap F E d₁]
    have hz1 : algebraMap F E z * algebraMap F E (c * b) ∈ O := hz 0
    have hz2 : algebraMap F E z * algebraMap F E d₁ ∈ O := hz 1
    refine ⟨c * b * d₁ * z, by simp [hc, hb0, hd₁0, hz0], fun G hG => ?_⟩
    have hG0 : _root_.GlobalTheory.HL.EichCont.Bd O (G 0 - A 0) (c * b) :=
      Bd_of_Bd_mul_of_mem_O (o := d₁ * z) (Bd_of_eq (by ring) (hG 0))
        (by rw [map_mul, mul_comm]; exact hz2)
    have hGs : ∀ i : Fin r, _root_.GlobalTheory.HL.EichCont.Bd O (G i.succ - A i.succ) d₁ := fun i =>
      Bd_of_Bd_mul_of_mem_O (o := c * b * z) (Bd_of_eq (by ring) (hG i.succ))
        (by rw [map_mul, mul_comm]; exact hz1)
    have hrest := hd₁ (fun i => G i.succ) hGs
    have hGsb : _root_.GlobalTheory.HL.EichCont.Bd O (List.ofFn fun i => G i.succ).prod b⁻¹ := by
      have h1 : _root_.GlobalTheory.HL.EichCont.Bd O
          ((List.ofFn fun i => G i.succ).prod - (List.ofFn fun i => A i.succ).prod) b⁻¹ :=
        Bd_of_Bd_mul_of_mem_O (o := c * a * b * w * b) (Bd_of_eq (by field_simp) hrest) (by
          have := O.mul_mem (O.mul_mem (O.mul_mem hwc haO) hbO) hbO
          simp only [map_mul]
          convert this using 1
          ring)
      have := Bd_add' hAs h1
      rwa [add_sub_cancel] at this
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have key : G 0 * (List.ofFn fun i => G i.succ).prod - A 0 * (List.ofFn fun i => A i.succ).prod =
        (G 0 - A 0) * (List.ofFn fun i => G i.succ).prod +
          A 0 * ((List.ofFn fun i => G i.succ).prod - (List.ofFn fun i => A i.succ).prod) := by
      rw [sub_mul, mul_sub]
      abel
    rw [key]
    refine Bd_add' ?_ ?_
    · exact Bd_of_eq (by field_simp) (Bd_mul' hG0 hGsb)
    · exact Bd_of_Bd_mul_of_mem_O (o := b * w) (Bd_of_eq (by field_simp) (Bd_mul' hA0 hrest))
        (by rw [map_mul]; exact O.mul_mem hbO hwO)

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in

theorem _root_.GlobalTheory.HL.EichCont.prod_eich_cont : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E)
    (X u : Fin r → Fin N → E) (s : Fin r → E) (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E))
    (he : ∀ i v, e i v = _root_.GlobalTheory.HL.eich L Hm (X i) (u i) (s i) v)
    (Λ : Submodule L.O (Fin N → E)) (hΛ : _root_.GlobalTheory.HL.IsLat L Λ) (c : Fˣ),
    ∃ d : Fˣ, ∀ (u' : Fin r → Fin N → E) (s' : Fin r → E)
      (e' : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)),
      (∀ i v, e' i v = _root_.GlobalTheory.HL.eich L Hm (X i) (u' i) (s' i) v) →
      (∀ i j, ∃ o ∈ L.O, u' i j - u i j = algebraMap F E d * o) →
      (∀ i, ∃ o ∈ L.O, s' i - s i = algebraMap F E d * o) →
      ∀ x ∈ Λ, ∃ y ∈ Λ, ((List.ofFn e).prod).symm ((List.ofFn e').prod x) - x =
        algebraMap F E c • y := by
  intro F _ _ _ _ _ E _ _ _ L N r Hm X u s e he Λ hΛ c
  have hden := exists_algebraMap_mul_mem_O L
  obtain ⟨β, hβ0, hβO, hβ⟩ := exists_algebraMap_mul_mem_O_forall hden
    (fun p : (Fin N × Fin N) ⊕ (Fin r × Fin N) =>
      Sum.elim (fun q => Hm q.1 q.2) (fun q => X q.1 q.2) p)
  have hH : ∀ i j, algebraMap F E β * Hm i j ∈ L.O := fun i j => hβ (Sum.inl (i, j))
  have hX : ∀ i k, algebraMap F E β * X i k ∈ L.O := fun i k => hβ (Sum.inr (i, k))
  have hXc : ∀ i k, algebraMap F E β * L.cj (X i k) ∈ L.O := fun i k => by
    have := _root_.GlobalTheory.UnramOrder.cj_mem L (hX i k)
    rwa [map_mul, L.cj.commutes] at this

  have hform1 : ∀ v o : Fin N → E, _root_.GlobalTheory.HL.EichCont.IntV L.O v → _root_.GlobalTheory.HL.EichCont.IntV L.O o →
      algebraMap F E β * _root_.GlobalTheory.HL.hf L Hm v o ∈ L.O := by
    intro v o hv ho
    unfold _root_.GlobalTheory.HL.hf
    rw [Finset.mul_sum]
    refine L.O.sum_mem fun a _ => ?_
    rw [Finset.mul_sum]
    refine L.O.sum_mem fun b _ => ?_
    have := L.O.mul_mem (L.O.mul_mem (hv a) (hH a b)) (_root_.GlobalTheory.UnramOrder.cj_mem L (ho b))
    convert this using 1
    ring
  have hform2 : ∀ v : Fin N → E, _root_.GlobalTheory.HL.EichCont.IntV L.O v → ∀ i,
      algebraMap F E β * algebraMap F E β * _root_.GlobalTheory.HL.hf L Hm v (X i) ∈ L.O := by
    intro v hv i
    unfold _root_.GlobalTheory.HL.hf
    rw [Finset.mul_sum]
    refine L.O.sum_mem fun a _ => ?_
    rw [Finset.mul_sum]
    refine L.O.sum_mem fun b _ => ?_
    have := L.O.mul_mem (L.O.mul_mem (hv a) (hH a b)) (hXc i b)
    convert this using 1
    ring
  have hsub : ∀ v w w' : Fin N → E, _root_.GlobalTheory.HL.hf L Hm v w -
      _root_.GlobalTheory.HL.hf L Hm v w' = _root_.GlobalTheory.HL.hf L Hm v (w - w') := by
    intro v w w'
    unfold _root_.GlobalTheory.HL.hf
    simp only [Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]
  have hsmul : ∀ (v o : Fin N → E) (t : F), _root_.GlobalTheory.HL.hf L Hm v
      (algebraMap F E t • o) = algebraMap F E t * _root_.GlobalTheory.HL.hf L Hm v o := by
    intro v o t
    unfold _root_.GlobalTheory.HL.hf
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, AlgEquiv.commutes, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hdiff : ∀ i (u₁ : Fin N → E) (s₁ : E) (t : F) (o : Fin N → E) (o' : E) (v : Fin N → E),
      u₁ - u i = algebraMap F E t • o → s₁ - s i = algebraMap F E t * o' →
      _root_.GlobalTheory.HL.eich L Hm (X i) u₁ s₁ v - _root_.GlobalTheory.HL.eich L Hm (X i) (u i) (s i) v =
        algebraMap F E t • (_root_.GlobalTheory.HL.hf L Hm v o • X i -
          _root_.GlobalTheory.HL.hf L Hm v (X i) • (o + o' • X i)) := by
    intro i u₁ s₁ t o o' v hu hs
    have hu' : u₁ = u i + algebraMap F E t • o := by rw [← hu]; abel
    have hs' : s₁ = s i + algebraMap F E t * o' := by rw [← hs]; ring
    have h1 : _root_.GlobalTheory.HL.hf L Hm v u₁ = _root_.GlobalTheory.HL.hf L Hm v (u i) +
        algebraMap F E t * _root_.GlobalTheory.HL.hf L Hm v o := by
      rw [← hsmul, ← hu, ← hsub]; ring
    unfold _root_.GlobalTheory.HL.eich
    rw [h1, hu', hs']
    ext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hbr : ∀ i (o : Fin N → E) (o' : E) (v : Fin N → E), _root_.GlobalTheory.HL.EichCont.IntV L.O v →
      _root_.GlobalTheory.HL.EichCont.IntV L.O o → o' ∈ L.O →
      _root_.GlobalTheory.HL.EichCont.IntV L.O (algebraMap F E (β ^ 3) • (_root_.GlobalTheory.HL.hf L Hm v o • X i -
        _root_.GlobalTheory.HL.hf L Hm v (X i) • (o + o' • X i))) := by
    intro i o o' v hv ho ho' k
    have t1 := L.O.mul_mem (L.O.mul_mem (hform1 v o hv ho) (hX i k)) hβO
    have t2 := L.O.mul_mem (L.O.mul_mem (hform2 v hv i) hβO) (ho k)
    have t3 := L.O.mul_mem (L.O.mul_mem (hform2 v hv i) ho') (hX i k)
    have := L.O.sub_mem t1 (L.O.add_mem t2 t3)
    convert this using 1
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, map_pow]
    ring
  let φ : ((Fin N → E) ≃ₗ[E] (Fin N → E)) →* Module.End E (Fin N → E) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom
  have hP : ∀ (f : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)) (y : Fin N → E),
      (List.ofFn f).prod y = (List.ofFn fun i => φ (f i)).prod y := by
    intro f y
    have : φ (List.ofFn f).prod = (List.ofFn fun i => φ (f i)).prod := by
      rw [map_list_prod, List.map_ofFn]; rfl
    rw [← this]; rfl
  obtain ⟨a, ha0, haO, ha⟩ : ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ L.O ∧
      ∀ x ∈ Λ, _root_.GlobalTheory.HL.EichCont.IntV L.O (algebraMap F E a • x) := by
    obtain ⟨S, hS⟩ := hΛ.1
    obtain ⟨a, ha0, haO, haz⟩ := exists_algebraMap_mul_mem_O_forall hden
      (fun p : S × Fin N => (p.1 : Fin N → E) p.2)
    refine ⟨a, ha0, haO, fun x hx => ?_⟩
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact fun j => haz (⟨y, hy⟩, j)
    | zero => exact fun j => by simp
    | add y z _ _ hy hz => exact fun j => by simpa [mul_add] using L.O.add_mem (hy j) (hz j)
    | smul o y _ hy =>
      exact fun j => by simpa [Subring.smul_def, mul_left_comm] using L.O.mul_mem o.2 (hy j)
  obtain ⟨b, hb0, hbO, hb⟩ : ∃ b : F, b ≠ 0 ∧ algebraMap F E b ∈ L.O ∧
      ∀ m, _root_.GlobalTheory.HL.EichCont.IntV L.O m → algebraMap F E b • m ∈ Λ := by
    have hstep : ∀ w ∈ Submodule.span E (Λ : Set (Fin N → E)),
        ∃ b : F, b ≠ 0 ∧ algebraMap F E b ∈ L.O ∧ algebraMap F E b • w ∈ Λ := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem y hy => exact ⟨1, one_ne_zero, by simp [L.O.one_mem], by simpa using hy⟩
      | zero => exact ⟨1, one_ne_zero, by simp [L.O.one_mem], by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨b₁, h₁0, h₁O, h₁⟩ := hy
        obtain ⟨b₂, h₂0, h₂O, h₂⟩ := hz
        refine ⟨b₁ * b₂, mul_ne_zero h₁0 h₂0, by rw [map_mul]; exact L.O.mul_mem h₁O h₂O, ?_⟩
        have e1 := Λ.smul_mem (⟨algebraMap F E b₂, h₂O⟩ : L.O) h₁
        have e2 := Λ.smul_mem (⟨algebraMap F E b₁, h₁O⟩ : L.O) h₂
        have := Λ.add_mem e1 e2
        convert this using 1
        simp only [Subring.smul_def, smul_smul, map_mul, smul_add, mul_comm]
      | smul t y _ hy =>
        obtain ⟨b₁, h₁0, h₁O, h₁⟩ := hy
        obtain ⟨w₁, hw0, hwO, hwt⟩ := hden t
        refine ⟨w₁ * b₁, mul_ne_zero hw0 h₁0, by rw [map_mul]; exact L.O.mul_mem hwO h₁O, ?_⟩
        have e1 := Λ.smul_mem (⟨algebraMap F E w₁ * t, hwt⟩ : L.O) h₁
        convert e1 using 1
        rw [Subring.smul_def, smul_smul, smul_smul, map_mul]
        congr 1
        show _ = algebraMap F E w₁ * t * algebraMap F E b₁
        ring
    choose bj hbj0 hbjO hbj using fun j : Fin N =>
      hstep (fun k => if j = k then (1 : E) else 0) (by rw [hΛ.2]; exact Submodule.mem_top)
    refine ⟨∏ j, bj j, Finset.prod_ne_zero_iff.2 fun j _ => hbj0 j,
      by rw [map_prod]; exact L.O.prod_mem fun j _ => hbjO j, fun m hm => ?_⟩
    have hej : ∀ j, algebraMap F E (∏ k, bj k) • (fun k => if j = k then (1 : E) else 0) ∈ Λ := by
      intro j
      have hO' : algebraMap F E (∏ k ∈ Finset.univ.erase j, bj k) ∈ L.O := by
        rw [map_prod]; exact L.O.prod_mem fun k _ => hbjO k
      have := Λ.smul_mem (⟨_, hO'⟩ : L.O) (hbj j)
      rwa [Subring.smul_def, smul_smul, ← map_mul,
        Finset.prod_erase_mul _ _ (Finset.mem_univ j)] at this
    rw [pi_eq_sum_univ m, Finset.smul_sum]
    refine Λ.sum_mem fun j _ => ?_
    rw [smul_comm]
    exact Λ.smul_mem (⟨m j, hm j⟩ : L.O) (hej j)
  obtain ⟨γ, hγ0, -, hγ⟩ := exists_algebraMap_mem_O_Bd_inv hden
    ((List.ofFn e).prod.symm : (Fin N → E) ≃ₗ[E] (Fin N → E)).toLinearMap
  obtain ⟨d₀, hd₀0, hd₀⟩ := exists_Bd_prod_sub_of_Bd_sub hden r (fun i => φ (e i))
    ((c : F) * b * a * γ) (by simp [hb0, ha0, hγ0])
  refine ⟨Units.mk0 (d₀ * β ^ 3) (by simp [hd₀0, hβ0]), fun u' s' e' he' hu' hs' x hx => ?_⟩
  choose ou hou hueq using hu'
  choose os hos hseq using hs'
  have hfac : ∀ i, _root_.GlobalTheory.HL.EichCont.Bd L.O (φ (e' i) - φ (e i)) d₀ := by
    intro i m hm
    refine ⟨_, hbr i (ou i) (os i) m hm (fun j => hou i j) (hos i), ?_⟩
    have := hdiff i (u' i) (s' i) (d₀ * β ^ 3) (ou i) (os i) m
      (funext fun j => by rw [Pi.sub_apply, hueq i j, Units.val_mk0]; rfl)
      (by rw [hseq i, Units.val_mk0])
    show e' i m - e i m = _
    rw [he', he, this, smul_smul, ← map_mul]
  obtain ⟨m₁, hm₁, e₁⟩ := hd₀ (fun i => φ (e' i)) hfac _ (ha x hx)
  obtain ⟨m₂, hm₂, e₂⟩ := hγ m₁ hm₁
  have e₂' : ((List.ofFn e).prod).symm m₁ = algebraMap F E γ⁻¹ • m₂ := e₂
  refine ⟨algebraMap F E b • m₂, hb m₂ hm₂, ?_⟩
  have hx' : (List.ofFn e').prod x - (List.ofFn e).prod x = algebraMap F E a⁻¹ •
      (algebraMap F E ((c : F) * b * a * γ) • m₁) := by
    rw [← e₁, LinearMap.sub_apply, ← hP e', ← hP e, map_smul, map_smul, ← smul_sub, smul_smul,
      ← map_mul, inv_mul_cancel₀ ha0, map_one, one_smul]
  calc ((List.ofFn e).prod).symm ((List.ofFn e').prod x) - x
      = ((List.ofFn e).prod).symm ((List.ofFn e').prod x - (List.ofFn e).prod x) := by
        rw [map_sub, LinearEquiv.symm_apply_apply]
    _ = algebraMap F E (c : F) • algebraMap F E b • m₂ := by
        rw [hx', smul_smul, ← map_mul, map_smul, e₂', smul_smul, ← map_mul, smul_smul, ← map_mul]
        congr 2
        field_simp

end GlobalTheory.HL.EichCont
end
end

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianEichlerProduct_continuous_on_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (X u : Fin r → Fin N → E) (s : Fin r → E) (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)) (he : ∀ i v, e i v = eich L Hm (X i) (u i) (s i) v) (Λ : Submodule L.O (Fin N → E)) (hΛ : IsLat L Λ) (c : Fˣ), ∃ d : Fˣ, ∀ (u' : Fin r → Fin N → E) (s' : Fin r → E) (e' : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ i v, e' i v = eich L Hm (X i) (u' i) (s' i) v) → (∀ i j, ∃ o ∈ L.O, u' i j - u i j = algebraMap F E d * o) → (∀ i, ∃ o ∈ L.O, s' i - s i = algebraMap F E d * o) → ∀ x ∈ Λ, ∃ y ∈ Λ, ((List.ofFn e).prod).symm ((List.ofFn e').prod x) - x = algebraMap F E c • y := by
  atlas_forward_decl GlobalTheory.HL.EichCont.prod_eich_cont
end

section
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section
namespace GlobalTheory.HL.SAN.IntParam

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem eich_int (L : LocE F E) {N : ℕ} {Hm : Matrix (Fin N) (Fin N) E}
    (hI : ∀ i j, Hm i j ∈ L.O) {x u v : Fin N → E} {s : E} (hx : ∀ j, x j ∈ L.O)
    (hu : ∀ j, u j ∈ L.O) (hs : s ∈ L.O) (hv : ∀ j, v j ∈ L.O) (j : Fin N) :
    eich L Hm x u s v j ∈ L.O := by
  simp only [eich, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact L.O.sub_mem (L.O.add_mem (hv j) (L.O.mul_mem (hf_int L hI hv hu) (hx j)))
    (L.O.mul_mem (hf_int L hI hv hx) (L.O.add_mem (hu j) (L.O.mul_mem hs (hx j))))

theorem prod_fix {N : ℕ} (y : Fin N → E) :
    ∀ l : List ((Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ g ∈ l, g y = y) → l.prod y = y := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons g l ih =>
    intro h
    rw [List.prod_cons, LinearEquiv.mul_apply, ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')),
      h g List.mem_cons_self]

theorem finiteRing_sq_sub_mul_sq_eq_of_card (L : LocE F E) (N : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (hH : IsHerm L Hm)
    (hI : ∀ i j, Hm i j ∈ L.O) : ∀ (r : ℕ) (X Y u : Fin r → Fin N → E) (s : Fin r → E)
    (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ i j, X i j ∈ L.O) → (∀ i j, Y i j ∈ L.O) →
    (∀ a b, hf L Hm (X a) (Y b) = if a = b then 1 else 0) → (∀ a b, hf L Hm (X a) (X b) = 0) →
    (∀ i, ∀ j, j ≤ i → hf L Hm (u i) (X j) = 0 ∧ hf L Hm (u i) (Y j) = 0) →
    (∀ i, s i + L.cj (s i) = hf L Hm (u i) (u i)) →
    (∀ i v, e i v = eich L Hm (X i) (u i) (s i) v) →
    (∀ x : Fin N → E, (∀ j, (List.ofFn e).prod x j ∈ L.O) ↔ ∀ j, x j ∈ L.O) →
    (∀ i j, u i j ∈ L.O) ∧ ∀ i, s i ∈ L.O := by
  intro r
  induction r with
  | zero => intro X Y u s e _ _ _ _ _ _ _ _; exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  | succ r ih =>
    intro X Y u s e hX hY hXY hXX hu hs he hn
    set n' := (List.ofFn fun i : Fin r => e i.succ).prod with hn'def
    have hprod : ∀ x, (List.ofFn e).prod x = e 0 (n' x) := by
      intro x; rw [List.ofFn_succ, List.prod_cons, LinearEquiv.mul_apply]

    have hfix : n' (Y 0) = Y 0 := by
      refine prod_fix (Y 0) _ fun g hg => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
      have h1 : hf L Hm (Y 0) (u i.succ) = 0 := by
        rw [← GlobalTheory.HL.Eichler.hf_cj L hH, (hu i.succ 0 (Fin.zero_le _)).2, map_zero]
      have h2 : hf L Hm (Y 0) (X i.succ) = 0 := by
        rw [← GlobalTheory.HL.Eichler.hf_cj L hH, hXY, if_neg (Fin.succ_ne_zero i), map_zero]
      rw [he, eich, h1, h2]; simp
    have h0 : e 0 (Y 0) = Y 0 - (u 0 + s 0 • X 0) := by
      have h1 : hf L Hm (Y 0) (u 0) = 0 := by
        rw [← GlobalTheory.HL.Eichler.hf_cj L hH, (hu 0 0 le_rfl).2, map_zero]
      have h2 : hf L Hm (Y 0) (X 0) = 1 := by
        rw [← GlobalTheory.HL.Eichler.hf_cj L hH, hXY, if_pos rfl, map_one]
      rw [he, eich, h1, h2]; simp
    have hnY : ∀ j, (List.ofFn e).prod (Y 0) j ∈ L.O := (hn (Y 0)).2 (hY 0)
    rw [hprod, hfix, h0] at hnY
    have hw : ∀ j, (u 0 + s 0 • X 0) j ∈ L.O := by
      intro j
      have := L.O.sub_mem (hY 0 j) (hnY j)
      simpa using this
    have hs0 : s 0 ∈ L.O := by
      have h := hf_int L hI hw (hY 0)
      rwa [GlobalTheory.HL.Eichler.hf_add_l, GlobalTheory.HL.Eichler.hf_smul_l, (hu 0 0 le_rfl).2, hXY, if_pos rfl,
        mul_one, zero_add] at h
    have hu0 : ∀ j, u 0 j ∈ L.O := by
      intro j
      have h := L.O.sub_mem (hw j) (L.O.mul_mem hs0 (hX 0 j))
      simpa using h

    have he0 : ∀ x, (∀ j, e 0 x j ∈ L.O) ↔ ∀ j, x j ∈ L.O := by
      intro x
      constructor
      · intro h j
        have hinv := GlobalTheory.HL.Eichler.eich_inv L hH (X 0) (u 0) (s 0) (hXX 0 0) (hu 0 0 le_rfl).1 (hs 0) x
        rw [← hinv, ← he]
        exact eich_int L hI (hX 0) (fun k => L.O.neg_mem (hu0 k)) (GlobalTheory.UnramOrder.cj_mem L hs0) h j
      · intro h j
        rw [he]
        exact eich_int L hI (hX 0) hu0 hs0 h j
    have hn2 : ∀ x : Fin N → E, (∀ j, (List.ofFn fun i : Fin r => e i.succ).prod x j ∈ L.O) ↔
        ∀ j, x j ∈ L.O := by
      intro x
      rw [← hn x, hprod, ← hn'def]
      exact (he0 (n' x)).symm
    obtain ⟨hU, hS⟩ := ih (fun i => X i.succ) (fun i => Y i.succ) (fun i => u i.succ)
      (fun i => s i.succ) (fun i => e i.succ) (fun i => hX i.succ) (fun i => hY i.succ)
      (fun a b => by rw [hXY]; simp only [Fin.succ_inj]) (fun a b => hXX a.succ b.succ)
      (fun i j hj => hu i.succ j.succ (Fin.succ_le_succ_iff.mpr hj)) (fun i => hs i.succ)
      (fun i v => he i.succ v) hn2
    refine ⟨fun i => Fin.cases hu0 (fun i => hU i) i, fun i => Fin.cases hs0 (fun i => hS i) i⟩

theorem eich_prod_params_int : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (hH : IsHerm L Hm) (hI : ∀ i j, Hm i j ∈ L.O) (X Y u : Fin r → Fin N → E) (s : Fin r → E) (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)) (hX : ∀ i j, X i j ∈ L.O) (hY : ∀ i j, Y i j ∈ L.O) (hXY : ∀ a b, hf L Hm (X a) (Y b) = if a = b then 1 else 0) (hXX : ∀ a b, hf L Hm (X a) (X b) = 0) (hu : ∀ i, ∀ j, j ≤ i → hf L Hm (u i) (X j) = 0 ∧ hf L Hm (u i) (Y j) = 0) (hs : ∀ i, s i + L.cj (s i) = hf L Hm (u i) (u i)) (he : ∀ i v, e i v = eich L Hm (X i) (u i) (s i) v) (hn : ∀ x : Fin N → E, (∀ j, (List.ofFn e).prod x j ∈ L.O) ↔ ∀ j, x j ∈ L.O), (∀ i j, u i j ∈ L.O) ∧ ∀ i, s i ∈ L.O := by
  intro F _ _ _ _ _ E _ _ _ L N r Hm hH hI X Y u s e hX hY hXY hXX hu hs he hn
  exact finiteRing_sq_sub_mul_sq_eq_of_card L N Hm hH hI r X Y u s e hX hY hXY hXX hu hs he hn

end GlobalTheory.HL.SAN.IntParam
end
end

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianEichlerProduct_params_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (hH : IsHerm L Hm) (hI : ∀ i j, Hm i j ∈ L.O) (X Y u : Fin r → Fin N → E) (s : Fin r → E) (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)) (hX : ∀ i j, X i j ∈ L.O) (hY : ∀ i j, Y i j ∈ L.O) (hXY : ∀ a b, hf L Hm (X a) (Y b) = if a = b then 1 else 0) (hXX : ∀ a b, hf L Hm (X a) (X b) = 0) (hu : ∀ i, ∀ j, j ≤ i → hf L Hm (u i) (X j) = 0 ∧ hf L Hm (u i) (Y j) = 0) (hs : ∀ i, s i + L.cj (s i) = hf L Hm (u i) (u i)) (he : ∀ i v, e i v = eich L Hm (X i) (u i) (s i) v) (hn : ∀ x : Fin N → E, (∀ j, (List.ofFn e).prod x j ∈ L.O) ↔ ∀ j, x j ∈ L.O), (∀ i j, u i j ∈ L.O) ∧ ∀ i, s i ∈ L.O := by
  atlas_forward_decl GlobalTheory.HL.SAN.IntParam.eich_prod_params_int
end

section
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.NormalFormRescaled

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem eich_smul_base (c : E) (hc : L.cj c = c) (x u : Fin n → E) (s : E) (v : Fin n → E) :
    eich L Hm (c • x) u s v = eich L Hm x (c • u) (c ^ 2 * s) v := by
  simp only [eich, Eichler.hf_smul_r, Eichler.hf_smul_l, hc]
  module

theorem cj_alg (a : F) : L.cj (algebraMap F E a) = algebraMap F E a := L.cj.commutes a

omit [TopologicalSpace E] in
theorem alg_inv_mul (a : Fˣ) : algebraMap F E ((a⁻¹ : Fˣ) : F) * algebraMap F E (a : F) = 1 := by
  rw [← map_mul, Units.inv_mul, map_one]

omit [TopologicalSpace E] in
theorem alg_mul_inv (a : Fˣ) : algebraMap F E (a : F) * algebraMap F E ((a⁻¹ : Fˣ) : F) = 1 := by
  rw [← map_mul, Units.mul_inv, map_one]

end

end GlobalTheory.HL.NormalFormRescaled

open GlobalTheory.HL.NormalFormRescaled in

theorem GlobalTheory.HL.nof_normal_form_rescaled : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (hsel : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) (a : Fin r → Fˣ) (X Y : Fin r → S.V) (hX : ∀ i, algebraMap F E (a i) • g i.castSucc = X i) (hY : ∀ i, gs i = algebraMap F E (a i) • Y i), (∀ i j, S.h (X i) (Y j) = if i = j then 1 else 0) ∧ (∀ i j, S.h (X i) (X j) = 0) ∧ (∀ i j, S.h (Y i) (Y j) = 0) ∧ ∀ n : S.GLV, n ∈ S.Nof g ↔ ∃ (u : Fin r → S.V) (s : Fin r → E) (e : Fin r → S.GLV), (∀ i, (∀ j, j ≤ i → S.h (u i) (X j) = 0 ∧ S.h (u i) (Y j) = 0) ∧ s i + L.cj (s i) = S.h (u i) (u i) ∧ ∀ v, e i v = eich L S.Hm (X i) (u i) (s i) v) ∧ n = (List.ofFn e).prod := by
  intro F _ _ _ _ _ E _ _ _ L r k S g gs hsel a X Y hX hY
  have hgg : ∀ i j : Fin r, hf L S.Hm (g i.castSucc) (g j.castSucc) = 0 := by
    intro i j
    rcases hsel with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2
    · rw [S.gram]; simp [Fin.castSucc_ne_last]
    · rw [S.gram']; simp [Fin.castSucc_ne_last]
  have hgs : ∀ i j : Fin r, hf L S.Hm (g i.castSucc) (gs j) = if i = j then 1 else 0 := by
    intro i j
    rcases hsel with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2
    · rw [S.dual]; simp [Fin.castSucc_inj]
    · rw [S.dual']; simp [Fin.castSucc_inj]
  have hss : ∀ i j : Fin r, hf L S.Hm (gs i) (gs j) = 0 := by
    intro i j
    rcases hsel with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2
    · exact S.iso i j
    · exact S.iso' i j
  have hg : ∀ i, g i.castSucc = algebraMap F E ((a i)⁻¹ : Fˣ) • X i := by
    intro i; rw [← hX i, smul_smul, alg_inv_mul, one_smul]
  have hY' : ∀ i, Y i = algebraMap F E ((a i)⁻¹ : Fˣ) • gs i := by
    intro i; rw [hY i, smul_smul, alg_inv_mul, one_smul]
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun n => ?_⟩
  · simp only [Frames.h]
    rw [← hX i, hY' j, Eichler.hf_smul_l, Eichler.hf_smul_r, cj_alg, hgs]
    split_ifs with h
    · subst h; rw [mul_one, alg_mul_inv]
    · simp
  · simp only [Frames.h]
    rw [← hX i, ← hX j, Eichler.hf_smul_l, Eichler.hf_smul_r, hgg]; simp
  · simp only [Frames.h]
    rw [hY' i, hY' j, Eichler.hf_smul_l, Eichler.hf_smul_r, hss]; simp
  rw [GlobalTheory.T.mem_flagUnipotent_iff_orderedEichlerProduct L r k S g gs hsel n]
  constructor
  · rintro ⟨u, s, e, he, hn⟩
    refine ⟨fun i => algebraMap F E ((a i)⁻¹ : Fˣ) • u i,
      fun i => algebraMap F E ((a i)⁻¹ : Fˣ) ^ 2 * s i, e, fun i => ?_, hn⟩
    obtain ⟨ho, hs, hev⟩ := he i
    refine ⟨fun j hj => ?_, ?_, fun v => ?_⟩
    · obtain ⟨h1, h2⟩ := ho j hj
      simp only [Frames.h] at h1 h2 ⊢
      constructor
      · rw [← hX j, Eichler.hf_smul_l, Eichler.hf_smul_r, h1]; simp
      · rw [hY' j, Eichler.hf_smul_l, Eichler.hf_smul_r, h2]; simp
    · simp only [Frames.h] at hs ⊢
      rw [map_mul, map_pow, cj_alg, Eichler.hf_smul_l, Eichler.hf_smul_r, cj_alg, ← hs]; ring
    · rw [hev v, hg i, eich_smul_base L _ _ (cj_alg L _)]
  · rintro ⟨u, s, e, he, hn⟩
    refine ⟨fun i => algebraMap F E (a i : F) • u i,
      fun i => algebraMap F E (a i : F) ^ 2 * s i, e, fun i => ?_, hn⟩
    obtain ⟨ho, hs, hev⟩ := he i
    refine ⟨fun j hj => ?_, ?_, fun v => ?_⟩
    · obtain ⟨h1, h2⟩ := ho j hj
      simp only [Frames.h] at h1 h2 ⊢
      constructor
      · rw [hg j, Eichler.hf_smul_l, Eichler.hf_smul_r, h1]; simp
      · rw [hY j, Eichler.hf_smul_l, Eichler.hf_smul_r, h2]; simp
    · simp only [Frames.h] at hs ⊢
      rw [map_mul, map_pow, cj_alg, Eichler.hf_smul_l, Eichler.hf_smul_r, cj_alg, ← hs]; ring
    · rw [hev v, hg i, eich_smul_base L _ _ (cj_alg L _), smul_smul, ← mul_assoc, ← mul_pow,
        alg_inv_mul, one_pow, one_mul, one_smul]
end

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFlagUnipotent_normalForm_rescaled : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (hsel : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) (a : Fin r → Fˣ) (X Y : Fin r → S.V) (hX : ∀ i, algebraMap F E (a i) • g i.castSucc = X i) (hY : ∀ i, gs i = algebraMap F E (a i) • Y i), (∀ i j, S.h (X i) (Y j) = if i = j then 1 else 0) ∧ (∀ i j, S.h (X i) (X j) = 0) ∧ (∀ i j, S.h (Y i) (Y j) = 0) ∧ ∀ n : S.GLV, n ∈ S.Nof g ↔ ∃ (u : Fin r → S.V) (s : Fin r → E) (e : Fin r → S.GLV), (∀ i, (∀ j, j ≤ i → S.h (u i) (X j) = 0 ∧ S.h (u i) (Y j) = 0) ∧ s i + L.cj (s i) = S.h (u i) (u i) ∧ ∀ v, e i v = eich L S.Hm (X i) (u i) (s i) v) ∧ n = (List.ofFn e).prod := by
  atlas_forward_decl GlobalTheory.HL.nof_normal_form_rescaled
end

section
open ValuativeRel

namespace GlobalTheory.SmulIntegralDenominator

theorem exists_smul_integral {K : Type} [Field K] [ValuativeRel K]
    {R : Type} [CommRing R] [Algebra K R] [Module.Finite K R] (x : R) :
    ∃ e : 𝒪[K], e ≠ 0 ∧ IsIntegral 𝒪[K] (e • x) := by
  have h1 : IsAlgebraic K x := (Algebra.IsIntegral.isIntegral (R := K) x).isAlgebraic
  have h2 : IsAlgebraic 𝒪[K] x := (IsFractionRing.isAlgebraic_iff 𝒪[K] K R).mpr h1
  exact h2.exists_integral_multiple

theorem common_denominator {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    {R : Type} [CommRing R] [Algebra K R] [TopologicalSpace R] (L : Formalism.MainNotions.S.Loc.LocE K R)
    {ι : Type} [Fintype ι] (f : ι → R) :
    ∃ e ∈ Valuation.integer (ValuativeRel.valuation K), e ≠ (0 : K) ∧
      ∀ i : ι, ∃ o ∈ L.O, f i = algebraMap K R e⁻¹ * o := by
  classical
  haveI : Module.Finite K R := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  choose e he0 he using fun i => exists_smul_integral (K := K) (f i)
  have hP : (∏ i, e i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => he0 i
  have hP' : ((∏ i, e i : 𝒪[K]) : K) ≠ 0 := fun h => hP (Subtype.ext h)
  refine ⟨((∏ i, e i : 𝒪[K]) : K), (∏ i, e i).2, hP', fun i => ?_⟩
  refine ⟨(∏ i, e i) • f i, ?_, ?_⟩
  · rw [L.O_def, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul]
    exact (he i).smul _
  · rw [Subring.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hP', map_one,
      one_mul]

theorem main : (let d1 : {K : Type} → [inst : Field K] → [inst_1 : ValuativeRel K] → [inst_2 : TopologicalSpace K] → {R : Type} → [inst_3 : CommRing R] → [inst_4 : Algebra K R] → [inst_5 : TopologicalSpace R] → Formalism.MainNotions.S.Loc.LocE K R → K → R → Prop := @(fun {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] {R : Type} [CommRing R] [Algebra K R] [TopologicalSpace R] (L : Formalism.MainNotions.S.Loc.LocE K R) (γ : K) (x : R) ↦ ∃ o ∈ Formalism.MainNotions.S.Loc.LocE.O L, x = (Algebra.algebraMap K R : K → R) γ * o); ∀ {K : Type} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K] {R : Type} [inst_3 : CommRing R] [inst_4 : Algebra K R] [inst_5 : TopologicalSpace R] (L : Formalism.MainNotions.S.Loc.LocE K R) {ι : Type} [Fintype ι] (f : ι → R), ∃ e ∈ Valuation.integer (ValuativeRel.valuation K), e ≠ (0 : K) ∧ ∀ (i : ι), d1 L e⁻¹ (f i)) := by
  intro d1 K _ _ _ R _ _ _ L ι _ f
  obtain ⟨e, he, he0, h⟩ := common_denominator L f
  exact ⟨e, he, he0, fun i => by obtain ⟨o, ho, hf⟩ := h i; exact ⟨o, ho, hf⟩⟩

end GlobalTheory.SmulIntegralDenominator
end

section
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory.HL.SAN

noncomputable section
namespace GlobalTheory.HL.EichlerParams

section Local
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
variable {R : Type} [CommRing R] [Algebra K R] [TopologicalSpace R]

def Sm (L : LocE K R) (γ : K) (x : R) : Prop := ∃ o ∈ L.O, x = algebraMap K R γ * o

variable (L : LocE K R)

theorem algO {k : K} (hk : k ∈ 𝒪[K]) : algebraMap K R k ∈ L.O :=
  (GlobalTheory.UnramOrder.algebraMap_mem_iff L k).2 hk

theorem sm_zero (γ : K) : Sm L γ 0 := ⟨0, L.O.zero_mem, by simp⟩

theorem sm_add {γ : K} {x y : R} (hx : Sm L γ x) (hy : Sm L γ y) : Sm L γ (x + y) := by
  obtain ⟨o, ho, rfl⟩ := hx; obtain ⟨o', ho', rfl⟩ := hy
  exact ⟨o + o', L.O.add_mem ho ho', by ring⟩

theorem sm_neg {γ : K} {x : R} (hx : Sm L γ x) : Sm L γ (-x) := by
  obtain ⟨o, ho, rfl⟩ := hx
  exact ⟨-o, L.O.neg_mem ho, by ring⟩

theorem sm_sub {γ : K} {x y : R} (hx : Sm L γ x) (hy : Sm L γ y) : Sm L γ (x - y) := by
  rw [sub_eq_add_neg]; exact sm_add L hx (sm_neg L hy)

theorem sm_mul {a b : K} {x y : R} (hx : Sm L a x) (hy : Sm L b y) : Sm L (a * b) (x * y) := by
  obtain ⟨o, ho, rfl⟩ := hx; obtain ⟨o', ho', rfl⟩ := hy
  exact ⟨o * o', L.O.mul_mem ho ho', by rw [map_mul]; ring⟩

theorem sm_cj {a : K} {x : R} (hx : Sm L a x) : Sm L a (L.cj x) := by
  obtain ⟨o, ho, rfl⟩ := hx
  exact ⟨L.cj o, GlobalTheory.UnramOrder.cj_mem L ho, by rw [map_mul, AlgEquiv.commutes]⟩

theorem sm_of_eq {a b k : K} {x : R} (hx : Sm L a x) (h : a = b * k) (hk : k ∈ 𝒪[K]) : Sm L b x := by
  obtain ⟨o, ho, rfl⟩ := hx
  exact ⟨algebraMap K R k * o, L.O.mul_mem (algO L hk) ho, by rw [h, map_mul]; ring⟩

theorem sm_sum {ι : Type} (s : Finset ι) {γ : K} (f : ι → R) (h : ∀ i ∈ s, Sm L γ (f i)) :
    Sm L γ (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using sm_zero L γ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact sm_add L (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem sm_one {x : R} : Sm L 1 x ↔ x ∈ L.O := by
  constructor
  · rintro ⟨o, ho, rfl⟩; simpa using ho
  · intro h; exact ⟨x, h, by simp⟩

theorem mem_of_sm {γ : K} {x : R} (hx : Sm L γ x) (hγ : γ ∈ 𝒪[K]) : x ∈ L.O :=
  (sm_one L).1 (sm_of_eq L hx (one_mul γ).symm hγ)

theorem hf_sm {N : ℕ} {a b c : K} {Hm : Matrix (Fin N) (Fin N) R} {x y : Fin N → R}
    (hx : ∀ i, Sm L a (x i)) (hH : ∀ i j, Sm L b (Hm i j)) (hy : ∀ j, Sm L c (y j)) :
    Sm L (a * b * c) (hf L Hm x y) :=
  sm_sum L _ _ fun i _ => sm_sum L _ _ fun j _ => sm_mul L (sm_mul L (hx i) (hH i j)) (sm_cj L (hy j))

theorem hf_add_l {N : ℕ} (Hm : Matrix (Fin N) (Fin N) R) (a b y : Fin N → R) :
    hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_add_r {N : ℕ} (Hm : Matrix (Fin N) (Fin N) R) (a b y : Fin N → R) :
    hf L Hm y (a + b) = hf L Hm y a + hf L Hm y b := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_sub_l {N : ℕ} (Hm : Matrix (Fin N) (Fin N) R) (a b y : Fin N → R) :
    hf L Hm (a - b) y = hf L Hm a y - hf L Hm b y := by
  simp [hf, sub_mul, Finset.sum_sub_distrib]


theorem exists_bound {ι : Type} [Fintype ι] (f : ι → R) : ∃ e ∈ 𝒪[K], e ≠ 0 ∧ ∀ i, Sm L e⁻¹ (f i) := by
  first
  | exact @_root_.GlobalTheory.SmulIntegralDenominator.main
  | exact _root_.GlobalTheory.SmulIntegralDenominator.main
  | (apply _root_.GlobalTheory.SmulIntegralDenominator.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulIntegralDenominator.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulIntegralDenominator.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulIntegralDenominator.main ..)

def piL {N r : ℕ} (Hm : Matrix (Fin N) (Fin N) R) (X Y : Fin r → Fin N → R) (T : Finset (Fin r))
    (v : Fin N → R) : Fin N → R :=
  fun j => v j - ∑ a ∈ T, (hf L Hm v (Y a) * X a j + hf L Hm v (X a) * Y a j)

theorem local_choice {N r : ℕ} (Hm : Matrix (Fin N) (Fin N) R) (X Y : Fin r → Fin N → R)
    (T : Finset (Fin r)) (up : Fin N → R)
    (horth : ∀ a ∈ T, hf L Hm up (X a) = 0 ∧ hf L Hm up (Y a) = 0)
    {e d' : K} (he : e ∈ 𝒪[K]) (he0 : e ≠ 0) (hd' : d' ∈ 𝒪[K])
    (bH : ∀ i j, Sm L e⁻¹ (Hm i j)) (bX : ∀ a j, Sm L e⁻¹ (X a j)) (bY : ∀ a j, Sm L e⁻¹ (Y a j))
    (bu : ∀ j, Sm L e⁻¹ (up j)) (v : Fin N → R) (hv : ∀ j, Sm L (2 * d' * e ^ 5) (v j - up j)) :
    (∀ j, Sm L (2 * d') (piL L Hm X Y T v j - up j)) ∧
      Sm L (2 * d') (hf L Hm (piL L Hm X Y T v) (piL L Hm X Y T v) - hf L Hm up up) := by
  have h2 : (2 : K) ∈ 𝒪[K] := by simpa using (𝒪[K]).natCast_mem 2
  have hv' : ∀ a ∈ T, hf L Hm v (Y a) = hf L Hm (v - up) (Y a) ∧
      hf L Hm v (X a) = hf L Hm (v - up) (X a) := by
    intro a ha
    rw [hf_sub_l, hf_sub_l, (horth a ha).1, (horth a ha).2, sub_zero, sub_zero]
    exact ⟨rfl, rfl⟩
  have hmv : ∀ j, Sm L (2 * d' * e ^ 5) ((v - up) j) := fun j => by simpa using hv j
  have hm' : ∀ j, Sm L (2 * d' * e ^ 2) (piL L Hm X Y T v j - up j) := by
    intro j
    have e1 : piL L Hm X Y T v j - up j = (v j - up j) -
        ∑ a ∈ T, (hf L Hm (v - up) (Y a) * X a j + hf L Hm (v - up) (X a) * Y a j) := by
      simp only [piL]
      rw [Finset.sum_congr rfl (fun a ha => by rw [(hv' a ha).1, (hv' a ha).2])]
      ring
    rw [e1]
    refine sm_sub L (sm_of_eq L (hv j) (by ring) (pow_mem he 3)) (sm_sum L _ _ fun a _ => ?_)
    have hk : 2 * d' * e ^ 5 * e⁻¹ * e⁻¹ * e⁻¹ = 2 * d' * e ^ 2 * 1 := by field_simp
    exact sm_add L
      (sm_of_eq L (sm_mul L (hf_sm L hmv bH (bY a)) (bX a j)) hk (𝒪[K]).one_mem)
      (sm_of_eq L (sm_mul L (hf_sm L hmv bH (bX a)) (bY a j)) hk (𝒪[K]).one_mem)
  refine ⟨fun j => sm_of_eq L (hm' j) (by ring) (pow_mem he 2), ?_⟩
  set m' : Fin N → R := fun j => piL L Hm X Y T v j - up j with hm'def
  have hpv : piL L Hm X Y T v = up + m' := by funext j; simp [m']
  have hm'' : ∀ j, Sm L (2 * d' * e ^ 2) (m' j) := hm'
  rw [hpv, hf_add_l, hf_add_r, hf_add_r]
  have e2 : hf L Hm up up + hf L Hm up m' + (hf L Hm m' up + hf L Hm m' m') - hf L Hm up up =
      hf L Hm up m' + hf L Hm m' up + hf L Hm m' m' := by ring
  rw [e2]
  refine sm_add L (sm_add L ?_ ?_) ?_
  · exact sm_of_eq L (hf_sm L bu bH hm'') (by field_simp) (𝒪[K]).one_mem
  · exact sm_of_eq L (hf_sm L hm'' bH bu) (by field_simp) (𝒪[K]).one_mem
  · exact sm_of_eq L (hf_sm L hm'' bH hm'') (by field_simp)
      ((𝒪[K]).mul_mem ((𝒪[K]).mul_mem h2 hd') (pow_mem he 3))

end Local

section Global
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem sig_sig (A : Places F E sig) (y : E) : sig (sig y) = y := by
  obtain ⟨p⟩ := exists_place F
  haveI := GlobalTheory.HL.PlacesInt.nontrivial_Ep (A.loc p)
  apply (A.loc p).ιE.injective
  rw [← (A.loc p).cj_ιE, ← (A.loc p).cj_ιE, ← A.L_cj, (A.L p).cj_cj]

theorem hq_swap (A : Places F E sig) {N : ℕ} (Hm : Matrix (Fin N) (Fin N) E)
    (hH : ∀ i j, sig (Hm j i) = Hm i j) (x y : Fin N → E) : sig (hq sig Hm x y) = hq sig Hm y x := by
  simp only [hq, map_sum, map_mul, sig_sig A]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hH]
  ring

theorem hq_sub_l {N : ℕ} (Hm : Matrix (Fin N) (Fin N) E) (a b y : Fin N → E) :
    hq sig Hm (a - b) y = hq sig Hm a y - hq sig Hm b y := by
  simp [hq, sub_mul, Finset.sum_sub_distrib]

theorem hq_sum_l {N : ℕ} (Hm : Matrix (Fin N) (Fin N) E) {ι : Type} (s : Finset ι) (f : ι → Fin N → E)
    (y : Fin N → E) : hq sig Hm (∑ a ∈ s, f a) y = ∑ a ∈ s, hq sig Hm (f a) y := by
  induction s using Finset.induction_on with
  | empty => simp [hq]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hq_add_l, ih]

def piQ (sig : E →ₐ[F] E) {N r : ℕ} (Hm : Matrix (Fin N) (Fin N) E) (X Y : Fin r → Fin N → E)
    (T : Finset (Fin r)) (w : Fin N → E) : Fin N → E :=
  fun j => w j - ∑ a ∈ T, (hq sig Hm w (Y a) * X a j + hq sig Hm w (X a) * Y a j)

theorem hq_piQ {N r : ℕ} (Hm : Matrix (Fin N) (Fin N) E) (X Y : Fin r → Fin N → E)
    (T : Finset (Fin r)) (w z : Fin N → E) :
    hq sig Hm (piQ sig Hm X Y T w) z = hq sig Hm w z -
      ∑ a ∈ T, (hq sig Hm w (Y a) * hq sig Hm (X a) z + hq sig Hm w (X a) * hq sig Hm (Y a) z) := by
  have e : piQ sig Hm X Y T w = w - ∑ a ∈ T, (hq sig Hm w (Y a) • X a + hq sig Hm w (X a) • Y a) := by
    funext j; simp [piQ, Finset.sum_apply]
  rw [e, hq_sub_l, hq_sum_l]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hq_add_l, hq_smul_l, hq_smul_l]

theorem bc_piQ (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {N r : ℕ}
    (Hm : Matrix (Fin N) (Fin N) E) (X Y : Fin r → Fin N → E) (T : Finset (Fin r)) (w : Fin N → E) :
    A.bc p (piQ sig Hm X Y T w) = piL (A.L p) (Hm.map (A.loc p).ιE) (fun a => A.bc p (X a))
      (fun a => A.bc p (Y a)) T (A.bc p w) := by
  have h5 : ∀ x y : Fin N → E, (A.loc p).ιE (hq sig Hm x y) =
      hf (A.L p) (Hm.map (A.loc p).ιE) (A.bc p x) (A.bc p y) :=
    fun x y => ((GlobalTheory.HL.RatExt.rational_extend A N p).2.2.2.2.1 Hm x y).symm
  funext j
  simp only [piQ, piL, Places.bc, map_sub, map_sum, map_add, map_mul, h5]

end Global

theorem strong_approx_params : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (hH : ∀ i j, sig (Hm j i) = Hm i j) (X Y : Fin r → Fin N → E) (T : Finset (Fin r)) (hXY : ∀ a b, hq sig Hm (X a) (Y b) = if a = b then 1 else 0) (hXX : ∀ a b, hq sig Hm (X a) (X b) = 0) (hYY : ∀ a b, hq sig Hm (Y a) (Y b) = 0) (up : ∀ p, Fin N → (A.loc p).Ep) (sp : ∀ p, (A.loc p).Ep) (horth : ∀ p, ∀ a ∈ T, hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (A.bc p (X a)) = 0 ∧ hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (A.bc p (Y a)) = 0) (hs : ∀ p, sp p + (A.L p).cj (sp p) = hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p)) (hint : {p | ¬ ((∀ j, up p j ∈ (A.L p).O) ∧ sp p ∈ (A.L p).O)}.Finite) (d : ∀ p, ((A.loc p).Fp)ˣ) (hd : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = d p}.Finite), ∃ (u : Fin N → E) (s : E), (∀ a ∈ T, hq sig Hm u (X a) = 0 ∧ hq sig Hm u (Y a) = 0) ∧ s + sig s = hq sig Hm u u ∧ ∀ p, (∀ j, ∃ o ∈ (A.L p).O, (A.loc p).ιE (u j) - up p j = algebraMap (A.loc p).Fp (A.loc p).Ep (d p) * o) ∧ ∃ o ∈ (A.L p).O, (A.loc p).ιE s - sp p = algebraMap (A.loc p).Fp (A.loc p).Ep (d p) * o := by
  intro F E _ _ _ _ _ sig A N r Hm hH X Y T hXY hXX hYY up sp horth hs hint d hd

  let good : HeightOneSpectrum (𝓞 F) → Prop := fun p =>
    (∀ i j, (A.loc p).ιE (Hm i j) ∈ (A.L p).O) ∧ (∀ a j, (A.loc p).ιE (X a j) ∈ (A.L p).O) ∧
    (∀ a j, (A.loc p).ιE (Y a j) ∈ (A.L p).O) ∧ ((∀ j, up p j ∈ (A.L p).O) ∧ sp p ∈ (A.L p).O) ∧
    (∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = d p) ∧
    (∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = 2)
  have IL := GlobalTheory.HL.PlacesInt.integers_local A
  have hgood : {p | ¬ good p}.Finite := by
    have s1 : (⋃ i, ⋃ j, {p | (A.loc p).ιE (Hm i j) ∉ (A.L p).O}).Finite :=
      Set.finite_iUnion fun i => Set.finite_iUnion fun j => IL.2.1 (Hm i j)
    have s2 : (⋃ a, ⋃ j, {p | (A.loc p).ιE (X a j) ∉ (A.L p).O}).Finite :=
      Set.finite_iUnion fun a => Set.finite_iUnion fun j => IL.2.1 (X a j)
    have s3 : (⋃ a, ⋃ j, {p | (A.loc p).ιE (Y a j) ∉ (A.L p).O}).Finite :=
      Set.finite_iUnion fun a => Set.finite_iUnion fun j => IL.2.1 (Y a j)
    have s6 : {p | (A.loc p).ιE (algebraMap F E 2⁻¹) ∉ (A.L p).O}.Finite := IL.2.1 _
    refine (((((s1.union s2).union s3).union hint).union hd).union s6).subset ?_
    intro p hp
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion] at hp ⊢
    by_contra hc
    push_neg at hc
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
    apply hp
    refine ⟨h1, h2, h3, h4, h5, ?_⟩
    haveI := (A.loc p).char0
    rw [(A.loc p).compat, GlobalTheory.UnramOrder.algebraMap_mem_iff, map_inv₀, map_ofNat] at h6
    have h2m : (2 : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp] := by simpa using (𝒪[(A.loc p).Fp]).natCast_mem 2
    refine ⟨Units.mkOfMulEqOne ⟨2, h2m⟩ ⟨2⁻¹, h6⟩ (Subtype.ext ?_), rfl⟩
    change (2 : (A.loc p).Fp) * 2⁻¹ = 1
    exact mul_inv_cancel₀ two_ne_zero

  have hE : ∀ p, ∃ e ∈ 𝒪[(A.loc p).Fp], e ≠ 0 ∧ (∀ i j, Sm (A.L p) e⁻¹ ((A.loc p).ιE (Hm i j))) ∧
      (∀ a j, Sm (A.L p) e⁻¹ ((A.loc p).ιE (X a j))) ∧ (∀ a j, Sm (A.L p) e⁻¹ ((A.loc p).ιE (Y a j))) ∧
      (∀ j, Sm (A.L p) e⁻¹ (up p j)) ∧ (good p → e = 1) := by
    intro p
    by_cases hg : good p
    · refine ⟨1, (𝒪[(A.loc p).Fp]).one_mem, one_ne_zero, ?_, ?_, ?_, ?_, fun _ => rfl⟩
      · intro i j; rw [inv_one]; exact (sm_one _).2 (hg.1 i j)
      · intro a j; rw [inv_one]; exact (sm_one _).2 (hg.2.1 a j)
      · intro a j; rw [inv_one]; exact (sm_one _).2 (hg.2.2.1 a j)
      · intro j; rw [inv_one]; exact (sm_one _).2 (hg.2.2.2.1.1 j)
    · obtain ⟨e, he, he0, h⟩ := exists_bound (A.L p)
        (Sum.elim (fun ij : Fin N × Fin N => (A.loc p).ιE (Hm ij.1 ij.2))
          (Sum.elim (fun aj : Fin r × Fin N => (A.loc p).ιE (X aj.1 aj.2))
            (Sum.elim (fun aj : Fin r × Fin N => (A.loc p).ιE (Y aj.1 aj.2)) (fun j => up p j))))
      exact ⟨e, he, he0, fun i j => h (Sum.inl (i, j)), fun a j => h (Sum.inr (Sum.inl (a, j))),
        fun a j => h (Sum.inr (Sum.inr (Sum.inl (a, j)))), fun j => h (Sum.inr (Sum.inr (Sum.inr j))),
        fun h' => absurd h' hg⟩
  choose e he he0 bH bX bY bu he1 using hE

  have hD : ∀ p, ∃ d' ∈ 𝒪[(A.loc p).Fp], d' ≠ 0 ∧ (∃ k ∈ 𝒪[(A.loc p).Fp], d' = d p * k) ∧
      (good p → d' = d p) := by
    intro p
    by_cases h : ((d p : (A.loc p).Fp)) ∈ 𝒪[(A.loc p).Fp]
    · exact ⟨d p, h, Units.ne_zero _, ⟨1, (𝒪[(A.loc p).Fp]).one_mem, (mul_one _).symm⟩, fun _ => rfl⟩
    · have hi : ((d p : (A.loc p).Fp))⁻¹ ∈ 𝒪[(A.loc p).Fp] :=
        ((ValuativeRel.valuation (A.loc p).Fp).valuationSubring.mem_or_inv_mem _).resolve_left h
      refine ⟨1, (𝒪[(A.loc p).Fp]).one_mem, one_ne_zero, ⟨_, hi, (mul_inv_cancel₀ (Units.ne_zero _)).symm⟩,
        fun hg => absurd ?_ h⟩
      obtain ⟨u, hu⟩ := hg.2.2.2.2.1
      rw [← hu]; exact u.1.2
  choose d' hd' hd'0 hdk hd'1 using hD
  have h2O : ∀ p, (2 : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp] := fun p => by
    simpa using (𝒪[(A.loc p).Fp]).natCast_mem 2
  have hne : ∀ p, (2 * d' p * e p ^ 5 : (A.loc p).Fp) ≠ 0 := fun p => by
    haveI := (A.loc p).char0
    exact mul_ne_zero (mul_ne_zero two_ne_zero (hd'0 p)) (pow_ne_zero 5 (he0 p))
  let δ : ∀ p, ((A.loc p).Fp)ˣ := fun p => Units.mk0 _ (hne p)
  have hδ : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = δ p}.Finite := by
    refine hgood.subset fun p hp hg => hp ?_
    obtain ⟨ud, hud⟩ := hg.2.2.2.2.1
    obtain ⟨u2, hu2⟩ := hg.2.2.2.2.2
    refine ⟨u2 * ud, ?_⟩
    simp only [δ, Units.val_mk0, he1 p hg, hd'1 p hg, one_pow, mul_one, Units.val_mul,
      MulMemClass.coe_mul, hu2, hud]

  have AP := GlobalTheory.T.strong_approximation_additive_quadratic_extension A δ hδ
  choose w hw using fun j => AP.2.1 (fun p => up p j) (hint.subset fun p hp h => hp (h.1 j))
  have hv : ∀ p j, Sm (A.L p) (2 * d' p * e p ^ 5) (A.bc p w j - up p j) := fun p j => hw j p
  set u := piQ sig Hm X Y T w with hu
  have LC : ∀ p, _ := fun p => local_choice (A.L p) (Hm.map (A.loc p).ιE) (fun a => A.bc p (X a))
    (fun a => A.bc p (Y a)) T (up p) (horth p) (he p) (he0 p) (hd' p) (bH p) (bX p) (bY p) (bu p)
    (A.bc p w) (hv p)
  have LC' : ∀ p, (∀ j, Sm (A.L p) (2 * d' p) (A.bc p u j - up p j)) ∧
      Sm (A.L p) (2 * d' p) (hf (A.L p) (Hm.map (A.loc p).ιE) (A.bc p u) (A.bc p u) -
        hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p)) := fun p => by
    rw [hu, bc_piQ]; exact LC p

  have hYX : ∀ a b, hq sig Hm (Y a) (X b) = if b = a then 1 else 0 := by
    intro a b; rw [← hq_swap A Hm hH, hXY]; split_ifs <;> simp
  have horthu : ∀ a ∈ T, hq sig Hm u (X a) = 0 ∧ hq sig Hm u (Y a) = 0 := by
    intro b hb
    rw [hu, hq_piQ, hq_piQ]
    constructor
    · simp [hXX, hYX, hb]
    · simp [hXY, hYY, hb]

  set t := hq sig Hm u u with ht
  have hιt : ∀ p, (A.loc p).ιE t = hf (A.L p) (Hm.map (A.loc p).ιE) (A.bc p u) (A.bc p u) :=
    fun p => ((GlobalTheory.HL.RatExt.rational_extend A N p).2.2.2.2.1 Hm u u).symm
  let y : ∀ p, (A.loc p).Ep := fun p => sp p + algebraMap (A.loc p).Fp (A.loc p).Ep 2⁻¹ *
    ((A.loc p).ιE t - hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p))
  have hyd : ∀ p, Sm (A.L p) (d p) (y p - sp p) := by
    intro p
    haveI := (A.loc p).char0
    have h1 : Sm (A.L p) (2⁻¹ : (A.loc p).Fp) (algebraMap (A.loc p).Fp (A.loc p).Ep 2⁻¹) :=
      ⟨1, (A.L p).O.one_mem, (mul_one _).symm⟩
    have h2 := sm_mul (A.L p) h1 (LC' p).2
    rw [← hιt p] at h2
    have e : y p - sp p = algebraMap (A.loc p).Fp (A.loc p).Ep 2⁻¹ *
        ((A.loc p).ιE t - hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p)) := by simp [y]
    rw [e]
    obtain ⟨k, hk, hk'⟩ := hdk p
    exact sm_of_eq (A.L p) h2 (by rw [hk']; field_simp) hk
  have hyO : {p | y p ∉ (A.L p).O}.Finite := by
    refine hgood.subset fun p hp hg => hp ?_
    have e : y p = sp p + (y p - sp p) := by ring
    obtain ⟨ud, hud⟩ := hg.2.2.2.2.1
    have hdO : ((d p : (A.loc p).Fp)) ∈ 𝒪[(A.loc p).Fp] := by rw [← hud]; exact ud.1.2
    rw [e]
    exact (A.L p).O.add_mem hg.2.2.2.1.2 (mem_of_sm (A.L p) (hyd p) hdO)
  have hytr : ∀ p, y p + (A.L p).cj (y p) = (A.loc p).ιE t := by
    intro p
    haveI := (A.loc p).char0
    have hcH : (A.L p).cj (hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p)) =
        hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p) := by
      rw [← hs p, map_add, (A.L p).cj_cj, add_comm]
    have hct : (A.L p).cj ((A.loc p).ιE t) = (A.loc p).ιE t := by
      rw [A.L_cj, (A.loc p).cj_ιE, ht, hq_swap A Hm hH]
    have h2 : algebraMap (A.loc p).Fp (A.loc p).Ep 2⁻¹ * 2 = 1 := by
      rw [← map_ofNat (algebraMap (A.loc p).Fp (A.loc p).Ep) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero,
        map_one]
    simp only [y, map_add, map_mul, map_sub, AlgEquiv.commutes, hcH, hct]
    linear_combination ((A.loc p).ιE t - hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p)) * h2 + hs p
  obtain ⟨s, hs1, hs2⟩ := (GlobalTheory.T.strong_approximation_additive_quadratic_extension A d hd).2.2 t y hyO hytr
  refine ⟨u, s, horthu, hs1, fun p => ⟨fun j => ?_, ?_⟩⟩
  · obtain ⟨k, hk, hk'⟩ := hdk p
    exact sm_of_eq (A.L p) ((LC' p).1 j) (by rw [hk']; ring) ((𝒪[(A.loc p).Fp]).mul_mem (h2O p) hk)
  · have h1 : Sm (A.L p) ((d p : (A.loc p).Fp)) ((A.loc p).ιE s - y p) := hs2 p
    have e : (A.loc p).ιE s - sp p = ((A.loc p).ιE s - y p) + (y p - sp p) := by ring
    rw [e]
    exact sm_add (A.L p) h1 (hyd p)

end GlobalTheory.HL.EichlerParams
end
end

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory.HL.SAN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_symplectic_basis_local_extension : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (hH : ∀ i j, sig (Hm j i) = Hm i j) (X Y : Fin r → Fin N → E) (T : Finset (Fin r)) (hXY : ∀ a b, hq sig Hm (X a) (Y b) = if a = b then 1 else 0) (hXX : ∀ a b, hq sig Hm (X a) (X b) = 0) (hYY : ∀ a b, hq sig Hm (Y a) (Y b) = 0) (up : ∀ p, Fin N → (A.loc p).Ep) (sp : ∀ p, (A.loc p).Ep) (horth : ∀ p, ∀ a ∈ T, hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (A.bc p (X a)) = 0 ∧ hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (A.bc p (Y a)) = 0) (hs : ∀ p, sp p + (A.L p).cj (sp p) = hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p)) (hint : {p | ¬ ((∀ j, up p j ∈ (A.L p).O) ∧ sp p ∈ (A.L p).O)}.Finite) (d : ∀ p, ((A.loc p).Fp)ˣ) (hd : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = d p}.Finite), ∃ (u : Fin N → E) (s : E), (∀ a ∈ T, hq sig Hm u (X a) = 0 ∧ hq sig Hm u (Y a) = 0) ∧ s + sig s = hq sig Hm u u ∧ ∀ p, (∀ j, ∃ o ∈ (A.L p).O, (A.loc p).ιE (u j) - up p j = algebraMap (A.loc p).Fp (A.loc p).Ep (d p) * o) ∧ ∃ o ∈ (A.L p).O, (A.loc p).ιE s - sp p = algebraMap (A.loc p).Fp (A.loc p).Ep (d p) * o := by
  atlas_forward_decl GlobalTheory.HL.EichlerParams.strong_approx_params
end

section
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section
namespace GlobalTheory.HL.SAN

private theorem hf_add_left_flag_measures' {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N : ℕ} (Hm : Matrix (Fin N) (Fin N) E)
    (a b y : Fin N → E) : hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem hf_smul_left_flag_measures' {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N : ℕ} (Hm : Matrix (Fin N) (Fin N) E)
    (c : E) (a y : Fin N → E) : hf L Hm (c • a) y = c * hf L Hm a y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem hq_sub_left {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {N : ℕ}
    (Hm : Matrix (Fin N) (Fin N) E) (a b y : Fin N → E) :
    hq sig Hm (a - b) y = hq sig Hm a y - hq sig Hm b y := by
  simp only [hq, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem hq_neg_left {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {N : ℕ}
    (Hm : Matrix (Fin N) (Fin N) E) (a y : Fin N → E) :
    hq sig Hm (-a) y = -hq sig Hm a y := by
  simp only [hq, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

private theorem algebraMap_integer_mem_O {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : LocE F E) (a : 𝒪[F]) : algebraMap F E (a : F) ∈ L.O := by
  rw [L.O_def]
  exact (isIntegral_algebraMap (x := a)).algebraMap

theorem core {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) (Λ : G.Lt) (hΛ : Submodule.IsLattice E Λ)
  (c : ∀ p, ((A.loc p).Fp)ˣ) (hc : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite)
  (n : ∀ p, (G.S p).GLV) (hn : {p | n p • A.lat p Λ ≠ A.lat p Λ}.Finite)
  (gF : ∀ p, Fin (r+1) → (G.S p).V) (gsF : ∀ p, Fin r → (G.S p).V) (X Y : Fin r → G.V)
  (hsel : ∀ p, (gF p = (G.S p).f ∧ gsF p = (G.S p).es) ∨ (gF p = (G.S p).f' ∧ gsF p = (G.S p).es'))
  (hX : ∀ p (a : Fin r), algebraMap (A.loc p).Fp (A.loc p).Ep ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • gF p a.castSucc = A.bc p (X a))
  (hY : ∀ p (a : Fin r), gsF p a = algebraMap (A.loc p).Fp (A.loc p).Ep ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (Y a))
  (hnN : ∀ p, n p ∈ (G.S p).Nof (gF p)) :
  ∃ g : G.GLV, (∀ p, ∃ g' ∈ (G.S p).Nof (gF p), A.Ext p g g') ∧ ∀ p g', A.Ext p g g' → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y := by
  classical
  have hinj : ∀ p, Function.Injective (A.loc p).ιE := fun p => by
    have := PlacesInt.nontrivial_Ep (A.loc p)
    exact (A.loc p).ιE.injective
  have hform : ∀ p (x y : Fin (k + 2 * r + 1) → E),
      (G.S p).h (A.bc p x) (A.bc p y) = (A.loc p).ιE (hq sig G.Hm x y) := by
    intro p x y
    have h := (RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1 G.Hm x y
    show hf (A.L p) (G.S p).Hm _ _ = _
    rw [G.Hm_eq p]
    exact h
  have hconj : ∀ p z, (A.L p).cj ((A.loc p).ιE z) = (A.loc p).ιE (sig z) := fun p z => by
    rw [A.L_cj p]
    exact (A.loc p).cj_ιE z
  obtain ⟨p0⟩ := exists_place F
  have hsig : ∀ z, sig (sig z) = z := fun z => by
    apply hinj p0
    rw [← hconj, ← hconj]
    exact (A.L p0).cj_cj _
  have hH : ∀ i j, sig (G.Hm j i) = G.Hm i j := fun i j => by
    have h2 := congrFun (congrFun (G.S p0).herm.1 i) j
    rw [G.Hm_eq p0] at h2
    simp only [cT, Matrix.map_apply] at h2
    apply hinj p0
    rw [← hconj]
    exact h2
  have hqsym : ∀ x y, hq sig G.Hm x y = sig (hq sig G.Hm y x) := by
    intro x y
    simp only [hq, map_sum, map_mul, hsig]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hH j i]
    ring
  have hXa : ∀ p (i : Fin r), algebraMap (A.loc p).Fp (A.loc p).Ep
      (((G.c p ^ (r - (i : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp) • gF p i.castSucc = A.bc p (X i) :=
    fun p i => by
      rw [Units.val_pow_eq_pow_val]
      exact hX p i
  have hYa : ∀ p (i : Fin r), gsF p i = algebraMap (A.loc p).Fp (A.loc p).Ep
      (((G.c p ^ (r - (i : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp) • A.bc p (Y i) :=
    fun p i => by
      rw [Units.val_pow_eq_pow_val]
      exact hY p i
  have hR : ∀ p, (∀ i j, (G.S p).h (A.bc p (X i)) (A.bc p (Y j)) = if i = j then 1 else 0) ∧
      (∀ i j, (G.S p).h (A.bc p (X i)) (A.bc p (X j)) = 0) ∧
      (∀ i j, (G.S p).h (A.bc p (Y i)) (A.bc p (Y j)) = 0) ∧
      ∀ m : (G.S p).GLV, m ∈ (G.S p).Nof (gF p) ↔ ∃ (u : Fin r → (G.S p).V) (s : Fin r → (A.loc p).Ep)
        (e : Fin r → (G.S p).GLV), (∀ i, (∀ j, j ≤ i → (G.S p).h (u i) (A.bc p (X j)) = 0 ∧
          (G.S p).h (u i) (A.bc p (Y j)) = 0) ∧ s i + (A.L p).cj (s i) = (G.S p).h (u i) (u i) ∧
          ∀ v, e i v = eich (A.L p) (G.S p).Hm (A.bc p (X i)) (u i) (s i) v) ∧ m = (List.ofFn e).prod := by
    intro p
    have := (A.loc p).lf
    have := (A.loc p).char0
    exact GlobalTheory.T.hermitianFlagUnipotent_normalForm_rescaled (A.L p) r k (G.S p) (gF p) (gsF p) (hsel p) (fun i => G.c p ^ (r - (i : ℕ)))
      (fun i => A.bc p (X i)) (fun i => A.bc p (Y i)) (hXa p) (hYa p)
  choose up sp ep hup hn_eq using fun p => ((hR p).2.2.2 (n p)).1 (hnN p)
  have hXY : ∀ a b, hq sig G.Hm (X a) (Y b) = if a = b then 1 else 0 := fun a b => by
    apply hinj p0
    rw [← hform, (hR p0).1 a b]
    split_ifs <;> simp
  have hXX : ∀ a b, hq sig G.Hm (X a) (X b) = 0 := fun a b => by
    apply hinj p0
    rw [← hform, (hR p0).2.1 a b, map_zero]
  have hYY : ∀ a b, hq sig G.Hm (Y a) (Y b) = 0 := fun a b => by
    apply hinj p0
    rw [← hform, (hR p0).2.2.1 a b, map_zero]
  set Bad : Set (HeightOneSpectrum (𝓞 F)) :=
    {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p} ∪
    {p | A.lat p Λ ≠ Submodule.span (A.L p).O
      (Set.range fun i => (Pi.single i 1 : Fin (k + 2 * r + 1) → (A.loc p).Ep))} ∪
    {p | n p • A.lat p Λ ≠ A.lat p Λ} ∪
    (⋃ i, ⋃ j, {p | (A.loc p).ιE (G.Hm i j) ∉ (A.L p).O}) ∪
    (⋃ a, ⋃ j, {p | (A.loc p).ιE (X a j) ∉ (A.L p).O}) ∪
    (⋃ a, ⋃ j, {p | (A.loc p).ιE (Y a j) ∉ (A.L p).O}) with hBad
  have hlatP := GlobalTheory.T.numberField_lattice_determined_by_local_lattices A (k + 2 * r + 1) Λ hΛ
  have hBadF : Bad.Finite := by
    have hi := (PlacesInt.integers_local A).2.1
    refine ((((hc.union hlatP.2.2).union hn).union ?_).union ?_).union ?_ <;>
      exact Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => hi _
  have hgood : ∀ p, p ∉ Bad →
      (∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p) ∧
      A.lat p Λ = Submodule.span (A.L p).O
        (Set.range fun i => (Pi.single i 1 : Fin (k + 2 * r + 1) → (A.loc p).Ep)) ∧
      n p • A.lat p Λ = A.lat p Λ ∧ (∀ i j, (A.loc p).ιE (G.Hm i j) ∈ (A.L p).O) ∧
      (∀ a j, (A.loc p).ιE (X a j) ∈ (A.L p).O) ∧ (∀ a j, (A.loc p).ιE (Y a j) ∈ (A.L p).O) := by
    intro p hp
    refine ⟨Classical.byContradiction fun h => hp ?_, Classical.byContradiction fun h => hp ?_,
      Classical.byContradiction fun h => hp ?_, fun i j => Classical.byContradiction fun h => hp ?_,
      fun a j => Classical.byContradiction fun h => hp ?_, fun a j => Classical.byContradiction fun h => hp ?_⟩
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, h⟩⟩)))
    · exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨j, h⟩⟩))
    · exact Or.inr (Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨j, h⟩⟩)
  have hstd : ∀ p, p ∉ Bad → ∀ x : Fin (k + 2 * r + 1) → (A.loc p).Ep,
      ((∀ j, (List.ofFn (ep p)).prod x j ∈ (A.L p).O) ↔ ∀ j, x j ∈ (A.L p).O) := by
    intro p hp x
    obtain ⟨-, hl, hnl, -⟩ := hgood p hp
    rw [← mem_coord (A.L p) ((List.ofFn (ep p)).prod x), ← mem_coord (A.L p) x, ← hl, ← hn_eq p]
    constructor
    · intro h
      rw [← hnl] at h
      obtain ⟨y, hy, hyx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
      rw [LinearEquiv.smul_def] at hyx
      rwa [← (n p).injective hyx]
    · intro h
      rw [← hnl]
      exact Submodule.smul_mem_pointwise_smul _ _ _ h
  have hint : ∀ p, p ∉ Bad → (∀ i j, up p i j ∈ (A.L p).O) ∧ ∀ i, sp p i ∈ (A.L p).O := by
    intro p hp
    obtain ⟨-, -, -, hHm, hXi, hYi⟩ := hgood p hp
    have := (A.loc p).lf
    have := (A.loc p).char0
    exact GlobalTheory.T.hermitianEichlerProduct_params_integral (A.L p) _ r (G.S p).Hm (G.S p).herm.1
      (fun i j => by rw [G.Hm_eq p]; exact hHm i j) (fun i => A.bc p (X i)) (fun i => A.bc p (Y i))
      (up p) (sp p) (ep p) (fun i j => hXi i j) (fun i j => hYi i j) (hR p).1 (hR p).2.1
      (fun i j hj => (hup p i).1 j hj) (fun i => (hup p i).2.1) (fun i v => (hup p i).2.2 v) (hstd p hp)
  have hdex : ∀ p, ∃ d : ((A.loc p).Fp)ˣ, (p ∉ Bad → d = 1) ∧
      ∀ (u' : Fin r → Fin (k + 2 * r + 1) → (A.loc p).Ep) (s' : Fin r → (A.loc p).Ep)
        (e' : Fin r → (G.S p).GLV),
        (∀ i v, e' i v = eich (A.L p) (G.S p).Hm (A.bc p (X i)) (u' i) (s' i) v) →
        (∀ i j, ∃ o ∈ (A.L p).O, u' i j - up p i j =
          algebraMap (A.loc p).Fp (A.loc p).Ep (d : (A.loc p).Fp) * o) →
        (∀ i, ∃ o ∈ (A.L p).O, s' i - sp p i =
          algebraMap (A.loc p).Fp (A.loc p).Ep (d : (A.loc p).Fp) * o) →
        ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, ((List.ofFn (ep p)).prod).symm ((List.ofFn e').prod x) - x =
          algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y := by
    intro p
    have := (A.loc p).lf
    have := (A.loc p).char0
    by_cases hp : p ∈ Bad
    · obtain ⟨d, hd⟩ := GlobalTheory.T.hermitianEichlerProduct_continuous_on_lattice (A.L p) (k + 2 * r + 1) r (G.S p).Hm (fun i => A.bc p (X i))
        (up p) (sp p) (ep p) (fun i v => (hup p i).2.2 v) (A.lat p Λ) (hlatP.2.1 p) (c p)
      exact ⟨d, fun h => absurd hp h, hd⟩
    · refine ⟨1, fun _ => rfl, ?_⟩
      intro u' s' e' he' hu' hs' x hx
      obtain ⟨⟨cu, hcu⟩, hl, -, hHm, hXi, -⟩ := hgood p hp
      obtain ⟨hui, hsi⟩ := hint p hp
      have hu'i : ∀ i j, u' i j ∈ (A.L p).O := fun i j => by
        obtain ⟨o, ho, h⟩ := hu' i j
        have h' : u' i j - up p i j = o := by simpa using h
        rw [show u' i j = up p i j + o by rw [← h']; ring]
        exact add_mem (hui i j) ho
      have hs'i : ∀ i, s' i ∈ (A.L p).O := fun i => by
        obtain ⟨o, ho, h⟩ := hs' i
        have h' : s' i - sp p i = o := by simpa using h
        rw [show s' i = sp p i + o by rw [← h']; ring]
        exact add_mem (hsi i) ho
      have hHm' : ∀ i j, (G.S p).Hm i j ∈ (A.L p).O := fun i j => by rw [G.Hm_eq p]; exact hHm i j
      have hx' : ∀ j, x j ∈ (A.L p).O := (mem_coord (A.L p) x).1 (hl ▸ hx)
      have hz := int_prod (A.L p) hHm' r (fun i => A.bc p (X i)) u' s' e' (fun i j => hXi i j) hu'i hs'i
        he' x hx'
      have hw := (hstd p hp (((List.ofFn (ep p)).prod).symm ((List.ofFn e').prod x))).1
        (by rw [LinearEquiv.apply_symm_apply]; exact hz)
      have hci : algebraMap (A.loc p).Fp (A.loc p).Ep (((c p)⁻¹ : ((A.loc p).Fp)ˣ) : (A.loc p).Fp) ∈ (A.L p).O := by
        have : (((c p)⁻¹ : ((A.loc p).Fp)ˣ) : (A.loc p).Fp) = ((cu⁻¹ : (𝒪[(A.loc p).Fp])ˣ) : 𝒪[(A.loc p).Fp]) := by
          rw [Units.val_inv_eq_inv_val, ← hcu, eq_comm]
          apply eq_inv_of_mul_eq_one_left
          exact_mod_cast Units.inv_mul cu
        rw [this]
        exact algebraMap_integer_mem_O (A.L p) _
      refine ⟨algebraMap (A.loc p).Fp (A.loc p).Ep (((c p)⁻¹ : ((A.loc p).Fp)ˣ) : (A.loc p).Fp) •
        (((List.ofFn (ep p)).prod).symm ((List.ofFn e').prod x) - x), ?_, ?_⟩
      · rw [hl]
        refine (mem_coord (A.L p) _).2 fun j => ?_
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        exact mul_mem hci (sub_mem (hw j) (hx' j))
      · rw [smul_smul, ← map_mul, Units.mul_inv, map_one, one_smul]
  choose d hd1 hd2 using hdex
  have hQex : ∀ i : Fin r, ∃ (u : Fin (k + 2 * r + 1) → E) (s : E),
      (∀ a ∈ (Finset.univ.filter fun j : Fin r => j ≤ i),
        hq sig G.Hm u (X a) = 0 ∧ hq sig G.Hm u (Y a) = 0) ∧ s + sig s = hq sig G.Hm u u ∧
      ∀ p, (∀ j, ∃ o ∈ (A.L p).O, (A.loc p).ιE (u j) - up p i j =
          algebraMap (A.loc p).Fp (A.loc p).Ep (d p : (A.loc p).Fp) * o) ∧
        ∃ o ∈ (A.L p).O, (A.loc p).ιE s - sp p i =
          algebraMap (A.loc p).Fp (A.loc p).Ep (d p : (A.loc p).Fp) * o := by
    intro i
    refine GlobalTheory.T.hermitian_symplectic_basis_local_extension A (k + 2 * r + 1) r G.Hm hH X Y (Finset.univ.filter fun j : Fin r => j ≤ i)
      hXY hXX hYY (fun p => up p i) (fun p => sp p i) (fun p a ha => ?_) (fun p => ?_) ?_ d ?_
    · have h := (hup p i).1 a (Finset.mem_filter.1 ha).2
      simp only [Frames.h, G.Hm_eq p] at h
      exact h
    · have h := (hup p i).2.1
      simp only [Frames.h, G.Hm_eq p] at h
      exact h
    · exact hBadF.subset fun p hp => Classical.byContradiction fun hpb =>
        hp ⟨fun j => (hint p hpb).1 i j, (hint p hpb).2 i⟩
    · exact hBadF.subset fun p hp => Classical.byContradiction fun hpb =>
        hp ⟨1, by rw [hd1 p hpb]; simp⟩
  choose uQ sQ hQ using hQex
  have hinjQ : ∀ i, Function.Injective (eQ sig G.Hm (X i) (uQ i) (sQ i)) := by
    intro i
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv' : v + hq sig G.Hm v (uQ i) • X i - hq sig G.Hm v (X i) • (uQ i + sQ i • X i) = 0 := hv
    have hii : i ∈ (Finset.univ.filter fun j : Fin r => j ≤ i) := by simp
    have hux : hq sig G.Hm (uQ i) (X i) = 0 := ((hQ i).1 i hii).1
    have hxu : hq sig G.Hm (X i) (uQ i) = 0 := by rw [hqsym, hux, map_zero]
    have hb : hq sig G.Hm v (X i) = 0 := by
      have h := congrArg (fun w => hq sig G.Hm w (X i)) hv'
      have hz0 : hq sig G.Hm 0 (X i) = 0 := by simp [hq]
      simp only [hq_sub_left, hq_add_l, hq_smul_l, hux, hXX i i, hz0] at h
      simpa using h
    rw [hb, zero_smul, sub_zero] at hv'
    have hv2 : v = -(hq sig G.Hm v (uQ i) • X i) := eq_neg_of_add_eq_zero_left hv'
    have ha : hq sig G.Hm v (uQ i) = 0 := by
      have h := congrArg (fun w => hq sig G.Hm w (uQ i)) hv2
      simp only [hq_neg_left, hq_smul_l, hxu, mul_zero, neg_zero] at h
      exact h
    rw [hv2, ha, zero_smul, neg_zero]
  let eR : Fin r → G.GLV := fun i => LinearEquiv.ofInjectiveEndo (eQ sig G.Hm (X i) (uQ i) (sQ i)) (hinjQ i)
  have heR : ∀ i v, eR i v = eQ sig G.Hm (X i) (uQ i) (sQ i) v := fun i v => by
    simp only [eR, LinearEquiv.coe_ofInjectiveEndo]
  have hext : ∀ p i, ∃ e' : (G.S p).GLV, A.Ext p (eR i) e' ∧ ∀ v, e' v =
      eich (A.L p) (G.S p).Hm (A.bc p (X i)) (A.bc p (uQ i)) ((A.loc p).ιE (sQ i)) v := by
    intro p i
    obtain ⟨e', he', -⟩ := (RatExt.rational_extend A (k + 2 * r + 1) p).2.2.1 (eR i)
    refine ⟨e', he', fun v => ?_⟩
    let M : (Fin (k + 2 * r + 1) → (A.loc p).Ep) →ₗ[(A.loc p).Ep] (Fin (k + 2 * r + 1) → (A.loc p).Ep) :=
      { toFun := fun w => eich (A.L p) (G.S p).Hm (A.bc p (X i)) (A.bc p (uQ i)) ((A.loc p).ιE (sQ i)) w
        map_add' := fun a b => by
          simp only [eich, hf_add_left_flag_measures']
          module
        map_smul' := fun t a => by
          simp only [eich, hf_smul_left_flag_measures', RingHom.id_apply]
          module }
    have hlin := RatExt.lin_ext (A.loc p).ιE (e' : (Fin (k + 2 * r + 1) → (A.loc p).Ep) →ₗ[(A.loc p).Ep] _) M
      (fun x => by
        show e' (A.bc p x) = eich (A.L p) (G.S p).Hm (A.bc p (X i)) (A.bc p (uQ i)) ((A.loc p).ιE (sQ i)) (A.bc p x)
        rw [he' x, heR, bc_eQ, G.Hm_eq p])
    exact LinearMap.congr_fun hlin v
  choose eL heL heL' using hext
  have hmem : ∀ p, (List.ofFn (eL p)).prod ∈ (G.S p).Nof (gF p) := by
    intro p
    refine ((hR p).2.2.2 _).2 ⟨fun i => A.bc p (uQ i), fun i => (A.loc p).ιE (sQ i), eL p,
      fun i => ⟨fun j hj => ?_, ?_, heL' p i⟩, rfl⟩
    · have hj' : j ∈ (Finset.univ.filter fun j : Fin r => j ≤ i) := by simp [hj]
      rw [hform, hform, ((hQ i).1 j hj').1, ((hQ i).1 j hj').2, map_zero]
      exact ⟨rfl, rfl⟩
    · rw [hform, ← (hQ i).2.1, map_add, hconj]
  refine ⟨(List.ofFn eR).prod, fun p => ⟨_, hmem p, ext_prod A p r eR (eL p) (heL p)⟩, ?_⟩
  intro p g' hg' x hx
  have hg'eq : g' = (List.ofFn (eL p)).prod :=
    ((RatExt.rational_extend A (k + 2 * r + 1) p).2.2.1 ((List.ofFn eR).prod)).unique hg'
      (ext_prod A p r eR (eL p) (heL p))
  rw [hg'eq, hn_eq p]
  exact hd2 p (fun i => A.bc p (uQ i)) (fun i => (A.loc p).ιE (sQ i)) (eL p) (heL' p)
    (fun i j => ((hQ i).2.2 p).1 j) (fun i => ((hQ i).2.2 p).2) x hx

theorem strong_approximation_unipotent : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsLattice E Λ → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ n : ∀ p, (G.S p).GLV, {p | n p • A.lat p Λ ≠ A.lat p Λ}.Finite → ((∀ p, n p ∈ (G.S p).N) → ∃ g ∈ G.N, ∀ p g', A.Ext p g g' → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y) ∧ ((∀ p, n p ∈ (G.S p).N') → ∃ g ∈ G.N', ∀ p g', A.Ext p g g' → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y) := by
  intro F E _ _ _ _ _ sig A r k G Λ hΛ c hc n hn
  refine ⟨fun hN => ?_, fun hN => ?_⟩
  · obtain ⟨g, hg1, hg2⟩ := core A r k G Λ hΛ c hc n hn (fun p => (G.S p).f) (fun p => (G.S p).es)
      (fun a => G.f a.castSucc) G.es (fun _ => Or.inl ⟨rfl, rfl⟩)
      (fun p a => by
        have h := G.f_eq p a.castSucc
        rwa [Fin.val_castSucc] at h)
      (fun p a => G.es_eq p a) hN
    exact ⟨g, hg1, hg2⟩
  · obtain ⟨g, hg1, hg2⟩ := core A r k G Λ hΛ c hc n hn (fun p => (G.S p).f') (fun p => (G.S p).es')
      (fun a => G.f' a.castSucc) G.es' (fun _ => Or.inr ⟨rfl, rfl⟩)
      (fun p a => by
        have h := G.f'_eq p a.castSucc
        rwa [Fin.val_castSucc] at h)
      (fun p a => G.es'_eq p a) hN
    exact ⟨g, hg1, hg2⟩

end GlobalTheory.HL.SAN
end
end

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strong_approximation_unipotent_alt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsLattice E Λ → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ n : ∀ p, (G.S p).GLV, {p | n p • A.lat p Λ ≠ A.lat p Λ}.Finite → ((∀ p, n p ∈ (G.S p).N) → ∃ g ∈ G.N, ∀ p g', A.Ext p g g' → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y) ∧ ((∀ p, n p ∈ (G.S p).N') → ∃ g ∈ G.N', ∀ p g', A.Ext p g g' → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y) := by
  atlas_forward_decl GlobalTheory.HL.SAN.strong_approximation_unipotent
end
