import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ExpToSat
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PExpbSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriGlCasselmanDatum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriDoubleCosetTorusNilpotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagPairs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureCballZpow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterBlockValue

section
open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwahori_double_coset_torus_nilpotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ x : Fin n → ℤ, StrictAnti x → ∀ a ∈ iwahori k (Fin n), ∀ b ∈ iwahori k (Fin n), ∃ m ∈ nO k n, ∃ c ∈ iwahori k (Fin n), a * tor ϖ x * b = m * tor ϖ x * c := by
  first | exact @GlobalTheory.CompanionTheory.IwJac.iwahori_mul_tor_mul_iwahori | exact GlobalTheory.CompanionTheory.IwJac.iwahori_mul_tor_mul_iwahori | (intros; apply GlobalTheory.CompanionTheory.IwJac.iwahori_mul_tor_mul_iwahori <;> assumption)
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.IwJac.FiltTop

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem val_le_one_of_ord {ϖ : kˣ} (h : ord k ϖ = 1) : valuation k (ϖ : k) ≤ 1 := by
  have h' : -WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k (valuation k (ϖ : k))) = 1 := h
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (valuation k (ϖ : k)) ≠ 0 := by simp
  have h1 : WithZero.log (φ (valuation k (ϖ : k))) = -1 := by omega
  rw [← φ.strictMono.le_iff_le, map_one, ← WithZero.exp_log h0, h1, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem tor_neg (ϖ : kˣ) (x : Fin n → ℤ) : tor ϖ (-x) = (tor ϖ x)⁻¹ := by
  unfold tor; rw [← map_inv]; congr 1; funext i; simp [_root_.zpow_neg]

theorem conj_tor_apply (ϖ : kˣ) (y : Fin n → ℤ) (m : GL (Fin n) k) (i j : Fin n) :
    ((MulAut.conj (tor ϖ y) m : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      ((ϖ ^ (y i - y j) : kˣ) : k) * (m : Matrix (Fin n) (Fin n) k) i j := by
  rw [MulAut.conj_apply, ← tor_neg, Units.val_mul, Units.val_mul]
  unfold tor
  rw [val_diagT, val_diagT, mul_diagonal, diagonal_mul, _root_.zpow_sub]
  simp only [Pi.neg_apply, _root_.zpow_neg, Units.val_mul, Units.val_inv_eq_inv_val]
  ring

theorem int_of_mem_KO {m : GL (Fin n) k} (h : m ∈ GlobalTheory.SplitWeil.KO k (Fin n)) (i j : Fin n) :
    valuation k ((m : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
  obtain ⟨u, rfl⟩ := h
  exact (u.val i j).2

theorem mem_KO_of_int {g : GL (Fin n) k}
    (h1 : ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1)
    (h2 : ∀ i j, valuation k (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ 1) :
    g ∈ GlobalTheory.SplitWeil.KO k (Fin n) := by
  have inj : Function.Injective ((algebraMap 𝒪[k] k).mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : (algebraMap 𝒪[k] k).mapMatrix A = g.val := rfl
  have hB : (algebraMap 𝒪[k] k).mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem mem_nO_of {g : GL (Fin n) k} (hg : g ∈ unipB k (Fin n))
    (h1 : ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1)
    (h2 : ∀ i j, valuation k (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ 1) :
    g ∈ nO k n := by
  refine ⟨mem_iwahori.2 ⟨mem_KO_of_int h1 h2, fun i j hji => ?_⟩, hg⟩
  rw [((mem_unipB k).1 hg).1 i j hji, map_zero]
  exact zero_lt_one

theorem conj_mem_nO {ϖ : kˣ} {y : Fin n → ℤ} {m : GL (Fin n) k} (hm : m ∈ unipB k (Fin n))
    (h1 : ∀ i j, i < j →
      valuation k (((ϖ ^ (y i - y j) : kˣ) : k) * (m : Matrix (Fin n) (Fin n) k) i j) ≤ 1)
    (h2 : ∀ i j, i < j →
      valuation k (((ϖ ^ (y i - y j) : kˣ) : k) * ((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ 1) :
    MulAut.conj (tor ϖ y) m ∈ nO k n := by
  have hu : ∀ m' ∈ unipB k (Fin n), (∀ i j, i < j →
      valuation k (((ϖ ^ (y i - y j) : kˣ) : k) * (m' : Matrix (Fin n) (Fin n) k) i j) ≤ 1) →
      MulAut.conj (tor ϖ y) m' ∈ unipB k (Fin n) ∧
        ∀ i j, valuation k (((MulAut.conj (tor ϖ y) m' : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    intro m' hm' h
    obtain ⟨h0, hd⟩ := (mem_unipB k).1 hm'
    refine ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, fun i j => ?_⟩
    · rw [conj_tor_apply, h0 i j hji, mul_zero]
    · rw [conj_tor_apply, hd, sub_self, zpow_zero, Units.val_one, mul_one]
    · rw [conj_tor_apply]
      rcases lt_trichotomy i j with hij | rfl | hij
      · exact h i j hij
      · rw [hd, sub_self, zpow_zero, Units.val_one, mul_one, map_one]
      · rw [h0 i j hij, mul_zero, map_zero]; exact zero_le'
  obtain ⟨a1, a2⟩ := hu m hm h1
  obtain ⟨_, b2⟩ := hu m⁻¹ (inv_mem hm) h2
  exact mem_nO_of a1 a2 (by rw [← map_inv]; exact b2)

theorem filt_top (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (ϖ : kˣ) (hϖ : ord k ϖ = 1) (x : Fin n → ℤ) (hx : StrictAnti x) :
    filt ϖ x n = (nO k n).map (MulAut.conj (tor ϖ x)).toMonoidHom := by
  have hv := val_le_one_of_ord hϖ
  have pint : ∀ i j : Fin n, i < j → valuation k ((ϖ ^ (x i - x j) : kˣ) : k) ≤ 1 := by
    intro i j hij
    obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 (hx hij).le)
    rw [he, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
    exact pow_le_one₀ zero_le' hv
  have cancel : ∀ i j : Fin n, valuation k ((ϖ ^ ((-x) i - (-x) j) : kˣ) : k) *
      valuation k ((ϖ ^ (x i - x j) : kˣ) : k) = 1 := by
    intro i j
    rw [← map_mul, ← Units.val_mul, ← _root_.zpow_add,
      show (-x) i - (-x) j + (x i - x j) = 0 by simp only [Pi.neg_apply]; ring,
      zpow_zero, Units.val_one, map_one]
  ext g
  rw [Subgroup.mem_map, mem_filt]
  constructor
  · rintro ⟨hg, dg, dg'⟩
    refine ⟨MulAut.conj (tor ϖ (-x)) g, conj_mem_nO hg.2 (fun i j hij => ?_) (fun i j hij => ?_), ?_⟩
    · rw [map_mul, ← cancel i j]
      exact mul_le_mul_right (dg i j hij (by have := j.isLt; omega)) _
    · rw [map_mul, ← cancel i j]
      exact mul_le_mul_right (dg' i j hij (by have := j.isLt; omega)) _
    · show MulAut.conj (tor ϖ x) (MulAut.conj (tor ϖ (-x)) g) = g
      rw [tor_neg]
      simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨m, hm, rfl⟩
    show MulAut.conj (tor ϖ x) m ∈ nO k n ∧ Deep ϖ x n (MulAut.conj (tor ϖ x) m) ∧
      Deep ϖ x n (MulAut.conj (tor ϖ x) m)⁻¹
    have key : ∀ m' ∈ nO k n, ∀ i j : Fin n,
        valuation k (((ϖ ^ (x i - x j) : kˣ) : k) * (m' : Matrix (Fin n) (Fin n) k) i j) ≤
          valuation k ((ϖ ^ (x i - x j) : kˣ) : k) := by
      intro m' hm' i j
      rw [map_mul]
      exact mul_le_of_le_one_right' (int_of_mem_KO (iwahori_le_KO k (Fin n) hm'.1) i j)
    have hm' := inv_mem hm
    refine ⟨conj_mem_nO hm.2 (fun i j hij => (key m hm i j).trans (pint i j hij))
      (fun i j hij => (key _ hm' i j).trans (pint i j hij)), fun i j _ _ => ?_, fun i j _ _ => ?_⟩
    · rw [conj_tor_apply]; exact key m hm i j
    · rw [← map_inv, conj_tor_apply]; exact key _ hm' i j

theorem filt_top' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ x : Fin n → ℤ, StrictAnti x →
      filt ϖ x n = (nO k n).map (MulAut.conj (tor ϖ x)).toMonoidHom :=
  fun k _ _ _ _ n ϖ hϖ x hx => filt_top k n ϖ hϖ x hx

end GlobalTheory.CompanionTheory.IwJac.FiltTop

end
end

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_eq_conj_nilpotent_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ x : Fin n → ℤ, StrictAnti x → filt ϖ x n = (nO k n).map (MulAut.conj (tor ϖ x)).toMonoidHom := by
  atlas_forward_decl GlobalTheory.CompanionTheory.IwJac.FiltTop.filt_top'
end

section
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical

namespace GlobalTheory.CompanionTheory.IwJac.StepIdx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem val_lt_one {ϖ : kˣ} (h : ord k ϖ = 1) : valuation k (ϖ : k) < 1 := by
  have h1 : ¬ valuation k ((1 : kˣ) : k) ≤ valuation k (ϖ : k) := by
    rw [GlobalTheory.OrdShellInt.val_le_iff_ord, ord_eq_zero (x := (1 : kˣ)) (by simp)]; omega
  simpa using h1

theorem val_le_of_lt_one {ϖ : kˣ} (h : ord k ϖ = 1) {y : k} (hy : valuation k y < 1) :
    valuation k y ≤ valuation k (ϖ : k) := by
  by_cases h0 : y = 0
  · subst h0; simp
  have h1 : ¬ valuation k ((1 : kˣ) : k) ≤ valuation k ((Units.mk0 y h0 : kˣ) : k) := by
    simpa using hy
  rw [GlobalTheory.OrdShellInt.val_le_iff_ord, ord_eq_zero (x := (1 : kˣ)) (by simp)] at h1
  have h2 := (GlobalTheory.OrdShellInt.val_le_iff_ord (Units.mk0 y h0) ϖ).2 (by omega)
  simpa using h2

def om (ϖ : kˣ) (h : ord k ϖ = 1) : 𝒪[k] := ⟨ϖ, (val_lt_one h).le⟩

theorem om_pow_dvd_iff {ϖ : kˣ} (h : ord k ϖ = 1) (a : 𝒪[k]) (m : ℕ) :
    om ϖ h ^ m ∣ a ↔ valuation k (a : k) ≤ valuation k ((ϖ : k) ^ m) := by
  refine ((Valuation.integer.integers (valuation k)).dvd_iff_le).trans ?_
  simp only [map_pow]
  rfl

theorem maximalIdeal_eq {ϖ : kˣ} (h : ord k ϖ = 1) :
    IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {om ϖ h} := by
  ext a
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one, Ideal.mem_span_singleton]
  have h1 := om_pow_dvd_iff h a 1
  rw [pow_one, pow_one] at h1
  rw [h1]
  constructor
  · intro ha
    exact val_le_of_lt_one h (lt_of_le_of_ne a.2 ha)
  · intro ha
    exact (lt_of_le_of_lt ha (val_lt_one h)).ne

theorem card_quot {ϖ : kˣ} (h : ord k ϖ = 1) (m : ℕ) :
    Nat.card (𝒪[k] ⧸ Ideal.span {om ϖ h ^ m}) = Nat.card 𝓀[k] ^ m := by
  rw [← Ideal.span_singleton_pow, ← maximalIdeal_eq h]
  have hq := cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal 𝒪[k]) (IsDiscreteValuationRing.not_a_field _) (i := m)
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hq
  exact hq

def ent (g : GL (Fin n) k) (i j : Fin n) : 𝒪[k] :=
  if h : valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 then ⟨_, h⟩ else 0

theorem nO_int {g : GL (Fin n) k} (hg : g ∈ nO k n) (i j : Fin n) :
    valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
  obtain ⟨⟨h, rfl⟩, -⟩ := mem_iwahori.1 hg.1
  exact ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i j).2

theorem ent_coe {g : GL (Fin n) k} (hg : g ∈ nO k n) (i j : Fin n) :
    (ent g i j : k) = (g : Matrix (Fin n) (Fin n) k) i j := by
  simp [ent, nO_int hg]

theorem mul_entry {ϖ : kˣ} {x : Fin n → ℤ} {d : ℕ} {g h : GL (Fin n) k} (hg : g ∈ filt ϖ x d)
    (hh : h ∈ filt ϖ x d) {i j : Fin n} (hij : j.val = i.val + (d + 1)) :
    valuation k (((g * h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j - (g : Matrix (Fin n) (Fin n) k) i j
        - (h : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k (((ϖ ^ (x i - x j) : kˣ)) : k) := by
  obtain ⟨hgO, dg, -⟩ := mem_filt.1 hg
  obtain ⟨hhO, dh, -⟩ := mem_filt.1 hh
  obtain ⟨g0, g1⟩ := (mem_unipB k).1 hgO.2
  obtain ⟨h0, h1⟩ := (mem_unipB k).1 hhO.2
  have hne : i ≠ j := by intro e; rw [e] at hij; omega
  have e : ((g * h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j - (g : Matrix (Fin n) (Fin n) k) i j
        - (h : Matrix (Fin n) (Fin n) k) i j =
      ∑ l, ((g : Matrix (Fin n) (Fin n) k) i l * (h : Matrix (Fin n) (Fin n) k) l j
        - (if l = j then (g : Matrix (Fin n) (Fin n) k) i j else 0)
        - (if l = i then (h : Matrix (Fin n) (Fin n) k) i j else 0)) := by
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp
  rw [e]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rcases lt_trichotomy l i with hl | rfl | hl
  · have a1 : l ≠ i := hl.ne
    have a2 : l ≠ j := by intro e; rw [e] at hl; have := Fin.lt_def.1 hl; omega
    rw [g0 i l hl, if_neg a1, if_neg a2]; simp
  · rw [g1, if_pos rfl, if_neg hne]; simp
  rcases lt_trichotomy l j with hl' | rfl | hl'
  · rw [if_neg hl.ne', if_neg hl'.ne, sub_zero, sub_zero, map_mul]
    have e : (((ϖ ^ (x i - x j) : kˣ)) : k) = ((ϖ ^ (x i - x l) : kˣ) : k) * ((ϖ ^ (x l - x j) : kˣ) : k) := by
      rw [← Units.val_mul, ← _root_.zpow_add]; congr 2; ring
    rw [e, map_mul]
    exact mul_le_mul' (dg _ _ hl (by have := Fin.lt_def.1 hl'; omega))
      (dh _ _ hl' (by have := Fin.lt_def.1 hl; omega))
  · rw [h1, if_pos rfl, if_neg hl.ne']; simp
  · have a2 : l ≠ j := hl'.ne'
    rw [h0 l j hl', if_neg hl.ne', if_neg a2]; simp

def tr0 (c : 𝒪[k]) (i j : Fin n) (hij : i ≠ j) : GL (Fin n) 𝒪[k] :=
  ⟨transvection i j c, transvection i j (-c),
    by rw [transvection_mul_transvection_same _ _ hij]; simp,
    by rw [transvection_mul_transvection_same _ _ hij]; simp⟩

def trv (c : 𝒪[k]) (i j : Fin n) (hij : i ≠ j) : GL (Fin n) k :=
  GeneralLinearGroup.map (algebraMap 𝒪[k] k) (tr0 c i j hij)

theorem trv_apply (c : 𝒪[k]) (i j : Fin n) (hij : i ≠ j) (a b : Fin n) :
    (trv c i j hij : Matrix (Fin n) (Fin n) k) a b =
      (1 : Matrix (Fin n) (Fin n) k) a b + if a = i ∧ b = j then (c : k) else 0 := by
  show algebraMap 𝒪[k] k ((transvection i j c : Matrix (Fin n) (Fin n) 𝒪[k]) a b) = _
  simp only [transvection, Matrix.add_apply, Matrix.single_apply, map_add, Matrix.one_apply]
  congr 1
  · split_ifs <;> simp
  · by_cases h : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := h
      rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩]
      rfl
    · rw [if_neg h, if_neg fun e => h ⟨e.1.symm, e.2.symm⟩, map_zero]

theorem trv_inv (c : 𝒪[k]) (i j : Fin n) (hij : i ≠ j) : (trv c i j hij)⁻¹ = trv (-c) i j hij := by
  have e : (tr0 c i j hij)⁻¹ = tr0 (-c) i j hij := Units.ext rfl
  rw [trv, ← map_inv, e]
  rfl

theorem trv_nO (c : 𝒪[k]) {i j : Fin n} (hij : i < j) : trv c i j hij.ne ∈ nO k n := by
  have low : ∀ a b : Fin n, b < a → (trv c i j hij.ne : Matrix (Fin n) (Fin n) k) a b = 0 := by
    intro a b hab
    rw [trv_apply, Matrix.one_apply_ne hab.ne', if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact absurd hij (not_lt.2 hab.le)
  refine ⟨mem_iwahori.2 ⟨⟨tr0 c i j hij.ne, rfl⟩, fun a b hab => ?_⟩, (mem_unipB k).2 ⟨low, fun a => ?_⟩⟩
  · rw [low a b hab]; simp
  · rw [trv_apply, Matrix.one_apply_eq, if_neg, add_zero]
    rintro ⟨rfl, h⟩
    exact hij.ne h

theorem trv_deep (ϖ : kˣ) (x : Fin n → ℤ) {d : ℕ} (c : 𝒪[k]) {i j : Fin n} (hij : i ≠ j)
    (hd : j.val = i.val + (d + 1)) : Deep ϖ x d (trv c i j hij) := by
  intro a b hab hb
  rw [trv_apply, Matrix.one_apply_ne hab.ne, if_neg, add_zero, map_zero]
  · exact zero_le'
  · rintro ⟨rfl, rfl⟩
    omega

theorem trv_filt (ϖ : kˣ) (x : Fin n → ℤ) {d : ℕ} (c : 𝒪[k]) {i j : Fin n} (hij : i < j)
    (hd : j.val = i.val + (d + 1)) : trv c i j hij.ne ∈ filt ϖ x d :=
  mem_filt.2 ⟨trv_nO c hij, trv_deep ϖ x c hij.ne hd, by rw [trv_inv]; exact trv_deep ϖ x _ hij.ne hd⟩

theorem coe_zpow_eq {ϖ : kˣ} {e : ℤ} (he : 0 ≤ e) : (((ϖ ^ e : kˣ)) : k) = (ϖ : k) ^ e.toNat := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le he
  simp

theorem mem_span_iff {ϖ : kˣ} (h : ord k ϖ = 1) (a : 𝒪[k]) {e : ℤ} (he : 0 ≤ e) :
    a ∈ Ideal.span {om ϖ h ^ e.toNat} ↔ valuation k (a : k) ≤ valuation k (((ϖ ^ e : kˣ)) : k) := by
  rw [Ideal.mem_span_singleton, om_pow_dvd_iff, coe_zpow_eq he]

abbrev AQ (ϖ : kˣ) (h : ord k ϖ = 1) (x : Fin n → ℤ) (p : Fin n × Fin n) : Type :=
  𝒪[k] ⧸ Ideal.span {om ϖ h ^ (x p.1 - x p.2).toNat}

theorem pair_lt {d : ℕ} (p : diagPairs n d) : p.1.1 < p.1.2 := by
  have := (Finset.mem_filter.1 p.2).2
  exact Fin.lt_def.2 (by omega)

theorem pair_eq {d : ℕ} (p : diagPairs n d) : p.1.2.val = p.1.1.val + (d + 1) :=
  (Finset.mem_filter.1 p.2).2

theorem pair_nonneg {x : Fin n → ℤ} (hx : StrictAnti x) {d : ℕ} (p : diagPairs n d) :
    0 ≤ x p.1.1 - x p.1.2 :=
  sub_nonneg.2 (hx (pair_lt p)).le

def phi {ϖ : kˣ} (h : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) (d : ℕ) :
    filt ϖ x d →* Multiplicative (∀ p : diagPairs n d, AQ ϖ h x p.1) :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd fun p => Ideal.Quotient.mk _ (ent g.1 p.1.1 p.1.2)) fun g g' => by
    rw [← ofAdd_add]
    congr 1
    funext p
    rw [Pi.add_apply, ← map_add, Ideal.Quotient.eq, mem_span_iff h _ (pair_nonneg hx p)]
    have e := mul_entry g.2 g'.2 (pair_eq p)
    have hO : g.1 * g'.1 ∈ nO k n := mul_mem g.2.1 g'.2.1
    have e2 : ((ent (g.1 * g'.1) p.1.1 p.1.2 - (ent g.1 p.1.1 p.1.2 + ent g'.1 p.1.1 p.1.2) : 𝒪[k]) : k) =
        ((g.1 * g'.1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p.1.1 p.1.2
          - (g.1 : Matrix (Fin n) (Fin n) k) p.1.1 p.1.2 - (g'.1 : Matrix (Fin n) (Fin n) k) p.1.1 p.1.2 := by
      show (ent (g.1 * g'.1) p.1.1 p.1.2 : k) - ((ent g.1 p.1.1 p.1.2 : k) + (ent g'.1 p.1.1 p.1.2 : k)) = _
      rw [ent_coe hO, ent_coe g.2.1, ent_coe g'.2.1]
      ring
    show valuation k ((ent (g.1 * g'.1) p.1.1 p.1.2 - (ent g.1 p.1.1 p.1.2 + ent g'.1 p.1.1 p.1.2) : 𝒪[k]) : k) ≤ _
    rw [e2]
    exact e

theorem phi_apply {ϖ : kˣ} (h : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) (d : ℕ) (g : filt ϖ x d) :
    phi h hx d g = Multiplicative.ofAdd fun p => Ideal.Quotient.mk _ (ent g.1 p.1.1 p.1.2) := rfl

theorem phi_eq_one_iff {ϖ : kˣ} (h : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) (d : ℕ) (g : filt ϖ x d) :
    phi h hx d g = 1 ↔ ∀ p : diagPairs n d, valuation k ((g.1 : Matrix (Fin n) (Fin n) k) p.1.1 p.1.2) ≤
      valuation k (((ϖ ^ (x p.1.1 - x p.1.2) : kˣ)) : k) := by
  rw [phi_apply, ← ofAdd_zero, Multiplicative.ofAdd.apply_eq_iff_eq, funext_iff]
  refine forall_congr' fun p => ?_
  rw [Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem, mem_span_iff h _ (pair_nonneg hx p), ent_coe g.2.1]

theorem deep_succ {ϖ : kˣ} (h : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) {d : ℕ} (g : filt ϖ x d)
    (hg : phi h hx d g = 1) : Deep ϖ x (d + 1) g.1 := by
  intro i j hij hj
  by_cases hd : j.val ≤ i.val + d
  · exact g.2.2.1 i j hij hd
  · have hm : (i, j) ∈ diagPairs n d := Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp only; omega⟩
    exact (phi_eq_one_iff h hx d g).1 hg ⟨_, hm⟩

theorem ker_phi {ϖ : kˣ} (h : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) (d : ℕ) :
    (phi h hx d).ker = (filt ϖ x (d + 1)).subgroupOf (filt ϖ x d) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hg
    have hi : phi h hx d g⁻¹ = 1 := by rw [map_inv, hg, inv_one]
    exact mem_filt.2 ⟨g.2.1, deep_succ h hx g hg, deep_succ h hx g⁻¹ hi⟩
  · intro hg
    refine (phi_eq_one_iff h hx d g).2 fun p => ?_
    exact (mem_filt.1 hg).2.1 _ _ (pair_lt p) (by have := pair_eq p; omega)

theorem phi_trv {ϖ : kˣ} (h : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) (d : ℕ) (p : diagPairs n d)
    (c : 𝒪[k]) :
    phi h hx d ⟨trv c p.1.1 p.1.2 (pair_lt p).ne, trv_filt ϖ x c (pair_lt p) (pair_eq p)⟩ =
      Multiplicative.ofAdd (Pi.single p (Ideal.Quotient.mk _ c)) := by
  rw [phi_apply]
  congr 1
  funext p'
  have hO := trv_nO c (pair_lt p)
  by_cases e : p' = p
  · subst e
    rw [Pi.single_eq_same]
    congr 1
    refine Subtype.ext ((ent_coe hO _ _).trans ?_)
    rw [trv_apply, Matrix.one_apply_ne (pair_lt p').ne, if_pos ⟨rfl, rfl⟩, zero_add]
  · rw [Pi.single_eq_of_ne e]
    have : ent (trv c p.1.1 p.1.2 (pair_lt p).ne) p'.1.1 p'.1.2 = 0 := by
      refine Subtype.ext ((ent_coe hO _ _).trans ?_)
      rw [trv_apply, Matrix.one_apply_ne (pair_lt p').ne, if_neg, add_zero]
      · rfl
      · rintro ⟨e1, e2⟩
        exact e (Subtype.ext (Prod.ext e1 e2))
    simp only [this, map_zero]

theorem phi_surjective {ϖ : kˣ} (h : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) (d : ℕ) :
    Function.Surjective (phi h hx d) := by
  intro f
  have key : f ∈ (phi h hx d).range := by
    have e : f = ∏ p, Multiplicative.ofAdd (Pi.single p (Multiplicative.toAdd f p) :
        ∀ p : diagPairs n d, AQ ϖ h x p.1) := by
      rw [← ofAdd_sum, Finset.univ_sum_single]
      rfl
    rw [e]
    refine Subgroup.prod_mem _ fun p _ => ?_
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (Multiplicative.toAdd f p)
    exact ⟨_, (phi_trv h hx d p c).trans (by rw [hc])⟩
  exact key

end GlobalTheory.CompanionTheory.IwJac.StepIdx

namespace GlobalTheory.CompanionTheory.IwJac

theorem relIndex_filt_succ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ x : Fin n → ℤ, StrictAnti x → ∀ d : ℕ, (filt ϖ x (d + 1)).relIndex (filt ϖ x d) = Nat.card 𝓀[k] ^ ∑ p ∈ diagPairs n d, (x p.1 - x p.2).toNat := by
  intro k _ _ _ _ n ϖ h x hx d
  rw [Subgroup.relIndex, ← StepIdx.ker_phi h hx d, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 (StepIdx.phi_surjective h hx d), Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
  simp only [StepIdx.card_quot h]
  rw [Finset.prod_pow_eq_pow_sum, Finset.sum_coe_sort (diagPairs n d) fun p => (x p.1 - x p.2).toNat]

end GlobalTheory.CompanionTheory.IwJac

end
end

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_relIndex_eq_residue_card_pow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ x : Fin n → ℤ, StrictAnti x → ∀ d : ℕ, (filt ϖ x (d + 1)).relIndex (filt ϖ x d) = Nat.card 𝓀[k] ^ ∑ p ∈ diagPairs n d, (x p.1 - x p.2).toNat := by
  atlas_forward_decl GlobalTheory.CompanionTheory.IwJac.relIndex_filt_succ
end

section
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical

namespace GlobalTheory.CompanionTheory.IwJac

theorem sum_pairs_sub (n : ℕ) (x : Fin n → ℤ) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), (x p.1 - x p.2) =
      ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * x i := by
  have h1 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), x p.1 =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then x i else 0 := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
  have h2 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), x p.2 =
      ∑ i : Fin n, ∑ j : Fin n, if j < i then x i else 0 := by
    rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_sub_distrib, h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have a1 : (∑ j : Fin n, if i < j then x i else 0) = ((n : ℤ) - 1 - (i : ℕ)) * x i := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have : (Finset.univ.filter fun j : Fin n => i < j) = Finset.Ioi i := by ext j; simp
    rw [this, Fin.card_Ioi]
    have := i.isLt
    congr 1
    omega
  have a2 : (∑ j : Fin n, if j < i then x i else 0) = ((i : ℕ) : ℤ) * x i := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have : (Finset.univ.filter fun j : Fin n => j < i) = Finset.Iio i := by ext j; simp
    rw [this, Fin.card_Iio]
  rw [a1, a2]
  ring

theorem sum_diagPairs (n : ℕ) (f : Fin n × Fin n → ℤ) :
    ∑ d ∈ Finset.range n, ∑ p ∈ diagPairs n d, f p =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), f p := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
    (t := Finset.range n) (g := fun p => p.2.val - p.1.val - 1)]
  · refine Finset.sum_congr rfl fun d hd => Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    have h1 := p.1.isLt
    have h2 := p.2.isLt
    simp only [diagPairs, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
    omega
  · intro p hp
    have h2 := p.2.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hp
    rw [Finset.mem_range]
    omega

theorem sum_diagPairs_toNat (n : ℕ) (x : Fin n → ℤ) (hx : StrictAnti x) :
    ((∑ d ∈ Finset.range n, ∑ p ∈ diagPairs n d, (x p.1 - x p.2).toNat : ℕ) : ℤ) =
      ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * x i := by
  rw [← sum_pairs_sub, ← sum_diagPairs]
  push_cast
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun p hp => ?_
  have hlt : p.1 < p.2 := by
    simp only [diagPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [Fin.lt_def]
    omega
  have := hx hlt
  exact Int.toNat_of_nonneg (by omega)

end GlobalTheory.CompanionTheory.IwJac

end
end

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_diag_pairs_toNat_eq_weighted_sum : ∀ (n : ℕ) (x : Fin n → ℤ), StrictAnti x → ((∑ d ∈ Finset.range n, ∑ p ∈ diagPairs n d, (x p.1 - x p.2).toNat : ℕ) : ℤ) = ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * x i := by
  atlas_forward_decl GlobalTheory.CompanionTheory.IwJac.sum_diagPairs_toNat
end

section
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac PositivityTheory.Rg.BcB.F.Tail.BS
open scoped Classical

namespace GlobalTheory.CompanionTheory.IwJac

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem filt_zero (ϖ : kˣ) (x : Fin n → ℤ) : filt ϖ x 0 = nO k n := by
  have h : ∀ g : GL (Fin n) k, Deep ϖ x 0 g := fun g i j hij hd => by
    have := Fin.lt_def.1 hij; omega
  ext g
  exact ⟨fun hg => hg.1, fun hg => ⟨hg, h _, h _⟩⟩

theorem filt_succ_le (ϖ : kˣ) (x : Fin n → ℤ) (d : ℕ) : filt ϖ x (d + 1) ≤ filt ϖ x d :=
  fun _ hg => ⟨hg.1, fun i j hij hd => hg.2.1 i j hij (by omega), fun i j hij hd => hg.2.2 i j hij (by omega)⟩

theorem relIndex_filt_zero {ϖ : kˣ} (h1 : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) (d : ℕ) :
    (filt ϖ x d).relIndex (nO k n) =
      Nat.card 𝓀[k] ^ ∑ e ∈ Finset.range d, ∑ p ∈ diagPairs n e, (x p.1 - x p.2).toNat := by
  induction d with
  | zero => rw [filt_zero]; simp
  | succ d ih =>
    have hle : ∀ e, filt ϖ x e ≤ nO k n := fun e _ hg => hg.1
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ (filt_succ_le ϖ x d) (hle d), ih, GlobalTheory.T.filtration_relIndex_eq_residue_card_pow k n ϖ h1 x hx d,
      Finset.sum_range_succ, pow_add, mul_comm]

theorem mk_fiber {ϖ : kˣ} (h1 : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) {m m' : GL (Fin n) k}
    (hm : m ∈ nO k n) (hm' : m' ∈ nO k n) :
    (QuotientGroup.mk (m * tor ϖ x) : GL (Fin n) k ⧸ iwahori k (Fin n)) = QuotientGroup.mk (m' * tor ϖ x) ↔
      m⁻¹ * m' ∈ filt ϖ x n := by
  have hnorm : (tor ϖ x)⁻¹ ∈ Subgroup.normalizer ((unipB k (Fin n) : Subgroup _) : Set (GL (Fin n) k)) :=
    inv_mem ((GlobalTheory.CompanionTheory.IwahoriDatumGL.iwahoriCass k n).norm_N _ ⟨_, rfl⟩)
  have e : (m * tor ϖ x)⁻¹ * (m' * tor ϖ x) = (tor ϖ x)⁻¹ * (m⁻¹ * m') * (tor ϖ x)⁻¹⁻¹ := by group
  rw [QuotientGroup.eq, e, GlobalTheory.T.filtration_eq_conj_nilpotent_integral k n ϖ h1 x hx]
  have hy : m⁻¹ * m' ∈ nO k n := mul_mem (inv_mem hm) hm'
  constructor
  · intro h
    refine ⟨_, ⟨h, (Subgroup.mem_normalizer_iff.1 hnorm _).1 hy.2⟩, ?_⟩
    simp [MulAut.conj_apply]
    group
  · rintro ⟨z, hz, e'⟩
    have : (tor ϖ x)⁻¹ * (m⁻¹ * m') * (tor ϖ x)⁻¹⁻¹ = z := by
      rw [← e']
      simp [MulAut.conj_apply]
      group
    rw [this]
    exact hz.1

theorem jacHk : JacHk := by
  intro k _ _ _ _ n V _ _ π _ ϖ h1 x hx u hu
  have hfix : ∀ b ∈ iwahori k (Fin n), π b u = u := fun b hb => GlobalTheory.IwahoriInj.mem_fixed.1 hu b hb
  set I := iwahori k (Fin n) with hI
  set t : GL (Fin n) k := tor ϖ x with ht
  set w : Jacquet π (unipB k (Fin n)) := Submodule.Quotient.mk (π t u) with hw
  let F : nO k n → GL (Fin n) k ⧸ I := fun m => QuotientGroup.mk (m.1 * t)
  have hval : ∀ m ∈ nO k n, ∀ b ∈ I, (Submodule.Quotient.mk (π (m * t * b) u) : Jacquet π (unipB k (Fin n))) = w := by
    intro m hm b hb
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfix b hb, hw, Submodule.Quotient.eq]
    exact GlobalTheory.IwahoriInj.sub_mem_twKer hm.2 _
  let f : GL (Fin n) k → ℂ := fun g => if ∃ a ∈ I, ∃ b ∈ I, g = a * t * b then (1 : ℂ) else 0

  have hsupp : ∀ q : GL (Fin n) k ⧸ I, (∃ a ∈ I, ∃ b ∈ I, q.out = a * t * b) ↔ q ∈ Set.range F := by
    intro q
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      obtain ⟨m, hm, c, hc, e2⟩ := GlobalTheory.T.iwahori_double_coset_torus_nilpotent k n ϖ h1 x hx a ha b hb
      rw [← ht] at e2
      refine ⟨⟨m, hm⟩, ?_⟩
      rw [← QuotientGroup.out_eq' q, e, e2]
      refine QuotientGroup.eq.2 ?_
      simpa [mul_assoc] using inv_mem hc
    · rintro ⟨m, rfl⟩
      have : (F m).out⁻¹ * (m.1 * t) ∈ I := QuotientGroup.eq.1 (QuotientGroup.out_eq' (F m))
      refine ⟨m.1, m.2.1, (m.1 * t)⁻¹ * (F m).out, ?_, by group⟩
      simpa using inv_mem this

  have hcard : Nat.card (Set.range F) = (filt ϖ x n).relIndex (nO k n) := by
    let Φ : (nO k n ⧸ (filt ϖ x n).subgroupOf (nO k n)) → Set.range F := fun c =>
      Quotient.liftOn' c (fun m => (⟨F m, m, rfl⟩ : Set.range F)) (fun a b hab => Subtype.ext
        ((mk_fiber h1 hx a.2 b.2).2 (Subgroup.mem_subgroupOf.1 (QuotientGroup.leftRel_apply.1 hab))))
    have hΦ : Function.Bijective Φ := by
      constructor
      · intro c c'
        refine Quotient.inductionOn₂' c c' fun a b e => ?_
        exact Quotient.sound' (QuotientGroup.leftRel_apply.2 (Subgroup.mem_subgroupOf.2
          ((mk_fiber h1 hx a.2 b.2).1 (congrArg Subtype.val e))))
      · rintro ⟨_, m, rfl⟩
        exact ⟨Quotient.mk'' m, rfl⟩
    exact (Nat.card_congr (Equiv.ofBijective Φ hΦ)).symm
  have hq : Nat.card 𝓀[k] ≠ 0 := Nat.card_pos.ne'
  have hcard' := hcard.trans (relIndex_filt_zero h1 hx n)
  have hQ : (Set.range F).Finite := by
    have : Finite (Set.range F) := Nat.finite_of_card_ne_zero (by rw [hcard']; exact pow_ne_zero _ hq)
    exact Set.toFinite _
  have hs : (Function.support fun q : GL (Fin n) k ⧸ I => f q.out • π q.out u).Finite := by
    refine hQ.subset fun q hq' => (hsupp q).1 ?_
    by_contra h
    exact hq' (by simp only [f, if_neg h, zero_smul])
  have e2 : ∀ q : GL (Fin n) k ⧸ I, (twKer π (unipB k (Fin n)) 1).mkQ.toAddMonoidHom (f q.out • π q.out u) =
      if q ∈ Set.range F then w else 0 := by
    intro q
    by_cases h : q ∈ Set.range F
    · obtain ⟨m, hm⟩ := id h
      have hb : (m.1 * t)⁻¹ * q.out ∈ I :=
        QuotientGroup.eq.1 ((show (QuotientGroup.mk (m.1 * t) : GL (Fin n) k ⧸ I) = q from hm).trans
          (QuotientGroup.out_eq' q).symm)
      have e : m.1 * t * ((m.1 * t)⁻¹ * q.out) = q.out := by group
      have hp : ∃ a ∈ I, ∃ b ∈ I, q.out = a * t * b := ⟨m.1, m.2.1, _, hb, e.symm⟩
      have := hval m.1 m.2 _ hb
      rw [e] at this
      simp only [f, if_pos hp, if_pos h, one_smul]
      exact this
    · have : ¬ ∃ a ∈ I, ∃ b ∈ I, q.out = a * t * b := fun h' => h ((hsupp q).1 h')
      simp only [f, if_neg this, if_neg h, zero_smul, map_zero]
  have e1 : (Submodule.Quotient.mk (hkS π I f u) : Jacquet π (unipB k (Fin n))) =
      ∑ᶠ q : GL (Fin n) k ⧸ I, if q ∈ Set.range F then w else 0 := by
    rw [← finsum_congr e2]
    exact AddMonoidHom.map_finsum (twKer π (unipB k (Fin n)) 1).mkQ.toAddMonoidHom hs
  have e3 : (∑ᶠ q : GL (Fin n) k ⧸ I, if q ∈ Set.range F then w else 0) = Nat.card (Set.range F) • w := by
    rw [finsum_eq_sum_of_support_subset (s := hQ.toFinset) _ (fun q hq' => by
      simp only [Set.Finite.coe_toFinset]
      by_contra h
      exact hq' (by simp only [if_neg h]))]
    rw [Finset.sum_congr rfl (fun q hq' => if_pos (hQ.mem_toFinset.1 hq')), Finset.sum_const,
      Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hQ]
  change (Submodule.Quotient.mk (hkS π I f u) : Jacquet π (unipB k (Fin n))) = _
  rw [e1, e3, hcard', ← GlobalTheory.T.sum_diag_pairs_toNat_eq_weighted_sum n x hx, zpow_natCast, ← Nat.cast_pow, jacBU_mk, Nat.cast_smul_eq_nsmul ℂ]
  rfl

end GlobalTheory.CompanionTheory.IwJac

end
end

open PositivityTheory.Rg.BcB.F.Tail.BS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_hecke_jacHk : JacHk := by
  atlas_forward_decl GlobalTheory.CompanionTheory.IwJac.jacHk
end

section
noncomputable section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open PositivityTheory.Rg.BcB.F.Tail.BS
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JacEigAt

theorem qV_pos {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : 0 < qV E w := by
  unfold qV
  exact Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem card_residue_eq_qV {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    Nat.card 𝓀[w.adicCompletion E] = qV E w := by
  have h := GlobalTheory.LocLanglands.resCard_eq_normV w
  simpa [GlobalTheory.SplitWeil.resCard, Formalism.ConjugateSelfDual.normV, qV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h

theorem modExp_points (n : ℕ) (a : Fin n) :
    modExp (fun _ : Fin n => Unit) a = (n : ℤ) - 1 - 2 * (a : ℕ) := by
  have h1 : (Finset.univ.filter fun b : Fin n => a < b) = Finset.Ioi a := by ext; simp
  have h2 : (Finset.univ.filter fun b : Fin n => b < a) = Finset.Iio a := by ext; simp
  have ha := a.2
  simp only [modExp, Fintype.card_unique, Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one, h1, h2,
    Fin.card_Ioi, Fin.card_Iio]
  omega

theorem nabs_zpow {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (h : ord k ϖ = 1) (m : ℤ) :
    GlobalTheory.SplitWeil.nabs k (ϖ ^ m) = (GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-m) := by
  have h1 : GlobalTheory.SplitWeil.nabs k (ϖ ^ m) = GlobalTheory.SplitWeil.nabs k ϖ ^ m := by
    simp [GlobalTheory.SplitWeil.nabs]
  rw [h1, GlobalTheory.LGrp.nabs_eq_zpow, h, _root_.zpow_neg, zpow_one, _root_.inv_zpow, _root_.zpow_neg]

theorem prod_zpow_sum {ι : Type} (s : Finset ι) (r : ℂ) (hr : r ≠ 0) (f : ι → ℤ) :
    ∏ a ∈ s, r ^ f a = r ^ ∑ a ∈ s, f a := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hr]

theorem absPow_term {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (h : ord (w.adicCompletion E) ϖ = 1) (e m : ℤ) :
    (absPow (w.adicCompletion E) ((e : ℂ) / 2) (ϖ ^ m) : ℂ) =
      (((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (-(e * m)) := by
  have hq : (0 : ℝ) < qV E w := by exact_mod_cast qV_pos w
  set r : ℝ := Real.sqrt (qV E w : ℝ) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hq
  have hrq : (GlobalTheory.SplitWeil.resCard (w.adicCompletion E) : ℝ) = r ^ (2 : ℤ) := by
    have : (GlobalTheory.SplitWeil.resCard (w.adicCompletion E) : ℝ) = qV E w := by
      simp [GlobalTheory.SplitWeil.resCard, card_residue_eq_qV]
    rw [this, hr, zpow_ofNat, Real.sq_sqrt hq.le]
  have hs : ((e : ℂ) / 2) = (((e : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hs, val_absPow_ofReal, nabs_zpow ϖ h, hrq, ← _root_.zpow_mul, ← Real.rpow_intCast, ← Real.rpow_mul hr0.le]
  have : (((2 * -m : ℤ) : ℝ)) * ((e : ℝ) / 2) = ((-(e * m) : ℤ) : ℝ) := by push_cast; ring
  rw [this, Real.rpow_intCast]
  push_cast
  rfl

theorem deltaHalf_inv {E : Type} [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (h : ord (w.adicCompletion E) ϖ = 1) (x : Fin n → ℤ) :
    (((deltaHalf (w.adicCompletion E) (fun _ : Fin n => Unit)
        (leviTorus (w.adicCompletion E) (Fin n) fun i => ϖ ^ x i))⁻¹ : ℂˣ) : ℂ) =
      (((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * x i) := by
  have hq : (0 : ℝ) < qV E w := by exact_mod_cast qV_pos w
  have hr : (((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hq).ne'
  have hd : ∀ i, GeneralLinearGroup.det
      (leviTorus (w.adicCompletion E) (Fin n) (fun i => ϖ ^ x i) i) = ϖ ^ x i :=
    fun i => congrFun ((leviTorus (w.adicCompletion E) (Fin n)).left_inv fun i => ϖ ^ x i) i
  rw [Units.val_inv_eq_inv_val, deltaHalf_apply, Units.coe_prod]
  simp only [hd, absPow_term w ϖ h, modExp_points]
  rw [prod_zpow_sum _ _ hr, ← _root_.zpow_neg, Finset.sum_neg_distrib, neg_neg]

end GlobalTheory.CompanionTheory.JacEigAt

open GlobalTheory.CompanionTheory.JacEigAt in
theorem GlobalTheory.CompanionTheory.JacEigAt.jacEig : JacEig := by
  intro E _ _ _ n w V _ _ π hπ ϖ hϖ ξ c x hx u hu heig
  have hord : ord (w.adicCompletion E) ϖ = 1 := (GlobalTheory.CompanionTheory.CtS.NuVal.ord_eq_ordL_unit w ϖ).trans hϖ
  have h := GlobalTheory.T.jacquet_hecke_jacHk (w.adicCompletion E) n V π hπ ϖ hord x hx u hu
  have hq : (0 : ℝ) < qV E w := by exact_mod_cast qV_pos w
  have hqh : qh w ≠ 0 := by
    unfold qh
    exact_mod_cast (Real.sqrt_pos.2 hq).ne'
  have hcard : ((Nat.card 𝓀[w.adicCompletion E] : ℕ) : ℂ) = qh w ^ (2 : ℤ) := by
    rw [card_residue_eq_qV, qh, zpow_ofNat, ← Complex.ofReal_pow, Real.sq_sqrt hq.le]
    simp
  set S : ℤ := ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * x i with hS
  have h' : (Submodule.Quotient.mk (hkS π (iwGL n w) (dcos n w (tdiag ϖ x)) u) :
      Jacquet π (unipB (w.adicCompletion E) (Fin n))) =
      ((Nat.card 𝓀[w.adicCompletion E] : ℂ) ^ S) •
        jacBU π (fun i => ϖ ^ x i) (Submodule.Quotient.mk u) := h
  rw [heig, Submodule.Quotient.mk_smul, hcard, ← _root_.zpow_mul] at h'
  have hj : jacB π (fun i => ϖ ^ x i) (Submodule.Quotient.mk u) =
      (qh w ^ S) • jacBU π (fun i => ϖ ^ x i) (Submodule.Quotient.mk u) := by
    have := jac_mk (points (Fin n)) π (leviTorus (w.adicCompletion E) (Fin n) fun i => ϖ ^ x i) u
    rw [deltaHalf_inv n w ϖ hord x] at this
    exact this
  have e2 : qh w ^ (2 * S) = qh w ^ S * qh w ^ S := by
    rw [two_mul, zpow_add₀ hqh]
  have hS0 : qh w ^ S ≠ 0 := zpow_ne_zero _ hqh
  rw [e2] at h'
  rw [hj]
  have h3 : (qh w ^ S) • ((qh w ^ S) • jacBU π (fun i => ϖ ^ x i) (Submodule.Quotient.mk u)) =
      (qh w ^ S) • ((c * pw ξ x) • (Submodule.Quotient.mk u : Jacquet π (unipB (w.adicCompletion E) (Fin n)))) := by
    rw [smul_smul, ← h', smul_smul]
    congr 1
    ring
  exact smul_right_injective _ hS0 h3

end
end

section
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.DlBridgeAt

theorem val_eq_uniformizer_of_ord {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ϖ : kˣ) (h : ord k ϖ = 1) :
    valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact uniformizer_ne_zero hy.symm
  have hu : valuation k ((Units.mk0 y hy0 : kˣ) : k) = uniformizer k := hy
  have h1 : ord k (Units.mk0 y hy0) = 1 := ord_eq_one hu
  have h2 : ord k (ϖ * (Units.mk0 y hy0)⁻¹) = 0 := by
    have h3 := ord_mul k (ϖ * (Units.mk0 y hy0)⁻¹) (Units.mk0 y hy0)
    rw [inv_mul_cancel_right] at h3
    omega
  have h4 := ord_eq_zero_iff.1 h2
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hu] at h4
  have hne : uniformizer k ≠ 0 := uniformizer_ne_zero
  exact (mul_inv_eq_one₀ hne).1 h4

end GlobalTheory.CompanionTheory.DlBridgeAt

open GlobalTheory.CompanionTheory.DlBridgeAt in

theorem GlobalTheory.CompanionTheory.DlBridgeAt.dlBridge : PositivityTheory.Rg.BcB.F.Tail.PExp.DlBridge := by
  intro E _ _ _ w ϖ hϖ
  have hord : ord (w.adicCompletion E) ϖ = 1 := (GlobalTheory.CompanionTheory.CtS.NuVal.ord_eq_ordL_unit w ϖ).trans hϖ
  refine ⟨val_eq_uniformizer_of_ord ϖ hord, fun N x => ?_⟩
  have hinv := GlobalTheory.CompanionTheory.JacEigAt.deltaHalf_inv N w ϖ hord x
  have hv := val_deltaHalf (w.adicCompletion E)
    (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i)
  have hm := deltaB_eq_modulus (fun i : Fin N => ϖ ^ x i)
  have hpos := modulus_pos (w.adicCompletion E)
    (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i)
  rw [Units.val_inv_eq_inv_val, hv] at hinv
  rw [hv, hm]
  change _ = GlobalTheory.BCT.qh w ^ _ at hinv
  rw [← hinv]
  set m := modulus (w.adicCompletion E) (fun _ : Fin N => Unit)
    (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i) with hmdef
  have hs : √m * √m = m := Real.mul_self_sqrt hpos.le
  have hs0 : √m ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have key : ∀ s : ℝ, s ≠ 0 → (s * s)⁻¹ * s = s⁻¹ := fun s h => by field_simp
  have h5 := key _ hs0
  rw [hs] at h5
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, h5]

end
end

namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_blocks_exponent : PositivityTheory.Rg.BcB.F.Tail.PExp.DlBridge := by
  atlas_forward_decl GlobalTheory.CompanionTheory.DlBridgeAt.dlBridge
end PExp
end Tail
end F
end BcB
end Rg
end PositivityTheory
end
