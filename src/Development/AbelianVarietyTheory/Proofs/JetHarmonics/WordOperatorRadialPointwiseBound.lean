import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointwiseBoundedOfMemBoundedFactorsMonoid
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormProductSpanLeftMulClosed
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinusHatsTaylorCoeffLeibnizRule
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlusHatsTaylorCoeffLeibnizRule
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.VecPolyMemSpanValuesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormActualOperatorsAlgebraicHypotheses
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPairConstantsPointwiseAdjointBoundedStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordOperatorColumnMemNormalFormProductSpan

section
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.HatCommutators

section lists
variable {A : Type} [Ring A]

theorem comm_ofFn {n : ℕ} (f : Fin n → A) (a : A) (h : ∀ l, Commute a (f l)) :
    Commute a (List.ofFn f).prod := by
  apply Commute.list_prod_right
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨l, rfl⟩ := hx
  exact h l

theorem ofFn_mul_inv : ∀ {n : ℕ} (f g : Fin n → A), (∀ l, f l * g l = 1) → (∀ l m, Commute (g l) (f m)) →
    (List.ofFn f).prod * (List.ofFn g).prod = 1
  | 0, _, _, _, _ => by simp
  | n + 1, f, g, h, hc => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have ih := ofFn_mul_inv (fun i => f i.succ) (fun i => g i.succ) (fun l => h _) (fun l m => hc _ _)
    have hc' := comm_ofFn (fun i : Fin n => f i.succ) (g 0) (fun l => hc _ _)
    rw [mul_assoc, ← mul_assoc _ (g 0), ← hc'.eq, mul_assoc, ih, mul_one, h]

theorem star_ofFn [StarRing A] : ∀ {n : ℕ} (f g : Fin n → A), (∀ l, star (f l) = g l) →
    (∀ l m, Commute (g l) (g m)) → star (List.ofFn f).prod = (List.ofFn g).prod
  | 0, _, _, _, _ => by simp
  | n + 1, f, g, h, hc => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, star_mul]
    have ih := star_ofFn (fun i => f i.succ) (fun i => g i.succ) (fun l => h _) (fun l m => hc _ _)
    have hc' := comm_ofFn (fun i : Fin n => g i.succ) (g 0) (fun l => hc _ _)
    rw [ih, h, hc'.eq]

end lists

variable {A : Type} [Ring A] [Algebra ℂ A]

section level
variable {r : ℕ} (L : LevelData A r)

theorem c_mem (l : Fin r) : L.c l ∈ L.fns := by simp [LevelData.fns]
theorem ci_mem (l : Fin r) : L.ci l ∈ L.fns := by simp [LevelData.fns]
theorem cb_mem (l : Fin r) : L.cb l ∈ L.fns := by simp [LevelData.fns]
theorem cbi_mem (l : Fin r) : L.cbi l ∈ L.fns := by simp [LevelData.fns]
theorem GG_mem : L.GG ∈ L.fns := by simp [LevelData.fns]

theorem fcomm {x y : A} (hx : x ∈ L.fns) (hy : y ∈ L.fns) : Commute x y := L.fns_comm x hx y hy

theorem comm_Dr {a : A} (h : ∀ g ∈ L.fns, Commute a g) : Commute a L.Dr :=
  comm_ofFn _ _ fun l => h _ (c_mem L l)
theorem comm_Drb {a : A} (h : ∀ g ∈ L.fns, Commute a g) : Commute a L.Drb :=
  comm_ofFn _ _ fun l => h _ (cb_mem L l)

theorem Dri_Dr : L.Dri * L.Dr = 1 :=
  ofFn_mul_inv _ _ L.ci_c fun l m => fcomm L (c_mem L l) (ci_mem L m)
theorem Drbi_Drb : L.Drbi * L.Drb = 1 :=
  ofFn_mul_inv _ _ L.cbi_cb fun l m => fcomm L (cb_mem L l) (cbi_mem L m)
theorem Dr_Drb : Commute L.Dr L.Drb :=
  comm_ofFn _ _ fun l => (comm_Dr L fun _ hg => fcomm L (cb_mem L l) hg).symm

end level

variable [StarRing A] {P : M.Par} (d : Q.NFData P A)

theorem mem_span {b h : A} (hb : b ∈ bmon d) (hh : h ∈ basics d) : b * h ∈ nfSpan d (basics d) 0 0 1 :=
  Submodule.subset_span ⟨b, hb, [h], rfl, by simpa using hh, by simp⟩

theorem kap_mem (f : M.Ty P → ℂ) : d.κ f ∈ bmon d :=
  Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨f, rfl⟩)))

theorem ssn_mem {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) : ssn d l ∈ bmon d :=
  Submonoid.subset_closure (Or.inl (Or.inr ⟨l, by simpa using hl, rfl⟩))

theorem star_ssn_mem {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) : star (ssn d l) ∈ bmon d :=
  Submonoid.subset_closure (Or.inr ⟨l, by simpa using hl, rfl⟩)

theorem rh_eq (hR : d.Rel) (y : ℂ) :
    rh d y = d.x y * d.L.R0 y +
      ∑ l ∈ Finset.Icc 1 (P.k - 1), ssn d l * (d.κ fun ρ => M.xEx P {l} ρ y) * d.L.Ahat y := by
  obtain ⟨-, hκ, hS, -⟩ := hR
  have hκ' : ∀ f, ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun f g hg => hκ f g (Or.inl hg)
  have hS' : ∀ l, ∀ g ∈ d.L.fns, Commute (d.SS l) g := fun l g hg => hS l g (Or.inl (Or.inl hg))
  have h1 : d.L.Drb * (d.L.GG * d.x y) = d.x y * (d.L.Drb * d.L.GG) := by
    have := ((comm_Drb d.L (hκ' fun ρ => M.xC P ρ y)).mul_right (hκ' _ _ (GG_mem d.L))).eq
    rw [← mul_assoc]; exact this.symm
  have h2 : ∀ l, ssn d l * (d.κ fun ρ => M.xEx P {l} ρ y) * d.L.Ahat y =
      d.L.Drb * (d.SS l * (d.κ fun ρ => M.xEx P {l} ρ y)) * d.L.Ar y := by
    intro l
    have hc := ((comm_Dr d.L (hS' l)).mul_left (comm_Dr d.L (hκ' fun ρ => M.xEx P {l} ρ y))).eq
    calc _ = d.L.Drb * d.L.Dri * ((d.SS l * (d.κ fun ρ => M.xEx P {l} ρ y)) * d.L.Dr) * d.L.Ar y := by
          simp only [ssn, LevelData.Ahat, mul_assoc]
      _ = d.L.Drb * (d.L.Dri * d.L.Dr) * (d.SS l * (d.κ fun ρ => M.xEx P {l} ρ y)) * d.L.Ar y := by
          rw [hc]; simp only [mul_assoc]
      _ = _ := by rw [Dri_Dr, mul_one]
  simp only [h2]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  change d.L.Drb * ((d.L.GG * d.x y * d.L.l0 y + d.weightedSumBis y) * d.L.Ar y + d.L.GG * d.x y * d.L.Br y) =
    d.x y * (d.L.Drb * d.L.GG * (d.L.l0 y * d.L.Ar y + d.L.Br y)) + d.L.Drb * d.weightedSumBis y * d.L.Ar y
  rw [← mul_assoc (d.x y), ← h1]
  noncomm_ring

theorem rhv_eq (hR : d.Rel) (hc : ∀ l, star (d.L.c l) = d.L.cb l) (hci : ∀ l, star (d.L.ci l) = d.L.cbi l)
    (y : ℂ) :
    rhv d y = d.x y * d.L.R0v y +
      ∑ l ∈ Finset.Icc 1 (P.k - 1), (d.κ fun ρ => M.xEx P {l} ρ y) * star (ssn d l) * d.L.Ahatv y := by
  obtain ⟨-, hκ, hS, -⟩ := hR
  have hκ' : ∀ f, ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun f g hg => hκ f g (Or.inl hg)
  have hS' : ∀ l, ∀ g ∈ d.L.fns, Commute (d.SS l) g := fun l g hg => hS l g (Or.inl (Or.inl hg))
  have h1 : d.L.Dr * (d.L.GG * d.x y) = d.x y * (d.L.Dr * d.L.GG) := by
    have := ((comm_Dr d.L (hκ' fun ρ => M.xC P ρ y)).mul_right (hκ' _ _ (GG_mem d.L))).eq
    rw [← mul_assoc]; exact this.symm
  have s1 : star d.L.Drb = d.L.Dr :=
    star_ofFn _ _ (fun l => by rw [← hc, star_star]) fun l m => fcomm d.L (c_mem _ l) (c_mem _ m)
  have s2 : star d.L.Dri = d.L.Drbi :=
    star_ofFn _ _ hci fun l m => fcomm d.L (cbi_mem _ l) (cbi_mem _ m)
  have h2 : ∀ l, (d.κ fun ρ => M.xEx P {l} ρ y) * star (ssn d l) * d.L.Ahatv y =
      d.L.Dr * ((d.κ fun ρ => M.xEx P {l} ρ y) * star (d.SS l)) * d.L.Avr y := by
    intro l
    have hs : Commute (star (d.SS l)) d.L.Dr := by
      rw [← s1]; exact (comm_Drb d.L (hS' l)).star_star
    have hc := ((comm_Dr d.L (hκ' fun ρ => M.xEx P {l} ρ y)).mul_left hs).eq
    calc _ = (d.κ fun ρ => M.xEx P {l} ρ y) * star (d.SS l) * (d.L.Drbi * (d.L.Dr * d.L.Drb)) * d.L.Avr y := by
          simp only [ssn, LevelData.Ahatv, star_mul, s1, s2, mul_assoc]
      _ = (d.κ fun ρ => M.xEx P {l} ρ y) * star (d.SS l) * d.L.Dr * d.L.Avr y := by
          rw [(Dr_Drb d.L).eq, ← mul_assoc d.L.Drbi, Drbi_Drb, one_mul]
      _ = _ := by rw [hc]
  simp only [h2]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  change d.L.Dr * ((d.L.GG * d.x y * d.L.m0 y + d.S12 y) * d.L.Avr y + d.L.GG * d.x y * d.L.Bvr y) =
    d.x y * (d.L.Dr * d.L.GG * (d.L.m0 y * d.L.Avr y + d.L.Bvr y)) + d.L.Dr * d.S12 y * d.L.Avr y
  rw [← mul_assoc (d.x y), ← h1]
  noncomm_ring

theorem xinv_mul (y : ℂ) (hy : ∀ ρ : M.Ty P, M.xC P ρ y ≠ 0) :
    (d.κ fun ρ => (M.xC P ρ y)⁻¹) * d.x y = 1 := by
  rw [Q.NFData.x, ← map_mul, ← map_one d.κ]
  congr 1
  funext ρ
  exact inv_mul_cancel₀ (hy ρ)

end GlobalTheory.HatNF.HatCommutators

namespace GlobalTheory.HatNF

open HatCommutators

theorem r0_mem_nfSpan_basics : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ y : ℝ, (∀ ρ : M.Ty P, M.xC P ρ (y : ℂ) ≠ 0 ∧ M.xC P ρ ((y : ℂ) - 1) ≠ 0 ∧ M.xC P ρ ((y : ℂ) + 1) ≠ 0) → d.L.R0 y ∈ nfSpan d (basics d) 0 0 1 ∧ d.L.R0v y ∈ nfSpan d (basics d) 0 0 1 := by
  intro P A _ _ _ _ d hd y hy
  obtain ⟨-, -, hR, -, hc, hci, -⟩ := hd
  have hx := xinv_mul d (y : ℂ) fun ρ => (hy ρ).1
  have hk := kap_mem d fun ρ => (M.xC P ρ (y : ℂ))⁻¹
  set k := d.κ fun ρ => (M.xC P ρ (y : ℂ))⁻¹
  constructor
  · have e : d.L.R0 y = k * rh d y - ∑ l ∈ Finset.Icc 1 (P.k - 1),
        (k * ssn d l * (d.κ fun ρ => M.xEx P {l} ρ y)) * d.L.Ahat y := by
      rw [rh_eq d hR, mul_add, ← mul_assoc, hx, one_mul, Finset.mul_sum]
      simp only [mul_assoc, add_sub_cancel_right]
    rw [e]
    refine Submodule.sub_mem _ (mem_span d hk ⟨y, hy, by simp⟩) (Submodule.sum_mem _ fun l hl => ?_)
    exact mem_span d (mul_mem (mul_mem hk (ssn_mem d hl)) (kap_mem d _)) ⟨y, hy, by simp⟩
  · have e : d.L.R0v y = k * rhv d y - ∑ l ∈ Finset.Icc 1 (P.k - 1),
        (k * (d.κ fun ρ => M.xEx P {l} ρ y) * star (ssn d l)) * d.L.Ahatv y := by
      rw [rhv_eq d hR hc hci, mul_add, ← mul_assoc, hx, one_mul, Finset.mul_sum]
      simp only [mul_assoc, add_sub_cancel_right]
    rw [e]
    refine Submodule.sub_mem _ (mem_span d hk ⟨y, hy, by simp⟩) (Submodule.sum_mem _ fun l hl => ?_)
    exact mem_span d (mul_mem (mul_mem hk (kap_mem d _)) (star_ssn_mem d hl)) ⟨y, hy, by simp⟩

end GlobalTheory.HatNF
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.R0_and_R0v_mem_nfSpan_basics_of_xC_ne_zero : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ y : ℝ, (∀ ρ : M.Ty P, M.xC P ρ (y : ℂ) ≠ 0 ∧ M.xC P ρ ((y : ℂ) - 1) ≠ 0 ∧ M.xC P ρ ((y : ℂ) + 1) ≠ 0) → d.L.R0 y ∈ nfSpan d (basics d) 0 0 1 ∧ d.L.R0v y ∈ nfSpan d (basics d) 0 0 1 := by
  atlas_forward_decl GlobalTheory.HatNF.r0_mem_nfSpan_basics
end

section
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

theorem hatExp_exists_bound (P : M.Par) :
    ∃ C : ℝ, ∀ t : ℝ, C ≤ t → ∀ ρ : M.Ty P, M.xC P ρ (t : ℂ) ≠ 0 := by
  obtain ⟨C, hC⟩ := (Set.toFinite
    ((fun x : M.Ty P × ℕ => -M.rho P x.1 x.2) ''
      ((Finset.univ ×ˢ Finset.Icc 1 (P.k - 1) : Finset (M.Ty P × ℕ)) : Set (M.Ty P × ℕ)))).bddAbove
  refine ⟨C + 1, fun t ht ρ => ?_⟩
  unfold M.xC
  refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
  have h1 : -M.rho P ρ i ≤ C :=
    hC ⟨(ρ, i), Finset.mem_coe.2 (Finset.mem_product.2 ⟨Finset.mem_univ _, hi⟩), rfl⟩
  have h2 : t + M.rho P ρ i ≠ 0 := (show 0 < t + M.rho P ρ i by linarith).ne'
  exact_mod_cast h2

theorem hatExp_exists_nodes (P : M.Par) (n : ℕ) :
    ∃ y : Fin n → ℝ, Function.Injective y ∧ ∀ i, ∀ ρ : M.Ty P,
      M.xC P ρ (y i : ℂ) ≠ 0 ∧ M.xC P ρ ((y i : ℂ) - 1) ≠ 0 ∧ M.xC P ρ ((y i : ℂ) + 1) ≠ 0 := by
  obtain ⟨C, hC⟩ := hatExp_exists_bound P
  refine ⟨fun i => C + 1 + (i : ℕ), fun i j h => ?_, fun i ρ => ?_⟩
  · have h' : ((i : ℕ) : ℝ) = (j : ℕ) := by simpa using h
    exact Fin.ext (by exact_mod_cast h')
  · have h0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    refine ⟨hC _ (by linarith) ρ, ?_, ?_⟩
    · have := hC (C + 1 + (i : ℕ) - 1) (by linarith) ρ
      rwa [Complex.ofReal_sub, Complex.ofReal_one] at this
    · have := hC (C + 1 + (i : ℕ) + 1) (by linarith) ρ
      rwa [Complex.ofReal_add _ 1, Complex.ofReal_one] at this

theorem hats_mem_nfSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (T : Set A) (a : ℕ), (∀ x ∈ basics d, x ∈ nfSpan d T 0 a 1) → ∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1 := by
  intro P A _ _ _ _ d hd T a hT
  have hle : nfSpan d (basics d) 0 0 1 ≤ nfSpan d T 0 a 1 := by
    unfold nfSpan
    refine Submodule.span_le.2 ?_
    rintro x ⟨b, hb, H, hH, hHT, rfl⟩
    obtain ⟨h, rfl⟩ := List.length_eq_one_iff.1 hH
    have h1 := ((GlobalTheory.T.normalFormProductSpan_left_mul_closed P A d hd T).1 0 a 1 h (hT h (hHT h (List.mem_singleton_self h)))).1 b hb
    simpa [nfSpan] using h1
  obtain ⟨y, hy, hreg⟩ := hatExp_exists_nodes P (P.r + 2)
  have hyc : Function.Injective fun i => (y i : ℂ) := fun i j h => hy (Complex.ofReal_injective h)
  have hyn : Function.Injective fun i => -(y i : ℂ) := fun i j h => hyc (neg_injective h)
  have key : ∀ (Z : ℂ → A) (X : ℕ → A) (ν : Fin (P.r + 2) → ℂ), Function.Injective ν →
      (∀ s : ℂ, Z s = ∑ j ∈ Finset.range (P.r + 2), s ^ j • X j) →
      (∀ i, Z (ν i) ∈ nfSpan d T 0 a 1) → ∀ s, Z s ∈ nfSpan d T 0 a 1 := by
    intro Z X ν hν hZ hi s
    refine (Submodule.span_le.2 ?_) ((GlobalTheory.T.mem_span_values_of_vector_polynomial A (P.r + 2) Z X ν hν hZ).2 s)
    rintro _ ⟨i, rfl⟩
    exact hi i
  obtain ⟨Xa, Xr, hXa, hXr, -⟩ := GlobalTheory.T.plusHats_taylorCoeff_leibniz_rule A P.r d.L 0
  obtain ⟨Va, Vr, hVa, hVr, -⟩ := GlobalTheory.T.minusHats_taylorCoeff_leibniz_rule A P.r d.L 0
  rintro X (((⟨s, rfl⟩ | ⟨s, rfl⟩) | ⟨s, rfl⟩) | ⟨s, rfl⟩)
  · have := key (fun s => d.L.Ahat (0 + s)) Xa _ hyc hXa
      (fun i => by simpa using hT _ ⟨y i, hreg i, Or.inl rfl⟩) s
    simpa using this
  · have := key (fun s => d.L.R0 (0 + s)) Xr _ hyc hXr
      (fun i => by simpa using hle (GlobalTheory.T.R0_and_R0v_mem_nfSpan_basics_of_xC_ne_zero P A d hd (y i) (hreg i)).1) s
    simpa using this
  · have := key (fun s => d.L.Ahatv (0 - s)) Va _ hyn hVa
      (fun i => by simpa using hT _ ⟨y i, hreg i, Or.inr (Or.inl rfl)⟩) (-s)
    simpa using this
  · have := key (fun s => d.L.R0v (0 - s)) Vr _ hyn hVr
      (fun i => by simpa using hle (GlobalTheory.T.R0_and_R0v_mem_nfSpan_basics_of_xC_ne_zero P A d hd (y i) (hreg i)).2) (-s)
    simpa using this

end GlobalTheory.HatNF
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hatLetters_mem_normalFormProductSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (T : Set A) (a : ℕ), (∀ x ∈ basics d, x ∈ nfSpan d T 0 a 1) → ∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1 := by
  atlas_forward_decl GlobalTheory.HatNF.hats_mem_nfSpan
end

section
section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem hats_prod_mem_nfSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (T : Set A) (a : ℕ), (∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1) → ∀ H : List A, (∀ h ∈ H, h ∈ hats d.L) → H.prod ∈ nfSpan d T 0 (a * H.length) H.length := by
  intro P A _ _ _ _ d hd T a ha H
  induction H with
  | nil =>
    intro _
    refine Submodule.subset_span ⟨1, (bmon d).one_mem, [], rfl, by simp, ?_⟩
    simp
  | cons X H ih =>
    intro hH
    have h1 := ih (fun h hh => hH h (List.mem_cons_of_mem _ hh))
    have h2 := (GlobalTheory.T.normalFormProductSpan_left_mul_closed P A d hd T).2 a ha 0 (a * H.length) H.length X
      (hH X List.mem_cons_self) _ h1
    rw [List.prod_cons, List.length_cons, Nat.mul_succ]
    exact h2

end GlobalTheory.HatNF
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.list_prod_hatLetters_mem_normalFormProductSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (T : Set A) (a : ℕ), (∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1) → ∀ H : List A, (∀ h ∈ H, h ∈ hats d.L) → H.prod ∈ nfSpan d T 0 (a * H.length) H.length := by
  atlas_forward_decl GlobalTheory.HatNF.hats_prod_mem_nfSpan
end

section
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open scoped ContDiff

namespace GlobalTheory.HatNF.MulCoord

noncomputable section

theorem exists_fderiv_log {m : ℕ} (γ : ℝ) (hγ : 0 < γ) (c : Fin m → ℂ) (hc : c ∈ OmX m) :
    ∃ D : (Fin m → ℂ) →L[ℝ] ℝ,
      HasFDerivAt (fun x : Fin m → ℂ => Real.log (Complex.normSq (∏ a, x a) * γ)) D c ∧
      ∀ l w, D (Pi.single l w) = 2 * ((c l).re * w.re + (c l).im * w.im) / Complex.normSq (c l) := by
  classical
  have hopen : IsOpen (OmX m) := by
    have : OmX m = ⋂ l, {x : Fin m → ℂ | x l ≠ 0} := by ext x; simp [OmX]
    rw [this]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  let pr : Fin m → ((Fin m → ℂ) →L[ℝ] ℂ) := fun a => ContinuousLinearMap.proj a
  let R : Fin m → ((Fin m → ℂ) →L[ℝ] ℝ) := fun a => Complex.reCLM.comp (pr a)
  let J : Fin m → ((Fin m → ℂ) →L[ℝ] ℝ) := fun a => Complex.imCLM.comp (pr a)
  have h1 : ∀ a, HasFDerivAt (fun x : Fin m → ℂ => Real.log (R a x * R a x + J a x * J a x))
      ((R a c * R a c + J a c * J a c)⁻¹ • ((R a c • R a + R a c • R a) + (J a c • J a + J a c • J a))) c := by
    intro a
    refine HasFDerivAt.log (((R a).hasFDerivAt.mul (R a).hasFDerivAt).add
      ((J a).hasFDerivAt.mul (J a).hasFDerivAt)) ?_
    have : Complex.normSq (c a) ≠ 0 := by simpa using hc a
    simpa [R, J, pr, Complex.normSq_apply] using this
  have h2 := (HasFDerivAt.fun_sum (u := Finset.univ) fun a _ => h1 a).add_const (Real.log γ)
  refine ⟨_, h2.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [hopen.mem_nhds hc] with x hx
    have hx' : ∀ a, Complex.normSq (x a) ≠ 0 := fun a => by simpa using hx a
    rw [map_prod, Real.log_mul (Finset.prod_ne_zero_iff.2 fun a _ => hx' a) hγ.ne',
      Real.log_prod (fun a _ => hx' a)]
    simp [R, J, pr, Complex.normSq_apply]
  · intro l w
    rw [ContinuousLinearMap.sum_apply, Finset.sum_eq_single l]
    · simp [R, J, pr, Complex.normSq_apply]
      ring
    · intro b _ hb
      simp [R, J, pr, Pi.single_eq_of_ne hb]
    · simp

theorem euler_mul {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : ℝ → ℝ) (hφ : LE.SmoothLog φ)
    (q : ℕ) (γ : ℝ) (hγ : 0 < γ) (c : Fin m → ℂ) (hc : c ∈ OmX m) (f : (Fin m → ℂ) → E)
    (hf : DifferentiableAt ℝ f c) (l : Fin m) :
    pOp l (fun x => ((LE.ld q φ (Complex.normSq (∏ a, x a) * γ) : ℝ) : ℂ) • f x) c =
      ((LE.ld q φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • pOp l f c +
        ((LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • f c ∧
    pbOp l (fun x => ((LE.ld q φ (Complex.normSq (∏ a, x a) * γ) : ℝ) : ℂ) • f x) c =
      ((LE.ld q φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • pbOp l f c +
        ((LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • f c := by
  obtain ⟨D, hD, hDl⟩ := exists_fderiv_log γ hγ c hc
  have hh : Differentiable ℝ (iteratedDeriv q fun u : ℝ => φ (Real.exp u)) :=
    ContDiff.differentiable_iteratedDeriv q hφ (by exact_mod_cast ENat.coe_lt_top q)
  have h1 : HasDerivAt (iteratedDeriv q fun u : ℝ => φ (Real.exp u))
      (LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ)) (Real.log (Complex.normSq (∏ a, c a) * γ)) := by
    rw [LE.ld, iteratedDeriv_succ]
    exact (hh _).hasDerivAt
  have h2 := Complex.ofRealCLM.hasFDerivAt.comp c (h1.comp_hasFDerivAt c hD)
  have h3 : HasFDerivAt (fun x => ((LE.ld q φ (Complex.normSq (∏ a, x a) * γ) : ℝ) : ℂ) • f x) _ c :=
    HasFDerivAt.smul h2 hf.hasFDerivAt
  have key : ∀ w, fderiv ℝ (fun x => ((LE.ld q φ (Complex.normSq (∏ a, x a) * γ) : ℝ) : ℂ) • f x) c
      (Pi.single l w) = ((LE.ld q φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • fderiv ℝ f c (Pi.single l w) +
        ((LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) *
          (2 * ((c l).re * w.re + (c l).im * w.im) / Complex.normSq (c l)) : ℝ) : ℂ) • f c := by
    intro w
    rw [h3.fderiv, ← hDl]
    simp [LE.ld]
  have hn : ((Complex.normSq (c l) : ℝ) : ℂ) ≠ 0 := by simpa using hc l
  have e1 : c l * (((c l).re : ℂ) - Complex.I * (c l).im) = (Complex.normSq (c l) : ℝ) := by
    apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
  have e2 : star (c l) * (((c l).re : ℂ) + Complex.I * (c l).im) = (Complex.normSq (c l) : ℝ) := by
    apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
  constructor
  · simp only [pOp, if_pos hc, wirt, key]
    simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
    push_cast
    match_scalars
    · ring
    · field_simp
      linear_combination (LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) : ℂ) * e1
    · ring
  · simp only [pbOp, if_pos hc, wirtBar, key]
    simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
    push_cast
    match_scalars
    · ring
    · field_simp
      linear_combination (LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) : ℂ) * e2
    · ring

section radial

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}

theorem end_ext (A B : Module.End ℂ (Q.RadSp k r z z' π π'))
    (h : ∀ Φ, ∀ c g, (c, g) ∈ Q.DomR k r z z' →
      (A Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g = (B Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g) : A = B := by
  refine LinearMap.ext fun Φ => Subtype.ext ?_
  funext c g
  by_cases hx : (c, g) ∈ Q.DomR k r z z'
  · exact h Φ c g hx
  · exact ((A Φ).2.1 (c, g) hx).trans ((B Φ).2.1 (c, g) hx).symm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem differentiableAt_coord (Φ : Q.RadSp k r z z' π π') (c : Fin r → ℂ) (g : Q.Mx k r)
    (hx : (c, g) ∈ Q.DomR k r z z') :
    DifferentiableAt ℝ (fun c' => (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c' g) c := by
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := Φ.2.2.1 (c, g) hx
  have h1 : DifferentiableAt ℝ F (c, g) :=
    (hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  have h2 : DifferentiableAt ℝ (fun c' : Fin r → ℂ => F (c', g)) c :=
    h1.comp c (differentiableAt_id.prodMk (differentiableAt_const g))
  refine h2.congr_of_eventuallyEq ?_
  have hc : ContinuousAt (fun c' : Fin r → ℂ => (c', g)) c := (continuous_id.prodMk continuous_const).continuousAt
  filter_upwards [hc.preimage_mem_nhds (hU.mem_nhds hxU)] with c' hc'
  exact hΦ (c', g) hc' hx.2.1

theorem commute_of_mul (A B : Module.End ℂ (Q.RadSp k r z z' π π')) (a b : (Fin r → ℂ) → Q.Mx k r → ℂ)
    (hA : ∀ Φ, ∀ c g, (c, g) ∈ Q.DomR k r z z' →
      (A Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g = a c g • (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g)
    (hB : P5.multiplicationOperator B b) : Commute A B := by
  refine end_ext _ _ fun Φ c g hx => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, hA _ c g hx, hB, hB, hA _ c g hx, smul_comm]

end radial

theorem mul_coord : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ q, (∀ l, X.op l 0 * W q = W q * X.op l 0 + W (q + 1) ∧ X.op l 3 * W q = W q * X.op l 3 + W (q + 1) ∧ Commute (X.op l 1) (W q) ∧ Commute (X.op l 2) (W q) ∧ Commute (X.op l 4) (W q) ∧ Commute (X.op l 5) (W q)) ∧ ∀ j, Commute (X.fn j) (W q) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d _ _ φ W hφ hW q
  refine ⟨fun l => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun j => ?_⟩
  · refine end_ext _ _ fun Φ c g hx => ?_
    have h := (euler_mul φ hφ q _ hx.2.2 c hx.1 _ (differentiableAt_coord Φ c g hx) l).1
    rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_add, Pi.add_apply,
      Pi.add_apply, hW q, hW (q + 1), X.op_apply, X.op_apply]
    simp only [Q.crd, opL, hW q Φ]
    exact h
  · refine end_ext _ _ fun Φ c g hx => ?_
    have h := (euler_mul φ hφ q _ hx.2.2 c hx.1 _ (differentiableAt_coord Φ c g hx) l).2
    rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_add, Pi.add_apply,
      Pi.add_apply, hW q, hW (q + 1), X.op_apply, X.op_apply]
    simp only [Q.crd, opL, hW q Φ]
    exact h
  · exact commute_of_mul _ _ (fun c _ => c l) _ (fun Φ c g _ => by rw [X.op_apply]; rfl) (hW q)
  · exact commute_of_mul _ _ (fun c _ => (c l)⁻¹) _ (fun Φ c g _ => by rw [X.op_apply]; rfl) (hW q)
  · exact commute_of_mul _ _ (fun c _ => star (c l)) _ (fun Φ c g _ => by rw [X.op_apply]; rfl) (hW q)
  · exact commute_of_mul _ _ (fun c _ => (star (c l))⁻¹) _ (fun Φ c g _ => by rw [X.op_apply]; rfl) (hW q)
  · exact commute_of_mul _ _ (fun _ g => Q.fnVal P.k P.r Bs.z Bs.z' j g) _
      (fun Φ c g hx => X.fn_apply j Φ (c, g) hx) (hW q)

end

end GlobalTheory.HatNF.MulCoord
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerDerivMultipliers_coordOps_commutation_relations : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ q, (∀ l, X.op l 0 * W q = W q * X.op l 0 + W (q + 1) ∧ X.op l 3 * W q = W q * X.op l 3 + W (q + 1) ∧ Commute (X.op l 1) (W q) ∧ Commute (X.op l 2) (W q) ∧ Commute (X.op l 4) (W q) ∧ Commute (X.op l 5) (W q)) ∧ ∀ j, Commute (X.fn j) (W q) := by
  atlas_forward_decl GlobalTheory.HatNF.MulCoord.mul_coord
end

section
section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory
open scoped ContDiff

theorem mulT_ld_contDiff {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv q (fun u : ℝ => φ (Real.exp u))) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv q hφ

theorem mulT_normSq_contDiff : ContDiff ℝ ∞ (fun w : ℂ => Complex.normSq w) := by
  have : (fun w : ℂ => Complex.normSq w) = fun w : ℂ => Complex.reCLM w * Complex.reCLM w + Complex.imCLM w * Complex.imCLM w := by
    funext w; simp [Complex.normSq_apply]
  rw [this]
  fun_prop

theorem mulT_contDiffOn {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) {a : ℝ} (ha : 0 < a) (T : ℝ) :
    ContDiffOn ℝ ∞ (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ))
      {w : ℂ | T < Complex.normSq w} := by
  have h1 : ContDiffOn ℝ ∞ (fun w : ℂ => Real.log (a * (Complex.normSq w - T)))
      {w : ℂ | T < Complex.normSq w} := by
    refine ContDiffOn.log (contDiff_const.mul (mulT_normSq_contDiff.sub contDiff_const)).contDiffOn ?_
    intro w hw
    exact (mul_pos ha (sub_pos.2 hw)).ne'
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((mulT_ld_contDiff hφ q).comp_contDiffOn h1)

theorem mulT_fderiv {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) {a : ℝ} (ha : 0 < a) (T : ℝ) {w : ℂ}
    (hw : T < Complex.normSq w) (v : ℂ) :
    fderiv ℝ (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) w v =
      ((LE.ld (q + 1) φ (a * (Complex.normSq w - T)) * (Complex.normSq w - T)⁻¹ *
        (2 * (w.re * v.re + w.im * v.im)) : ℝ) : ℂ) := by
  have hp : 0 < Complex.normSq w - T := sub_pos.2 hw
  have hn : HasFDerivAt (fun w : ℂ => Complex.normSq w)
      ((2 * w.re) • Complex.reCLM + (2 * w.im) • Complex.imCLM) w := by
    have : (fun w : ℂ => Complex.normSq w) =
        fun w : ℂ => Complex.reCLM w * Complex.reCLM w + Complex.imCLM w * Complex.imCLM w := by
      funext w; simp [Complex.normSq_apply]
    rw [this]
    have h1 := Complex.reCLM.hasFDerivAt (x := w)
    have h2 := Complex.imCLM.hasFDerivAt (x := w)
    refine ((h1.mul h1).add (h2.mul h2)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp
    ring
  have h1 := ((hn.sub_const T).const_mul a).log (mul_pos ha hp).ne'
  have h2 : HasDerivAt (iteratedDeriv q (fun u : ℝ => φ (Real.exp u)))
      (LE.ld (q + 1) φ (a * (Complex.normSq w - T))) (Real.log (a * (Complex.normSq w - T))) := by
    unfold LE.ld
    rw [iteratedDeriv_succ]
    exact (((mulT_ld_contDiff hφ q).differentiable (by simp)) _).hasDerivAt
  have h3 := Complex.ofRealCLM.hasFDerivAt.comp w (h2.comp_hasFDerivAt w h1)
  have h4 : fderiv ℝ (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) w = _ := h3.fderiv
  rw [h4]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_apply,
    add_apply, Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  congr 1
  field_simp

theorem mulT_dZ {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) {a : ℝ} (ha : 0 < a) (T : ℝ) {w : ℂ}
    (hw : T < Complex.normSq w) :
    NF.dZ (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) w =
      star w * ((((Complex.normSq w - T : ℝ) : ℂ))⁻¹ *
        ((LE.ld (q + 1) φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) ∧
    NF.dZb (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) w =
      w * ((((Complex.normSq w - T : ℝ) : ℂ))⁻¹ *
        ((LE.ld (q + 1) φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) := by
  unfold NF.dZ NF.dZb
  rw [mulT_fderiv hφ q ha T hw, mulT_fderiv hφ q ha T hw, ← Complex.ofReal_inv]
  generalize LE.ld (q + 1) φ (a * (Complex.normSq w - T)) = b
  generalize (Complex.normSq w - T)⁻¹ = e
  constructor <;> apply Complex.ext <;> simp <;> ring

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx4 in

theorem t_mul_mulG (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (hφ : LE.SmoothLog φ)
    (hW : IsMulG P Bs φ W) (q : ℕ) (Y : ℂ) :
    X.t Y 1 0 * W q = W q * X.t Y 1 0 - X.fn 2 * X.fn 5 * W (q + 1) * X.t Y 1 1 ∧
      X.t Y 1 1 * W q = W q * X.t Y 1 1 ∧
      X.t Y 0 1 * W q = W q * X.t Y 0 1 + X.fn 0 * X.fn 5 * W (q + 1) * X.t Y 1 1 := by
  have hU := isOpen_normSq_gt (Tz P.k P.r Bs.z * Tz P.k P.r Bs.z')
  have hDU := Dp_maps (k := P.k) (r := P.r) Bs.z Bs.z'
  have hD := Qx5.Dp_open P.k P.r Bs.z Bs.z'
  have ha : ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', 0 < Complex.normSq (∏ a, x.1 a) := fun x hx =>
    Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hx.1 a)
  have key := fun (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r)
      (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') =>
    zeta_smooth_level Bs.z Bs.z' hD hU hDU (mulT_contDiffOn hφ q (ha x hx) _) (Qx5.slice_smooth Φ.2 hx.1)
      ⟨hx.2.1, hx.2.2⟩ Y
  have hd := fun (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') =>
    mulT_dZ hφ q (ha x hx) _ (hDU x.2 hx.2.2)
  have hWa : ∀ (p : ℕ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ) (g : Q.Mx P.k P.r),
      (W p Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        ((LE.ld p φ (Complex.normSq (∏ a, c a) * (Complex.normSq (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) g) -
          Tz P.k P.r Bs.z * Tz P.k P.r Bs.z')) : ℝ) : ℂ) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g :=
    fun p Φ c g => hW p Φ c g
  have ht : ∀ (a b : Fin 2) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r),
      x ∈ Q.DomR P.k P.r Bs.z Bs.z' → (X.t Y a b (W q Φ) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
        Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y a b (fun y =>
          ((LE.ld q φ (Complex.normSq (∏ a, x.1 a) * (Complex.normSq (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) y) -
            Tz P.k P.r Bs.z * Tz P.k P.r Bs.z')) : ℝ) : ℂ) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 y) x.2 := by
    intro a b Φ x hx
    rw [X.t_apply Y a b _ x hx]
    congr 1
    funext y
    exact hWa q Φ x.1 y
  refine ⟨end_ext_dom fun Φ x hx => ?_, end_ext_dom fun Φ x hx => ?_, end_ext_dom fun Φ x hx => ?_⟩
  · rw [Module.End.mul_apply, ht 1 0 Φ x hx, (key Φ x hx).1, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply,
      Pi.sub_apply, X.fn_apply 2 _ x hx, X.fn_apply 5 _ x hx, hWa, hWa,
      X.t_apply Y 1 0 Φ x hx, X.t_apply Y 1 1 Φ x hx, (hd x hx).1, smul_smul, smul_smul, mul_assoc]
    rfl
  · rw [Module.End.mul_apply, ht 1 1 Φ x hx, (key Φ x hx).2.1, Module.End.mul_apply, hWa,
      X.t_apply Y 1 1 Φ x hx]
  · rw [Module.End.mul_apply, ht 0 1 Φ x hx, (key Φ x hx).2.2, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_add, Pi.add_apply,
      Pi.add_apply, X.fn_apply 0 _ x hx, X.fn_apply 5 _ x hx, hWa, hWa,
      X.t_apply Y 0 1 Φ x hx, X.t_apply Y 1 1 Φ x hx, (hd x hx).2, smul_smul, smul_smul, mul_assoc]
    rfl

theorem nf_t_mul_mulG : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ (q : ℕ) (Y : ℂ), X.t Y 1 0 * W q = W q * X.t Y 1 0 - X.fn 2 * X.fn 5 * W (q + 1) * X.t Y 1 1 ∧ X.t Y 1 1 * W q = W q * X.t Y 1 1 ∧ X.t Y 0 1 * W q = W q * X.t Y 0 1 + X.fn 0 * X.fn 5 * W (q + 1) * X.t Y 1 1 :=
  fun Wp Wq _ _ _ _ _ _ P Bs X _ _ _ _ _ _ _ φ W hφ hW q Y => t_mul_mulG Wp Wq P Bs X φ W hφ hW q Y

end GlobalTheory.HatNF
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalForm_entries_commutator_multiplier : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ (q : ℕ) (Y : ℂ), X.t Y 1 0 * W q = W q * X.t Y 1 0 - X.fn 2 * X.fn 5 * W (q + 1) * X.t Y 1 1 ∧ X.t Y 1 1 * W q = W q * X.t Y 1 1 ∧ X.t Y 0 1 * W q = W q * X.t Y 0 1 + X.fn 0 * X.fn 5 * W (q + 1) * X.t Y 1 1 := by
  atlas_forward_decl GlobalTheory.HatNF.nf_t_mul_mulG
end

section
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.MulRelAlg

theorem exists_real_xC_ne_zero (P : M.Par) : ∃ Y : ℝ, ∀ ρ : M.Ty P, M.xC P ρ (Y : ℂ) ≠ 0 := by
  classical
  obtain ⟨Y, hY⟩ := Infinite.exists_notMem_finset
    (((Finset.univ : Finset (M.Ty P)) ×ˢ Finset.Icc 1 (P.k - 1)).image fun x => -M.rho P x.1 x.2)
  refine ⟨Y, fun ρ => ?_⟩
  unfold M.xC
  refine Finset.prod_ne_zero_iff.2 fun i hi h => hY ?_
  refine Finset.mem_image.2 ⟨(ρ, i), Finset.mem_product.2 ⟨Finset.mem_univ _, hi⟩, ?_⟩
  have h' : Y + M.rho P ρ i = 0 := by exact_mod_cast h
  show -M.rho P ρ i = Y
  linarith

theorem up_unique {P : M.Par} {l : ℕ} {σ ρ ρ' : M.Ty P} (h : M.Up P l σ ρ) (h' : M.Up P l σ ρ') : ρ = ρ' := by
  funext i
  exact Fin.ext ((h i).trans (h' i).symm)

theorem not_up_self {P : M.Par} {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) : ¬ M.Up P l ρ ρ := by
  intro h
  rw [Finset.mem_Icc] at hl
  have := h ⟨l - 1, by omega⟩
  rw [if_pos (by show l - 1 + 1 = l; omega)] at this
  omega

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem proj_raising_sum_proj_eq_zero (d : Q.NFData P A) (h : d.Rel) (Y : ℂ) (ρ : M.Ty P) :
    d.κ (Pi.single ρ 1) * d.weightedSumBis Y * d.κ (Pi.single ρ 1) = 0 := by
  classical
  unfold Q.NFData.weightedSumBis
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun l hl => ?_
  have h4 := h.2.2.2.1 l (fun σ => if M.Up P l σ ρ then 1 else 0) (Pi.single ρ 1) (by
    intro σ σ' hu
    by_cases e : σ' = ρ
    · subst e; simp [hu]
    · have : ¬ M.Up P l σ ρ := fun h2 => e (up_unique hu h2)
      simp [this, e])
  rw [← mul_assoc, h4, mul_assoc, mul_assoc, ← map_mul, ← map_mul]
  have : ((fun σ => if M.Up P l σ ρ then (1 : ℂ) else 0) *
      ((fun σ => M.xEx P {l} σ Y) * Pi.single ρ 1) : M.Ty P → ℂ) = 0 := by
    funext σ
    by_cases e : σ = ρ
    · subst e; simp [not_up_self hl]
    · simp [e]
  rw [this, map_zero, mul_zero]

theorem eq_zero_of_blocks (d : Q.NFData P A) (X : A) (hc : ∀ f, Commute (d.κ f) X)
    (h0 : ∀ ρ, d.κ (Pi.single ρ 1) * X * d.κ (Pi.single ρ 1) = 0) : X = 0 := by
  classical
  have h1 : ∀ ρ, d.κ (Pi.single ρ 1) * X = 0 := by
    intro ρ
    have := h0 ρ
    rw [mul_assoc, ← (hc _).eq, ← mul_assoc, ← map_mul, ← Pi.single_mul, mul_one] at this
    exact this
  have h2 : ∑ ρ : M.Ty P, d.κ (Pi.single ρ 1) = 1 := by
    rw [← map_sum, ← map_one d.κ]
    congr 1
    exact Finset.univ_sum_single (1 : M.Ty P → ℂ)
  rw [← one_mul X, ← h2, Finset.sum_mul]
  exact Finset.sum_eq_zero fun ρ _ => h1 ρ

theorem star_GGi [StarModule ℂ A] {r : ℕ} (L : LevelData A r) (h : IsStarLevel L) : star L.GGi = L.GGi := by
  have hb : star L.ζb = L.ζ := by rw [← h.1, star_star]
  have hG : star L.GG = L.GG := by
    rw [L.GG_def, star_sub, star_mul, h.1, hb, ← algebraMap_star_comm, h.2.2]
  have : star L.GGi * L.GG = 1 := by rw [← hG, ← star_mul, L.GG_GGi, star_one]
  calc star L.GGi = star L.GGi * L.GG * L.GGi := by rw [mul_assoc, L.GG_GGi, mul_one]
    _ = L.GGi := by rw [this, one_mul]

theorem nab_rel (d : Q.NFData P A) (h : d.Rel) (m m' : A) (hf : ∀ f ∈ d.L.fns, Commute f m)
    (hf' : ∀ f ∈ d.L.fns, Commute f m') (hκ : ∀ f, Commute (d.κ f) m) (hκ' : ∀ f, Commute (d.κ f) m')
    (hQ : ∀ Y : ℝ, d.QQ Y 1 0 * m = m * d.QQ Y 1 0 - d.L.ζb * d.L.GGi * m' * d.QQ Y 1 1) :
    d.L.nab * m = m * d.L.nab + d.L.ζb * d.L.GGi * m' := by
  classical
  obtain ⟨Y, hY⟩ := exists_real_xC_ne_zero P
  have hQ := hQ Y
  have e10 : d.QQ Y 1 0 = d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y := rfl
  have e11 : d.QQ Y 1 1 = d.L.GG * d.x Y := rfl
  rw [e10, e11] at hQ
  have mG : d.L.GG ∈ d.L.fns := by simp [LevelData.fns]
  have mGi : d.L.GGi ∈ d.L.fns := by simp [LevelData.fns]
  have mz : d.L.ζb ∈ d.L.fns := by simp [LevelData.fns]
  have kG : ∀ f, Commute (d.κ f) d.L.GG := fun f => h.2.1 f _ (Or.inl mG)
  have kGi : ∀ f, Commute (d.κ f) d.L.GGi := fun f => h.2.1 f _ (Or.inl mGi)
  have kz : ∀ f, Commute (d.κ f) d.L.ζb := fun f => h.2.1 f _ (Or.inl mz)
  have kn : ∀ f, Commute (d.κ f) d.L.nab := fun f => h.2.1 f _ (Or.inr (by simp))
  have kk : ∀ f, Commute (d.κ f) (d.x Y) := fun f => by
    unfold Q.NFData.x; exact (Commute.all _ _).map d.κ
  set Z : A := m * d.L.nab + d.L.ζb * d.L.GGi * m' - d.L.nab * m with hZ
  set g : A := d.L.GG * d.x Y with hg
  have kZ : ∀ f, Commute (d.κ f) Z := fun f =>
    (((hκ f).mul_right (kn f)).add_right (((kz f).mul_right (kGi f)).mul_right (hκ' f))).sub_right
      ((kn f).mul_right (hκ f))
  have gm : Commute g m := (hf _ mG).mul_left (hκ _)
  have gw : Commute g (d.L.ζb * d.L.GGi * m') :=
    (Commute.mul_right (Commute.mul_right (d.L.fns_comm _ mG _ mz) (d.L.fns_comm _ mG _ mGi)) (hf' _ mG)).mul_left
      (((kz _).mul_right (kGi _)).mul_right (hκ' _))
  have um : Commute (algebraMap ℂ A ((Y : ℂ) + 1 / 2) * (d.L.ζb * d.L.GGi)) m :=
    Commute.mul_left (Algebra.commutes _ _) ((hf _ mz).mul_left (hf _ mGi))
  have hX : g * Z = m * d.weightedSumBis Y - d.weightedSumBis Y * m := by
    have e1 : m * (g * d.L.l0 Y) = g * (m * d.L.l0 Y) := by rw [← mul_assoc, ← gm.eq, mul_assoc]
    rw [add_mul, mul_add, e1, ← gw.eq] at hQ
    have e2 : Z = d.L.l0 Y * m - m * d.L.l0 Y + d.L.ζb * d.L.GGi * m' := by
      unfold LevelData.l0
      rw [sub_mul, mul_sub, um.eq, hZ]
      noncomm_ring
    rw [e2, mul_add, mul_sub, ← mul_assoc g _ m, eq_sub_of_add_eq hQ]
    abel
  have hX0 : g * Z = 0 := by
    refine eq_zero_of_blocks d _ (fun f => ((kG f).mul_right (kk f)).mul_right (kZ f)) fun ρ => ?_
    have := proj_raising_sum_proj_eq_zero d h Y ρ
    rw [hX, mul_sub, sub_mul, ← mul_assoc, (hκ _).eq, mul_assoc m, mul_assoc m, this, ← mul_assoc _ _ m,
      mul_assoc _ m, ← (hκ _).eq, ← mul_assoc, this]
    simp
  have hinv : d.κ (fun ρ => (M.xC P ρ Y)⁻¹) * d.L.GGi * g = 1 := by
    rw [hg, mul_assoc, ← mul_assoc d.L.GGi, d.L.GGi_GG, one_mul]
    unfold Q.NFData.x
    rw [← map_mul, ← map_one d.κ]
    congr 1
    funext ρ
    exact inv_mul_cancel₀ (hY ρ)
  have : Z = 0 := by rw [← one_mul Z, ← hinv, mul_assoc, hX0, mul_zero]
  exact (sub_eq_zero.1 this).symm

theorem mulRel_of_entries : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ m : ℕ → A, (∀ q, (∀ f ∈ d.L.fns, Commute f (m q)) ∧ (∀ l, d.L.p l * m q = m q * d.L.p l + m (q + 1)) ∧ (∀ l, d.L.pb l * m q = m q * d.L.pb l + m (q + 1)) ∧ (∀ f : M.Ty P → ℂ, Commute (d.κ f) (m q)) ∧ star (m q) = m q ∧ ∀ Y : ℝ, d.QQ Y 1 0 * m q = m q * d.QQ Y 1 0 - d.L.ζb * d.L.GGi * m (q + 1) * d.QQ Y 1 1) → MulRel d.L m := by
  intro P A _ _ _ _ d hd m hm q
  obtain ⟨-, hs, hr, -⟩ := hd
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hm q
  obtain ⟨k1, -, -, k4, k5, -⟩ := hm (q + 1)
  have hn := nab_rel d hr (m q) (m (q + 1)) h1 k1 h4 k4 h6
  refine ⟨h1, h2, h3, hn, ?_⟩
  have hb : star d.L.ζb = d.L.ζ := by rw [← hs.1, star_star]
  have mGi : d.L.GGi ∈ d.L.fns := by simp [LevelData.fns]
  have mz : d.L.ζ ∈ d.L.fns := by simp [LevelData.fns]
  have hst := congrArg star hn
  rw [star_add, star_mul, star_mul, star_mul, star_mul, hs.2.1, h5, k5, hb, star_GGi d.L hs,
    d.L.fns_comm _ mGi _ mz, ← ((k1 _ mz).mul_left (k1 _ mGi)).eq] at hst
  rw [hst]
  abel

end GlobalTheory.HatNF.MulRelAlg
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connection_mulRel_of_entry_relations : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ m : ℕ → A, (∀ q, (∀ f ∈ d.L.fns, Commute f (m q)) ∧ (∀ l, d.L.p l * m q = m q * d.L.p l + m (q + 1)) ∧ (∀ l, d.L.pb l * m q = m q * d.L.pb l + m (q + 1)) ∧ (∀ f : M.Ty P → ℂ, Commute (d.κ f) (m q)) ∧ star (m q) = m q ∧ ∀ Y : ℝ, d.QQ Y 1 0 * m q = m q * d.QQ Y 1 0 - d.L.ζb * d.L.GGi * m (q + 1) * d.QQ Y 1 1) → MulRel d.L m := by
  atlas_forward_decl GlobalTheory.HatNF.MulRelAlg.mulRel_of_entries
end

section
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.MulRelActual

section pairs

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mkPair_mul_mkPair (a b c d : Module.End ℂ V) : Q.mkP a b * Q.mkP c d = Q.mkP (a * c) (d * b) := rfl
theorem mkPair_add_mkPair (a b c d : Module.End ℂ V) : Q.mkP a b + Q.mkP c d = Q.mkP (a + c) (b + d) := rfl
theorem mkPair_sub_mkPair (a b c d : Module.End ℂ V) : Q.mkP a b - Q.mkP c d = Q.mkP (a - c) (b - d) := rfl
theorem mkPair_congr {a b c d : Module.End ℂ V} (h : a = c) (h' : b = d) : Q.mkP a b = Q.mkP c d := by rw [h, h']

theorem snd_eq_of_mkPair_eq {a b c d : Module.End ℂ V} (h : Q.mkP a b = Q.mkP c d) : b = d :=
  congrArg (fun x : Q.Pr V => MulOpposite.unop (Prod.snd x)) h

theorem commute_mkP {a b w : Module.End ℂ V} (ha : Commute a w) (hb : Commute b w) :
    Commute (Q.mkP a b) (Q.mkP w w) := by
  change Q.mkP a b * Q.mkP w w = Q.mkP w w * Q.mkP a b
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair]
  exact mkPair_congr ha.eq hb.eq.symm

theorem exists_mkP (x : Q.Pr V) : ∃ a b, x = Q.mkP a b := ⟨Prod.fst x, MulOpposite.unop (Prod.snd x), rfl⟩

end pairs

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

omit [FiniteDimensional ℂ Wp] in
theorem hsVec_smul (s : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (s • A) = s • B.hsVec A := rfl

omit [FiniteDimensional ℂ Wp] in
theorem hsVec_sub (A A' : Wq →L[ℂ] Wp) : B.hsVec (A - A') = B.hsVec A - B.hsVec A' := rfl

omit [FiniteDimensional ℂ Wp] in
theorem eq_zero_of_hsVec {A : Wq →L[ℂ] Wp} (h : B.hsVec A = 0) : A = 0 := by
  have h1 : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0 := fun i => congrArg (fun v => v i) h
  apply ContinuousLinearMap.coe_injective
  apply (stdOrthonormalBasis ℂ Wq).toBasis.ext
  intro i
  simpa using h1 i

omit [FiniteDimensional ℂ Wp] in
theorem eq_of_inner {A A' : Wq →L[ℂ] Wp}
    (h : inner ℂ (B.hsVec (A - A')) (B.hsVec A) = inner ℂ (B.hsVec (A - A')) (B.hsVec A')) : A = A' := by
  have h1 : inner ℂ (B.hsVec (A - A')) (B.hsVec (A - A')) = 0 := by
    nth_rewrite 2 [hsVec_sub]
    rw [inner_sub_right, h, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_hsVec (inner_self_eq_zero.1 h1))

variable {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem radSp_ext {Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'}
    (h : ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) : Φ = Ψ := by
  apply Subtype.ext
  funext c g
  by_cases hx : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z'
  · exact h (c, g) hx
  · rw [Φ.2.1 (c, g) hx, Ψ.2.1 (c, g) hx]

theorem commute_of_adj {a b w : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
    {m : (Fin P.r → ℂ) → Q.Mx P.k P.r → ℂ} (hw : P5.multiplicationOperator w m)
    (hab : ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
      B.hsInner ((a Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) =
        B.hsInner ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) ((b Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)) :
    Commute a w := by
  refine LinearMap.ext fun Φ => radSp_ext fun x hx => ?_
  apply eq_of_inner
  have h1 := hab (w Φ) (a (w Φ) - w (a Φ)) x hx
  have h2 := hab Φ (a (w Φ) - w (a Φ)) x hx
  unfold B.hsInner at h1 h2
  rw [hw Φ, hsVec_smul, inner_smul_right, ← h2, ← inner_smul_right, ← hsVec_smul, ← hw (a Φ)] at h1
  exact h1

theorem commute_of_ptAdj {x : RA P Bs} (hx : PtAdj P Bs x) {w : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
    {m : (Fin P.r → ℂ) → Q.Mx P.k P.r → ℂ} (hw : P5.multiplicationOperator w m) : Commute x (Q.mkP w w) := by
  obtain ⟨a, b, rfl⟩ := exists_mkP x
  refine commute_mkP (commute_of_adj (b := b) hw hx) (commute_of_adj (b := a) hw fun Φ Ψ y hy => ?_)
  have h := hx Ψ Φ y hy
  unfold B.hsInner at h ⊢
  rw [← inner_conj_symm, ← inner_conj_symm (B.hsVec ((a Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2))]
  exact congrArg _ h.symm

end hs

theorem mulRel_actual : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → MulRel d.L (fun q => Q.mkP (W q) (W q)) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN φ W hφ hW
  have hH := (GlobalTheory.T.normalForm_actualOperators_algebraicHypotheses Wp Wq P Bs X μ L st l0 d hD hN).1
  have hK := GlobalTheory.T.radialPairConstants_pointwiseAdjoint_bounded Wp Wq P Bs X μ L st l0 d hD hN
  have hC := GlobalTheory.T.eulerDerivMultipliers_coordOps_commutation_relations Wp Wq P Bs X μ L st l0 d hD hN φ W hφ hW
  have hT := GlobalTheory.T.normalForm_entries_commutator_multiplier Wp Wq P Bs X μ L st l0 d hD hN φ W hφ hW
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩, -, hR, hQ⟩ := hN
  have hκ : ∀ q (f : M.Ty P → ℂ), Commute (d.κ f) (Q.mkP (W q) (W q)) := fun q f =>
    commute_of_ptAdj (hK f).1 (hW q)
  have hf : ∀ q, ∀ f ∈ d.L.fns, Commute f (Q.mkP (W q) (W q)) := by
    intro q f hf
    obtain ⟨ho, hfn⟩ := hC q
    rcases hf with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | hf)
    · rw [h3]; exact commute_mkP (ho l).2.2.1 (ho l).2.2.2.2.1
    · rw [h4]; exact commute_mkP (ho l).2.2.2.1 (ho l).2.2.2.2.2
    · rw [h5]; exact commute_mkP (ho l).2.2.2.2.1 (ho l).2.2.1
    · rw [h6]; exact commute_mkP (ho l).2.2.2.2.2 (ho l).2.2.2.1
    · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h7]; exact commute_mkP (hfn _) (hfn _)
      · rw [h8]; exact commute_mkP (hfn _) (hfn _)
      · rw [h9]; exact commute_mkP (hfn _) (hfn _)
      · rw [h10]; exact commute_mkP (hfn _) (hfn _)
      · rw [h11]; exact commute_mkP (hfn _) (hfn _)
      · rw [h12]; exact commute_mkP (hfn _) (hfn _)
  refine GlobalTheory.T.connection_mulRel_of_entry_relations P (RA P Bs) d hH _ fun q => ⟨hf q, fun l => ?_, fun l => ?_, hκ q, rfl, fun Y => ?_⟩
  · rw [h1, mkPair_mul_mkPair, mkPair_mul_mkPair, mkPair_add_mkPair]
    refine mkPair_congr ((hC q).1 l).1 ?_
    rw [neg_mul, ((hC q).1 l).2.1, mul_neg]; abel
  · rw [h2, mkPair_mul_mkPair, mkPair_mul_mkPair, mkPair_add_mkPair]
    refine mkPair_congr ((hC q).1 l).2.1 ?_
    rw [neg_mul, ((hC q).1 l).1, mul_neg]; abel
  · have mζ : d.L.ζb ∈ d.L.fns := Or.inr (by simp)
    have mG : d.L.GG ∈ d.L.fns := Or.inr (by simp)
    have mGi : d.L.GGi ∈ d.L.fns := Or.inr (by simp)
    have e11 : d.QQ Y 1 1 = d.L.GG * d.x Y := rfl
    have c11 : ∀ g ∈ d.L.fns, Commute (d.QQ Y 1 1) g := fun g hg => by
      rw [e11]
      exact Commute.mul_left (d.L.fns_comm _ mG _ hg) (hR.2.1 _ g (Or.inl hg))
    have c11m : Commute (d.QQ Y 1 1) (Q.mkP (W (q + 1)) (W (q + 1))) := by
      rw [e11]
      exact Commute.mul_left (hf _ _ mG) (hκ _ _)
    have cζG : Commute d.L.ζb d.L.GGi := d.L.fns_comm _ mζ _ mGi
    have key : d.L.ζb * d.L.GGi * Q.mkP (W (q + 1)) (W (q + 1)) * d.QQ Y 1 1 =
        d.QQ Y 1 1 * (Q.mkP (W (q + 1)) (W (q + 1)) * (d.L.GGi * d.L.ζb)) := by
      rw [← (((c11 _ mζ).mul_right (c11 _ mGi)).mul_right c11m).eq,
        (Commute.mul_left (hf (q + 1) _ mζ) (hf (q + 1) _ mGi)).eq, cζG.eq]
    have hY : star (Y : ℂ) = Y := Complex.conj_ofReal Y
    have q10 : d.QQ Y 1 0 = Q.mkP (X.t Y 1 0) (X.t Y 0 1) := by
      rw [← hQ]
      change Q.mkP (X.t Y 1 0) (X.t (star (Y : ℂ)) 0 1) = _
      rw [hY]
    have q11 : d.QQ Y 1 1 = Q.mkP (X.t Y 1 1) (X.t Y 1 1) := by
      rw [← hQ]
      change Q.mkP (X.t Y 1 1) (X.t (star (Y : ℂ)) 1 1) = _
      rw [hY]
    rw [q11, h9, h12] at key
    rw [q10, q11, h9, h12]
    simp only [mkPair_mul_mkPair, mkPair_sub_mkPair] at key ⊢
    refine mkPair_congr (hT q Y).1 ?_
    rw [snd_eq_of_mkPair_eq key, (hT q Y).2.2]
    abel

end GlobalTheory.HatNF.MulRelActual
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.radialMultipliers_satisfy_normalForm_relations : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → MulRel d.L (fun q => Q.mkP (W q) (W q)) := by
  atlas_forward_decl GlobalTheory.HatNF.MulRelActual.mulRel_actual
end

section
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

open MeasureTheory in
private theorem exists_hat_mul_m_eq_double_sum {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
    (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r) (h : A) (Z : ℂ → A) (Xc : ℕ → A)
    (hZ : ∀ s : ℂ, Z s = ∑ j ∈ Finset.range (r + 2), s ^ j • Xc j)
    (hrule : ∀ m : ℕ → A, _root_.GlobalTheory.HatNF.MulRel L m → ∀ q,
      h * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xc j)
    (hmem : ∀ s, Z s ∈ _root_.GlobalTheory.HatNF.hats L) :
    ∃ (d : Fin (r + 2) → Fin (r + 2) → ℂ) (g : Fin (r + 2) → A),
      (∀ i, g i ∈ _root_.GlobalTheory.HatNF.hats L) ∧ ∀ m : ℕ → A, _root_.GlobalTheory.HatNF.MulRel L m → ∀ q,
        h * m q = ∑ j : Fin (r + 2), ∑ i : Fin (r + 2), d j i • (m (q + j) * g i) := by
  have hν : Function.Injective (fun i : Fin (r + 2) => ((i : ℕ) : ℂ)) :=
    fun i j hij => Fin.ext (by simpa using hij)
  have hspan := (_root_.GlobalTheory.vecPoly_mem_span_values A (r + 2) Z Xc _ hν hZ).1
  have hcoef : ∀ j : Fin (r + 2), ∃ c : Fin (r + 2) → ℂ,
      ∑ i, c i • Z ((i : ℕ) : ℂ) = Xc j :=
    fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hspan j j.2)
  choose d hd using hcoef
  refine ⟨d, fun i => Z ((i : ℕ) : ℂ), fun i => hmem _, fun m hm q => ?_⟩
  rw [hrule m hm q, Finset.sum_range (fun j => m (q + j) * Xc j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hd j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm]

open MeasureTheory in
private theorem exists_hat_mul_multiplier_expansion {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
    (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r) {h : A} (hh : h ∈ _root_.GlobalTheory.HatNF.hats L) :
    ∃ (d : Fin (r + 2) → Fin (r + 2) → ℂ) (g : Fin (r + 2) → A),
      (∀ i, g i ∈ _root_.GlobalTheory.HatNF.hats L) ∧ ∀ m : ℕ → A, _root_.GlobalTheory.HatNF.MulRel L m → ∀ q,
        h * m q = ∑ j : Fin (r + 2), ∑ i : Fin (r + 2), d j i • (m (q + j) * g i) := by
  unfold _root_.GlobalTheory.HatNF.hats at hh
  rcases hh with ((⟨Y, rfl⟩ | ⟨Y, rfl⟩) | ⟨Y, rfl⟩) | ⟨Y, rfl⟩
  · obtain ⟨Xa, Xr, hXa, hXr, hrel⟩ := _root_.GlobalTheory.HatTaylorPlus.taylor_plus A r L Y
    exact exists_hat_mul_m_eq_double_sum L _ (fun s => L.Ahat (Y + s)) Xa hXa
      (fun m hm q => (hrel m hm q).1)
      (fun s => by unfold _root_.GlobalTheory.HatNF.hats; exact Or.inl (Or.inl (Or.inl ⟨_, rfl⟩)))
  · obtain ⟨Xa, Xr, hXa, hXr, hrel⟩ := _root_.GlobalTheory.HatTaylorPlus.taylor_plus A r L Y
    exact exists_hat_mul_m_eq_double_sum L _ (fun s => L.R0 (Y + s)) Xr hXr
      (fun m hm q => (hrel m hm q).2)
      (fun s => by unfold _root_.GlobalTheory.HatNF.hats; exact Or.inl (Or.inl (Or.inr ⟨_, rfl⟩)))
  · obtain ⟨Xa, Xr, hXa, hXr, hrel⟩ := _root_.GlobalTheory.HatNF.TaylorMinus.taylor_minus A r L Y
    exact exists_hat_mul_m_eq_double_sum L _ (fun s => L.Ahatv (Y - s)) Xa hXa
      (fun m hm q => (hrel m hm q).1)
      (fun s => by unfold _root_.GlobalTheory.HatNF.hats; exact Or.inl (Or.inr ⟨_, rfl⟩))
  · obtain ⟨Xa, Xr, hXa, hXr, hrel⟩ := _root_.GlobalTheory.HatNF.TaylorMinus.taylor_minus A r L Y
    exact exists_hat_mul_m_eq_double_sum L _ (fun s => L.R0v (Y - s)) Xr hXr
      (fun m hm q => (hrel m hm q).2)
      (fun s => by unfold _root_.GlobalTheory.HatNF.hats; exact Or.inr ⟨_, rfl⟩)

open MeasureTheory in
private theorem exists_hatWord_mul_multiplier_expansion {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
    (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r) (H : List A) (hH : ∀ h ∈ H, h ∈ _root_.GlobalTheory.HatNF.hats L) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℕ) (c : ι → ℂ) (P : ι → List A),
      (∀ i, a i ≤ H.length * (r + 1) ∧ (P i).length = H.length ∧
        ∀ h ∈ P i, h ∈ _root_.GlobalTheory.HatNF.hats L) ∧
      ∀ m : ℕ → A, _root_.GlobalTheory.HatNF.MulRel L m → ∀ q,
        H.prod * m q = ∑ i, c i • (m (q + a i) * (P i).prod) := by
  induction H with
  | nil =>
    exact ⟨Unit, inferInstance, fun _ => 0, fun _ => 1, fun _ => [],
      fun _ => ⟨by simp, rfl, by simp⟩, fun m _ q => by simp⟩
  | cons h H ih =>
    obtain ⟨ι, _, a, c, P, hP, hrep⟩ := ih fun x hx => hH x (List.mem_cons_of_mem _ hx)
    obtain ⟨d, g, hg, hrel⟩ := exists_hat_mul_multiplier_expansion L (hH h List.mem_cons_self)
    refine ⟨ι × Fin (r + 2) × Fin (r + 2), inferInstance, fun x => a x.1 + x.2.1,
      fun x => c x.1 * d x.2.1 x.2.2, fun x => g x.2.2 :: P x.1, fun x => ⟨?_, ?_, ?_⟩,
      fun m hm q => ?_⟩
    · have h1 := (hP x.1).1
      have h2 : (x.2.1 : ℕ) ≤ r + 1 := Nat.lt_succ_iff.mp x.2.1.isLt
      rw [List.length_cons, Nat.succ_mul]
      linarith
    · simp [(hP x.1).2.1]
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hg _
      · exact (hP x.1).2.2 y hy
    · rw [List.prod_cons, mul_assoc, hrep m hm q, Finset.mul_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type, mul_smul_comm, ← mul_assoc, hrel m hm (q + a i), Finset.sum_mul,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [List.prod_cons, smul_mul_assoc, smul_smul, add_assoc, mul_assoc]

open MeasureTheory in

theorem _root_.GlobalTheory.HatNF.prod_hats_mul_multiplier : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r), ∀ H : List A, (∀ h ∈ H, h ∈ _root_.GlobalTheory.HatNF.hats L) → ∃ ts : List (ℕ × ℂ × List A), (∀ t ∈ ts, t.1 ≤ H.length * (r + 1) ∧ t.2.2.length = H.length ∧ ∀ h ∈ t.2.2, h ∈ _root_.GlobalTheory.HatNF.hats L) ∧ ∀ m : ℕ → A, _root_.GlobalTheory.HatNF.MulRel L m → ∀ q, H.prod * m q = (ts.map fun t => t.2.1 • (m (q + t.1) * t.2.2.prod)).sum := by
  intro A _ _ r L H hH
  obtain ⟨ι, _, a, c, P, hP, hrep⟩ := exists_hatWord_mul_multiplier_expansion L H hH
  refine ⟨(Finset.univ : Finset ι).toList.map fun i => (a i, c i, P i), ?_, fun m hm q => ?_⟩
  · intro t ht
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht
    exact hP i
  · rw [hrep m hm q, List.map_map, Finset.sum_map_toList]
    rfl

end GlobalTheory.HatNF
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hatLetters_prod_mul_multiplier_leibniz : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ H : List A, (∀ h ∈ H, h ∈ hats L) → ∃ ts : List (ℕ × ℂ × List A), (∀ t ∈ ts, t.1 ≤ H.length * (r + 1) ∧ t.2.2.length = H.length ∧ ∀ h ∈ t.2.2, h ∈ hats L) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, H.prod * m q = (ts.map fun t => t.2.1 • (m (q + t.1) * t.2.2.prod)).sum := by
  atlas_forward_decl GlobalTheory.HatNF.prod_hats_mul_multiplier
end

section
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.RadBound

section abstract

variable {ι α : Type}

def Bd (p : ι → Prop) (ok : α → Prop) (val : α → ι → ℝ) (wt f : ι → ℝ) : Prop :=
  ∃ (C : ℝ) (Ts : List α), 0 ≤ C ∧ (∀ H ∈ Ts, ok H) ∧
    ∀ i, p i → f i ≤ C * wt i * (Ts.map fun H => val H i).sum

variable {p : ι → Prop} {ok : α → Prop} {val : α → ι → ℝ}

theorem sum_val_nonneg (hv : ∀ H i, 0 ≤ val H i) (Ts : List α) (i : ι) :
    0 ≤ (Ts.map fun H => val H i).sum :=
  List.sum_nonneg (by
    intro y hy
    obtain ⟨H, -, rfl⟩ := List.mem_map.1 hy
    exact hv H i)

theorem Bd.zero {wt : ι → ℝ} : Bd p ok val wt (fun _ => 0) :=
  ⟨0, [], le_rfl, by simp, by simp⟩

theorem Bd.add (hv : ∀ H i, 0 ≤ val H i) {wt f g : ι → ℝ} (hw : ∀ i, p i → 0 ≤ wt i)
    (hf : Bd p ok val wt f) (hg : Bd p ok val wt g) : Bd p ok val wt (fun i => f i + g i) := by
  obtain ⟨C, Ts, hC, hT, h⟩ := hf
  obtain ⟨C', Ts', hC', hT', h'⟩ := hg
  refine ⟨C + C', Ts ++ Ts', add_nonneg hC hC', ?_, fun i hi => ?_⟩
  · intro H hH
    rcases List.mem_append.1 hH with h1 | h1
    · exact hT H h1
    · exact hT' H h1
  · rw [List.map_append, List.sum_append]
    have h1 := h i hi
    have h2 := h' i hi
    have s1 := sum_val_nonneg hv Ts i
    have s2 := sum_val_nonneg hv Ts' i
    have w := hw i hi
    have e1 := mul_nonneg (mul_nonneg hC w) s2
    have e2 := mul_nonneg (mul_nonneg hC' w) s1
    nlinarith

theorem Bd.mono {wt wt' f g u : ι → ℝ} {K : ℝ} (hK : 0 ≤ K) (hu : ∀ i, p i → 0 ≤ u i)
    (hg : Bd p ok val wt g) (hfg : ∀ i, p i → f i ≤ K * u i * g i) (hw : ∀ i, p i → wt' i = u i * wt i) :
    Bd p ok val wt' f := by
  obtain ⟨C, Ts, hC, hT, h⟩ := hg
  refine ⟨K * C, Ts, mul_nonneg hK hC, hT, fun i hi => (hfg i hi).trans ?_⟩
  have := mul_le_mul_of_nonneg_left (h i hi) (mul_nonneg hK (hu i hi))
  rw [hw i hi]
  refine this.trans (le_of_eq ?_)
  ring

theorem Bd.listSum {β : Type} (hv : ∀ H i, 0 ≤ val H i) {wt : ι → ℝ} (hw : ∀ i, p i → 0 ≤ wt i)
    (g : β → ι → ℝ) (l : List β) (h : ∀ t ∈ l, Bd p ok val wt (g t)) :
    Bd p ok val wt (fun i => (l.map fun t => g t i).sum) := by
  induction l with
  | nil => simpa using Bd.zero
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Bd.add hv hw (h t (by simp)) (ih fun t' ht' => h t' (by simp [ht']))

end abstract

section actual

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem nv_nonneg (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) :
    0 ≤ nv Φ x := norm_nonneg _

theorem nv_add (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) :
    nv (Φ + Ψ) x ≤ nv Φ x + nv Ψ x := by
  have h : ∀ A A' : Wq →L[ℂ] Wp, B.hsVec (A + A') = B.hsVec A + B.hsVec A' := fun _ _ => rfl
  unfold nv
  rw [Submodule.coe_add, Pi.add_apply, Pi.add_apply, h]
  exact norm_add_le _ _

theorem nv_smul (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) :
    nv (c • Φ) x = ‖c‖ * nv Φ x := by
  have h : ∀ (c : ℂ) (A : Wq →L[ℂ] Wp), B.hsVec (c • A) = c • B.hsVec A := fun _ _ => rfl
  unfold nv
  rw [Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, h, norm_smul]

theorem nv_zero (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) :
    nv (0 : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') x = 0 := by
  have := nv_smul (0 : ℂ) (0 : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') x
  simpa using this

theorem nv_mulOp {W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
    {m : (Fin P.r → ℂ) → Q.Mx P.k P.r → ℂ} (hW : P5.multiplicationOperator W m)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) :
    nv (W Φ) x = ‖m x.1 x.2‖ * nv Φ x := by
  have h : ∀ (c : ℂ) (A : Wq →L[ℂ] Wp), B.hsVec (c • A) = c • B.hsVec A := fun _ _ => rfl
  unfold nv
  rw [hW, h, norm_smul]

theorem fst_mul (a b : RA P Bs) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    (a * b).1 Φ = a.1 (b.1 Φ) := rfl

theorem fst_add (a b : RA P Bs) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    (a + b).1 Φ = a.1 Φ + b.1 Φ := rfl

theorem fst_zero (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : (0 : RA P Bs).1 Φ = 0 := rfl

theorem fst_one (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : (1 : RA P Bs).1 Φ = Φ := rfl

theorem fst_smul (c : ℂ) (a : RA P Bs) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    (c • a).1 Φ = c • a.1 Φ := rfl

theorem nv_pow {y : RA P Bs} {x : (Fin P.r → ℂ) × Q.Mx P.k P.r} {t : ℝ}
    (h : ∀ Φ, nv (y.1 Φ) x = t * nv Φ x) (n : ℕ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    nv ((y ^ n).1 Φ) x = t ^ n * nv Φ x := by
  induction n with
  | zero => rw [pow_zero, pow_zero, fst_one, one_mul]
  | succ n ih => rw [pow_succ', fst_mul, h, ih, pow_succ']; ring

theorem nv_listSum {β : Type} (g : β → RA P Bs) (l : List β) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) :
    nv ((l.map g).sum.1 Φ) x ≤ (l.map fun t => nv ((g t).1 Φ) x).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, fst_zero, nv_zero, le_refl]
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons, fst_add]
    exact (nv_add _ _ _).trans (by linarith)

theorem span_bd {X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π'} {μ : Measure (Mt P.k P.r)}
    {L : LevelData (RA P Bs) P.r} {st : Start (RA P Bs)} {l0 : ℕ} {d : Q.NFData P (RA P Bs)}
    (hD : P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0) (hN : IsNF X d) (T : Set (RA P Bs)) (i j n : ℕ)
    (y : RA P Bs) (hy : y ∈ nfSpan d T i j n) :
    Bd (fun q : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' × ((Fin P.r → ℂ) × Q.Mx P.k P.r) =>
        q.2 ∈ Q.DomR P.k P.r Bs.z Bs.z')
      (fun H : List (RA P Bs) => H.length = n ∧ ∀ h ∈ H, h ∈ T) (fun H q => nv (H.prod.1 q.1) q.2)
      (fun q => (dR P Bs q.2.1 q.2.2)⁻¹ ^ i * (gR P Bs q.2.1 q.2.2)⁻¹ ^ j) (fun q => nv (y.1 q.1) q.2) := by
  have hb := (GlobalTheory.T.pointwise_bounded_radial_ops_closure_and_functions Wp Wq P Bs X μ L st l0 d hD hN).2.2.2.2.2.2.2
  have hw : ∀ q : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' × ((Fin P.r → ℂ) × Q.Mx P.k P.r),
      q.2 ∈ Q.DomR P.k P.r Bs.z Bs.z' →
      0 ≤ (dR P Bs q.2.1 q.2.2)⁻¹ ^ i * (gR P Bs q.2.1 q.2.2)⁻¹ ^ j := by
    intro q hq
    have h1 := (hb q.1 q.2 hq).1
    have h2 := (hb q.1 q.2 hq).2.1
    positivity
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hbm, H, hl, hH, rfl⟩ := hy
    obtain ⟨C, hC, hCb⟩ := GlobalTheory.T.pointwiseBounded_of_mem_boundedFactors_monoid Wp Wq P Bs X μ L st l0 d hD hN b hbm
    refine ⟨C, [H], hC, by simpa using ⟨hl, hH⟩, fun q hq => ?_⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, fst_mul]
    refine (hCb _ _ hq).trans (le_of_eq ?_)
    rw [nv_pow (fun Φ => (hb Φ q.2 hq).2.2.1), nv_pow (fun Φ => (hb Φ q.2 hq).2.2.2)]
    ring
  | zero => simpa only [fst_zero, nv_zero] using Bd.zero
  | add y z _ _ hy hz =>
    refine Bd.mono (K := 1) (u := fun _ => 1) zero_le_one (fun _ _ => zero_le_one)
      (Bd.add (fun _ _ => nv_nonneg _ _) hw hy hz) (fun q _ => ?_) (fun _ _ => (one_mul _).symm)
    rw [fst_add, one_mul, one_mul]
    exact nv_add _ _ _
  | smul c y _ hy =>
    refine Bd.mono (K := ‖c‖) (u := fun _ => 1) (norm_nonneg _) (fun _ _ => zero_le_one)
      hy (fun q _ => ?_) (fun _ _ => (one_mul _).symm)
    rw [fst_smul, nv_smul, mul_one]

end actual

theorem word_bound : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ (T : Set (RA P Bs)) (a : ℕ), (∀ x ∈ basics d, x ∈ nfSpan d T 0 a 1) → ∀ w : List (Letter ℂ S), admitted st w → ∃ (C : ℝ) (J : ℕ) (Ts : List (List (RA P Bs))), 0 ≤ C ∧ (∀ H ∈ Ts, H.length = w.length ∧ ∀ h ∈ H, h ∈ T) ∧ ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (e : Ix S), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', nv ((((ofWord L st w).F * TL.bTA L w) e e1).1 (W 0 Φ)) x ≤ C * ((dR P Bs x.1 x.2)⁻¹ ^ w.length * (gR P Bs x.1 x.2)⁻¹ ^ (a * w.length)) * (∑ j ∈ Finset.range (J + 1), |LE.ld j φ (gR P Bs x.1 x.2)|) * (Ts.map fun H => nv (H.prod.1 Φ) x).sum := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN S _ _ T a hT w hw
  obtain ⟨hH, hTie⟩ := GlobalTheory.T.normalForm_actualOperators_algebraicHypotheses Wp Wq P Bs X μ L st l0 d hD hN
  have hb := (GlobalTheory.T.pointwise_bounded_radial_ops_closure_and_functions Wp Wq P Bs X μ L st l0 d hD hN).2.2.2.2.2.2.2
  have hhat := GlobalTheory.T.hatLetters_mem_normalFormProductSpan P _ d hH T a hT
  set N := w.length with hNdef
  let ι : Type := (ℝ → ℝ) × (ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) ×
    Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' × ((Fin P.r → ℂ) × Q.Mx P.k P.r)
  let p : ι → Prop := fun q => LE.SmoothLog q.1 ∧ IsMulG P Bs q.1 q.2.1 ∧ q.2.2.2 ∈ Q.DomR P.k P.r Bs.z Bs.z'
  let ok : List (RA P Bs) → Prop := fun H => H.length = N ∧ ∀ h ∈ H, h ∈ T
  let val : List (RA P Bs) → ι → ℝ := fun H q => nv (H.prod.1 q.2.2.1) q.2.2.2
  let G : ι → ℝ := fun q => (gR P Bs q.2.2.2.1 q.2.2.2.2)⁻¹ ^ (a * N)
  let Dd : ι → ℝ := fun q => (dR P Bs q.2.2.2.1 q.2.2.2.2)⁻¹ ^ N
  let Sg : ι → ℝ := fun q => ∑ j ∈ Finset.range (N * (P.r + 1) + 1), |LE.ld j q.1 (gR P Bs q.2.2.2.1 q.2.2.2.2)|
  have hv : ∀ H q, 0 ≤ val H q := fun _ _ => nv_nonneg _ _
  have hG : ∀ q, p q → 0 ≤ G q := fun q hq => by
    have h2 := (hb q.2.2.1 q.2.2.2 hq.2.2).2.1
    positivity
  have hDd : ∀ q, p q → 0 ≤ Dd q := fun q hq => by
    have h2 := (hb q.2.2.1 q.2.2.2 hq.2.2).1
    positivity
  have hS : ∀ q, p q → 0 ≤ Sg q := fun q _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h1 : ∀ H : List (RA P Bs), H.length = N → (∀ h ∈ H, h ∈ hats d.L) →
      Bd p ok val G (fun q => nv (H.prod.1 q.2.2.1) q.2.2.2) := by
    intro H hl hh
    have hm := GlobalTheory.T.list_prod_hatLetters_mem_normalFormProductSpan P _ d hH T a hhat H hh
    rw [hl] at hm
    obtain ⟨C, Ts, hC, hTs, h⟩ := span_bd hD hN T 0 (a * N) N _ hm
    refine ⟨C, Ts, hC, hTs, fun q hq => ?_⟩
    have := h q.2.2 hq.2.2
    simpa only [pow_zero, one_mul] using this
  have h2 : ∀ H : List (RA P Bs), H.length = N → (∀ h ∈ H, h ∈ hats d.L) →
      Bd p ok val (fun q => Sg q * G q) (fun q => nv (H.prod.1 (q.2.1 0 q.2.2.1)) q.2.2.2) := by
    intro H hl hh
    obtain ⟨ts, hts, hmul⟩ := GlobalTheory.T.hatLetters_prod_mul_multiplier_leibniz _ P.r d.L H hh
    have h3 : ∀ t ∈ ts, Bd p ok val (fun q => Sg q * G q)
        (fun q => nv ((t.2.1 • (Q.mkP (q.2.1 (0 + t.1)) (q.2.1 (0 + t.1)) * t.2.2.prod : RA P Bs)).1 q.2.2.1)
          q.2.2.2) := by
      intro t ht
      obtain ⟨hj, hl', hh'⟩ := hts t ht
      refine Bd.mono (K := ‖t.2.1‖) (u := Sg) (norm_nonneg _) hS (h1 t.2.2 (hl'.trans hl) hh')
        (fun q hq => ?_) (fun _ _ => rfl)
      rw [fst_smul, nv_smul, fst_mul, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      change nv (q.2.1 (0 + t.1) _) _ ≤ _
      rw [nv_mulOp (hq.2.1 _), Complex.norm_real, Real.norm_eq_abs, zero_add]
      refine mul_le_mul_of_nonneg_right ?_ (nv_nonneg _ _)
      refine Finset.single_le_sum (f := fun j => |LE.ld j q.1 (gR P Bs q.2.2.2.1 q.2.2.2.2)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_range.2 ?_)
      rw [hl] at hj
      omega
    refine Bd.mono (K := 1) (u := fun _ => 1) zero_le_one (fun _ _ => zero_le_one)
      (Bd.listSum hv (fun q hq => mul_nonneg (hS q hq) (hG q hq)) _ ts h3) (fun q hq => ?_)
      (fun _ _ => (one_mul _).symm)
    have hr := hmul _ (GlobalTheory.T.radialMultipliers_satisfy_normalForm_relations Wp Wq P Bs X μ L st l0 d hD hN q.1 q.2.1 hq.1 hq.2.1) 0
    rw [one_mul, one_mul]
    have e : H.prod.1 (q.2.1 0 q.2.2.1) = (H.prod * (Q.mkP (q.2.1 0) (q.2.1 0) : RA P Bs)).1 q.2.2.1 := rfl
    rw [e, hr]
    exact nv_listSum _ _ _ _
  have h4 : ∀ e : Ix S, Bd p ok val (fun q => Dd q * (Sg q * G q))
      (fun q => nv ((((ofWord L st w).F * TL.bTA L w) e e1).1 (q.2.1 0 q.2.2.1)) q.2.2.2) := by
    intro e
    obtain ⟨C, Hs, hC, hHs, h⟩ := span_bd hD hN _ _ _ _ _ (GlobalTheory.T.wordOperator_column_mem_normalFormProductSpan P _ d hH L st _ hTie S w hw e)
    refine Bd.mono (K := C) (u := Dd) hC hDd
      (Bd.listSum hv (fun q hq => mul_nonneg (hS q hq) (hG q hq)) _ Hs
        (fun H hH' => h2 H (hHs H hH').1 (hHs H hH').2)) (fun q hq => ?_) (fun _ _ => rfl)
    have := h (q.2.1 0 q.2.2.1, q.2.2.2) hq.2.2
    simpa only [pow_zero, mul_one] using this
  obtain ⟨C, Ts, hC, hTs, h⟩ := Bd.listSum hv (fun q hq => mul_nonneg (hDd q hq) (mul_nonneg (hS q hq) (hG q hq)))
    _ (Finset.univ : Finset (Ix S)).toList (fun e _ => h4 e)
  refine ⟨C, N * (P.r + 1), Ts, hC, hTs, fun φ W hφ hW Φ e x hx => ?_⟩
  have h5 := h (φ, W, Φ, x) ⟨hφ, hW, hx⟩
  beta_reduce at h5
  rw [Finset.sum_map_toList] at h5
  refine (Finset.single_le_sum (f := fun e : Ix S => nv ((((ofWord L st w).F * TL.bTA L w) e e1).1 (W 0 Φ)) x)
    (fun _ _ => nv_nonneg _ _) (Finset.mem_univ e)).trans (h5.trans (le_of_eq ?_))
  simp only [Dd, Sg, G, val]
  ring

end GlobalTheory.HatNF.RadBound
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wordOperator_radial_pointwise_bound : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ (T : Set (RA P Bs)) (a : ℕ), (∀ x ∈ basics d, x ∈ nfSpan d T 0 a 1) → ∀ w : List (Letter ℂ S), admitted st w → ∃ (C : ℝ) (J : ℕ) (Ts : List (List (RA P Bs))), 0 ≤ C ∧ (∀ H ∈ Ts, H.length = w.length ∧ ∀ h ∈ H, h ∈ T) ∧ ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (e : Ix S), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', nv ((((ofWord L st w).F * TL.bTA L w) e e1).1 (W 0 Φ)) x ≤ C * ((dR P Bs x.1 x.2)⁻¹ ^ w.length * (gR P Bs x.1 x.2)⁻¹ ^ (a * w.length)) * (∑ j ∈ Finset.range (J + 1), |LE.ld j φ (gR P Bs x.1 x.2)|) * (Ts.map fun H => nv (H.prod.1 Φ) x).sum := by
  atlas_forward_decl GlobalTheory.HatNF.RadBound.word_bound
end
