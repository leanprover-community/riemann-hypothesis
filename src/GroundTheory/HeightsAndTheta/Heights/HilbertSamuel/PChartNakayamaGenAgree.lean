module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDefs
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKoszulCechComplex
import Mathlib.Tactic.TypeStar
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GeneratedModOfSubsingleton
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace ChartNakayamaGen

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

def chart (c : ∀ k, ι k) : KH.Cell K ι 0 :=
  ⟨fun k => {c k}, fun k => Finset.singleton_nonempty _, by simp⟩

theorem eq_chart (J : KH.Cell K ι 0) : J = chart (fun k => (J.2.1 k).choose) := by
  apply Subtype.ext
  funext k
  have h0 : (J.1 k).card - 1 = 0 := (Finset.sum_eq_zero_iff.mp J.2.2) k (Finset.mem_univ k)
  have h1 : (J.1 k).card = 1 := by have := Finset.card_pos.mpr (J.2.1 k); omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
  have hc : (J.2.1 k).choose ∈ J.1 k := (J.2.1 k).choose_spec
  show J.1 k = {(J.2.1 k).choose}
  generalize (J.2.1 k).choose = x at hc ⊢
  rw [ha, Finset.mem_singleton] at hc
  rw [ha, hc]

def chartMon (c : ∀ k, ι k) (e : K → ℕ) : MRingOver S ι :=
  ∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ e k

theorem chartMon_add (c : ∀ k, ι k) (e f : K → ℕ) :
    chartMon (S := S) c (e + f) = chartMon c e * chartMon c f := by
  simp only [chartMon, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem chartMon_zero (c : ∀ k, ι k) : chartMon (S := S) c 0 = 1 := by
  simp [chartMon]

theorem chartMon_mem (c : ∀ k, ι k) (e : K → ℕ) : chartMon (S := S) c e ∈ KH.cellMon S (chart c).1 :=
  Submonoid.prod_mem _ fun k _ =>
    Submonoid.pow_mem _ (by
      apply Submonoid.subset_closure
      exact ⟨k, c k, Finset.mem_singleton_self _, rfl⟩) _

theorem isMultiHomog_pow {p : MRingOver S ι} {a : K → ℕ} (hp : IsMultiHomog p a) (n : ℕ) :
    IsMultiHomog (p ^ n) (n • a) :=
  GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_pow hp n

theorem isMultiHomog_prod {β : Type} (s : Finset β) (f : β → MRingOver S ι) (a : β → K → ℕ)
    (h : ∀ i ∈ s, IsMultiHomog (f i) (a i)) : IsMultiHomog (∏ i ∈ s, f i) (∑ i ∈ s, a i) :=
  GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_prod s f a h

theorem isMultiHomog_chartMon (c : ∀ k, ι k) (e : K → ℕ) : IsMultiHomog (chartMon (S := S) c e) e :=
  GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_chartMono c e

theorem exists_chartMon {c : ∀ k, ι k} {v : MRingOver S ι} (hv : v ∈ KH.cellMon S (chart c).1) :
    ∃ e, v = chartMon c e := by
  classical
  induction hv using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    have hik : i = c k := Finset.mem_singleton.mp hi
    subst hik
    refine ⟨Pi.single k 1, ?_⟩
    rw [chartMon, Finset.prod_eq_single k]
    · simp
    · intro l _ hl
      simp [hl]
    · intro h
      exact absurd (Finset.mem_univ k) h
  | one => exact ⟨0, (chartMon_zero c).symm⟩
  | mul f g _ _ hf hg =>
    obtain ⟨e, rfl⟩ := hf
    obtain ⟨e', rfl⟩ := hg
    exact ⟨e + e', (chartMon_add c e e').symm⟩

theorem cellMon_notMem {P : Ideal (MRingOver S ι)} (hP : P.IsPrime) {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨k, c k⟩ : MRingOver S ι) ∉ P) {v : MRingOver S ι}
    (hv : v ∈ KH.cellMon S (chart c).1) : v ∉ P := by
  induction hv using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    have hik : i = c k := Finset.mem_singleton.mp hi
    subst hik
    exact hc k
  | one => exact fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  | mul f g _ _ hf hg => exact fun h => (hP.mem_or_mem h).elim hf hg

theorem dvd_of_mem_pair {c c' : ∀ k, ι k} {v : MRingOver S ι}
    (hv : v ∈ KH.cellMon S (fun k => ({c k, c' k} : Finset (ι k)))) :
    ∃ e : ℕ, v ∣ chartMon c (fun _ => e) * chartMon c' (fun _ => e) := by
  classical
  induction hv using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    refine ⟨1, ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have h : (X ⟨k, c k⟩ : MRingOver S ι) ∣ chartMon c (fun _ => 1) := by
        simpa [chartMon] using
          Finset.dvd_prod_of_mem (fun l => (X ⟨l, c l⟩ : MRingOver S ι)) (Finset.mem_univ k)
      exact h.mul_right _
    · rw [Finset.mem_singleton.mp hi]
      have h : (X ⟨k, c' k⟩ : MRingOver S ι) ∣ chartMon c' (fun _ => 1) := by
        simpa [chartMon] using
          Finset.dvd_prod_of_mem (fun l => (X ⟨l, c' l⟩ : MRingOver S ι)) (Finset.mem_univ k)
      exact h.mul_left _
  | one => exact ⟨0, one_dvd _⟩
  | mul f g _ _ hf hg =>
    obtain ⟨e, he⟩ := hf
    obtain ⟨e', he'⟩ := hg
    refine ⟨e + e', ?_⟩
    have h : chartMon (S := S) c (fun _ => e + e') * chartMon c' (fun _ => e + e') =
        (chartMon c (fun _ => e) * chartMon c' (fun _ => e)) *
          (chartMon c (fun _ => e') * chartMon c' (fun _ => e')) := by
      rw [show (fun _ : K => e + e') = (fun _ => e) + (fun _ => e') from rfl, chartMon_add, chartMon_add]
      ring
    rw [h]
    exact mul_dvd_mul he he'

def pairCell (c : ∀ k, ι k) (k : K) (j : ι k) (hj : j ≠ c k) : KH.Cell K ι 1 :=
  ⟨Function.update (fun l => ({c l} : Finset (ι l))) k {c k, j}, fun l => by
      by_cases hl : l = k
      · subst hl
        simp
      · simp [Function.update_of_ne hl], by
      rw [Finset.sum_eq_single k]
      · simp [Finset.card_pair hj.symm]
      · intro l _ hl
        simp [Function.update_of_ne hl]
      · simp⟩

theorem res_eq_of_pair {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] (c : ∀ k, ι k) (k : K)
    (j : ι k) (hj : j ≠ c k) (f : KH.CechC S ι M 0) (hf : KH.cechD S ι M 0 f = 0) :
    KH.cellRes S M (chart c).1 (pairCell c k j hj).1 (f (chart c)) =
      KH.cellRes S M (chart (Function.update c k j)).1 (pairCell c k j hj).1
        (f (chart (Function.update c k j))) :=
  KoszulCechComplex.res_agree hf (pairCell c k j hj).1 (chart c) (chart (Function.update c k j))
    (fun l => by by_cases hl : l = k; · subst hl; simp [chart, pairCell]
                 · simp [chart, pairCell, Function.update_of_ne hl])
    (fun l => by by_cases hl : l = k; · subst hl; simp [chart, pairCell]
                 · simp [chart, pairCell, Function.update_of_ne hl])
    k (fun l hl => by simp [chart, Function.update_of_ne hl])

theorem res_agree {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (z : KH.CechC S ι M 0)
    (hz : KH.cechD S ι M 0 z = 0) (c c' : ∀ k, ι k) (U : ∀ k, Finset (ι k)) (hc : ∀ k, c k ∈ U k)
    (hc' : ∀ k, c' k ∈ U k) :
    KH.cellRes S M (chart c).1 U (z (chart c)) = KH.cellRes S M (chart c').1 U (z (chart c')) := by
  classical
  suffices H : ∀ s : Finset K, ∀ c : ∀ k, ι k, (∀ k, c k ∈ U k) → (∀ l ∉ s, c l = c' l) →
      KH.cellRes S M (chart c).1 U (z (chart c)) = KH.cellRes S M (chart c').1 U (z (chart c')) from
    H Finset.univ c hc fun l hl => (hl (Finset.mem_univ l)).elim
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro c _ h
    have e : c = c' := funext fun l => h l (Finset.notMem_empty l)
    subst e
    rfl
  | insert k s _ ih =>
    intro c hcU h
    have hc₂U : ∀ l, Function.update c k (c' k) l ∈ U l := fun l => by
      by_cases hl : l = k
      · subst hl; simp [hc' l]
      · simp [Function.update_of_ne hl, hcU l]
    have hrest : ∀ l ∉ s, Function.update c k (c' k) l = c' l := fun l hl => by
      by_cases hlk : l = k
      · subst hlk; simp
      · rw [Function.update_of_ne hlk]; exact h l (by simp [hlk, hl])
    rw [← ih _ hc₂U hrest]
    exact KoszulCechComplex.res_agree hz U (chart c) (chart (Function.update c k (c' k)))
      (fun l => Finset.singleton_subset_iff.mpr (hcU l))
      (fun l => Finset.singleton_subset_iff.mpr (hc₂U l))
      k (fun l hl => by simp [chart, Function.update_of_ne hl])

end ChartNakayamaGen

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
