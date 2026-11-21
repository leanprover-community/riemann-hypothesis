import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxesCompactExhaust
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalTuplesDiscreteCocompactAdelic
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteInterClosedBallOfSeparated
import BuildAid.ForwardExisting
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaK

section
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic.Packing

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Λ : Type} [AddCommGroup Λ]

def Sep (e : Λ →+ V) (r R : ℝ) (s : Finset Λ) : Prop :=
  (∀ l ∈ s, ‖e l‖ ≤ R) ∧ (s : Set Λ).Pairwise fun a b => r ≤ ‖e a - e b‖

theorem Sep.card_le {e : Λ →+ V} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) {s : Finset Λ}
    (hs : Sep e r R s) : (s.card : ℝ) ≤ (3 * R / r) ^ Module.finrank ℝ V := by
  classical
  have hinj : Set.InjOn e (s : Set Λ) := by
    intro a ha b hb hab
    by_contra hne
    have : r ≤ ‖e a - e b‖ := hs.2 ha hb hne
    rw [hab, sub_self, norm_zero] at this
    linarith
  have hcard : (s.image e).card = s.card := Finset.card_image_of_injOn hinj
  have h1 := GlobalTheory.finset_card_le_of_separated (s.image e) hr (hr.le.trans hrR) (0 : V)
    (by
      intro a ha
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 ha
      simpa using hs.1 l hl)
    (by
      intro a ha b hb hab
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
      have hlm : l ≠ m := fun h => hab (by rw [h])
      rw [dist_eq_norm]
      exact hs.2 hl hm hlm)
  rw [hcard] at h1
  exact h1.trans (GlobalTheory.one_add_two_mul_div_pow_le hr hrR _)

theorem exists_max_sep (e : Λ →+ V) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ∃ s : Finset Λ, Sep e r R s ∧ ∀ t : Finset Λ, Sep e r R t → t.card ≤ s.card := by
  let S : Set ℕ := {n | ∃ s : Finset Λ, Sep e r R s ∧ s.card = n}
  have hne : S.Nonempty := ⟨0, ∅, ⟨by simp, by simp⟩, rfl⟩
  have hbd : BddAbove S := by
    refine ⟨⌊(3 * R / r) ^ Module.finrank ℝ V⌋₊, ?_⟩
    rintro n ⟨s, hs, rfl⟩
    exact Nat.le_floor (Sep.card_le hr hrR hs)
  obtain ⟨s, hs, hc⟩ := Nat.sSup_mem hne hbd
  exact ⟨s, hs, fun t ht => hc ▸ le_csSup hbd ⟨t, ht, rfl⟩⟩

theorem Sep.exists_near {e : Λ →+ V} {r R : ℝ} (hr : 0 < r) {s : Finset Λ}
    (hs : Sep e r R s) (hmax : ∀ t : Finset Λ, Sep e r R t → t.card ≤ s.card)
    {l : Λ} (hl : ‖e l‖ ≤ R) : ∃ t ∈ s, ‖e (l - t)‖ ≤ r := by
  classical
  by_contra hcon
  push_neg at hcon
  have hns : l ∉ s := fun h => by
    have := hcon l h
    simp only [sub_self, map_zero, norm_zero] at this
    linarith
  have hins : Sep e r R (insert l s) := by
    refine ⟨?_, ?_⟩
    · intro m hm
      rcases Finset.mem_insert.1 hm with rfl | hm
      · exact hl
      · exact hs.1 m hm
    · rw [Finset.coe_insert]
      refine Set.pairwise_insert.2 ⟨hs.2, ?_⟩
      intro b hb _
      have h := hcon b hb
      rw [map_sub] at h
      exact ⟨h.le, by rw [norm_sub_rev]; exact h.le⟩
  have := hmax _ hins
  rw [Finset.card_insert_of_notMem hns] at this
  omega

end GlobalTheory.CompanionTheory.Adelic.Packing

open GlobalTheory.CompanionTheory.Adelic.Packing in

theorem GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Type)
      [AddCommGroup Λ] (e : Λ →+ V) (r R : ℝ), 0 < r → r ≤ R →
      ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤
        ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V) *
          ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) l := by
  intro V _ _ _ Λ _ e r R hr hrR
  classical
  obtain ⟨s, hs, hmax⟩ := exists_max_sep e hr hrR
  set f : Λ → ℝ≥0∞ := Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) with hf
  have hpt : ∀ l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤
      ∑ t ∈ s, f (l - t) := by
    intro l
    by_cases hl : ‖e l‖ ≤ R
    · obtain ⟨t, ht, hlt⟩ := hs.exists_near hr hmax hl
      have h1 : f (l - t) = 1 := Set.indicator_of_mem (s := {l : Λ | ‖e l‖ ≤ r}) hlt _
      calc Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤ 1 :=
            Set.indicator_le_self' (fun _ _ => zero_le) l
        _ = f (l - t) := h1.symm
        _ ≤ ∑ t ∈ s, f (l - t) :=
            Finset.single_le_sum (f := fun t => f (l - t)) (fun _ _ => zero_le) ht
    · rw [Set.indicator_of_notMem (by simpa using hl)]
      exact zero_le
  have hshift : ∀ t : Λ, ∑' l : Λ, f (l - t) = ∑' l : Λ, f l := fun t =>
    (Equiv.subRight t).tsum_eq f
  have hcard : (s.card : ℝ≥0∞) ≤ ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V) := by
    have h3 : (s.card : ℝ) ≤ (5 * R / r) ^ Module.finrank ℝ V := by
      refine (Sep.card_le hr hrR hs).trans (pow_le_pow_left₀ (by have := hr.le.trans hrR; positivity) ?_ _)
      have := hr.le.trans hrR
      gcongr
      norm_num
    calc (s.card : ℝ≥0∞) = ENNReal.ofReal (s.card : ℝ) := (ENNReal.ofReal_natCast _).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h3
  calc ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l
      ≤ ∑' l : Λ, ∑ t ∈ s, f (l - t) := ENNReal.tsum_le_tsum hpt
    _ = ∑ t ∈ s, ∑' l : Λ, f (l - t) := by
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ = (s.card : ℝ≥0∞) * ∑' l : Λ, f l := by
        simp only [hshift, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by gcongr
end

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_ball_count_ratio_bound : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Type) [AddCommGroup Λ] (e : Λ →+ V) (r R : ℝ), 0 < r → r ≤ R → ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤ ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V) * ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) l := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Pack

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def intSub {d M : ℕ} (b : Module.Basis (Fin d) F E) {Λ : Type} [AddCommGroup Λ]
    (e : Λ →+ (Fin 1 → Fin M → AF F ⊗[F] E)) (N : ℕ) : AddSubgroup Λ where
  carrier := {l | ∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin (e l)) a i) ∈ latV b v}
  zero_mem' := by
    intro v a i k
    simp [projV, projFin]
  add_mem' := by
    intro x y hx hy v a i k
    have h := add_mem (hx v a i k) (hy v a i k)
    simpa [projV, projFin, mul_add, map_add] using h
  neg_mem' := by
    intro x hx v a i k
    have h := neg_mem (hx v a i k)
    simpa [projV, projFin, mul_neg, map_neg] using h

def coord (hF : IsTotallyReal F) {d M : ℕ} (b : Module.Basis (Fin d) F E) :
    (Fin 1 → Fin M → AF F ⊗[F] E) →+ PiLp 1 (fun _ : Fin 1 × Fin M × Fin d × InfinitePlace F => ℝ) :=
  AddMonoidHom.mk' (fun X => WithLp.toLp 1 fun p =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal p.2.2.2)
      ((Algebra.TensorProduct.basis (Ainf F) b).repr (projInf X p.1 p.2.1) p.2.2.1 p.2.2.2)) (by
    intro X Y
    ext p
    simp only [projInf, map_add, Pi.add_apply, Finsupp.coe_add, PiLp.add_apply]
    exact map_add _ _ _)

theorem norm_coord (hF : IsTotallyReal F) {d M : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin 1 → Fin M → AF F ⊗[F] E) : ‖coord hF b X‖ = sizeTup b (projInf X) := by
  rw [PiLp.norm_eq_of_L1]
  simp only [sizeTup, sizeInf, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun v _ => ?_
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal v)).norm_map_of_map_zero
    (map_zero _) _

theorem finrank_coord (hF : IsTotallyReal F) (d M : ℕ) :
    Module.finrank ℝ (PiLp 1 (fun _ : Fin 1 × Fin M × Fin d × InfinitePlace F => ℝ)) =
      d * Module.finrank ℚ F * M := by
  have h : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
    simp only [IsTotallyReal.nrComplexPlaces_eq_zero] at h1 h2
    omega
  rw [(WithLp.linearEquiv 1 ℝ _).finrank_eq, Module.finrank_fintype_fun_eq_card]
  simp only [Fintype.card_prod, Fintype.card_fin, h]
  ring

theorem box_packing : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ), ∀ (Λ : Type) [AddCommGroup Λ] (e : Λ →+ (Fin 1 → Fin M → AF F ⊗[F] E)) (N : ℕ) (r R : ℝ), 0 < r → r ≤ R → ∑' l : Λ, (Set.indicator (box b N R) (fun _ => (1 : ℝ≥0∞))) (e l) ≤ ENNReal.ofReal ((5 * R / r) ^ (2 * Module.finrank ℚ F * M)) * ∑' l : Λ, (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e l) := by
  intro F E _ _ _ _ _ σ hσ d b M Λ _ e N r R hr hrR
  obtain ⟨hF, -, h2, -⟩ := hσ
  have hd : d = 2 := by
    rw [← h2, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  have key := GlobalTheory.T.lattice_ball_count_ratio_bound (PiLp 1 (fun _ : Fin 1 × Fin M × Fin 2 × InfinitePlace F => ℝ)) (intSub b e N)
    ((coord hF b).comp (e.comp (intSub b e N).subtype)) r R hr hrR
  rw [finrank_coord hF 2 M] at key
  have conv : ∀ t : ℝ, ∑' l : Λ, (Set.indicator (box b N t) (fun _ => (1 : ℝ≥0∞))) (e l) =
      ∑' l : intSub b e N, Set.indicator {l : intSub b e N |
        ‖((coord hF b).comp (e.comp (intSub b e N).subtype)) l‖ ≤ t} (fun _ => (1 : ℝ≥0∞)) l := by
    intro t
    have h := tsum_subtype ((intSub b e N : AddSubgroup Λ) : Set Λ)
      (fun l => Set.indicator {l : Λ | sizeTup b (projInf (e l)) ≤ t} (fun _ => (1 : ℝ≥0∞)) l)
    refine Eq.trans ?_ (Eq.trans h.symm ?_)
    · refine tsum_congr fun l => ?_
      have hb : e l ∈ box b N t ↔ l ∈ ((intSub b e N : AddSubgroup Λ) : Set Λ) ∧
          l ∈ {l : Λ | sizeTup b (projInf (e l)) ≤ t} := Iff.rfl
      by_cases hm : e l ∈ box b N t
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hb.1 hm).1, Set.indicator_of_mem (hb.1 hm).2]
      · rw [Set.indicator_of_notMem hm]
        by_cases h1 : l ∈ ((intSub b e N : AddSubgroup Λ) : Set Λ)
        · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem fun h => hm (hb.2 ⟨h1, h⟩)]
        · rw [Set.indicator_of_notMem h1]
    · refine tsum_congr fun l => ?_
      simp [Set.indicator, norm_coord]
  rw [conv R, conv r]
  exact key

end GlobalTheory.CompanionTheory.SW.Pack
end
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_box_lattice_count_ratio : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ), ∀ (Λ : Type) [AddCommGroup Λ] (e : Λ →+ (Fin 1 → Fin M → AF F ⊗[F] E)) (N : ℕ) (r R : ℝ), 0 < r → r ≤ R → ∑' l : Λ, (Set.indicator (box b N R) (fun _ => (1 : ℝ≥0∞))) (e l) ≤ ENNReal.ofReal ((5 * R / r) ^ (2 * Module.finrank ℚ F * M)) * ∑' l : Λ, (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e l) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.Pack.box_packing
end

section
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LatCount

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def ratHom (M : ℕ) : (Fin 1 → Fin M → E) →+ (Fin 1 → Fin M → AF F ⊗[F] E) where
  toFun := ratTup (AF F)
  map_zero' := by
    funext a i
    simp [ratTup]
  map_add' X Y := by
    funext a i
    simp [ratTup]

lemma box_mono {d M n : ℕ} (b : Module.Basis (Fin d) F E) (N : ℕ) {r r' : ℝ} (h : r ≤ r') :
    (box b N r : Set (Fin n → Fin M → AF F ⊗[F] E)) ⊆ box b N r' :=
  fun _ hX => ⟨hX.1, hX.2.trans h⟩

lemma sizeInf_nonneg {d : ℕ} (b : Module.Basis (Fin d) F E) (y : Ainf F ⊗[F] E) : 0 ≤ sizeInf b y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma repr_projInf_ratTup {d M n : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → E)
    (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Ainf F) b).repr (projInf (ratTup (AF F) X) a i) k =
      algebraMap F (Ainf F) (b.repr (X a i) k) := by
  have : projInf (ratTup (AF F) X) a i = (1 : Ainf F) ⊗ₜ[F] X a i := by
    simp [projInf, ratTup, inclR]
  rw [this, Algebra.TensorProduct.basis_repr_tmul]
  simp

lemma sizeTup_ratTup_pos {d M n : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → E)
    (hX : X ≠ 0) : 0 < sizeTup b (projInf (ratTup (AF F) X)) := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hX
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  obtain ⟨k, hk⟩ : ∃ k, b.repr (X a i) k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hi (b.repr.map_eq_zero_iff.mp (Finsupp.ext h))
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  set Y := projInf (ratTup (AF F) X : Fin n → Fin M → AF F ⊗[F] E) with hY
  have h1 : 0 < ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k v‖ := by
    rw [hY, repr_projInf_ratTup, norm_pos_iff]
    change algebraMap F v.Completion (b.repr (X a i) k) ≠ 0
    exact (map_ne_zero _).mpr hk
  have h2 : ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k v‖ ≤ sizeInf b (Y a i) :=
    (Finset.single_le_sum
      (f := fun v => ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k v‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ v)).trans
    (Finset.single_le_sum
      (f := fun k => ∑ v, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k v‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k))
  have h3 : sizeInf b (Y a i) ≤ sizeTup b Y :=
    (Finset.single_le_sum (f := fun i => sizeInf b (Y a i))
      (fun _ _ => sizeInf_nonneg b _) (Finset.mem_univ i)).trans
    (Finset.single_le_sum (f := fun a => ∑ i, sizeInf b (Y a i))
      (fun _ _ => Finset.sum_nonneg fun _ _ => sizeInf_nonneg b _) (Finset.mem_univ a))
  linarith

end SlopeTestRemainingChoices

lemma exists_pos_lt {α : Type} {S : Set α} (hS : S.Finite) (f : α → ℝ) (hf : ∀ x ∈ S, 0 < f x) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ x ∈ S, r < f x :=
  _root_.Bl.FirstLemmaK.goal1 hS f hf

theorem count_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (M : ℕ) (Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E)), IsCompact Ω → ∃ x₀ C : ℝ, ∀ x : ℝ, ∑' X : {X : Fin 1 → Fin M → E // X ≠ 0}, (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) (((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • ratTup (AF F) X.1) ≤ if x < x₀ then 0 else ENNReal.ofReal (C * Real.exp (2 * Module.finrank ℚ F * M * x)) := by
  intro F E _ _ _ _ _ σ hCM τ hτ M Ω hΩ
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let b := Module.finBasis F E
  obtain ⟨hcpt, hexh, hflow⟩ := GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hCM _ b 1 M
  obtain ⟨-, hfin, -⟩ := GlobalTheory.T.rational_tuples_discrete_cocompact_adelic F E σ hCM 1 M
  obtain ⟨N, r, hN, hr, hsub⟩ := hexh Ω hΩ

  obtain ⟨r₀, h0, h1, hsmall⟩ := exists_pos_lt
    (((hfin _ (hcpt N 1 hN)).subset (Set.inter_subset_left
      (t := {X : Fin 1 → Fin M → E | X ≠ 0}))))
    (fun X => sizeTup b (projInf (ratTup (AF F) X)))
    (fun X hX => sizeTup_ratTup_pos b X hX.2)
  have hnone : ∀ X : Fin 1 → Fin M → E, X ≠ 0 → ratTup (AF F) X ∉ box b N r₀ := by
    intro X hX hmem
    have := hsmall X ⟨box_mono b N h1 hmem, hX⟩
    exact absurd hmem.2 (not_le.mpr this)
  have hscale : ∀ (x : ℝ) (Y : Fin 1 → Fin M → AF F ⊗[F] E),
      ((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • Y ∈ Ω →
        Y ∈ box b N (Real.exp x * r) := by
    intro x Y hY
    refine (hflow τ hτ N (Real.exp x * r) (-x) Y).mp ?_
    have : Real.exp (-x) * (Real.exp x * r) = r := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    rw [this]
    exact hsub hY
  refine ⟨Real.log (r₀ / r), (5 * r / r₀) ^ (2 * Module.finrank ℚ F * M), fun x => ?_⟩
  split_ifs with hx
  ·
    have hlt : Real.exp x * r < r₀ := by
      have := (Real.lt_log_iff_exp_lt (div_pos h0 hr)).mp hx
      exact (lt_div_iff₀ hr).mp this
    refine le_of_eq (ENNReal.tsum_eq_zero.mpr fun X => Set.indicator_of_notMem ?_ _)
    intro hmem
    exact hnone X.1 X.2 (box_mono b N hlt.le (hscale x _ hmem))
  · have hge : r₀ ≤ Real.exp x * r := by
      have := (Real.log_le_iff_le_exp (div_pos h0 hr)).mp (not_lt.mp hx)
      exact (div_le_iff₀ hr).mp this
    set e := ratHom (F := F) (E := E) M with he
    have hone : ∑' l : Fin 1 → Fin M → E,
        (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) (e l) ≤ 1 := by
      rw [tsum_eq_single 0]
      · exact Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => by simp)
      · intro X hX
        exact Set.indicator_of_notMem (hnone X hX) _
    have hpack := GlobalTheory.T.adelic_box_lattice_count_ratio F E σ hCM _ b M (Fin 1 → Fin M → E) e N r₀ (Real.exp x * r) h0 hge
    calc ∑' X : {X : Fin 1 → Fin M → E // X ≠ 0}, (Set.indicator Ω (fun _ => (1 : ℝ≥0∞)))
            (((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • ratTup (AF F) X.1)
        ≤ ∑' X : {X : Fin 1 → Fin M → E // X ≠ 0},
            (Set.indicator (box b N (Real.exp x * r)) (fun _ => (1 : ℝ≥0∞))) (e X.1) := by
          refine ENNReal.tsum_le_tsum fun X => ?_
          by_cases hm : ((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) •
              ratTup (AF F) X.1 ∈ Ω
          · have hm' : e X.1 ∈ box b N (Real.exp x * r) := hscale x _ hm
            rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm']
          · rw [Set.indicator_of_notMem hm]
            exact bot_le
      _ ≤ ∑' l : Fin 1 → Fin M → E,
            (Set.indicator (box b N (Real.exp x * r)) (fun _ => (1 : ℝ≥0∞))) (e l) :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
            (fun l => (Set.indicator (box b N (Real.exp x * r)) (fun _ => (1 : ℝ≥0∞))) (e l))
      _ ≤ ENNReal.ofReal ((5 * (Real.exp x * r) / r₀) ^ (2 * Module.finrank ℚ F * M)) * 1 :=
          hpack.trans (mul_le_mul_right hone _)
      _ = ENNReal.ofReal ((5 * r / r₀) ^ (2 * Module.finrank ℚ F * M) *
            Real.exp (2 * Module.finrank ℚ F * M * x)) := by
          rw [mul_one]
          congr 1
          have : (2 * (Module.finrank ℚ F : ℝ) * M * x) =
              ((2 * Module.finrank ℚ F * M : ℕ) : ℝ) * x := by push_cast; ring
          rw [this, Real.exp_nat_mul, ← mul_pow]
          congr 1
          ring

end GlobalTheory.CompanionTheory.SW.LatCount
end
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flow_lattice_count_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (M : ℕ) (Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E)), IsCompact Ω → ∃ x₀ C : ℝ, ∀ x : ℝ, ∑' X : {X : Fin 1 → Fin M → E // X ≠ 0}, (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) (((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • ratTup (AF F) X.1) ≤ if x < x₀ then 0 else ENNReal.ofReal (C * Real.exp (2 * Module.finrank ℚ F * M * x)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.LatCount.count_le
end
