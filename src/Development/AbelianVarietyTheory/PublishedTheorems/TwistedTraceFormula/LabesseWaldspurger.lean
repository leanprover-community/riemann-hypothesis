import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing

section
noncomputable section

open MeasureTheory Finset
open scoped InnerProductSpace ContDiff Classical

namespace GlobalTheory.Chamber

variable {k : ℕ}

abbrev A0 (k : ℕ) : Type := EuclideanSpace ℝ (Fin k)

abbrev SV (k : ℕ) : Type := Fin k → SignType

def vec (u : SV k) : A0 k := WithLp.toLp 2 fun i => (u i : ℝ)

def Below (u u' : SV k) : Prop := ∀ i, u i ≠ 0 → u' i = u i

def IsPar (P : Finset (SV k)) : Prop := 0 ∉ P ∧ ∀ u ∈ P, ∀ u' ∈ P, Below u u' ∨ Below u' u

def aP (P : Finset (SV k)) : Submodule ℝ (A0 k) := Submodule.span ℝ (vec '' (P : Set (SV k)))

def pr (P : Finset (SV k)) : A0 k →L[ℝ] A0 k := (aP P).starProjection

def IsLevi (𝔞 : Submodule ℝ (A0 k)) : Prop := ∃ P, IsPar P ∧ aP P = 𝔞

def aMQ (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) : Submodule ℝ (A0 k) := 𝔞 ⊓ (aP Q)ᗮ

def parF (𝔞 : Submodule ℝ (A0 k)) (R : Finset (SV k)) : Finset (Finset (SV k)) :=
  univ.filter fun Q => IsPar Q ∧ aP Q ≤ 𝔞 ∧ R ⊆ Q

def parP (𝔞 : Submodule ℝ (A0 k)) (R : Finset (SV k)) : Finset (Finset (SV k)) :=
  univ.filter fun P => IsPar P ∧ aP P = 𝔞 ∧ R ⊆ P

def between (P R : Finset (SV k)) : Finset (Finset (SV k)) := P.powerset.filter (R ⊆ ·)

def wt (Q : Finset (SV k)) (u : SV k) : A0 k := vec u - pr Q (vec u)

def rt (P : Finset (SV k)) (u : SV k) : A0 k := wt (P.erase u) u

def tau (P Q : Finset (SV k)) (H : A0 k) : ℝ := if ∀ u ∈ P \ Q, 0 < ⟪rt P u, H⟫_ℝ then 1 else 0

def tauHat (P Q : Finset (SV k)) (H : A0 k) : ℝ := if ∀ u ∈ P \ Q, 0 < ⟪wt Q u, H⟫_ℝ then 1 else 0

def gamP (P R : Finset (SV k)) (X H : A0 k) : ℝ :=
  ∑ S ∈ between P R, (-1) ^ (S \ R).card * tau P S H * tauHat S R (H - X)

def gamM (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) (X : Finset (SV k) → A0 k) (H : A0 k) : ℝ :=
  ∑ P ∈ parF 𝔞 Q, (-1) ^ (P \ Q).card * tauHat P Q (H - X P)

def IsOrth (𝔞 : Submodule ℝ (A0 k)) (X : Finset (SV k) → A0 k) : Prop :=
  ∀ P ∈ parF 𝔞 ∅, ∀ Q ⊆ P, X Q = pr Q (X P)

def IsGMFam (𝔞 : Submodule ℝ (A0 k)) (c : Finset (SV k) → A0 k → ℂ) : Prop :=
  ∀ P ∈ parF 𝔞 ∅, ContDiff ℝ ∞ (c P) ∧ ∀ Q ⊆ P, ∀ l, c Q l = c P (pr Q l)

def eL (l H : A0 k) : ℂ := Complex.exp (Complex.I * (⟪l, H⟫_ℝ : ℝ))

def expFam (X : Finset (SV k) → A0 k) : Finset (SV k) → A0 k → ℂ := fun P l => eL l (X P)

def epsOf (s : Finset (SV k)) (b : SV k → A0 k) (l : A0 k) : ℂ :=
  (√(Matrix.gram ℝ fun u : s => b u).det : ℝ) * ∏ u ∈ s, (Complex.I * (⟪l, b u⟫_ℝ : ℝ))⁻¹

def eps (P Q : Finset (SV k)) : A0 k → ℂ := epsOf (P \ Q) (rt P)

def epsHat (P Q : Finset (SV k)) : A0 k → ℂ := epsOf (P \ Q) (wt Q)

def generic (k : ℕ) : Set (A0 k) := {l | ∀ P, IsPar P → ∀ Q ⊆ P, ∀ u ∈ P \ Q, ⟪l, wt Q u⟫_ℝ ≠ 0}

def sumM (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) (c : Finset (SV k) → A0 k → ℂ) (l : A0 k) : ℂ :=
  ∑ P ∈ parP 𝔞 Q, eps P Q l * c P l

def sumP (P R : Finset (SV k)) (c : Finset (SV k) → A0 k → ℂ) (l : A0 k) : ℂ :=
  ∑ S ∈ between P R, (-1) ^ (P \ S).card * epsHat P S l * eps S R l * c S l

def cM (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) (c : Finset (SV k) → A0 k → ℂ) : A0 k → ℂ :=
  extendFrom (generic k) (sumM 𝔞 Q c)

def cP (P R : Finset (SV k)) (c : Finset (SV k) → A0 k → ℂ) : A0 k → ℂ := extendFrom (generic k) (sumP P R c)

def stdVec (j : Fin k) : SV k := fun i => if i ≤ j then 1 else 0

def stdPar (J : Finset (Fin k)) : Finset (SV k) := J.image stdVec

def invSV (π : Equiv.Perm (Fin k)) (ε : Fin k → SignTypeˣ) (u : SV k) : SV k := fun i => ε i * u (π i)

def inverseChamberMap (π : Equiv.Perm (Fin k)) (ε : Fin k → SignTypeˣ) (H : A0 k) : A0 k :=
  WithLp.toLp 2 fun i => ((ε i : SignType) : ℝ) * H (π i)

def weylPar (π : Equiv.Perm (Fin k)) (ε : Fin k → SignTypeˣ) : Finset (SV k) := (stdPar univ).image (invSV π ε)

def Regular (c : ℝ) (T : A0 k) : Prop := (∀ i j, i < j → c ≤ T i - T j) ∧ ∀ i, c ≤ T i

theorem mem_parF {𝔞 : Submodule ℝ (A0 k)} {R Q : Finset (SV k)} : Q ∈ parF 𝔞 R ↔ IsPar Q ∧ aP Q ≤ 𝔞 ∧ R ⊆ Q := by
  simp [parF]

theorem mem_parP {𝔞 : Submodule ℝ (A0 k)} {R P : Finset (SV k)} : P ∈ parP 𝔞 R ↔ IsPar P ∧ aP P = 𝔞 ∧ R ⊆ P := by
  simp [parP]

theorem IsPar.mono {P Q : Finset (SV k)} (h : IsPar P) (e : Q ⊆ P) : IsPar Q :=
  ⟨fun h0 => h.1 (e h0), fun u hu u' hu' => h.2 u (e hu) u' (e hu')⟩

theorem vecSpan_mono {P Q : Finset (SV k)} (e : Q ⊆ P) : aP Q ≤ aP P := Submodule.span_mono (Set.image_mono e)

theorem isPar_stdPar (J : Finset (Fin k)) : IsPar (stdPar J) := by
  refine ⟨fun h => ?_, fun u hu u' hu' => ?_⟩
  · obtain ⟨j, -, e⟩ := mem_image.1 h
    simpa [stdVec] using congrFun e j
  · obtain ⟨j, -, rfl⟩ := mem_image.1 hu
    obtain ⟨j', -, rfl⟩ := mem_image.1 hu'
    have key : ∀ a b : Fin k, a ≤ b → Below (stdVec a) (stdVec b) := fun a b h i hi => by
      have : i ≤ a := by by_contra e; exact hi (if_neg e)
      simp [stdVec, this, this.trans h]
    exact (le_total j j').imp (key _ _) (key _ _)

theorem exists_top {α : Type} {r : α → α → Prop} (ht : ∀ a b c, r a b → r b c → r a c) (A : Finset α) (hA : A.Nonempty)
    (h : ∀ a ∈ A, ∀ b ∈ A, r a b ∨ r b a) : ∃ a ∈ A, ∀ b ∈ A, r b a := by
  induction hA using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨a, mem_singleton_self a, fun b hb => (mem_singleton.1 hb).symm ▸ or_self_iff.1 (h a (by simp) a (by simp))⟩
  | cons a s ha hs ih =>
    obtain ⟨b, hb, hb'⟩ := ih fun x hx y hy => h x (mem_cons_of_mem hx) y (mem_cons_of_mem hy)
    rcases h a (mem_cons_self _ _) b (mem_cons_of_mem hb) with e | e
    · exact ⟨b, mem_cons_of_mem hb, fun c hc => (mem_cons.1 hc).elim (· ▸ e) (hb' c)⟩
    · exact ⟨a, mem_cons_self _ _, fun c hc => (mem_cons.1 hc).elim
        (·.symm ▸ or_self_iff.1 (h a (mem_cons_self _ _) a (mem_cons_self _ _))) fun hc => ht _ _ _ (hb' c hc) e⟩

theorem IsPar.vec_notMem {P : Finset (SV k)} (h : IsPar P) {u : SV k} (hu : u ∈ P) : vec u ∉ aP (P.erase u) := by
  obtain ⟨a, ha, hA⟩ := exists_top (r := Below) (fun a b c h h' i hi => (h' i (h i hi ▸ hi)).trans (h i hi))
    (insert 0 ((P.erase u).filter (Below · u))) (insert_nonempty _ _) fun a ha b hb => by
      rcases mem_insert.1 ha with rfl | ha
      · exact .inl fun i hi => (hi rfl).elim
      rcases mem_insert.1 hb with rfl | hb
      · exact .inr fun i hi => (hi rfl).elim
      exact h.2 a (mem_of_mem_erase (mem_filter.1 ha).1) b (mem_of_mem_erase (mem_filter.1 hb).1)
  have key : ∀ a b : SV k, Below a b → a ≠ b → ∃ i, b i ≠ 0 ∧ a i = 0 := fun a b hab hne => by
    by_contra! hn
    exact hne (funext fun i => by
      by_cases e : b i = 0
      · by_contra e'; exact e' ((hab i (e ▸ e')).symm)
      · exact (hab i (hn i e)).symm)
  obtain ⟨i, hi, hai⟩ := key a u (by
      rcases mem_insert.1 ha with rfl | ha
      · exact fun i hi => (hi rfl).elim
      · exact (mem_filter.1 ha).2) (by
      rcases mem_insert.1 ha with rfl | ha
      · exact fun e => h.1 (e ▸ hu)
      · exact ne_of_mem_erase (mem_filter.1 ha).1)
  have h1 : ∀ b ∈ P.erase u, Below b u → b i = 0 := fun b hb hbu => by
    by_contra e; exact e ((hA b (mem_insert_of_mem (mem_filter.2 ⟨hb, hbu⟩)) i e).symm.trans hai)
  have fin : ∀ φ : A0 k →ₗ[ℝ] ℝ, φ (vec u) ≠ 0 → (∀ b ∈ P.erase u, φ (vec b) = 0) → vec u ∉ aP (P.erase u) :=
    fun φ h0 hb hm => h0 ((Submodule.span_le (p := LinearMap.ker φ)).2 (by rintro _ ⟨b, hb', rfl⟩; exact hb b hb') hm)
  have sq : ∀ s : SignType, s ≠ 0 → (s : ℝ) * s = 1 := fun s hs => by cases s <;> simp_all
  by_cases hB : ((P.erase u).filter (Below u ·)).Nonempty
  · obtain ⟨b, hb, hB⟩ := exists_top (r := fun a b => Below b a)
      (fun a b c h h' i hi => (h i (h' i hi ▸ hi)).trans (h' i hi)) _ hB fun a ha b hb =>
        h.2 b (mem_of_mem_erase (mem_filter.1 hb).1) a (mem_of_mem_erase (mem_filter.1 ha).1)
    obtain ⟨j, hj, huj⟩ := key u b (mem_filter.1 hb).2 (ne_of_mem_erase (mem_filter.1 hb).1).symm
    refine fin ((u i : ℝ) • EuclideanSpace.projₗ i - (b j : ℝ) • EuclideanSpace.projₗ j) (by simp [vec, huj, sq _ hi])
      fun c hc => ?_
    rcases h.2 c (mem_of_mem_erase hc) u hu with e | e
    · have : c j = 0 := by by_contra e'; exact e' ((e j e').symm.trans huj)
      simp [vec, h1 c hc e, this]
    · simp [vec, e i hi, hB c (mem_filter.2 ⟨hc, e⟩) j hj, sq _ hi, sq _ hj]
  · refine fin (EuclideanSpace.projₗ i) (left_ne_zero_of_mul ((sq _ hi).trans_ne one_ne_zero)) fun c hc => ?_
    rcases h.2 c (mem_of_mem_erase hc) u hu with e | e
    · simp [vec, h1 c hc e]
    · exact (hB ⟨c, mem_filter.2 ⟨hc, e⟩⟩).elim

theorem IsPar.wt_ne_zero {P Q : Finset (SV k)} (h : IsPar P) (e : Q ⊆ P) {u : SV k} (hu : u ∈ P \ Q) : wt Q u ≠ 0 :=
  fun h0 => h.vec_notMem (mem_sdiff.1 hu).1 (vecSpan_mono (fun v hv => mem_erase.2
    ⟨fun (e' : v = u) => (mem_sdiff.1 hu).2 (e' ▸ hv), e hv⟩) (sub_eq_zero.1 h0 ▸ Submodule.starProjection_apply_mem _ _))

theorem dense_generic : Dense (generic k) := by
  have e : generic k = ⋂ x : {x : Finset (SV k) × Finset (SV k) × SV k // IsPar x.1 ∧ x.2.1 ⊆ x.1 ∧ x.2.2 ∈ x.1 \ x.2.1},
      ((Submodule.span ℝ {wt x.1.2.1 x.1.2.2})ᗮ : Set (A0 k))ᶜ := by
    ext l
    simp only [generic, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff, SetLike.mem_coe,
      Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact ⟨fun h x => h _ x.2.1 _ x.2.2.1 _ x.2.2.2, fun h P hP Q hQ u hu => h ⟨(P, Q, u), hP, hQ, hu⟩⟩
  rw [e]
  refine dense_iInter_of_isOpen (fun x => (Submodule.isClosed_orthogonal _).isOpen_compl) fun x => ?_
  rw [← interior_eq_empty_iff_dense_compl, ← Set.not_nonempty_iff_eq_empty]
  intro h
  have := (Submodule.orthogonal_eq_top_iff _).1 (Submodule.eq_top_of_nonempty_interior' _ h)
  exact x.2.1.wt_ne_zero x.2.2.1 x.2.2.2 (Submodule.span_singleton_eq_bot.1 this)

theorem IsOrth.mono {𝔞 𝔟 : Submodule ℝ (A0 k)} {X : Finset (SV k) → A0 k} (h : IsOrth 𝔞 X) (e : 𝔟 ≤ 𝔞) : IsOrth 𝔟 X :=
  fun P hP => h P (mem_parF.2 ⟨(mem_parF.1 hP).1, (mem_parF.1 hP).2.1.trans e, empty_subset _⟩)

theorem IsOrth.sub {𝔞 : Submodule ℝ (A0 k)} {X Y : Finset (SV k) → A0 k} (h : IsOrth 𝔞 X) (h' : IsOrth 𝔞 Y) :
    IsOrth 𝔞 (X - Y) := fun P hP Q e => by rw [Pi.sub_apply, Pi.sub_apply, map_sub, ← h P hP Q e, ← h' P hP Q e]

theorem IsOrth.sub_mem_span {𝔞 : Submodule ℝ (A0 k)} {X : Finset (SV k) → A0 k} (h : IsOrth 𝔞 X) {P P' : Finset (SV k)}
    (hP : P ∈ parP 𝔞 ∅) (hP' : P' ∈ parP 𝔞 ∅) {u : SV k} (hu : u ∈ P) (e : P.erase u ⊆ P') :
    X P - X P' ∈ Submodule.span ℝ {rt P u} := by
  obtain ⟨h1, h2, -⟩ := mem_parP.1 hP
  obtain ⟨h1', h2', -⟩ := mem_parP.1 hP'
  have hF := mem_parF.2 ⟨h1, h2.le, empty_subset P⟩
  have hF' := mem_parF.2 ⟨h1', h2'.le, empty_subset P'⟩
  have hm : X P - X P' ∈ aP P := sub_mem (h P hF P subset_rfl ▸ Submodule.starProjection_apply_mem _ _)
    (h2 ▸ h2' ▸ h P' hF' P' subset_rfl ▸ Submodule.starProjection_apply_mem _ _)
  have h0 : pr (P.erase u) (X P - X P') = 0 := by rw [map_sub, ← h P hF _ (erase_subset _ _), ← h P' hF' _ e, sub_self]
  rw [aP, ← insert_erase hu, coe_insert, Set.image_insert_eq, Submodule.mem_span_insert, insert_erase hu] at hm
  obtain ⟨c, y, hy, e⟩ := hm
  refine Submodule.mem_span_singleton.2 ⟨c, ?_⟩
  rw [e, map_add, map_smul, show pr (P.erase u) y = y from Submodule.starProjection_eq_self_iff.2 hy] at h0
  rw [e, rt, wt, smul_sub, sub_eq_add_neg, neg_eq_of_add_eq_zero_right h0]

theorem IsOrth.isGMFam {𝔞 : Submodule ℝ (A0 k)} {X : Finset (SV k) → A0 k} (h : IsOrth 𝔞 X) : IsGMFam 𝔞 (expFam X) :=
  fun P hP => ⟨Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (contDiff_id.inner ℝ contDiff_const))), fun Q e l => by
      simp only [expFam, eL, h P hP Q e, pr, Submodule.inner_starProjection_left_eq_right]⟩

theorem IsGMFam.mul {𝔞 : Submodule ℝ (A0 k)} {c d : Finset (SV k) → A0 k → ℂ} (h : IsGMFam 𝔞 c) (h' : IsGMFam 𝔞 d) :
    IsGMFam 𝔞 (c * d) := fun P hP =>
  ⟨(h P hP).1.mul (h' P hP).1, fun Q e l => congrArg₂ (· * ·) ((h P hP).2 Q e l) ((h' P hP).2 Q e l)⟩

example (c : Finset (SV k) → A0 k → ℂ) (l : A0 k) : sumP ∅ ∅ c l = c ∅ l := by
  have h : ∀ b : SV k → A0 k, epsOf (∅ \ ∅) b l = 1 := fun b => by
    have : IsEmpty ↥((∅ : Finset (SV k)) \ ∅) := ⟨fun x => by simpa using x.2⟩
    rw [epsOf, Matrix.det_isEmpty]; simp
  simp only [sumP, between, powerset_empty, filter_singleton, Subset.refl, if_true, sum_singleton, eps, epsHat, h]
  simp

example (X : Finset (SV k) → A0 k) (H : A0 k) : gamM ⊥ ∅ X H = 1 := by
  have : parF (⊥ : Submodule ℝ (A0 k)) ∅ = {∅} := by
    ext Q
    rw [mem_parF, mem_singleton]
    refine ⟨fun h => eq_empty_of_forall_notMem fun u hu => h.1.vec_notMem hu ?_, fun e => ?_⟩
    · rw [(Submodule.mem_bot ℝ).1 (h.2.1 (Submodule.subset_span ⟨u, hu, rfl⟩))]; exact zero_mem _
    · subst e; simp [IsPar, aP]
  simp [gamM, this, tauHat]

end GlobalTheory.Chamber

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act parab)
open scoped TensorProduct NNReal Classical

namespace GlobalTheory.TruncKer

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def subFlag {V : HSpace E} (𝔉 : IsoFlag V) (J : Finset (Fin 𝔉.k)) : IsoFlag V where
  k := J.card
  X i := 𝔉.X (Fin.cases (motive := fun _ => Fin (𝔉.k + 1)) 0 (fun i => (J.orderEmbOfFin rfl i).succ) i)
  zero := 𝔉.zero
  strictMono := 𝔉.strictMono.comp fun a b h => by
    induction b using Fin.cases with
    | zero => exact absurd h (Fin.not_lt_zero _)
    | succ b =>
      induction a using Fin.cases with
      | zero => exact Fin.succ_pos _
      | succ a => exact Fin.succ_lt_succ_iff.2 ((J.orderEmbOfFin rfl).strictMono (Fin.succ_lt_succ_iff.1 h))
  iso := 𝔉.le_perp _ _

structure WittFrame (V : HSpace E) where

  e : Fin (wittIndex V) → V.V

  f : Fin (wittIndex V) → V.V
  ee : ∀ i j, V.hD (e i) (e j) = 0
  ff : ∀ i j, V.hD (f i) (f j) = 0
  ef : ∀ i j, V.hD (e i) (f j) = if i = j then 1 else 0

namespace WittFrame

variable {V : HSpace E} (Φ : WittFrame V)

theorem linearIndependent_e : LinearIndependent E Φ.e :=
  LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun j => V.hT (Φ.f j))
    (fun j i h => (Φ.ef i j).trans (if_neg h.symm)) fun i => (Φ.ef i i).trans (if_pos rfl)

def flag0 : IsoFlag V := .ofVectors Φ.e Φ.linearIndependent_e Φ.ee

def stdFlag (J : Finset (Fin (wittIndex V))) : IsoFlag V := subFlag Φ.flag0 J

def sub (u : SV (wittIndex V)) : Submodule E V.V := Submodule.span E (Φ.e '' {i | u i = 1} ∪ Φ.f '' {i | u i = -1})

theorem sub_stdVec (j : Fin (wittIndex V)) : Φ.sub (stdVec j) = Φ.flag0.X j.succ := by
  have h1 : {i | stdVec j i = 1} = {i : Fin (wittIndex V) | i.val < j.succ.val} := Set.ext fun i => by
    simp [stdVec, Nat.lt_succ_iff]
  have h2 : {i | stdVec j i = -1} = ∅ := Set.ext fun i => by
    simp only [stdVec, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]; split_ifs <;> decide
  rw [sub, h1, h2, Set.image_empty, Set.union_empty]; rfl

variable (hc : CMData F E) (R : Type) [CommRing R] [Algebra F R]

def par (P : Finset (SV (wittIndex V))) : Subgroup (HA R hc.sig V.gram) := ⨅ u ∈ P, parab hc V R (Φ.sub u)

def levi (P : Finset (SV (wittIndex V))) : Subgroup (HA R hc.sig V.gram) :=
  ⨅ u ∈ P, parab hc V R (Φ.sub u) ⊓ parab hc V R (Φ.sub (-u))

def coef (i : Fin (wittIndex V)) : (Fin V.rank → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E where
  toFun y := hLin hc.sig V.gram R y (coordR V R (Φ.f i))
  map_add' y y' := hLin_add_left _ _ _ y y' _
  map_smul' c y := hLin_smul_left _ _ _ c y _

theorem coef_coordR (i : Fin (wittIndex V)) (x : V.V) : Φ.coef hc R i (coordR V R x) = inclR R (V.hD x (Φ.f i)) := by
  change hR R hc.sig V.gram _ _ = inclR R (V.hT _ _)
  rw [IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
  simp [hR, Formalism.UG.hform, coordR, JR, inclR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, CMData.sig, TensorProduct.tmul_sum, starRingEnd_apply]

theorem coef_eq_zero (i : Fin (wittIndex V)) {y : Fin V.rank → R ⊗[F] E}
    (hy : y ∈ extSub (F := F) V R (Φ.flag0.X i.castSucc)) : Φ.coef hc R i y = 0 := by
  refine (Submodule.span_le (p := LinearMap.ker (Φ.coef hc R i))).2 ?_ hy
  rintro _ ⟨x, hx, rfl⟩
  have : V.hT (Φ.f i) x = 0 := (Submodule.span_le (p := LinearMap.ker (V.hT (Φ.f i)))).2 (by
    rintro _ ⟨j, hj, rfl⟩
    exact (Φ.ef j i).trans (if_neg (Fin.ne_of_val_ne (ne_of_lt hj)))) hx
  exact (Φ.coef_coordR hc R i x).trans (by rw [HSpace.hD, this, map_zero])

theorem sub_coef_mem (i : Fin (wittIndex V)) {y : Fin V.rank → R ⊗[F] E}
    (hy : y ∈ extSub (F := F) V R (Φ.flag0.X i.succ)) :
    y - Φ.coef hc R i y • coordR V R (Φ.e i) ∈ extSub (F := F) V R (Φ.flag0.X i.castSucc) := by
  have h1 : ∀ x ∈ Φ.flag0.X i.succ, x - V.hT (Φ.f i) x • Φ.e i ∈ Φ.flag0.X i.castSucc := fun x hx => by
    have := (Submodule.span_le (p := (Φ.flag0.X i.castSucc).comap (LinearMap.id - (V.hT (Φ.f i)).smulRight (Φ.e i)))).2 (by
      rintro _ ⟨j, hj, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply]
      rw [show V.hT (Φ.f i) (Φ.e j) = _ from Φ.ef j i]
      split_ifs with e
      · rw [e, one_smul, sub_self]; exact zero_mem _
      · rw [zero_smul, sub_zero]
        exact Submodule.subset_span ⟨j, lt_of_le_of_ne (Nat.lt_succ_iff.1 hj) (Fin.val_ne_of_ne e), rfl⟩) hx
    simpa using this
  suffices h : extSub (F := F) V R (Φ.flag0.X i.succ) ≤ (extSub (F := F) V R (Φ.flag0.X i.castSucc)).comap
    (LinearMap.id - (Φ.coef hc R i).smulRight (coordR V R (Φ.e i))) by simpa using h hy
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  have := h1 x hx
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply]
  rw [coef_coordR]
  convert coordR_mem (F := F) V R this using 1
  funext a; simp [coordR, HSpace.hD]

def chi (i : Fin (wittIndex V)) : Φ.flag0.par hc R →* R ⊗[F] E where
  toFun p := Φ.coef hc R i (act hc V p.1 (coordR V R (Φ.e i)))
  map_one' := by rw [OneMemClass.coe_one, IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_one, coef_coordR, Φ.ef, if_pos rfl, map_one]
  map_mul' p q := by
    have he : coordR (F := F) V R (Φ.e i) ∈ extSub (F := F) V R (Φ.flag0.X i.succ) :=
      coordR_mem V R (Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩)
    have h1 := Φ.coef_eq_zero hc R i (mem_parab_iff_maps.1 (IsoFlag.mem_par.1 p.2 i.castSucc) _
      (Φ.sub_coef_mem hc R i (mem_parab_iff_maps.1 (IsoFlag.mem_par.1 q.2 i.succ) _ he)))
    rw [IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_sub, map_sub, sub_eq_zero, act, act, act, Matrix.mulVec_smul, map_smul, smul_eq_mul] at h1
    rw [MulMemClass.coe_mul, IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, mul_comm]
    exact h1

def IsWeylRep (π : Equiv.Perm (Fin (wittIndex V))) (ε : Fin (wittIndex V) → SignTypeˣ) (w : GRat hc.sig V.gram) : Prop :=
  ∀ u, ∀ x ∈ Φ.sub (invSV π ε u), ratAct hc V w x ∈ Φ.sub u

def IsGood (L : Submodule (𝓞 E) (Fin V.rank → E)) (a : GL (Fin V.rank) (AF F ⊗[F] E)) : Prop :=
  Submodule.IsLattice E L ∧ (∀ v, IsSelfDualAt hc.sig V.gram L v) ∧
  (∀ i, V.frame.equivFun (Φ.e i) ∈ L ∧ V.frame.equivFun (Φ.f i) ∈ L) ∧ IsMajorantFrame hc.sig V.gram a ∧
  ∀ (w : InfinitePlace F) (i : Fin (wittIndex V)),
    (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ hc.sig) (Formalism.UG.bc (compInf F E w) a⁻¹).1 * (Formalism.UG.bc (compInf F E w) a⁻¹).1) *ᵥ
      coordR V w.Completion (Φ.e i) = JR w.Completion V.gram *ᵥ coordR V w.Completion (Φ.f i)

end WittFrame


def IsSSPart {n : ℕ} (γ s : Matrix (Fin n) (Fin n) E) : Prop :=
  Module.End.IsSemisimple (Matrix.toLin' s) ∧ Commute γ s ∧ IsNilpotent (γ - s)

def IsSSClass {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (𝔬 : Set (GRat σ J)) : Prop :=
  ∃ δ : GRat σ J, Module.End.IsSemisimple (Matrix.toLin' δ.1.1) ∧
    𝔬 = {γ | ∃ s : GRat σ J, IsSSPart γ.1.1 s.1.1 ∧ IsConj δ s}

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} (Φ : WittFrame V) (K : Subgroup (GA D V))

abbrev GF (V : HSp D) : Type := GRat D.sp.cm.sig V.gram

abbrev rat (V : HSp D) : GF V →* GA D V := ratEmb D.sp.cm.sig V.gram

def absChi (i : Fin (wittIndex V)) : PA Φ.flag0 →* ℝ≥0 :=
  (Doubling.absE D.host.F D.host.E).comp (Φ.chi D.sp.cm (AF D.host.F) i).toHomUnits

def H0 (x : GA D V) : A0 (wittIndex V) := WithLp.toLp 2 fun i => Real.log (Doubling.iwAbs (absChi Φ i) K x)

def unipMeas (𝔉 : IsoFlag V) : Measure (NA 𝔉) := (quotMeasure (NQ 𝔉) Measure.haar Set.univ)⁻¹ • Measure.haar

def kerP (J : Finset (Fin (wittIndex V))) (𝔬 : Set (GF V)) (f : GA D V → ℂ) (x y : GA D V) : ℂ :=
  ∑' δ : {δ : GF V // δ ∈ 𝔬 ∧ rat V δ ∈ Φ.levi D.sp.cm (AF D.host.F) (stdPar J)},
    ∫ n : NA (Φ.stdFlag J), f (x⁻¹ * rat V δ * n * y) ∂unipMeas (Φ.stdFlag J)

def kT (𝔬 : Set (GF V)) (f : GA D V → ℂ) (T : A0 (wittIndex V)) (x : GA D V) : ℂ :=
  ∑ J : Finset (Fin (wittIndex V)), (-1) ^ J.card * ∑' ξ : Quot ((Φ.stdFlag J).parRat D.sp.cm),
    tauHat (stdPar J) ∅ (H0 Φ K (rat V ξ.out * x) - T) * kerP Φ J 𝔬 f (rat V ξ.out * x) (rat V ξ.out * x)

def Ys (π : Equiv.Perm (Fin (wittIndex V))) (ε : Fin (wittIndex V) → SignTypeˣ) (w : GF V) (x : GA D V)
    (T : A0 (wittIndex V)) : A0 (wittIndex V) := inverseChamberMap π ε (T - H0 Φ K (rat V w * x))

def Yfam (x : GA D V) (T : A0 (wittIndex V)) (Q : Finset (SV (wittIndex V))) : A0 (wittIndex V) :=
  if h : ∃ s : Equiv.Perm (Fin (wittIndex V)) × (Fin (wittIndex V) → SignTypeˣ) × GF V,
      Φ.IsWeylRep D.sp.cm s.1 s.2.1 s.2.2 ∧ Q ⊆ weylPar s.1 s.2.1 then
    pr Q (Ys Φ K h.choose.1 h.choose.2.1 h.choose.2.2 x T) else 0

def weight (𝔞 : Submodule ℝ (A0 (wittIndex V))) (T : A0 (wittIndex V)) (x : GA D V) : ℝ :=
  ∫ H : aMQ 𝔞 ∅, gamM 𝔞 ∅ (Yfam Φ K x T) H

def volA (𝔞 : Submodule ℝ (A0 (wittIndex V))) (I : Subgroup (GA D V)) (dt : Measure I) : ℝ :=
  (quotMeasure ((GQ V).subgroupOf I) dt).real {q | ‖𝔞.starProjection (H0 Φ K (q.out : I))‖ < 1} /
    (volume : Measure (aMQ 𝔞 ∅)).real (Metric.ball 0 1)

def IsMinLevi (γ : GF V) (P : Finset (SV (wittIndex V))) : Prop :=
  IsPar P ∧ rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) P ∧
    ∀ (g : GF V) P', IsPar P' → rat V (g * γ * g⁻¹) ∈ Φ.levi D.sp.cm (AF D.host.F) P' → P'.card ≤ P.card

end GlobalTheory.TruncKer

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act parab)
open Formalism.UG (cT cT_mul cT_one)
open scoped TensorProduct NNReal Classical

namespace GlobalTheory.TruncKer

theorem exists_majorant {A : Type} [CommRing A] (σ : A →+* A) {n k m : ℕ} (J : Matrix (Fin n) (Fin n) A)
    (C D : Matrix (Fin n) (Fin k) A) (M : Matrix (Fin n) (Fin m) A) (r : A) (hr : σ r = r) (h2 : 2 * r * r = 1)
    (hCC : cT σ C * J * C = 0) (hDD : cT σ D * J * D = 0) (hCD : cT σ C * J * D = 1) (hDC : cT σ D * J * C = 1)
    (hMC : cT σ M * J * C = 0) (hMD : cT σ M * J * D = 0) (hCM : cT σ C * J * M = 0) (hDM : cT σ D * J * M = 0)
    (ε : Fin m → Bool) (hMM : cT σ M * J * M = diagonal fun i => if ε i then 1 else -1) (hn : m + 2 * k = n) :
    ∃ (b : GL (Fin n) A) (ε' : Fin n → Bool), cT σ b.1 * J * b.1 = (diagonal fun i => if ε' i then 1 else -1) ∧
      cT σ (b⁻¹).1 * (b⁻¹).1 * C = J * D := by
  obtain ⟨e⟩ : Nonempty ((Fin k ⊕ Fin k) ⊕ Fin m ≃ Fin n) := Fintype.card_eq.1 (by simp; omega)
  let a0 := fromCols (fromCols (r • (C + D)) (r • (C - D))) M
  let s : (Fin k ⊕ Fin k) ⊕ Fin m → Bool := Sum.elim (Sum.elim (fun _ => true) fun _ => false) ε
  let Δ : Matrix _ _ A := diagonal fun i => if s i then 1 else -1
  have hc : cT σ a0 = fromRows (fromRows (r • (cT σ C + cT σ D)) (r • (cT σ C - cT σ D))) (cT σ M) := by
    ext (i | i) j
    · rcases i with i | i <;> simp [cT, a0, hr, mul_add, mul_sub]
    · simp [cT, a0]
  have hrr : r * r + r * r = 1 := by rw [← h2]; ring
  have h0 : cT σ a0 * J * a0 = Δ := by
    rw [hc]
    simp only [a0, fromRows_mul, mul_fromCols, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.sub_mul,
      Matrix.mul_add, Matrix.mul_sub, hCC, hDD, hCD, hDC, hMC, hMD, hCM, hDM, hMM]
    ext (i | i) (j | j)
    · rcases i with i | i <;> rcases j with j | j <;> by_cases h : i = j <;>
        simp [Δ, s, h, diagonal, mul_add, mul_sub, hrr]
      linear_combination (-1 : A) * hrr
    · rcases i with i | i <;> simp [Δ]
    · rcases j with j | j <;> simp [Δ]
    · by_cases h : i = j <;> simp [Δ, s, diagonal, h]
      congr
  have hΔ : Δ * Δ = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; split_ifs <;> simp
  have h1 : a0 * (cT σ a0 * (J * D)) = C := by
    rw [← Matrix.mul_assoc (cT σ a0), hc]
    simp only [a0, fromRows_mul, fromCols_mul_fromRows, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
      Matrix.sub_mul, hDD, hCD, hMD, Matrix.mul_zero, Matrix.mul_one, add_zero, sub_zero, smul_smul]
    rw [← smul_add, add_add_sub_cancel, smul_add, ← add_smul, hrr, one_smul]
  let a := a0.submatrix id e.symm
  have hca : cT σ a = (cT σ a0).submatrix e.symm id := rfl
  have h3 : cT σ a * J * a = Δ.submatrix e.symm e.symm := by rw [← h0]; rfl
  have h4 : (Δ.submatrix e.symm e.symm * (cT σ a * J)) * a = 1 := by
    rw [Matrix.mul_assoc, h3, submatrix_mul_equiv, hΔ, submatrix_one_equiv]
  let b : GL (Fin n) A := ⟨a, _, mul_eq_one_comm.1 h4, h4⟩
  refine ⟨b, s ∘ e.symm, h3.trans (submatrix_diagonal_equiv _ _), ?_⟩
  have h5 : b.1 * (cT σ b.1 * (J * D)) = C := by
    rw [← h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc a0]
    congr 1
    exact submatrix_mul_equiv a0 (cT σ a0) id e.symm id
  rw [← h5, Matrix.mul_assoc, ← Matrix.mul_assoc (b⁻¹).1, Units.inv_mul, Matrix.one_mul, ← Matrix.mul_assoc, ← cT_mul,
    Units.mul_inv, cT_one, Matrix.one_mul]

theorem exists_lattice {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (V V' : HSpace E) (ι : V'.V →ₗ[E] V.V) (hι : HSpace.IsIsomEmb V' V ι) {k : ℕ} (e f : Fin k → V.V)
    (ee : ∀ a b, V.hT (e a) (e b) = 0) (ff : ∀ a b, V.hT (f a) (f b) = 0)
    (fe : ∀ a b, V.hT (f a) (e b) = if a = b then 1 else 0) (he : ∀ a x, V.hT (ι x) (e a) = 0)
    (hf : ∀ a x, V.hT (ι x) (f a) = 0)
    (ht : LinearMap.range ι ⊔ Submodule.span E (Set.range e ∪ Set.range f) = ⊤) :
    ∃ L : Submodule (𝓞 E) V.V, Submodule.IsLattice E L ∧ Formalism.HermitianLatticesTheory.IsUnimodular V.hT L ∧ ∀ i, e i ∈ L ∧ f i ∈ L := by
  have sy : ∀ x y, V.hT y x = star (V.hT x y) := fun x y => (V.herm.eq x y).symm
  have ef : ∀ a b, V.hT (e a) (f b) = if a = b then 1 else 0 := fun a b => by
    rw [sy, fe]; by_cases h : a = b <;> simp [h, eq_comm]
  have he' : ∀ a x, V.hT (e a) (ι x) = 0 := fun a x => by rw [sy, he, star_zero]
  have hf' : ∀ a x, V.hT (f a) (ι x) = 0 := fun a x => by rw [sy, hf, star_zero]
  have st : ∀ z ∈ (1 : Submodule (𝓞 E) E), star z ∈ (1 : Submodule (𝓞 E) E) := fun z hz =>
    Submodule.mem_one.2 (SelfDual.sig_mem_range hc.sig (Submodule.mem_one.1 hz))
  have o1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have hd : ∀ {S : HSpace E} (L : Submodule (𝓞 E) S.V) x, x ∈ Formalism.HermitianLatticesTheory.dual S.hT L ↔
      ∀ y ∈ L, S.hT y x ∈ (1 : Submodule (𝓞 E) E) := fun L x => by
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]; rfl
  let G : Set V.V := (Set.range e ∪ Set.range f) ∪ ι '' V'.L0
  have hG : Submodule.span (𝓞 E) G =
      Submodule.span (𝓞 E) (Set.range e ∪ Set.range f) ⊔ V'.L0.map (ι.restrictScalars (𝓞 E)) := by
    rw [Submodule.span_union]; congr 1; exact Submodule.span_eq (V'.L0.map (ι.restrictScalars (𝓞 E)))
  have hE : ∀ i, e i ∈ Submodule.span (𝓞 E) G := fun i => Submodule.subset_span (.inl (.inl ⟨i, rfl⟩))
  have hF : ∀ i, f i ∈ Submodule.span (𝓞 E) G := fun i => Submodule.subset_span (.inl (.inr ⟨i, rfl⟩))
  have dec : ∀ x, ∃ c, x = ι c + (∑ i, V.hT (f i) x • e i + ∑ i, V.hT (e i) x • f i) := fun x => by
    obtain ⟨_, ⟨c, rfl⟩, y, hy, rfl⟩ := Submodule.mem_sup.1 (ht.ge (Submodule.mem_top (x := x)))
    refine ⟨c, ?_⟩
    simp only [map_add, he', hf', zero_add, add_right_inj]
    induction hy using Submodule.span_induction with
    | mem y hy => rcases hy with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> simp [ee, ff, ef, fe]
    | zero => simp
    | add y z _ _ h1 h2 =>
      simp only [map_add, add_smul, Finset.sum_add_distrib]
      rw [add_add_add_comm, ← h1, ← h2]
    | smul a y _ h1 =>
      simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum, ← smul_add, ← h1]
  have lin : ∀ x, (∀ y ∈ G, V.hT x y ∈ (1 : Submodule (𝓞 E) E)) → ∀ y ∈ Submodule.span (𝓞 E) G,
      V.hT x y ∈ (1 : Submodule (𝓞 E) E) := fun x h y hy =>
    (Submodule.span_le (p := (1 : Submodule (𝓞 E) E).comap ((V.hT x).restrictScalars (𝓞 E)))).2 h hy
  refine ⟨Submodule.span (𝓞 E) G, ⟨?_, ?_⟩, Submodule.ext fun x => (hd _ x).trans ⟨fun h => ?_, fun hx y hy => ?_⟩,
    fun i => ⟨hE i, hF i⟩⟩
  · rw [hG]
    exact (Submodule.fg_span ((Set.finite_range e).union (Set.finite_range f))).sup (V'.standardTuple_isLattice.fg.map _)
  · rw [Submodule.span_span_of_tower, Submodule.span_union, Submodule.span_image, V'.standardTuple_isLattice.span_eq_top,
      Submodule.map_top, sup_comm, ht]
  · obtain ⟨c, hx⟩ := dec x
    have sm : ∀ z ∈ (1 : Submodule (𝓞 E) E), ∀ y ∈ Submodule.span (𝓞 E) G, z • y ∈ Submodule.span (𝓞 E) G := by
      intro z hz y hy
      obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hz
      rw [algebraMap_smul]; exact Submodule.smul_mem _ r hy
    have hc' : c ∈ V'.L0 := V'.baseLattice_isUnimodular ▸ (hd _ c).2 fun y hy => by
      have := h (ι y) (Submodule.subset_span (.inr ⟨y, hy, rfl⟩))
      rw [hx] at this
      simpa [he, hf, hι y c] using this
    rw [hx]
    exact add_mem (Submodule.subset_span (.inr ⟨c, hc', rfl⟩)) (add_mem
      (sum_mem fun i _ => sm _ (h _ (hF i)) _ (hE i)) (sum_mem fun i _ => sm _ (h _ (hE i)) _ (hF i)))
  · refine lin y (fun x hx => sy x y ▸ st _ (lin x (fun y hy => ?_) y hy)) x hx
    have ite : ∀ a b : Fin k, (if a = b then (1 : E) else 0) ∈ (1 : Submodule (𝓞 E) E) := fun a b => by
      split_ifs; exacts [o1, zero_mem _]
    rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨a, ha, rfl⟩ <;> rcases hy with (⟨b, rfl⟩ | ⟨b, rfl⟩) | ⟨b, hb, rfl⟩
    rotate_right
    · rw [hι]
      exact (hd _ b).1 (V'.baseLattice_isUnimodular.symm ▸ hb) a ha
    all_goals simp only [ee, ff, ef, fe, he, hf, he', hf', zero_mem, ite]

section Arch

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
  (V : HSpace E)

def cols {p : Type} (x : p → V.V) : Matrix (Fin V.rank) p E := of fun a i => V.frame.repr (x i) a

theorem gram_cols {p q : Type} (x : p → V.V) (y : q → V.V) :
    cT (hc.sig : E →+* E) (cols V x) * V.gram * cols V y = of fun i j => V.hT (x i) (y j) := by
  ext i j
  rw [of_apply, IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord, Finset.sum_comm]
  simp only [Matrix.mul_apply, Finset.sum_mul]; rfl

theorem exists_majorant_of_frame (V' : HSpace E) (ι : V'.V →ₗ[E] V.V) (hι : HSpace.IsIsomEmb V' V ι) {k : ℕ}
    (e f : Fin k → V.V) (ee : ∀ a b, V.hT (e a) (e b) = 0) (ff : ∀ a b, V.hT (f a) (f b) = 0)
    (fe : ∀ a b, V.hT (f a) (e b) = if a = b then 1 else 0) (he : ∀ a x, V.hT (ι x) (e a) = 0)
    (hf : ∀ a x, V.hT (ι x) (f a) = 0) (hr : V'.rank + 2 * k = V.rank) (R : Type) [CommRing R] [Algebra F R] (ρ : R)
    (hρ : 2 * ρ * ρ = 1) (c : Matrix (Fin V'.rank) (Fin V'.rank) (R ⊗[F] E)) (ε : Fin V'.rank → Bool)
    (hcc : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig) c * JR R V'.gram * c = diagonal fun i => if ε i then 1 else -1) :
    ∃ (b : GL (Fin V.rank) (R ⊗[F] E)) (ε' : Fin V.rank → Bool),
      cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig) b.1 * JR R V.gram * b.1 = (diagonal fun i => if ε' i then 1 else -1) ∧
      cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig) (b⁻¹).1 * (b⁻¹).1 * (cols V e).map (inclR (F := F) R) =
        JR R V.gram * (cols V f).map (inclR (F := F) R) := by
  have sy : ∀ x y, V.hT y x = star (V.hT x y) := fun x y => (V.herm.eq x y).symm
  have kk : ∀ {p q : ℕ} (x : Fin p → V.V) (y : Fin q → V.V),
      (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig) ((cols V x).map (inclR (F := F) R)) *
        JR (F := F) R V.gram : Matrix (Fin _) (Fin V.rank) (R ⊗[F] E)) * (cols V y).map (inclR (F := F) R) = (of fun i j => V.hT (x i) (y j)).map (inclR (F := F) R) :=
    fun x y => by rw [AutFunCounterexample.cT_map_gen, JR, ← Matrix.map_mul, ← Matrix.map_mul, gram_cols]
  have k0 : ∀ {p q : ℕ} (x : Fin p → V.V) (y : Fin q → V.V), (∀ i j, V.hT (x i) (y j) = 0) →
      (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig) ((cols V x).map (inclR (F := F) R)) *
        JR (F := F) R V.gram : Matrix (Fin _) (Fin V.rank) (R ⊗[F] E)) * (cols V y).map (inclR (F := F) R) = (0 : Matrix _ _ (R ⊗[F] E)) := fun x y h => by
    rw [kk]; exact Matrix.ext fun i j => (congrArg (inclR R) (h i j)).trans (map_zero _)
  have k1 : ∀ (x y : Fin k → V.V), (∀ i j, V.hT (x i) (y j) = if i = j then 1 else 0) →
      (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig) ((cols V x).map (inclR (F := F) R)) *
        JR (F := F) R V.gram : Matrix (Fin _) (Fin V.rank) (R ⊗[F] E)) * (cols V y).map (inclR (F := F) R) = (1 : Matrix _ _ (R ⊗[F] E)) := fun x y h => by
    rw [kk, show (of fun i j => V.hT (x i) (y j)) = 1 from Matrix.ext h, Matrix.map_one _ (map_zero _) (map_one _)]
  refine exists_majorant _ _ _ _ ((cols V fun i => ι (V'.frame i)).map (inclR (F := F) R) * c)
    (algebraMap R _ ρ) ?_ ?_ (k0 _ _ ee) (k0 _ _ ff) (k1 _ _ fun i j => ?_) (k1 _ _ fe) ?_ ?_ ?_ ?_ ε ?_ hr
  · simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  · rw [← map_ofNat (algebraMap R (R ⊗[F] E)) 2, ← map_mul, ← map_mul, hρ, map_one]
  · rw [sy, fe]; by_cases h : i = j <;> simp [h, eq_comm]
  · rw [cT_mul, Matrix.mul_assoc (cT _ c), Matrix.mul_assoc (cT _ c), k0 _ _ fun _ _ => he _ _, Matrix.mul_zero]
  · rw [cT_mul, Matrix.mul_assoc (cT _ c), Matrix.mul_assoc (cT _ c), k0 _ _ fun _ _ => hf _ _, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, k0 _ _ fun _ _ => by rw [sy, he, star_zero], Matrix.zero_mul]
  · rw [← Matrix.mul_assoc, k0 _ _ fun _ _ => by rw [sy, hf, star_zero], Matrix.zero_mul]
  · rw [cT_mul, ← hcc, ← Matrix.mul_assoc, Matrix.mul_assoc (cT _ c), Matrix.mul_assoc (cT _ c), kk]
    exact congrArg (fun X : Matrix _ _ E => cT _ c * X.map (inclR (F := F) R) * c) (Matrix.ext fun i j => hι _ _)

theorem unitary_extension {A n m : Type} [CommRing A] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (σ : A →+* A) {J : Matrix n n A} {B : Matrix n m A} {S P : Matrix m m A} {Q : Matrix m n A}
    (h1 : cT σ B * J = S * Q) (h2 : J * B = cT σ Q * S) (hQB : Q * B = 1) (hP : cT σ P * S * P = S) :
    cT σ (1 + B * (P - 1) * Q) * J * (1 + B * (P - 1) * Q) = J := by
  have hc1 : cT σ (1 + B * (P - 1) * Q) = 1 + cT σ Q * (cT σ P - 1) * cT σ B := by
    have e1 : cT σ (P - 1) = cT σ P - cT σ 1 := Matrix.ext fun _ _ => map_sub σ _ _
    have e2 : ∀ X : Matrix n n A, cT σ (1 + X) = cT σ 1 + cT σ X := fun X => Matrix.ext fun _ _ => map_add σ _ _
    rw [e2, cT_one, cT_mul, cT_mul, e1, cT_one, Matrix.mul_assoc]
  have h3 : ∀ X : Matrix m n A, J * (B * X) = cT σ Q * (S * X) := fun X => by
    rw [← Matrix.mul_assoc, h2, Matrix.mul_assoc]
  have h4 : ∀ X : Matrix m n A, Q * (B * X) = X := fun X => by rw [← Matrix.mul_assoc, hQB, Matrix.one_mul]
  have h5 := congrArg (fun X => cT σ Q * (X * Q)) hP
  rw [hc1, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc _ (cT σ B), h1]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_assoc, h3, h4] at h5 ⊢
  rw [h5]; abel

theorem sign_unit (ε : SignTypeˣ) (h : ε ≠ 1) : (ε : SignType) = -1 := by
  have h0 := ε.ne_zero
  have h1 : (ε : SignType) ≠ 1 := fun e => h (Units.ext e)
  generalize (ε : SignType) = s at h0 h1
  revert s; decide

theorem WittFrame.exists_isWeylRep (Φ : WittFrame V) (π : Equiv.Perm (Fin (wittIndex V)))
    (ε : Fin (wittIndex V) → SignTypeˣ) : ∃ w, Φ.IsWeylRep hc π ε w := by
  let b : Fin (wittIndex V) × Bool → V.V := fun a => if a.2 then Φ.e a.1 else Φ.f a.1
  let τ : Equiv.Perm (Fin (wittIndex V) × Bool) :=
    (Equiv.prodCongrRight fun i => if ε i = 1 then Equiv.refl Bool else Equiv.boolNot).trans (π.prodCongr (.refl _))
  have hτ : ∀ i s, τ (i, s) = (π i, if ε i = 1 then s else !s) := fun i s => by
    by_cases h : ε i = 1 <;> simp [τ, h]
  clear_value τ
  let σ : E →+* E := hc.sig
  let S : Matrix (Fin (wittIndex V) × Bool) (Fin (wittIndex V) × Bool) E :=
    (1 : Matrix _ _ E).submatrix id ((Equiv.refl _).prodCongr Equiv.boolNot)
  have fe : ∀ i j, V.hT (Φ.f i) (Φ.e j) = if i = j then 1 else 0 := fun i j => (Φ.ef j i).trans (by simp only [eq_comm])
  have ef : ∀ i j, V.hT (Φ.e i) (Φ.f j) = if i = j then 1 else 0 := fun i j => by
    rw [← V.herm.eq, fe]; by_cases h : i = j <;> simp [h, eq_comm]
  have ee : ∀ i j, V.hT (Φ.e i) (Φ.e j) = 0 := fun i j => Φ.ee j i
  have ff : ∀ i j, V.hT (Φ.f i) (Φ.f j) = 0 := fun i j => Φ.ff j i
  have hB : cT σ (cols V b) * V.gram * cols V b = S := by
    rw [gram_cols]
    ext ⟨i, _ | _⟩ ⟨j, _ | _⟩ <;> simp [b, S, ee, ff, ef, fe, Matrix.one_apply]
  have hSS : S * S = 1 := by
    refine (Matrix.mul_submatrix_one (Equiv.refl _) _ S).trans ?_
    ext ⟨i, s⟩ ⟨j, t⟩
    simp [S, Matrix.one_apply]
  have hS : cT σ S = S := by
    ext ⟨i, _ | _⟩ ⟨j, _ | _⟩ <;> simp [cT, S, Matrix.one_apply, eq_comm, apply_ite σ]
  let P : Matrix (Fin (wittIndex V) × Bool) (Fin (wittIndex V) × Bool) E := (1 : Matrix _ _ E).submatrix id τ
  have hBP : cols V b * P = cols V (b ∘ τ) := Matrix.mul_submatrix_one (Equiv.refl _) τ _
  have hP : cT σ P * S * P = S := by
    rw [← hB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul, Matrix.mul_assoc, hBP, gram_cols, gram_cols]
    ext ⟨i, _ | _⟩ ⟨j, _ | _⟩ <;> by_cases h1 : ε i = 1 <;> by_cases h2 : ε j = 1 <;>
      simp [hτ, b, ee, ff, ef, fe, h1, h2] <;> (rintro rfl; contradiction)
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = S * (cT σ (cols V b) * V.gram) := ⟨_, rfl⟩
  have hQB : Q * cols V b = 1 := by rw [hQ, Matrix.mul_assoc, hB, hSS]
  have h1 : cT σ (cols V b) * V.gram = S * Q := by rw [hQ, ← Matrix.mul_assoc S S, hSS, Matrix.one_mul]
  have h2 : V.gram * cols V b = cT σ Q * S := by
    have := congrArg (cT σ) h1
    rwa [cT_mul, cT_mul, AutFunCompare.cT_cT', IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_gram, hS] at this
  have hw := unitary_extension σ h1 h2 hQB hP
  have hi : V.gram⁻¹ * (cT σ (1 + cols V b * (P - 1) * Q) * V.gram) * (1 + cols V b * (P - 1) * Q) = 1 := by
    rw [Matrix.mul_assoc, hw, Matrix.nonsing_inv_mul _ (IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V)]
  let w : GRat hc.sig V.gram := ⟨⟨_, _, mul_eq_one_comm.1 hi, hi⟩, hw⟩
  have hwb : ∀ a, ratAct hc V w (b a) = b (τ a) := fun a => by
    have : (1 + cols V b * (P - 1) * Q) * cols V b = cols V (b ∘ τ) := by
      rw [Matrix.add_mul, Matrix.mul_assoc, hQB, Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hBP,
        add_sub_cancel]
    refine V.frame.repr.injective (DFunLike.coe_injective ?_)
    rw [ratAct, Matrix.repr_toLin]
    exact funext fun i => congrFun (congrFun this i) a
  refine ⟨w, fun u x hx => (Submodule.span_le (p := (Φ.sub u).comap (ratAct hc V w))).2 ?_ hx⟩
  have hε : ∀ i, ε i ≠ 1 → (ε i : SignType) = -1 := fun i => sign_unit (ε i)
  rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
  · refine Submodule.subset_span ((hwb (i, true)).symm ▸ ?_)
    by_cases h : ε i = 1
    · exact .inl ⟨π i, by simpa [invSV, h] using hi, by simp [b, hτ, h]⟩
    · exact .inr ⟨π i, by simpa [invSV, hε i h, neg_eq_iff_eq_neg] using hi, by simp [b, hτ, h]⟩
  · refine Submodule.subset_span ((hwb (i, false)).symm ▸ ?_)
    by_cases h : ε i = 1
    · exact .inr ⟨π i, by simpa [invSV, h] using hi, by simp [b, hτ, h]⟩
    · exact .inl ⟨π i, by simpa [invSV, hε i h] using hi, by simp [b, hτ, h]⟩

end Arch

theorem exists_subset_weylPar {k : ℕ} {Q : Finset (SV k)} (h : IsPar Q) : ∃ π ε, Q ⊆ weylPar π ε := by
  let ρ : Fin k → ℕ := fun i => (Q.filter (· i = 0)).card
  refine ⟨(Tuple.sort ρ).symm, fun i => if ∃ u ∈ Q, u i = -1 then -1 else 1, fun u hu => ?_⟩
  have hne : (Finset.univ.filter (u · ≠ 0)).Nonempty := by
    by_contra e
    exact h.1 ((funext fun i => by_contra fun hi => e ⟨i, by simpa using hi⟩ : u = 0) ▸ hu)
  obtain ⟨i₀, h0, hm⟩ := Finset.exists_max_image _ (Tuple.sort ρ).symm hne
  have h0 : u i₀ ≠ 0 := by simpa using h0
  refine Finset.mem_image.2 ⟨stdVec ((Tuple.sort ρ).symm i₀), Finset.mem_image_of_mem _ (Finset.mem_univ _),
    funext fun i => ?_⟩
  by_cases hi : u i = 0
  · have : ρ i₀ < ρ i := Finset.card_lt_card ⟨fun v hv => Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hv).1, by
      rcases h.2 u hu v (Finset.mem_filter.1 hv).1 with e | e
      · exact (h0 ((e i₀ h0).symm.trans (Finset.mem_filter.1 hv).2)).elim
      · by_contra e'; exact e' ((e i e').symm.trans hi)⟩,
      fun e => h0 (Finset.mem_filter.1 (e (Finset.mem_filter.2 ⟨hu, hi⟩))).2⟩
    have h2 : ¬(Tuple.sort ρ).symm i ≤ (Tuple.sort ρ).symm i₀ := fun e =>
      this.not_ge (by simpa using Tuple.monotone_sort ρ e)
    simp [invSV, stdVec, h2, hi]
  · have h2 := hm i (by simpa using hi)
    simp only [invSV, stdVec, h2, if_true, mul_one]
    split_ifs with e
    · obtain ⟨v, hv, e⟩ := e
      rcases h.2 u hu v hv with e' | e'
      · exact e.symm.trans (e' i hi)
      · exact ((e' i (by simp [e])).trans e).symm
    · have : u i ≠ -1 := fun e' => e ⟨u, hu, e'⟩
      generalize u i = s at hi this
      cases s <;> simp_all

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isGood {D : D7} (V : HSp D) : ∃ (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a := by
  obtain ⟨hr, ι, hι, C, hC, hM⟩ := isWittLower_minusHyp (V := V) (le_refl (wittIndex V))
  generalize minusHyp V (wittIndex V) le_rfl = V' at hr ι hι hM
  have hinj : Function.Injective ι := (injective_iff_map_eq_zero ι).2 fun x hx =>
    V'.nondeg.1 x fun y => by rw [← hι, hx]; simp
  have key := fun {p q : ℕ} (x : Fin p → V.V) (y : Fin q → V.V) i j => congrFun (congrFun (gram_cols D.sp.cm V x y) i) j
  let e : Fin (wittIndex V) → V.V := fun i => AutFunCompare.vecOf V (Cᵀ i)
  have eC : cols V e = C := Matrix.ext fun a i => AutFunCompare.repr_vecOf V _ a
  have eM : (cols V fun i => ι (V'.frame i)) = Formalism.L2.Theta.frameMat V V' ι :=
    Matrix.ext fun a i => (LinearMap.toMatrix_apply _ _ _ _ _).symm
  have ee : ∀ a b, V.hT (e a) (e b) = 0 := fun a b => (key e e a b).symm.trans (by rw [eC, hC.2]; rfl)
  have he : ∀ a x, V.hT (ι x) (e a) = 0 := fun a x => by
    have : ∀ i, V.hT (ι (V'.frame i)) (e a) = 0 := fun i =>
      (key (fun i => ι (V'.frame i)) e i a).symm.trans (by rw [eC, eM, hM]; rfl)
    rw [← V'.frame.sum_repr x]
    simp only [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, this, smul_zero, Finset.sum_const_zero]
  obtain ⟨f, ff, fe, hf, ht⟩ := GlobalTheory.exists_hyperbolic_completion _ _ V.hT V.herm V.nondeg (LinearMap.range ι)
    (by rintro _ ⟨x, rfl⟩ h; rw [V'.nondeg.1 x fun y => (hι x y).symm.trans (h _ ⟨y, rfl⟩), map_zero]) _ e
    (linearIndependent_vecOf hC.1) ee (by rintro a _ ⟨x, rfl⟩; exact he a x)
    (by rw [LinearMap.finrank_range_of_inj hinj, V'.rank_eq, V.rank_eq, hr])
  have hf' : ∀ a x, V.hT (ι x) (f a) = 0 := fun a x => hf a _ ⟨x, rfl⟩
  obtain ⟨L, h1, h2, h3⟩ := exists_lattice D.sp.cm V V' ι hι e f ee ff fe he hf' ht
  let V₂ : HSp D := { V with L0 := L, standardTuple_isLattice := h1, baseLattice_isUnimodular := h2 }
  let Φ : WittFrame V := ⟨e, f, fun i j => ee j i, fun i j => ff j i, fun i j => (fe j i).trans (by simp only [eq_comm])⟩
  have hρ : ∀ w : InfinitePlace D.host.F, ∃ ρ : w.Completion, 2 * ρ * ρ = 1 := fun w => by
    have := D.sp.cm.totReal
    let ρ := InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
    exact ⟨ρ.symm (√2)⁻¹, ρ.injective (by
      rw [map_mul, map_mul, ρ.apply_symm_apply, map_ofNat, map_one, mul_assoc, ← mul_inv,
        Real.mul_self_sqrt zero_le_two, mul_inv_cancel₀ two_ne_zero])⟩
  choose ρ hρ using hρ
  choose c ε₀ hc using Frames.exists_arch_frame (isCMExt_host D) (Orb.isHermND_gram V')
  choose b ε hb hb' using fun w : InfinitePlace D.host.F =>
    exists_majorant_of_frame D.sp.cm V V' ι hι e f ee ff fe he hf' hr w.Completion (ρ w) (hρ w) _ _ (hc w)
  obtain ⟨a, -, ha⟩ := Frames.exists_GL_of_components ∅ (fun _ => 1) (fun _ _ => rfl) b
  refine ⟨Φ, frameLat V₂, a, SelfDual.isLattice_frameLat V₂, SelfDual.isSelfDualAt_frameLat D V₂, fun i => ?_,
    fun w => ⟨ε w, ha w ▸ hb w⟩, fun w i => ?_⟩
  · have : ∀ x ∈ L, V.frame.equivFun x ∈ frameLat V₂ := fun x hx =>
      show V.frame.equivFun.symm (V.frame.equivFun x) ∈ L by rwa [LinearEquiv.symm_apply_apply]
    exact ⟨this _ (h3 i).1, this _ (h3 i).2⟩
  · rw [map_inv, ha]
    exact funext fun a => congrFun (congrFun (hb' w) a) i

variable {D : D7} {V : HSp D} {Φ : WittFrame V} {K : Subgroup (GA D V)}

theorem exists_Yfam_eq {Q : Finset (SV (wittIndex V))} (h : IsPar Q) : ∃ π ε w, Φ.IsWeylRep D.sp.cm π ε w ∧
    Q ⊆ weylPar π ε ∧ ∀ x T, Yfam Φ K x T Q = pr Q (Ys Φ K π ε w x T) := by
  obtain ⟨π, ε, e⟩ := exists_subset_weylPar h
  obtain ⟨w, hw⟩ := Φ.exists_isWeylRep D.sp.cm V π ε
  have : ∃ s : Equiv.Perm (Fin (wittIndex V)) × (Fin (wittIndex V) → SignTypeˣ) × GF V,
      Φ.IsWeylRep D.sp.cm s.1 s.2.1 s.2.2 ∧ Q ⊆ weylPar s.1 s.2.1 := ⟨(π, ε, w), hw, e⟩
  exact ⟨_, _, _, this.choose_spec.1, this.choose_spec.2, fun x T => dif_pos this⟩

theorem continuous_absChi (i : Fin (wittIndex V)) : Continuous (absChi Φ i) := by
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have hm : Continuous fun g : PA Φ.flag0 => (HA.mat _ D.sp.cm.sig V.gram g.1).1 :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_subtype_val
  have h : Continuous (Φ.chi D.sp.cm (AF D.host.F) i) := by
    change Continuous fun p : PA Φ.flag0 => hR _ D.sp.cm.sig V.gram _ (act D.sp.cm V p.1 _)
    simp only [hR_eq, act]
    exact continuous_const.dotProduct (continuous_const.matrix_mulVec (hm.matrix_mulVec continuous_const))
  exact Doubling.continuous_absE.comp (Units.continuous_iff.2 ⟨h, h.comp continuous_inv⟩)

theorem mul_mem_riemannRochSpace_add (hK : IsCompact (K : Set (GA D V))) (p : PA Φ.flag0) {k : GA D V} (hk : k ∈ K) (i : Fin (wittIndex V)) :
    H0 Φ K (p * k) i = Real.log (absChi Φ i p) := by
  have := Doubling.t2Space_adeleRing' (F := D.host.F)
  exact congrArg (fun r : ℝ≥0 => Real.log r) (Doubling.iwAbs_mul_of_triv
    (Doubling.triv_of_isCompact (Φ.flag0.isClosed_par _ _) (continuous_absChi i) hK) p hk)

theorem WittFrame.IsGood.isCompact {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {a : GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)} (h : Φ.IsGood D.sp.cm L a) :
    IsCompact (levelAll D.sp.cm.sig V.gram L a : Set (GA D V)) :=
  have := h.1
  Doubling.isCompact_levelAll (isCMExt_host D) _ _ _

end GlobalTheory.TruncKer

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU GlobalTheory.TruncKer GlobalTheory.Orb
open scoped ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chamber

example {k : ℕ} (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) :
    (volume : Measure (aMQ 𝔞 Q)) = (stdOrthonormalBasis ℝ (aMQ 𝔞 Q)).toBasis.addHaar := rfl

def ExpFamilyIntegral : Prop :=
  ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ X, IsOrth 𝔞 X → IsGMFam 𝔞 (expFam X) ∧ ∀ Q ∈ parF 𝔞 ∅,
    (Integrable (fun H : aMQ 𝔞 Q => gamM 𝔞 Q X H) ∧
      ∀ l, cM 𝔞 Q (expFam X) l = eL l (X Q) * ∫ H : aMQ 𝔞 Q, eL l H * gamM 𝔞 Q X H) ∧
    (Integrable (fun H : aMQ (aP Q) ∅ => gamP Q ∅ (X Q) H) ∧
      ∀ l, cP Q ∅ (expFam X) l = ∫ H : aMQ (aP Q) ∅, eL l H * gamP Q ∅ (X Q) H)

def FamilySmooth : Prop :=
  ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ c, IsGMFam 𝔞 c → ∀ Q ∈ parF 𝔞 ∅,
    (ContDiff ℝ ∞ (cM 𝔞 Q c) ∧ Set.EqOn (cM 𝔞 Q c) (sumM 𝔞 Q c) (generic k)) ∧
    ∀ R ⊆ Q, ContDiff ℝ ∞ (cP Q R c) ∧ Set.EqOn (cP Q R c) (sumP Q R c) (generic k)

def FamilyProduct : Prop :=
  ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ c d, IsGMFam 𝔞 c → IsGMFam 𝔞 d → ∀ R ∈ parF 𝔞 ∅, ∀ l,
    cM 𝔞 R (c * d) l = ∑ Q ∈ parF 𝔞 R, cM 𝔞 Q c l * cP Q R d l

end GlobalTheory.Chamber

namespace GlobalTheory.TruncKer

variable {D : D7} {V : HSp D} (Φ : WittFrame V) (K : Subgroup (GA D V)) (μ : Measure (GA D V))

def OrthogonalY : Prop :=
  ∀ x T, IsOrth ⊤ (Yfam Φ K x T) ∧
    ∀ π ε w, Φ.IsWeylRep D.sp.cm π ε w → Yfam Φ K x T (weylPar π ε) = Ys Φ K π ε w x T

def KernelConvergence : Prop :=
  ∀ f ∈ CcGA V, ∃ c : ℝ, ∀ T, Regular c T →
    (∀ 𝔬, IsSSClass 𝔬 → Integrable (descend (GQ V) (kT Φ K 𝔬 f T)) (autMeasure V μ)) ∧
    {𝔬 | IsSSClass 𝔬 ∧ ∫ q, ‖descend (GQ V) (kT Φ K 𝔬 f T) q‖ ∂autMeasure V μ ≠ 0}.Finite

def WeightedOrbital : Prop :=
  ∀ f ∈ CcGA V, ∀ γ : GF V, IsRegSS γ.1.1 → ∀ P, IsMinLevi Φ γ P →
    ∀ (dt : Measure (cent (rat V γ))) [dt.IsHaarMeasure], ∃ c : ℝ, ∀ T, Regular c T →
      Integrable (descend (cent (rat V γ)) fun x => (weight Φ K (aP P) T x : ℂ) * conjFn (rat V γ) f x)
        (quotMeas (cent (rat V γ)) dt μ) ∧
      ∫ q, descend (GQ V) (kT Φ K {δ | IsConj γ δ} f T) q ∂autMeasure V μ =
        volA Φ K (aP P) (cent (rat V γ)) dt *
          wOrbInt (cent (rat V γ)) dt μ (rat V γ) (fun x => weight Φ K (aP P) T x) f

end GlobalTheory.TruncKer

namespace GlobalTheory.Published

def LabesseWaldspurger : Prop :=
  (ExpFamilyIntegral ∧ FamilySmooth ∧ FamilyProduct) ∧
  ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a →
    OrthogonalY Φ (levelAll D.sp.cm.sig V.gram L a) ∧
    ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure],
      KernelConvergence Φ (levelAll D.sp.cm.sig V.gram L a) μ ∧ WeightedOrbital Φ (levelAll D.sp.cm.sig V.gram L a) μ

example (D : D7) : wittIndex (CuspDecay.Model.plane D) = 1 ∧
    ∃ (Φ : WittFrame (CuspDecay.Model.plane D)) (L : _) (a : _), Φ.IsGood D.sp.cm L a :=
  ⟨wittIndex_plane D, exists_isGood _⟩

end GlobalTheory.Published

end
end
