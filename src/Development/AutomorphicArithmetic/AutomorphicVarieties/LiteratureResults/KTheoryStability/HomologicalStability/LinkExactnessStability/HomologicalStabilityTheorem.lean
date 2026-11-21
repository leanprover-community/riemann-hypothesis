import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.MemSplitSeqIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KAcyclicHomology
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SurjectiveHMapZeroOfStaircase
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.HomologyRowExactOfStabilisationPattern
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SplitSeqFirstPageIsoAndDifferential
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SplitSequenceRepComplexExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SplitSeqExactAtOfTwoMulAddStableRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsSyzygyFactorization

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem stab_surj_bottom : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i → Function.Exact (d (p + 1)).hom (d p).hom) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q), (∀ p q, p ≤ i + 2 → IsIso (e p q)) → (∀ p q, p + 1 ≤ i + 2 → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → (∀ p q, Even p → 2 ≤ p → p + q = i → Function.Injective (s p q).hom) → (∀ p q, Even p → 2 ≤ p → p + q = i + 1 → Function.Surjective (s p q).hom) → Function.Surjective (s 0 i).hom := by
  intro k G _ _ i C d hd hs hex M e s hiso hsq hinj hsur
  have hsurjH : Function.Surjective (hMap (d 0) i).hom := by
    refine GlobalTheory.T.surjective_hMap_zero_of_staircase k G i C d hd hs hex ?_
    intro p q hp hpq
    refine GlobalTheory.T.homology_row_exact_of_stabilisation_pattern k G C d hd M e s (i + 2) hiso hsq p q (by omega) ?_ ?_
    · intro hev
      exact hinj p q hev (by obtain ⟨r, hr⟩ := hev; omega) hpq
    · intro hodd
      exact hsur (p + 1) q hodd.add_one (by omega) (by omega)
  have h0 : e 1 i ≫ hMap (d 0) i = s 0 i ≫ e 0 i := by
    have hev : Even 0 := ⟨0, rfl⟩
    rw [hsq 0 i (by omega)]
    exact if_pos hev
  haveI := hiso 0 i (by omega)
  haveI := hiso 1 i (by omega)
  have b0 := ConcreteCategory.bijective_of_isIso (e 0 i)
  have b1 := ConcreteCategory.bijective_of_isIso (e 1 i)
  intro y
  obtain ⟨w, hw⟩ := hsurjH (e 0 i y)
  obtain ⟨x, rfl⟩ := b1.2 w
  refine ⟨x, b0.1 ?_⟩
  rw [← hw]
  have h1 := congrArg (fun f : M 1 i ⟶ groupHomology (C 0) i => f.hom x) h0
  simpa using h1.symm

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.quillen_stabilisation_surjective_bottom : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i → Function.Exact (d (p + 1)).hom (d p).hom) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q), (∀ p q, p ≤ i + 2 → IsIso (e p q)) → (∀ p q, p + 1 ≤ i + 2 → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → (∀ p q, Even p → 2 ≤ p → p + q = i → Function.Injective (s p q).hom) → (∀ p q, Even p → 2 ≤ p → p + q = i + 1 → Function.Surjective (s p q).hom) → Function.Surjective (s 0 i).hom := by
  first
  | exact @GlobalTheory.HomStab.stab_surj_bottom
end
end

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab

theorem grpHMap_stab_surjective_congr (R : Type) [CommRing R] (i a b a' b' : ℕ) (h : a ≤ b) (h' : a' ≤ b') (ha : a = a') (hb : b = b')
    (hs : Function.Surjective (grpHMap (stab R a b h) i).hom) :
    Function.Surjective (grpHMap (stab R a' b' h') i).hom := by
  subst ha hb; exact hs

theorem grpHMap_stab_surjective_step : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ i : ℕ, (∀ q m m' (h : m ≤ m'), q < i → m' = m + 1 → (2 * q + s + 1 ≤ m → Function.Surjective (grpHMap (stab R m m' h) q).hom) ∧ (2 * q + s + 2 ≤ m → Function.Injective (grpHMap (stab R m m' h) q).hom)) → ∀ m m' (h : m ≤ m'), m' = m + 1 → 2 * i + s + 1 ≤ m → Function.Surjective (grpHMap (stab R m m' h) i).hom := by
  intro R _ s hsr i IH m m' h hm hi
  obtain ⟨e, he, hc⟩ := GlobalTheory.T.splitSeq_firstPage_iso_and_differential R s hsr (m + 1)
  obtain ⟨hdd, hd0, hex⟩ := GlobalTheory.T.splitSequence_rep_complex_exact R (m + 1)
  have key := GlobalTheory.T.quillen_stabilisation_surjective_bottom ℤ (GL (Fin (m + 1)) R) i (splitRep R (m + 1)) (splitD R (m + 1)) hdd
    (hd0 (GlobalTheory.T.splitSeq_exactAt_of_two_mul_add_stableRange_le R s hsr (m + 1) 0 (by omega)))
    (fun p hp => hex p (GlobalTheory.T.splitSeq_exactAt_of_two_mul_add_stableRange_le R s hsr (m + 1) (p + 1) (by omega)))
    (fun p q => grpH (GL (Fin (m + 1 - p)) R) q) e
    (fun p q => grpHMap (stab R (m + 1 - (p + 1)) (m + 1 - p) (by omega)) q)
    (fun p q hp => he p q (by omega))
    (fun p q hp => hc p q (by omega))
    (fun p q hp h2 hpq => (IH q (m + 1 - (p + 1)) (m + 1 - p) (by omega) (by omega) (by omega)).2 (by omega))
    (fun p q hp h2 hpq => (IH q (m + 1 - (p + 1)) (m + 1 - p) (by omega) (by omega) (by omega)).1 (by omega))
  exact grpHMap_stab_surjective_congr R i _ _ m m' _ h (by omega) (by omega) key

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
theorem _root_.GlobalTheory.T.groupHomology_GL_stab_surjective_of_stableRange_induction : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ i : ℕ, (∀ q m m' (h : m ≤ m'), q < i → m' = m + 1 → (2 * q + s + 1 ≤ m → Function.Surjective (grpHMap (stab R m m' h) q).hom) ∧ (2 * q + s + 2 ≤ m → Function.Injective (grpHMap (stab R m m' h) q).hom)) → ∀ m m' (h : m ≤ m'), m' = m + 1 → 2 * i + s + 1 ≤ m → Function.Surjective (grpHMap (stab R m m' h) i).hom := by
  first
  | exact @GlobalTheory.HomStab.grpHMap_stab_surjective_step
  | exact @GlobalTheory.HomStab.grpHMap_stab_surjective_congr
end
end

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.StairMid

variable {k G : Type} [CommRing k] [Group G]

def shC (C : ℕ → Rep k G) (Z : Rep k G) : ℕ → Rep k G
  | 0 => Z
  | n + 1 => C (n + 2)

def shD (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p) (Z : Rep k G) (b : C 2 ⟶ Z) :
    ∀ p, shC C Z (p + 1) ⟶ shC C Z p
  | 0 => b
  | p + 1 => d (p + 2)

theorem main : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i + 1 → Function.Exact (d (p + 1)).hom (d p).hom) → (∀ p q, 2 ≤ p → p + q = i + 1 → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom) → Function.Exact (hMap (d 1) i).hom (hMap (d 0) i).hom := by
  intro k G _ _ i C d hd hs hex hH
  obtain ⟨Z, ι, hι, b, hse, hbι, hbs, hdb, hexb⟩ := GlobalTheory.T.exists_syzygy_factorization k G C d hd hs (hex 0 (by omega))
  have hfun : ∀ {A B : Rep k G} (f : A ⟶ B), hMap f i = (groupHomology.functor k G i).map f := fun f => rfl
  have hsurj : Function.Surjective (hMap b i).hom := by
    refine GlobalTheory.T.surjective_hMap_zero_of_staircase k G i (shC C Z) (shD C d Z b) ?_ hbs ?_ ?_
    · intro p
      cases p with
      | zero => exact hdb
      | succ p => exact hd (p + 2)
    · intro p hp
      cases p with
      | zero => exact hexb (hex 1 (by omega))
      | succ p => exact hex (p + 2) (by omega)
    · intro p q hp hpq
      obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
      exact hH (r + 2) q (by omega) (by omega)
  have hles := (ShortComplex.moduleCat_exact_iff _).1 (groupHomology.mapShortComplex₂_exact hse i)
  have hcomp : hMap (d 1) i = hMap b i ≫ hMap ι i := by
    rw [hfun, hfun, hfun, ← hbι]
    exact (groupHomology.functor k G i).map_comp b ι
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hles x hx
    obtain ⟨z, rfl⟩ := hsurj y
    refine ⟨z, ?_⟩
    rw [hcomp]
    exact hy
  · rintro ⟨z, rfl⟩
    have h0 : hMap (d 1) i ≫ hMap (d 0) i = 0 := by
      have e := (groupHomology.functor k G i).map_comp (d 1) (d 0)
      rw [hd 0, Functor.map_zero] at e
      rw [hfun, hfun]
      exact e.symm
    rw [← ModuleCat.comp_apply, h0]
    rfl

end GlobalTheory.HomStab.StairMid

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.exact_hMap_one_zero_of_staircase : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i + 1 → Function.Exact (d (p + 1)).hom (d p).hom) → (∀ p q, 2 ≤ p → p + q = i + 1 → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom) → Function.Exact (hMap (d 1) i).hom (hMap (d 0) i).hom := by
  first
  | exact @GlobalTheory.HomStab.StairMid.main
end
end

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory

theorem injective_stabilisation_bottom_of_rows_exact : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i + 1 → Function.Exact (d (p + 1)).hom (d p).hom) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q), (∀ p q, p ≤ i + 3 → IsIso (e p q)) → (∀ p q, p + 1 ≤ i + 3 → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → (∀ p q, Even p → 2 ≤ p → p + q = i + 1 → Function.Injective (s p q).hom) → (∀ p q, Even p → 4 ≤ p → p + q = i + 2 → Function.Surjective (s p q).hom) → Function.Injective (s 0 i).hom := by
  intro k G _ _ i C d hdd hsurj hex M e s hiso hcomm hinj hsur
  have hE : Function.Exact (hMap (d 1) i).hom (hMap (d 0) i).hom := by
    refine T.exact_hMap_one_zero_of_staircase k G i C d hdd hsurj hex ?_
    intro p q hp hpq
    refine T.homology_row_exact_of_stabilisation_pattern k G C d hdd M e s (i + 3) hiso hcomm p q (by omega) ?_ ?_
    · intro hev
      exact hinj p q hev hp hpq
    · intro hodd
      have h3 : 3 ≤ p := by
        obtain ⟨m, rfl⟩ := hodd
        omega
      exact hsur (p + 1) q (by simpa using hodd.add_one) (by omega) (by omega)
  have h0 := hcomm 0 i (by omega)
  have h1 := hcomm 1 i (by omega)
  simp only [Even.zero, if_true] at h0
  have h1' : e 2 i ≫ hMap (d 1) i = 0 := by
    simpa using h1
  haveI := hiso 1 i (by omega)
  haveI := hiso 2 i (by omega)
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hx1 : (hMap (d 0) i).hom ((e 1 i).hom x) = 0 := by
    have := congrArg (fun f => f.hom x) h0
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    rw [this, hx, map_zero]
  obtain ⟨y, hy⟩ := (hE _).mp hx1
  have hy2 : y = (e 2 i).hom ((inv (e 2 i)).hom y) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, IsIso.inv_hom_id]
    rfl
  have hzero : (e 1 i).hom x = 0 := by
    rw [← hy, hy2]
    have := congrArg (fun f => f.hom ((inv (e 2 i)).hom y)) h1'
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    rw [this]
    rfl
  have : x = (inv (e 1 i)).hom ((e 1 i).hom x) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, IsIso.hom_inv_id]
    rfl
  rw [this, hzero, map_zero]

end GlobalTheory

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.quillen_stabilisation_injective_bottom : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i + 1 → Function.Exact (d (p + 1)).hom (d p).hom) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q), (∀ p q, p ≤ i + 3 → IsIso (e p q)) → (∀ p q, p + 1 ≤ i + 3 → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → (∀ p q, Even p → 2 ≤ p → p + q = i + 1 → Function.Injective (s p q).hom) → (∀ p q, Even p → 4 ≤ p → p + q = i + 2 → Function.Surjective (s p q).hom) → Function.Injective (s 0 i).hom := by
  first
  | exact @GlobalTheory.injective_stabilisation_bottom_of_rows_exact
end
end

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory

theorem homStab_GL_inj_step : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ i : ℕ, (∀ q m m' (h : m ≤ m'), q < i → m' = m + 1 → (2 * q + s + 1 ≤ m → Function.Surjective (grpHMap (stab R m m' h) q).hom) ∧ (2 * q + s + 2 ≤ m → Function.Injective (grpHMap (stab R m m' h) q).hom)) → ∀ m m' (h : m ≤ m'), m' = m + 1 → 2 * i + s + 2 ≤ m → Function.Injective (grpHMap (stab R m m' h) i).hom := by
  intro R _ s hs i ih m m' h hm hi
  subst hm
  obtain ⟨e, he, hed⟩ := GlobalTheory.T.splitSeq_firstPage_iso_and_differential R s hs (m + 1)
  obtain ⟨hdd, hsurj, hex⟩ := GlobalTheory.T.splitSequence_rep_complex_exact R (m + 1)
  have key := GlobalTheory.T.quillen_stabilisation_injective_bottom ℤ (GL (Fin (m + 1)) R) i (splitRep R (m + 1)) (splitD R (m + 1)) hdd
    (hsurj (GlobalTheory.T.splitSeq_exactAt_of_two_mul_add_stableRange_le R s hs (m + 1) 0 (by omega)))
    (fun p hp => hex p (GlobalTheory.T.splitSeq_exactAt_of_two_mul_add_stableRange_le R s hs (m + 1) (p + 1) (by omega)))
    (fun p q => grpH (GL (Fin (m + 1 - p)) R) q) e
    (fun p q => grpHMap (stab R (m + 1 - (p + 1)) (m + 1 - p) (by omega)) q)
    (fun p q hp => he p q (by omega))
    (fun p q hp => hed p q (by omega))
    (fun p q hp h2 hpq => (ih q (m + 1 - (p + 1)) (m + 1 - p) (by omega) (by omega) (by omega)).2 (by omega))
    (fun p q hp h4 hpq => (ih q (m + 1 - (p + 1)) (m + 1 - p) (by omega) (by omega) (by omega)).1 (by omega))
  exact key

end GlobalTheory

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
theorem _root_.GlobalTheory.T.groupHomology_GL_stab_injective_of_stableRange_induction : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ i : ℕ, (∀ q m m' (h : m ≤ m'), q < i → m' = m + 1 → (2 * q + s + 1 ≤ m → Function.Surjective (grpHMap (stab R m m' h) q).hom) ∧ (2 * q + s + 2 ≤ m → Function.Injective (grpHMap (stab R m m' h) q).hom)) → ∀ m m' (h : m ≤ m'), m' = m + 1 → 2 * i + s + 2 ≤ m → Function.Injective (grpHMap (stab R m m' h) i).hom := by
  first
  | exact @GlobalTheory.homStab_GL_inj_step
end
end

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab

theorem kStability_main : UpperTheory.V.Published.KStability := by
  intro R _ s hs
  have key : ∀ i : ℕ, ∀ m m' (h : m ≤ m'), m' = m + 1 →
      (2 * i + s + 1 ≤ m → Function.Surjective (grpHMap (stab R m m' h) i).hom) ∧
      (2 * i + s + 2 ≤ m → Function.Injective (grpHMap (stab R m m' h) i).hom) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      have hyp : ∀ q m m' (h : m ≤ m'), q < i → m' = m + 1 →
          (2 * q + s + 1 ≤ m → Function.Surjective (grpHMap (stab R m m' h) q).hom) ∧
          (2 * q + s + 2 ≤ m → Function.Injective (grpHMap (stab R m m' h) q).hom) :=
        fun q m m' h hq hm => ih q hq m m' h hm
      intro m m' h hm
      exact ⟨GlobalTheory.T.groupHomology_GL_stab_surjective_of_stableRange_induction R s hs i hyp m m' h hm, GlobalTheory.T.groupHomology_GL_stab_injective_of_stableRange_induction R s hs i hyp m m' h hm⟩
  intro i n hn
  have h1 := key i n (n + 1) (Nat.le_succ n) rfl
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨(h1.2 hn), (h1.1 (by omega))⟩

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
end
end
