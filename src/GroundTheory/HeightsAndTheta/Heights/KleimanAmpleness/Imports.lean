import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellResMemLocPart
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ConstVanishHypSegment
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisMore

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell faceSign)

namespace CechConstVanish

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]
  {V : Type} [AddCommGroup V]

def pt (a : ∀ k, ι k) : Cell K ι 0 :=
  ⟨fun l => {a l}, fun _ => Finset.singleton_nonempty _, by simp⟩

def edge (a : ∀ k, ι k) (k : K) (u v : ι k) (h : u ≠ v) : Cell K ι 1 :=
  ⟨Function.update (fun l => ({a l} : Finset (ι l))) k {u, v}, by
    refine ⟨fun l => ?_, ?_⟩
    · by_cases hl : l = k
      · subst hl; simp
      · simp [Function.update_of_ne hl]
    · rw [Finset.sum_eq_single k]
      · simp [Finset.card_pair h]
      · intro l _ hl; simp [Function.update_of_ne hl]
      · simp⟩

def tri (a : ∀ k, ι k) (k : K) (u v w : ι k) (huv : u < v) (hvw : v < w) : Cell K ι 2 :=
  ⟨Function.update (fun l => ({a l} : Finset (ι l))) k {u, v, w}, by
    refine ⟨fun l => ?_, ?_⟩
    · by_cases hl : l = k
      · subst hl; simp
      · simp [Function.update_of_ne hl]
    · rw [Finset.sum_eq_single k]
      · rw [Function.update_self, Finset.card_insert_of_notMem (by simp [huv.ne, (huv.trans hvw).ne]),
          Finset.card_pair hvw.ne]
      · intro l _ hl; simp [Function.update_of_ne hl]
      · simp⟩

def sq (a : ∀ k, ι k) (k k' : K) (hk : k ≠ k') (u v : ι k) (u' v' : ι k') (h : u ≠ v) (h' : u' ≠ v') :
    Cell K ι 2 :=
  ⟨Function.update (Function.update (fun l => ({a l} : Finset (ι l))) k {u, v}) k' {u', v'}, by
    refine ⟨fun l => ?_, ?_⟩
    · by_cases hl : l = k'
      · subst hl; simp
      · by_cases hl' : l = k
        · subst hl'; simp [Function.update_of_ne hl]
        · simp [Function.update_of_ne hl, Function.update_of_ne hl']
    · have e : ∀ l, ((Function.update (Function.update (fun l => ({a l} : Finset (ι l))) k {u, v}) k' {u', v'}
          l).card - 1) = (if l = k then 1 else 0) + (if l = k' then 1 else 0) := by
        intro l
        by_cases hl : l = k'
        · subst hl; simp [Finset.card_pair h', Ne.symm hk]
        · by_cases hl' : l = k
          · subst hl'; simp [Finset.card_pair h, hl]
          · simp [hl, hl']
      simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]⟩

theorem term_face {n : ℕ} (f : Cell K ι n → V) (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) (T : Cell K ι n)
    (hT : Function.update I k ((I k).erase i) = T.1)
    [Decidable ((∀ l, (Function.update I k ((I k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I k ((I k).erase i) l).card - 1) = n)] :
    (if h : (∀ l, (Function.update I k ((I k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I k ((I k).erase i) l).card - 1) = n then
      faceSign I k i • f ⟨Function.update I k ((I k).erase i), h⟩ else 0) = faceSign I k i • f T := by
  have h : (∀ l, (Function.update I k ((I k).erase i) l).Nonempty) ∧
      ∑ l, ((Function.update I k ((I k).erase i) l).card - 1) = n := by rw [hT]; exact T.2
  rw [dif_pos h]
  have e : (⟨Function.update I k ((I k).erase i), h⟩ : Cell K ι n) = T := Subtype.ext hT
  rw [e]

theorem term_single {n : ℕ} (f : Cell K ι n → V) (I : ∀ k, Finset (ι k)) (k : K) (i : ι k)
    (hI : I k = {i})
    [Decidable ((∀ l, (Function.update I k ((I k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I k ((I k).erase i) l).card - 1) = n)] :
    (if h : (∀ l, (Function.update I k ((I k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I k ((I k).erase i) l).card - 1) = n then
      faceSign I k i • f ⟨Function.update I k ((I k).erase i), h⟩ else 0) = 0 := by
  rw [dif_neg]
  intro h
  have := h.1 k
  rw [Function.update_self, hI] at this
  simp at this

theorem pt_update (a : ∀ k, ι k) (k : K) (x : ι k) :
    (pt (Function.update a k x)).1 = Function.update (fun l => ({a l} : Finset (ι l))) k {x} := by
  funext l
  by_cases hl : l = k
  · subst hl; simp [pt]
  · simp [pt, Function.update_of_ne hl]

theorem constD_edge (f : Cell K ι 0 → V) (a : ∀ k, ι k) (k : K) (u v : ι k) (h : u < v) :
    constD K ι V 0 f (edge a k u v h.ne) = f (pt (Function.update a k v)) - f (pt (Function.update a k u)) := by
  have hE : ∀ l, l ≠ k → (edge a k u v h.ne).1 l = {a l} := fun l hl => by simp [edge, Function.update_of_ne hl]
  have hEk : (edge a k u v h.ne).1 k = {u, v} := by simp [edge]
  have hpre : ∑ l ∈ Finset.univ.filter (· < k), (((edge a k u v h.ne).1 l).card - 1) = 0 :=
    Finset.sum_eq_zero fun l hl => by rw [hE l (ne_of_lt (Finset.mem_filter.mp hl).2)]; simp
  simp only [constD]
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_congr hEk (fun _ _ => rfl), Finset.sum_pair h.ne,
      term_face _ _ _ _ (pt (Function.update a k v)), term_face _ _ _ _ (pt (Function.update a k u))]
    · simp [faceSign, hpre, hEk, Finset.filter_insert, Finset.filter_singleton, h, not_lt_of_gt h]
      abel
    all_goals
      rw [pt_update, hEk]
      simp only [edge, Function.update_idem]
      congr 1
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      have := h.ne
      grind
  · intro l _ hl
    exact Finset.sum_eq_zero fun i hi => by
      rw [hE l hl, Finset.mem_singleton] at hi
      subst hi
      exact term_single _ _ _ _ (hE l hl)
  · simp

theorem constD_tri (z : Cell K ι 1 → V) (a : ∀ k, ι k) (k : K) (u v w : ι k) (huv : u < v) (hvw : v < w) :
    constD K ι V 1 z (tri a k u v w huv hvw) =
      z (edge a k v w hvw.ne) - z (edge a k u w (huv.trans hvw).ne) + z (edge a k u v huv.ne) := by
  have huw := huv.trans hvw
  have hE : ∀ l, l ≠ k → (tri a k u v w huv hvw).1 l = {a l} := fun l hl => by
    simp [tri, Function.update_of_ne hl]
  have hEk : (tri a k u v w huv hvw).1 k = {u, v, w} := by simp [tri]
  have hpre : ∑ l ∈ Finset.univ.filter (· < k), (((tri a k u v w huv hvw).1 l).card - 1) = 0 :=
    Finset.sum_eq_zero fun l hl => by rw [hE l (ne_of_lt (Finset.mem_filter.mp hl).2)]; simp
  simp only [constD]
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_congr hEk (fun _ _ => rfl), Finset.sum_insert (by simp [huv.ne, huw.ne]), Finset.sum_pair hvw.ne,
      term_face _ _ _ _ (edge a k v w hvw.ne), term_face _ _ _ _ (edge a k u w huw.ne),
      term_face _ _ _ _ (edge a k u v huv.ne)]
    · have h1 : ({u, v, w} : Finset (ι k)).filter (· < u) = ∅ := by
        ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]; grind
      have h2 : ({u, v, w} : Finset (ι k)).filter (· < v) = {u} := by
        ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]; grind
      have h3 : ({u, v, w} : Finset (ι k)).filter (· < w) = {u, v} := by
        ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]; grind
      simp only [faceSign, hpre, hEk, h1, h2, h3, Finset.card_empty, Finset.card_singleton,
        Finset.card_pair huv.ne]
      simp
      abel
    all_goals
      rw [hEk]
      simp only [edge, tri, Function.update_idem]
      congr 1
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      grind
  · intro l _ hl
    exact Finset.sum_eq_zero fun i hi => by
      rw [hE l hl, Finset.mem_singleton] at hi
      subst hi
      exact term_single _ _ _ _ (hE l hl)
  · simp

theorem constD_sq (z : Cell K ι 1 → V) (a : ∀ k, ι k) (k k' : K) (hk : k < k') (u v : ι k) (u' v' : ι k')
    (h : u < v) (h' : u' < v') :
    constD K ι V 1 z (sq a k k' hk.ne u v u' v' h.ne h'.ne) =
      z (edge (Function.update a k v) k' u' v' h'.ne) - z (edge (Function.update a k u) k' u' v' h'.ne)
        - z (edge (Function.update a k' v') k u v h.ne) + z (edge (Function.update a k' u') k u v h.ne) := by
  have hE : ∀ l, l ≠ k → l ≠ k' → (sq a k k' hk.ne u v u' v' h.ne h'.ne).1 l = {a l} := fun l h1 h2 => by
    simp [sq, Function.update_of_ne h1, Function.update_of_ne h2]
  have hEk : (sq a k k' hk.ne u v u' v' h.ne h'.ne).1 k = {u, v} := by
    simp [sq, Function.update_of_ne hk.ne]
  have hEk' : (sq a k k' hk.ne u v u' v' h.ne h'.ne).1 k' = {u', v'} := by simp [sq]
  have hpre : ∑ l ∈ Finset.univ.filter (· < k), (((sq a k k' hk.ne u v u' v' h.ne h'.ne).1 l).card - 1) = 0 :=
    Finset.sum_eq_zero fun l hl => by
      have hl' := (Finset.mem_filter.mp hl).2
      rw [hE l (ne_of_lt hl') (ne_of_lt (hl'.trans hk))]; simp
  have hpre' : ∑ l ∈ Finset.univ.filter (· < k'), (((sq a k k' hk.ne u v u' v' h.ne h'.ne).1 l).card - 1) = 1 := by
    rw [Finset.sum_eq_single k]
    · rw [hEk, Finset.card_pair h.ne]
    · intro l hl h1
      rw [hE l h1 (ne_of_lt (Finset.mem_filter.mp hl).2)]; simp
    · simp [hk]
  simp only [constD]
  rw [Finset.sum_eq_add_of_mem k k' (Finset.mem_univ _) (Finset.mem_univ _) hk.ne]
  · rw [Finset.sum_congr hEk (fun _ _ => rfl), Finset.sum_pair h.ne, Finset.sum_congr hEk' (fun _ _ => rfl),
      Finset.sum_pair h'.ne,
      term_face _ _ _ _ (edge (Function.update a k v) k' u' v' h'.ne),
      term_face _ _ _ _ (edge (Function.update a k u) k' u' v' h'.ne),
      term_face _ _ _ _ (edge (Function.update a k' v') k u v h.ne),
      term_face _ _ _ _ (edge (Function.update a k' u') k u v h.ne)]
    · simp [faceSign, hpre, hpre', hEk, hEk', Finset.filter_insert, Finset.filter_singleton, h, h',
        not_lt_of_gt h, not_lt_of_gt h']
      abel
    all_goals
      funext l
      rcases eq_or_ne l k with rfl | h1
      · simp only [sq, edge, Function.update_self, Function.update_of_ne hk.ne]
        try (ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; grind)
      rcases eq_or_ne l k' with rfl | h2
      · simp only [sq, edge, Function.update_self, Function.update_of_ne h1]
        try (ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; grind)
      · simp [sq, edge, Function.update_of_ne h1, Function.update_of_ne h2]
  · intro l _ hl
    exact Finset.sum_eq_zero fun i hi => by
      rw [hE l hl.1 hl.2, Finset.mem_singleton] at hi
      subst hi
      exact term_single _ _ _ _ (hE l hl.1 hl.2)

theorem tri_sub {G : ∀ k, Finset (ι k)} {a : ∀ k, ι k} (ha : ∀ l, a l ∈ G l) {k : K} {u v w : ι k}
    (huv : u < v) (hvw : v < w) (hu : u ∈ G k) (hv : v ∈ G k) (hw : w ∈ G k) :
    ∀ l, (tri a k u v w huv hvw).1 l ⊆ G l := by
  intro l
  by_cases hl : l = k
  · subst hl; simp [tri, Finset.insert_subset_iff, hu, hv, hw]
  · simp [tri, Function.update_of_ne hl, ha l]

theorem sq_sub {G : ∀ k, Finset (ι k)} {a : ∀ k, ι k} (ha : ∀ l, a l ∈ G l) {k k' : K} (hk : k ≠ k')
    {u v : ι k} {u' v' : ι k'} (h : u ≠ v) (h' : u' ≠ v') (hu : u ∈ G k) (hv : v ∈ G k) (hu' : u' ∈ G k')
    (hv' : v' ∈ G k') : ∀ l, (sq a k k' hk u v u' v' h h').1 l ⊆ G l := by
  intro l
  by_cases hl : l = k'
  · subst hl; simp [sq, Finset.insert_subset_iff, hu', hv']
  · by_cases hl' : l = k
    · subst hl'; simp [sq, Function.update_of_ne hl, Finset.insert_subset_iff, hu, hv]
    · simp [sq, Function.update_of_ne hl, Function.update_of_ne hl', ha l]

theorem edge_congr {a b : ∀ k, ι k} {k : K} {u v : ι k} (h : u ≠ v) (hab : ∀ l, l ≠ k → a l = b l) :
    edge a k u v h = edge b k u v h := by
  apply Subtype.ext
  funext l
  by_cases hl : l = k
  · subst hl; simp [edge]
  · simp [edge, Function.update_of_ne hl, hab l hl]

section Oriented

variable (z : Cell K ι 1 → V)

def oz (a : ∀ k, ι k) (k : K) (u v : ι k) : V :=
  if h : u < v then z (edge a k u v h.ne) else if h' : v < u then -z (edge a k v u h'.ne) else 0

theorem oz_of_lt {a : ∀ k, ι k} {k : K} {u v : ι k} (h : u < v) : oz z a k u v = z (edge a k u v h.ne) := by
  simp [oz, h]

theorem oz_self (a : ∀ k, ι k) (k : K) (u : ι k) : oz z a k u u = 0 := by
  simp [oz]

theorem oz_swap (a : ∀ k, ι k) (k : K) (u v : ι k) : oz z a k v u = -oz z a k u v := by
  rcases lt_trichotomy u v with h | rfl | h
  · simp [oz, h, not_lt_of_gt h]
  · simp [oz]
  · simp [oz, h, not_lt_of_gt h]

theorem oz_congr {a b : ∀ k, ι k} {k : K} (u v : ι k) (hab : ∀ l, l ≠ k → a l = b l) :
    oz z a k u v = oz z b k u v := by
  unfold oz
  split_ifs with h1 h2
  · rw [edge_congr _ hab]
  · rw [edge_congr _ hab]
  · rfl

variable {G : ∀ k, Finset (ι k)} (hz : ∀ I : Cell K ι 2, (∀ k, I.1 k ⊆ G k) → constD K ι V 1 z I = 0)
include hz

theorem oz_tri {a : ∀ k, ι k} (ha : ∀ l, a l ∈ G l) {k : K} {x u v : ι k} (hx : x ∈ G k) (hu : u ∈ G k)
    (hv : v ∈ G k) : oz z a k x v - oz z a k x u = oz z a k u v := by
  have hA : ∀ p q r : ι k, p ∈ G k → q ∈ G k → r ∈ G k → p < q → q < r →
      oz z a k p r = oz z a k p q + oz z a k q r := by
    intro p q r hp hq hr hpq hqr
    have e := hz _ (tri_sub ha hpq hqr hp hq hr)
    rw [constD_tri] at e
    rw [oz_of_lt z hpq, oz_of_lt z hqr, oz_of_lt z (hpq.trans hqr), ← sub_eq_zero, ← neg_eq_zero, ← e]
    abel
  by_cases e1 : x = u
  · subst e1; rw [oz_self, sub_zero]
  by_cases e2 : u = v
  · subst e2; rw [oz_self, sub_self]
  by_cases e3 : x = v
  · subst e3; rw [oz_self, zero_sub, oz_swap z a k u x, neg_neg]
  rw [sub_eq_iff_eq_add']
  have s1 := oz_swap z a k x u
  have s2 := oz_swap z a k u v
  have s3 := oz_swap z a k x v
  rcases lt_or_gt_of_ne e1 with h1 | h1 <;> rcases lt_or_gt_of_ne e2 with h2 | h2 <;>
    rcases lt_or_gt_of_ne e3 with h3 | h3
  all_goals first
    | exact absurd (h1.trans h2) (lt_asymm h3)
    | exact absurd (h2.trans h1) (lt_asymm h3)
    | exact hA x u v hx hu hv h1 h2
    | (first
        | have hh := hA u x v hu hx hv h1 h3
        | have hh := hA u v x hu hv hx h2 h3
        | have hh := hA x v u hx hv hu h3 h2
        | have hh := hA v x u hv hx hu h3 h1
        | have hh := hA v u x hv hu hx h2 h1
       simp only [s1, s2, s3] at hh ⊢
       first
        | (rw [← sub_eq_zero] at hh ⊢; rw [← hh]; abel1)
        | (rw [← sub_eq_zero] at hh ⊢; rw [← neg_eq_zero, ← hh]; abel1))

end Oriented

section Square

variable (z : Cell K ι 1 → V) {G : ∀ k, Finset (ι k)}
  (hz : ∀ I : Cell K ι 2, (∀ k, I.1 k ⊆ G k) → constD K ι V 1 z I = 0)
include hz

theorem oz_sq_core {a : ∀ k, ι k} (ha : ∀ l, a l ∈ G l) {k k' : K} (hk : k < k') {u v : ι k} {u' v' : ι k'}
    (h : u < v) (h' : u' < v') (hu : u ∈ G k) (hv : v ∈ G k) (hu' : u' ∈ G k') (hv' : v' ∈ G k') :
    oz z (Function.update a k v) k' u' v' - oz z (Function.update a k u) k' u' v' =
      oz z (Function.update a k' v') k u v - oz z (Function.update a k' u') k u v := by
  have e := hz _ (sq_sub ha hk.ne h.ne h'.ne hu hv hu' hv')
  rw [constD_sq z a k k' hk u v u' v' h h'] at e
  rw [oz_of_lt z h', oz_of_lt z h', oz_of_lt z h, oz_of_lt z h, ← sub_eq_zero, ← e]
  abel

theorem oz_sq_lt {a : ∀ k, ι k} (ha : ∀ l, a l ∈ G l) {k k' : K} (hk : k < k') {u v : ι k} {u' v' : ι k'}
    (hu : u ∈ G k) (hv : v ∈ G k) (hu' : u' ∈ G k') (hv' : v' ∈ G k') :
    oz z (Function.update a k v) k' u' v' - oz z (Function.update a k u) k' u' v' =
      oz z (Function.update a k' v') k u v - oz z (Function.update a k' u') k u v := by
  have step : ∀ p q : ι k, p ∈ G k → q ∈ G k → p < q →
      oz z (Function.update a k q) k' u' v' - oz z (Function.update a k p) k' u' v' =
        oz z (Function.update a k' v') k p q - oz z (Function.update a k' u') k p q := by
    intro p q hp hq hpq
    rcases lt_trichotomy u' v' with h' | rfl | h'
    · exact oz_sq_core z hz ha hk hpq h' hp hq hu' hv'
    · simp [oz_self]
    · have c := oz_sq_core z hz ha hk hpq h' hp hq hv' hu'
      rw [oz_swap z (Function.update a k q) k' v' u', oz_swap z (Function.update a k p) k' v' u']
      rw [← sub_eq_zero] at c ⊢
      rw [← neg_eq_zero, ← c]
      abel
  rcases lt_trichotomy u v with h | rfl | h
  · exact step u v hu hv h
  · simp [oz_self]
  · have c := step v u hv hu h
    rw [oz_swap z (Function.update a k' v') k v u, oz_swap z (Function.update a k' u') k v u]
    rw [← sub_eq_zero] at c ⊢
    rw [← neg_eq_zero, ← c]
    abel

theorem oz_sq {a : ∀ k, ι k} (ha : ∀ l, a l ∈ G l) {k k' : K} (hk : k ≠ k') {u v : ι k} {u' v' : ι k'}
    (hu : u ∈ G k) (hv : v ∈ G k) (hu' : u' ∈ G k') (hv' : v' ∈ G k') :
    oz z (Function.update a k v) k' u' v' - oz z (Function.update a k u) k' u' v' =
      oz z (Function.update a k' v') k u v - oz z (Function.update a k' u') k u v := by
  rcases lt_or_gt_of_ne hk with h | h
  · exact oz_sq_lt z hz ha h hu hv hu' hv'
  · exact (oz_sq_lt z hz ha h hu' hv' hu hv).symm

end Square

def mix (e b : ∀ k, ι k) (s : Finset K) : ∀ k, ι k := fun l => if l ∈ s then b l else e l

theorem mix_mem {G : ∀ k, Finset (ι k)} {e b : ∀ k, ι k} (he : ∀ l, e l ∈ G l) (hb : ∀ l, b l ∈ G l)
    (s : Finset K) : ∀ l, mix e b s l ∈ G l := by
  intro l
  unfold mix
  split_ifs
  · exact hb l
  · exact he l

theorem sum_initial (g : Finset K → V) (s : Finset K) :
    ∑ m ∈ s, (g (s.filter (· ≤ m)) - g (s.filter (· < m))) = g s - g ∅ := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [Finset.sum_insert has]
    have e1 : (insert a s).filter (· ≤ a) = insert a s := by
      apply Finset.filter_true_of_mem
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact le_rfl
      · exact (ha x hx).le
    have e2 : (insert a s).filter (· < a) = s := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hlt⟩
        · exact absurd hlt (lt_irrefl _)
        · exact hx
      · intro hx
        exact ⟨Or.inr hx, ha x hx⟩
    have e3 : ∀ m ∈ s, (insert a s).filter (· ≤ m) = s.filter (· ≤ m) := fun m hm => by
      rw [Finset.filter_insert, if_neg (not_le.mpr (ha m hm))]
    have e4 : ∀ m ∈ s, (insert a s).filter (· < m) = s.filter (· < m) := fun m hm => by
      rw [Finset.filter_insert, if_neg (not_lt.mpr (ha m hm).le)]
    rw [e1, e2, Finset.sum_congr rfl (fun m hm => by rw [e3 m hm, e4 m hm]), ih]
    abel

def pathF (z : Cell K ι 1 → V) (e b : ∀ k, ι k) : V :=
  ∑ m, oz z (mix e b (Finset.univ.filter (· < m))) m (e m) (b m)

def gpath (z : Cell K ι 1 → V) (e a : ∀ k, ι k) (k : K) (u v : ι k) (s : Finset K) : V :=
  if k ∈ s then oz z (mix e a s) k u v else 0

section Path

variable (z : Cell K ι 1 → V) {G : ∀ k, Finset (ι k)}
  (hz : ∀ I : Cell K ι 2, (∀ k, I.1 k ⊆ G k) → constD K ι V 1 z I = 0)
  {e a : ∀ k, ι k} (he : ∀ l, e l ∈ G l) (ha : ∀ l, a l ∈ G l) {k : K} {u v : ι k} (hu : u ∈ G k) (hv : v ∈ G k)
include hz he ha hu hv

theorem term_lt {m : K} (hmk : m < k) :
    oz z (mix e (Function.update a k v) (Finset.univ.filter (· < m))) m (e m) (Function.update a k v m) -
      oz z (mix e (Function.update a k u) (Finset.univ.filter (· < m))) m (e m) (Function.update a k u m) =
      gpath z e a k u v (Finset.univ.filter (· ≤ m)) - gpath z e a k u v (Finset.univ.filter (· < m)) := by
  have h3 : mix e (Function.update a k v) (Finset.univ.filter (· < m)) =
      mix e (Function.update a k u) (Finset.univ.filter (· < m)) := by
    funext l
    by_cases hl : l < m
    · simp [mix, hl, Function.update_of_ne (ne_of_lt (hl.trans hmk))]
    · simp [mix, hl]
  rw [h3, Function.update_of_ne (ne_of_lt hmk), Function.update_of_ne (ne_of_lt hmk), sub_self]
  simp [gpath, not_le.mpr hmk, not_lt.mpr hmk.le]

theorem term_eq :
    oz z (mix e (Function.update a k v) (Finset.univ.filter (· < k))) k (e k) (Function.update a k v k) -
      oz z (mix e (Function.update a k u) (Finset.univ.filter (· < k))) k (e k) (Function.update a k u k) =
      gpath z e a k u v (Finset.univ.filter (· ≤ k)) - gpath z e a k u v (Finset.univ.filter (· < k)) := by
  have hB : ∀ x : ι k, ∀ l, l ≠ k → mix e (Function.update a k x) (Finset.univ.filter (· < k)) l =
      mix e a (Finset.univ.filter (· < k)) l := by
    intro x l hl
    simp [mix, Function.update_of_ne hl]
  have hC : ∀ l, l ≠ k → mix e a (Finset.univ.filter (· ≤ k)) l = mix e a (Finset.univ.filter (· < k)) l := by
    intro l hl
    simp [mix, le_iff_lt_or_eq, hl]
  rw [Function.update_self, Function.update_self, oz_congr z _ _ (hB v), oz_congr z _ _ (hB u),
    oz_tri z hz (mix_mem he ha _) (he k) hu hv]
  simp only [gpath, Finset.mem_filter, Finset.mem_univ, true_and, le_refl, if_true, lt_irrefl, if_false,
    sub_zero]
  exact (oz_congr z u v hC).symm

theorem term_gt {m : K} (hkm : k < m) :
    oz z (mix e (Function.update a k v) (Finset.univ.filter (· < m))) m (e m) (Function.update a k v m) -
      oz z (mix e (Function.update a k u) (Finset.univ.filter (· < m))) m (e m) (Function.update a k u m) =
      gpath z e a k u v (Finset.univ.filter (· ≤ m)) - gpath z e a k u v (Finset.univ.filter (· < m)) := by
  have hU : ∀ x : ι k, mix e (Function.update a k x) (Finset.univ.filter (· < m)) =
      Function.update (mix e a (Finset.univ.filter (· < m))) k x := by
    intro x
    funext l
    rcases eq_or_ne l k with rfl | hl
    · simp [mix, hkm]
    · simp [mix, Function.update_of_ne hl]
  have hA : Function.update (mix e a (Finset.univ.filter (· < m))) m (a m) =
      mix e a (Finset.univ.filter (· ≤ m)) := by
    funext l
    rcases eq_or_ne l m with rfl | hl
    · simp [mix]
    · simp [mix, le_iff_lt_or_eq, hl]
  have hE : Function.update (mix e a (Finset.univ.filter (· < m))) m (e m) =
      mix e a (Finset.univ.filter (· < m)) := by
    funext l
    rcases eq_or_ne l m with rfl | hl
    · simp [mix]
    · simp [Function.update_of_ne hl]
  rw [hU, hU, Function.update_of_ne (ne_of_gt hkm), Function.update_of_ne (ne_of_gt hkm),
    oz_sq z hz (mix_mem he ha _) (ne_of_lt hkm) hu hv (he m) (ha m), hA, hE]
  simp [gpath, hkm.le, hkm]

theorem pathF_edge :
    pathF z e (Function.update a k v) - pathF z e (Function.update a k u) = oz z a k u v := by
  unfold pathF
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ m, oz z (mix e (Function.update a k v) (Finset.univ.filter (· < m))) m (e m)
        (Function.update a k v m) -
      oz z (mix e (Function.update a k u) (Finset.univ.filter (· < m))) m (e m) (Function.update a k u m) =
      gpath z e a k u v (Finset.univ.filter (· ≤ m)) - gpath z e a k u v (Finset.univ.filter (· < m)) := by
    intro m
    rcases lt_trichotomy m k with h | rfl | h
    · exact term_lt z hz he ha hu hv h
    · exact term_eq z hz he ha hu hv
    · exact term_gt z hz he ha hu hv h
  rw [Finset.sum_congr rfl (fun m _ => hterm m), sum_initial]
  have hm : mix e a Finset.univ = a := funext fun l => by simp [mix]
  simp [gpath, hm]

end Path

theorem exists_edge (J : Cell K ι 1) : ∃ (a : ∀ k, ι k) (k : K) (u v : ι k) (h : u < v),
    (∀ l, a l ∈ J.1 l) ∧ u ∈ J.1 k ∧ v ∈ J.1 k ∧ J = edge a k u v h.ne := by
  rcases J with ⟨I, hne, hs⟩
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun l => (I l).card - 1) (by rw [hs]; exact one_ne_zero)
  have hk1 : (I k).card - 1 ≤ 1 := hs ▸ Finset.single_le_sum (f := fun l => (I l).card - 1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hk2 : (I k).card = 2 := by omega
  have ha : ∀ l, (hne l).choose ∈ I l := fun l => (hne l).choose_spec
  have hl1 : ∀ l, l ≠ k → I l = {(hne l).choose} := by
    intro l hl
    have h2 := Finset.sum_le_sum_of_subset (f := fun l => (I l).card - 1) (Finset.subset_univ {k, l})
    rw [Finset.sum_pair (Ne.symm hl), hs] at h2
    have hc : (I l).card = 1 := by have := (hne l).card_pos; omega
    exact Finset.eq_singleton_iff_unique_mem.mpr ⟨ha l, fun y hy => Finset.card_le_one.mp hc.le y hy _ (ha l)⟩
  obtain ⟨p, q, hpq, hpq'⟩ := Finset.card_eq_two.mp hk2
  rcases lt_or_gt_of_ne hpq with h | h
  · refine ⟨fun l => (hne l).choose, k, p, q, h, ha, by simp [hpq'], by simp [hpq'],
      Subtype.ext (funext fun l => ?_)⟩
    show I l = Function.update (fun l => ({(hne l).choose} : Finset (ι l))) k {p, q} l
    by_cases hl : l = k
    · subst hl; rw [Function.update_self, hpq']
    · rw [Function.update_of_ne hl]; exact hl1 l hl
  · refine ⟨fun l => (hne l).choose, k, q, p, h, ha, by simp [hpq'], by simp [hpq'],
      Subtype.ext (funext fun l => ?_)⟩
    show I l = Function.update (fun l => ({(hne l).choose} : Finset (ι l))) k {q, p} l
    by_cases hl : l = k
    · subst hl; rw [Function.update_self, hpq', Finset.pair_comm]
    · rw [Function.update_of_ne hl]; exact hl1 l hl

noncomputable def vtx (c : Cell K ι 0) : ∀ k, ι k := fun l => (c.2.1 l).choose

theorem vtx_pt (a : ∀ k, ι k) : vtx (pt a) = a :=
  funext fun l => Finset.mem_singleton.mp ((pt a).2.1 l).choose_spec

theorem full : CechConstVanish.Statement := by
  intro K _ _ ι _ V _ G z hz
  by_cases hG : ∀ k, (G k).Nonempty
  swap
  · simp only [not_forall, Finset.not_nonempty_iff_eq_empty] at hG
    obtain ⟨k, hk⟩ := hG
    refine ⟨0, fun J hJ => ?_⟩
    exfalso
    obtain ⟨i, hi⟩ := J.2.1 k
    have := hJ k hi
    rw [hk] at this
    simp at this
  choose e he using hG
  refine ⟨fun c => pathF z e (vtx c), fun J hJ => ?_⟩
  obtain ⟨a, k, u, v, huv, haJ, hu, hv, rfl⟩ := exists_edge J
  have ha : ∀ l, a l ∈ G l := fun l => hJ l (haJ l)
  rw [constD_edge _ a k u v huv, vtx_pt, vtx_pt, pathF_edge z hz he ha (hJ k hu) (hJ k hv), oz_of_lt z huv]

end CechConstVanish

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cellMon cellRes locPart mIdealOver mConeMapOver chartRingOver quotPart)

noncomputable section

namespace CechPointEval

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Homog

theorem isMultiHomog_zero (a : K → ℕ) : IsMultiHomog (0 : MRingOver F ι) a := by
  intro m hm
  simp at hm

theorem isMultiHomog_C (r : F) : IsMultiHomog (C r : MRingOver F ι) 0 := by
  intro m hm k
  rw [C_apply] at hm
  rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
  simp

theorem isMultiHomog_add {p q : MRingOver F ι} {a : K → ℕ} (hp : IsMultiHomog p a)
    (hq : IsMultiHomog q a) : IsMultiHomog (p + q) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact hp m h k
  · exact hq m h k

theorem isMultiHomog_smul {p : MRingOver F ι} {a : K → ℕ} (s : F) (hp : IsMultiHomog p a) :
    IsMultiHomog (s • p) a :=
  fun m hm k => hp m (support_smul hm) k

theorem isMultiHomog_mul {p q : MRingOver F ι} {a b : K → ℕ} (hp : IsMultiHomog p a)
    (hq : IsMultiHomog q b) : IsMultiHomog (p * q) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.mp (support_mul p q hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hp m₁ h₁ k, hq m₂ h₂ k]

theorem isMultiHomog_X_pow [DecidableEq K] (k : K) (i : ι k) (n : ℕ) :
    IsMultiHomog ((X ⟨k, i⟩ : MRingOver F ι) ^ n) (Pi.single k n) := by
  classical
  rw [X_pow_eq_monomial]
  intro m hm l
  rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
  by_cases hl : l = k
  · subst hl
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hj (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm
    · simp
  · rw [Pi.single_eq_of_ne hl]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hl (Sigma.mk.inj_iff.mp h).1.symm

theorem isMultiHomog_prod_X (c : ∀ k, ι k) (e : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRingOver F ι) ^ e k) e := by
  classical
  have h : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRingOver F ι) ^ e k)
      (∑ k ∈ s, Pi.single k (e k)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using isMultiHomog_C (F := F) (ι := ι) 1
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact isMultiHomog_mul (isMultiHomog_X_pow k (c k) (e k)) ih
  simpa [Finset.univ_sum_single] using h Finset.univ

end Homog

section Eval

variable {Ω : Type} [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)

theorem mConeMapOver_homog {g : MRingOver F ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    mConeMapOver F y g = C (aeval y g) * ∏ k, (X k : MvPolynomial K Ω) ^ d k := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  simp only [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hX : ∏ p : Σ k, ι k, (X p.1 : MvPolynomial K Ω) ^ μ p = ∏ k, (X k : MvPolynomial K Ω) ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (X k : MvPolynomial K Ω) ^ μ ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg μ hμ k]
  rw [mConeMapOver, aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, MvPolynomial.algebraMap_apply, map_mul, map_prod, map_pow, hX]
  ring

theorem aeval_eq_zero_of_mem {f : MRingOver F ι} (hf : f ∈ mIdealOver F y) : aeval y f = 0 := by
  have h : (MvPolynomial.eval (fun _ : K => (1 : Ω))).comp (mConeMapOver F y).toRingHom =
      (aeval y : MRingOver F ι →ₐ[F] Ω).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [mConeMapOver, MvPolynomial.algebraMap_apply]
    · intro p
      simp [mConeMapOver]
  have h2 := RingHom.congr_fun h f
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2
  rw [← h2, show mConeMapOver F y f = 0 from (RingHom.mem_ker).mp hf, map_zero]

theorem mk_eq_zero_of_aeval {g : MRingOver F ι} {d : K → ℕ} (hg : IsMultiHomog g d) (h0 : aeval y g = 0) :
    Ideal.Quotient.mk (mIdealOver F y) g = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  show g ∈ RingHom.ker (mConeMapOver F y)
  rw [RingHom.mem_ker, mConeMapOver_homog y hg, h0, map_zero, zero_mul]

def ev0 : (MRingOver F ι ⧸ mIdealOver F y) →ₐ[F] Ω :=
  Ideal.Quotient.liftₐ (mIdealOver F y) (aeval y) (fun _ hf => aeval_eq_zero_of_mem y hf)

theorem evalAtPoint_mk (p : MRingOver F ι) : ev0 y (Ideal.Quotient.mk (mIdealOver F y) p) = aeval y p := rfl

theorem evalAtPoint_smul (r : MRingOver F ι) (m : MRingOver F ι ⧸ mIdealOver F y) :
    ev0 y (r • m) = aeval y r * ev0 y m := by
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
  show ev0 y (Ideal.Quotient.mk _ (r * m)) = _
  rw [evalAtPoint_mk, evalAtPoint_mk, map_mul]

def Good (I : ∀ k, Finset (ι k)) : Prop :=
  ∀ k, ∀ i ∈ I k, y ⟨k, i⟩ ≠ 0

variable {y}

theorem aeval_ne_zero_of_mem {I : ∀ k, Finset (ι k)} (hI : Good y I) {t : MRingOver F ι}
    (ht : t ∈ cellMon F I) : aeval y t ≠ 0 := by
  unfold ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon at ht
  induction ht using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, i, hi, rfl⟩ := hx
    rw [aeval_X]
    exact hI k i hi
  | one => simp
  | mul x z _ _ hx hz => rw [map_mul]; exact mul_ne_zero hx hz

variable (y)

def ev (I : ∀ k, Finset (ι k)) (hI : Good y I)
    (x : LocalizedModule (cellMon F I) (MRingOver F ι ⧸ mIdealOver F y)) : Ω :=
  LocalizedModule.liftOn x (fun p => ev0 y p.1 / aeval y (p.2 : MRingOver F ι)) (by
    rintro ⟨a, s⟩ ⟨b, t⟩ ⟨u, hu⟩
    simp only [Submonoid.smul_def] at hu
    have h := congrArg (ev0 y) hu
    rw [evalAtPoint_smul, evalAtPoint_smul, evalAtPoint_smul, evalAtPoint_smul] at h
    have hu0 := aeval_ne_zero_of_mem hI u.2
    have hs0 := aeval_ne_zero_of_mem hI s.2
    have ht0 := aeval_ne_zero_of_mem hI t.2
    dsimp only
    rw [div_eq_div_iff hs0 ht0]
    have h' := mul_left_cancel₀ hu0 h
    linear_combination h')

theorem ev_mk (I : ∀ k, Finset (ι k)) (hI : Good y I) (m : MRingOver F ι ⧸ mIdealOver F y)
    (s : cellMon F I) : ev y I hI (LocalizedModule.mk m s) = ev0 y m / aeval y (s : MRingOver F ι) :=
  LocalizedModule.liftOn_mk _ _ _

def evLin (I : ∀ k, Finset (ι k)) (hI : Good y I) :
    LocalizedModule (cellMon F I) (MRingOver F ι ⧸ mIdealOver F y) →ₗ[F] Ω where
  toFun := ev y I hI
  map_add' x x' := by
    induction x using LocalizedModule.induction_on with
    | h m s =>
      induction x' using LocalizedModule.induction_on with
      | h m' s' =>
        have hs0 := aeval_ne_zero_of_mem hI s.2
        have hs0' := aeval_ne_zero_of_mem hI s'.2
        rw [LocalizedModule.mk_add_mk, ev_mk, ev_mk, ev_mk]
        simp only [Submonoid.smul_def, map_add, evalAtPoint_smul, Submonoid.coe_mul, map_mul]
        field_simp
  map_smul' s x := by
    induction x using LocalizedModule.induction_on with
    | h m t =>
      rw [LocalizedModule.smul'_mk, ev_mk, ev_mk, map_smul, smul_div_assoc, RingHom.id_apply]

open Classical in

def evMap (I : ∀ k, Finset (ι k)) :
    LocalizedModule (cellMon F I) (MRingOver F ι ⧸ mIdealOver F y) →ₗ[F] Ω :=
  if h : Good y I then evLin y I h else 0

theorem evMap_mk {I : ∀ k, Finset (ι k)} (hI : Good y I) (g : MRingOver F ι) (t : cellMon F I) :
    evMap y I (LocalizedModule.mk (Ideal.Quotient.mk (mIdealOver F y) g) t) =
      aeval y g / aeval y (t : MRingOver F ι) := by
  unfold evMap
  rw [dif_pos hI]
  exact ev_mk y I hI _ t

end Eval

section Rep

variable {V : Ideal (MRingOver F ι)}

theorem exists_homog_of_mem_quotPart {d : K → ℤ} {m : MRingOver F ι ⧸ V} (hm : m ∈ quotPart F V d) :
    ∃ g : MRingOver F ι, IsMultiHomog g (fun k => (d k).toNat) ∧ ((∀ k, 0 ≤ d k) ∨ g = 0) ∧
      Ideal.Quotient.mk V g = m := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, ⟨hnn, hp⟩, rfl⟩ := hx
    exact ⟨p, hp, Or.inl hnn, rfl⟩
  | zero => exact ⟨0, isMultiHomog_zero _, Or.inr rfl, map_zero _⟩
  | add x x' _ _ h h' =>
    obtain ⟨g, hg, hd, rfl⟩ := h
    obtain ⟨g', hg', hd', rfl⟩ := h'
    refine ⟨g + g', isMultiHomog_add hg hg', ?_, map_add _ _ _⟩
    rcases hd with hd | rfl
    · exact Or.inl hd
    · rcases hd' with hd' | rfl
      · exact Or.inl hd'
      · exact Or.inr (add_zero 0)
  | smul s x _ h =>
    obtain ⟨g, hg, hd, rfl⟩ := h
    refine ⟨s • g, isMultiHomog_smul s hg, ?_, ?_⟩
    · rcases hd with hd | rfl
      · exact Or.inl hd
      · exact Or.inr (smul_zero s)
    · rw [← Ideal.Quotient.mkₐ_eq_mk F, map_smul]

theorem exists_rep {T : Submonoid (MRingOver F ι)} {β : K → ℤ}
    {x : LocalizedModule T (MRingOver F ι ⧸ V)} (hx : x ∈ locPart ι (quotPart F V) T β) :
    ∃ (g : MRingOver F ι) (t : T) (a : K → ℕ), IsMultiHomog (t : MRingOver F ι) a ∧
      IsMultiHomog g (fun k => (β k + a k).toNat) ∧ ((∀ k, 0 ≤ β k + a k) ∨ g = 0) ∧
      x = LocalizedModule.mk (Ideal.Quotient.mk V g) t := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    obtain ⟨g, hg, hd, rfl⟩ := exists_homog_of_mem_quotPart hm
    exact ⟨g, t, a, ht, hg, hd, rfl⟩
  | zero =>
    refine ⟨0, 1, 0, ?_, isMultiHomog_zero _, Or.inr rfl, ?_⟩
    · simpa using isMultiHomog_C (F := F) (ι := ι) 1
    · rw [map_zero, LocalizedModule.zero_mk]
  | add x x' _ _ h h' =>
    obtain ⟨g, t, a, ht, hg, hd, rfl⟩ := h
    obtain ⟨g', t', a', ht', hg', hd', rfl⟩ := h'
    rcases hd with hd | rfl
    swap
    · exact ⟨g', t', a', ht', hg', hd', by rw [map_zero, LocalizedModule.zero_mk, zero_add]⟩
    rcases hd' with hd' | rfl
    swap
    · exact ⟨g, t, a, ht, hg, Or.inl hd, by rw [map_zero, LocalizedModule.zero_mk, add_zero]⟩
    refine ⟨(t' : MRingOver F ι) * g + (t : MRingOver F ι) * g', t * t', a + a', ?_, ?_, Or.inl ?_, ?_⟩
    · simpa using isMultiHomog_mul ht ht'
    · have e1 : (fun k => (β k + ((a + a') k : ℕ)).toNat) = a' + (fun k => (β k + a k).toNat) := by
        funext k
        have := hd k
        simp only [Pi.add_apply, Nat.cast_add]
        omega
      have e2 : (fun k => (β k + ((a + a') k : ℕ)).toNat) = a + (fun k => (β k + a' k).toNat) := by
        funext k
        have := hd' k
        simp only [Pi.add_apply, Nat.cast_add]
        omega
      refine isMultiHomog_add ?_ ?_
      · rw [e1]; exact isMultiHomog_mul ht' hg
      · rw [e2]; exact isMultiHomog_mul ht hg'
    · intro k
      have := hd k
      simp only [Pi.add_apply, Nat.cast_add]
      omega
    · rw [LocalizedModule.mk_add_mk]
      congr 1
  | smul s x _ h =>
    obtain ⟨g, t, a, ht, hg, hd, rfl⟩ := h
    refine ⟨s • g, t, a, ht, isMultiHomog_smul s hg, ?_, ?_⟩
    · rcases hd with hd | rfl
      · exact Or.inl hd
      · exact Or.inr (smul_zero s)
    · rw [LocalizedModule.smul'_mk, ← Ideal.Quotient.mkₐ_eq_mk F, map_smul]

end Rep

variable {Ω : Type} [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)

theorem evMap_injOn {I : ∀ k, Finset (ι k)} (hI : Good y I) (β : K → ℤ) :
    Set.InjOn (evMap (F := F) y I) (locPart ι (quotPart F (mIdealOver F y)) (cellMon F I) β) := by
  intro x hx x' hx' hxx'
  rw [← sub_eq_zero]
  have hs : x - x' ∈ locPart ι (quotPart F (mIdealOver F y)) (cellMon F I) β := sub_mem hx hx'
  have h0 : evMap y I (x - x') = 0 := by rw [map_sub, hxx', sub_self]
  obtain ⟨g, t, a, -, hg, -, he⟩ := exists_rep hs
  rw [he] at h0 ⊢
  rw [evMap_mk y hI, div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · rw [mk_eq_zero_of_aeval y hg h0, LocalizedModule.zero_mk]
  · exact absurd h0 (aeval_ne_zero_of_mem hI t.2)

end CechPointEval

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cellMon cellRes locPart mIdealOver mConeMapOver chartRingOver quotPart)

noncomputable section

namespace CechPointEval

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)

def chart (c : ∀ k, ι k) : ∀ k, Finset (ι k) := fun k => {c k}

theorem prod_X_mem (c : ∀ k, ι k) (e : K → ℕ) :
    ∏ k, (X ⟨k, c k⟩ : MRingOver F ι) ^ e k ∈ cellMon F (chart c) :=
  Submonoid.prod_mem _ fun k _ =>
    Submonoid.pow_mem _ (Submonoid.subset_closure (show (X ⟨k, c k⟩ : MRingOver F ι) ∈
      {f | ∃ k, ∃ i ∈ chart c k, f = X ⟨k, i⟩} from ⟨k, c k, Finset.mem_singleton_self _, rfl⟩)) _

theorem aeval_prod_X (c : ∀ k, ι k) (e : K → ℕ) :
    aeval y (∏ k, (X ⟨k, c k⟩ : MRingOver F ι) ^ e k) = ∏ k, y ⟨k, c k⟩ ^ e k := by
  simp [map_prod]

theorem prod_pow_add (c : ∀ k, ι k) (b b' : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (b + b') k = (∏ k, y ⟨k, c k⟩ ^ b k) * ∏ k, y ⟨k, c k⟩ ^ b' k := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => pow_add _ _ _

theorem aeval_div_mem_chartRing (c : ∀ k, ι k) {p : MRingOver F ι} {d : K → ℕ} (hp : IsMultiHomog p d) :
    aeval y p / ∏ k, y ⟨k, c k⟩ ^ d k ∈ chartRingOver F y c := by
  classical
  rw [p.as_sum, map_sum, Finset.sum_div]
  refine Subalgebra.sum_mem _ fun μ hμ => ?_
  have hdeg := hp μ hμ
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have key : (∏ q : Σ k, ι k, y q ^ μ q) / ∏ k, y ⟨k, c k⟩ ^ d k =
      ∏ q : Σ k, ι k, (y q / y ⟨q.1, c q.1⟩) ^ μ q := by
    rw [Finset.prod_congr rfl fun q _ => div_pow (y q) _ (μ q), Finset.prod_div_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show _ = ∏ i, y ⟨k, c k⟩ ^ μ ⟨k, i⟩
    rw [Finset.prod_pow_eq_pow_sum, hdeg k]
  rw [mul_div_assoc, key, ← Algebra.smul_def]
  exact Subalgebra.smul_mem _ (Subalgebra.prod_mem _ fun q _ => Subalgebra.pow_mem _
    (Algebra.subset_adjoin (Set.mem_range_self (f := fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) q)) _) _

theorem exists_of_mem_chartRing (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {w : Ω}
    (hw : w ∈ chartRingOver F y c) :
    ∃ (b : K → ℕ) (h : MRingOver F ι), IsMultiHomog h b ∧ w = aeval y h / ∏ k, y ⟨k, c k⟩ ^ b k := by
  classical
  have hP : ∀ b : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ b k ≠ 0 :=
    fun b => Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  induction hw using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨q, rfl⟩ := hx
    refine ⟨Pi.single q.1 1, X q, by simpa using isMultiHomog_X_pow (F := F) q.1 q.2 1, ?_⟩
    rw [aeval_X, Finset.prod_eq_single q.1]
    · simp
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, pow_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  | algebraMap r =>
    exact ⟨0, C r, isMultiHomog_C r, by simp⟩
  | add x x' _ _ h h' =>
    obtain ⟨b, p, hp, rfl⟩ := h
    obtain ⟨b', p', hp', rfl⟩ := h'
    refine ⟨b + b', p * ∏ k, X ⟨k, c k⟩ ^ b' k + p' * ∏ k, X ⟨k, c k⟩ ^ b k, ?_, ?_⟩
    · refine isMultiHomog_add (isMultiHomog_mul hp (isMultiHomog_prod_X c b')) ?_
      rw [add_comm b b']
      exact isMultiHomog_mul hp' (isMultiHomog_prod_X c b)
    · rw [map_add, map_mul, map_mul, aeval_prod_X, aeval_prod_X, prod_pow_add]
      field_simp [hP b, hP b']
  | mul x x' _ _ h h' =>
    obtain ⟨b, p, hp, rfl⟩ := h
    obtain ⟨b', p', hp', rfl⟩ := h'
    refine ⟨b + b', p * p', isMultiHomog_mul hp hp', ?_⟩
    rw [map_mul, prod_pow_add, div_mul_div_comm]

theorem image_eq_chart (hfield : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → IsField (chartRingOver F y c))
    {I : ∀ k, Finset (ι k)} (hI : Good y I) {c : ∀ k, ι k} (hcI : ∀ k, c k ∈ I k) (β : K → ℤ) :
    (locPart ι (quotPart F (mIdealOver F y)) (cellMon F I) β).map (evMap y I) =
      (locPart ι (quotPart F (mIdealOver F y)) (cellMon F (chart c)) β).map (evMap y (chart c)) := by
  classical
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hI k (c k) (hcI k)
  have hcg : Good y (chart c) := fun k i hi => by rw [Finset.mem_singleton.mp hi]; exact hc k
  have hsub : ∀ k, chart c k ⊆ I k := fun k => Finset.singleton_subset_iff.mpr (hcI k)
  have hP : ∀ b : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ b k ≠ 0 :=
    fun b => Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hres : ∀ x, evMap y I (cellRes F _ (chart c) I x) = evMap y (chart c) x := by
    intro x
    induction x using LocalizedModule.induction_on with
    | h m t =>
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective m
      rw [CechPointVanish.cellRes_mk (CechPointVanish.cellMon_mono hsub), evMap_mk y hI, evMap_mk y hcg]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨g, t, a, ht, hg, hd, rfl⟩ := exists_rep hx
    rcases hd with hd | rfl
    swap
    · rw [map_zero, LocalizedModule.zero_mk, map_zero]
      exact Submodule.zero_mem _
    have ht0 := aeval_ne_zero_of_mem hI t.2
    have hu := aeval_div_mem_chartRing y c ht
    have hu0 : (⟨_, hu⟩ : chartRingOver F y c) ≠ 0 :=
      fun h => div_ne_zero ht0 (hP a) (congrArg Subtype.val h)
    obtain ⟨v, hv⟩ := (hfield c hc).mul_inv_cancel hu0
    obtain ⟨b, h, hh, hvh⟩ := exists_of_mem_chartRing y c hc v.2
    have hprod : aeval y (t : MRingOver F ι) * aeval y h =
        (∏ k, y ⟨k, c k⟩ ^ a k) * ∏ k, y ⟨k, c k⟩ ^ b k := by
      have e := congrArg Subtype.val hv
      simp only [Subalgebra.coe_mul, Subalgebra.coe_one] at e
      rw [hvh] at e
      field_simp [hP a, hP b] at e
      linear_combination e
    have hh0 : aeval y h ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hprod
      exact mul_ne_zero (hP a) (hP b) hprod.symm
    refine ⟨LocalizedModule.mk (Ideal.Quotient.mk _ (g * h)) ⟨_, prod_X_mem c (a + b)⟩, ?_, ?_⟩
    · refine Submodule.subset_span ⟨_, ⟨_, prod_X_mem c (a + b)⟩, a + b, isMultiHomog_prod_X c (a + b),
        Submodule.subset_span ⟨g * h, ⟨?_, ?_⟩, rfl⟩, rfl⟩
      · intro k
        have := hd k
        simp only [Pi.add_apply, Nat.cast_add]
        omega
      · have e : (fun k => ((β + fun k => ((a + b) k : ℤ)) k).toNat) = (fun k => (β k + a k).toNat) + b := by
          funext k
          have := hd k
          simp only [Pi.add_apply, Nat.cast_add]
          omega
        rw [e]
        exact isMultiHomog_mul hg hh
    · rw [evMap_mk y hcg, evMap_mk y hI, map_mul, aeval_prod_X, prod_pow_add, ← hprod]
      exact mul_div_mul_right _ _ hh0
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨cellRes F _ (chart c) I x,
      CechPointVanish.cellRes_mem_locPart (CechPointVanish.cellMon_mono hsub) β hx, hres x⟩

end CechPointEval

theorem CechPointEval.full : CechPointEval.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y hfield β
  classical
  by_cases h0 : ∃ c₀ : ∀ k, ι k, ∀ k, y ⟨k, c₀ k⟩ ≠ 0
  · obtain ⟨c₀, hc₀⟩ := h0
    refine ⟨(locPart ι (quotPart F (mIdealOver F y)) (cellMon F (CechPointEval.chart c₀)) β).map
      (CechPointEval.evMap y (CechPointEval.chart c₀)), CechPointEval.evMap y,
      fun I hIne hI => ⟨fun g t => CechPointEval.evMap_mk y hI g t, CechPointEval.evMap_injOn y hI β, ?_⟩⟩
    choose c hc using hIne
    let U : ∀ k, Finset (ι k) := fun k => {c k, c₀ k}
    have hU : CechPointEval.Good y U := by
      intro k i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hI k _ (hc k)
      · rw [Finset.mem_singleton.mp hi]
        exact hc₀ k
    rw [CechPointEval.image_eq_chart y hfield hI hc,
      ← CechPointEval.image_eq_chart y hfield hU (c := c) (fun k => by simp [U]),
      CechPointEval.image_eq_chart y hfield hU (c := c₀) (fun k => by simp [U])]
  · refine ⟨⊥, CechPointEval.evMap y, fun I hIne hI => absurd ?_ h0⟩
    choose c hc using hIne
    exact ⟨c, fun k => hI k (c k) (hc k)⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem CechPointVanish.full : CechPointVanish.Statement :=
  CechPointVanish.proof CechConstVanish.full CechPointEval.full

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
