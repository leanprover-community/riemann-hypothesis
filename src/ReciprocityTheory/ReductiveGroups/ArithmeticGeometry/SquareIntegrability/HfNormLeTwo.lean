import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS

section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MvPolynomial

noncomputable section

variable {E : Type} [Field E] [NumberField E] {n nb : ℕ} {dim : (E →+* ℂ) → ℕ}

section Expand
variable (bs : Fin nb → Block E n dim)

abbrev Choice := ∀ j : Fin nb, Fin (bs j).c → Equiv.Perm (Fin (bs j).i)

abbrev Slot := Σ j : Fin nb, Fin (bs j).c × Fin (bs j).i

def sgnT (T : Choice bs) : ℂ := ∏ j, ∏ r, ((Equiv.Perm.sign (T j r) : ℤ) : ℂ)

def letter (T : Choice bs) (t : Slot bs) : Letter n dim :=
  ((bs t.1).col t.2.2, ⟨(bs t.1).τ, Fin.castLE (bs t.1).hi (T t.1 t.2.1 t.2.2)⟩)

theorem block_poly_expand (B : Block E n dim) :
    B.poly = ∑ p : Fin B.c → Equiv.Perm (Fin B.i),
      (∏ r, ((Equiv.Perm.sign (p r) : ℤ) : MvPolynomial (Letter n dim) ℂ)) *
        ∏ r, ∏ b, X (B.col b, ⟨B.τ, Fin.castLE B.hi (p r b)⟩) := by
  rw [Block.poly, Matrix.det_apply', ← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.prod_mul_distrib]
  rfl

theorem determinantPoly_expand :
    P1 bs = ∑ T : Choice bs, sgnT bs T • ∏ t : Slot bs, X (letter bs T t) := by
  rw [P1]
  simp only [block_poly_expand]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_mul_distrib, MvPolynomial.smul_eq_C_mul]
  congr 1
  · simp only [sgnT, map_prod, map_intCast]
  · rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Fintype.prod_prod_type]
    rfl

end Expand

section PD
variable (X : PT E) (bs : Fin nb → Block E n X.dim)

open Classical in

def lst (T : Choice bs) : List (Fin n × Vsp X.dim) :=
  (Multiset.map (letter bs T) Finset.univ.val).toList.map
    (fun l => (l.1, EuclideanSpace.single l.2 (1 : ℂ)))

theorem prod_X_letter (T : Choice bs) :
    (∏ t : Slot bs, MvPolynomial.X (letter bs T t) : MvPolynomial (Letter n X.dim) ℂ) =
      monomial (∑ t : Slot bs, Finsupp.single (letter bs T t) 1) 1 := by
  rw [MvPolynomial.monomial_sum_one]
  rfl

theorem toMultiset_letters (T : Choice bs) :
    Finsupp.toMultiset (∑ t : Slot bs, Finsupp.single (letter bs T t) 1) =
      Multiset.map (letter bs T) Finset.univ.val := by
  rw [map_sum]
  simp only [Finsupp.toMultiset_single, one_nsmul]
  rw [Finset.sum_eq_multiset_sum]
  have h : ∀ (s : Multiset (Slot bs)),
      (s.map fun t => ({letter bs T t} : Multiset (Letter n X.dim))).sum = s.map (letter bs T) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih => simp [ih]
  exact h _

theorem polyDeriv_determinantPoly_tensor (s : Fin n → (Fin 1 → Vsp X.dim) → ℂ)
    (hs : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (s k)) :
    polyDeriv (P1 bs) dir (tens X s) 0 =
      ∑ T : Choice bs, sgnT bs T * ∏ k, d1 (s k) (colL (lst X bs T) k).length
        (fun j => (colL (lst X bs T) k).get j) := by
  rw [determinantPoly_expand, jof_polyDeriv_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [polyDeriv_smul, prod_X_letter, polyDeriv_monomial_one, pdTerm_eq_itD, toMultiset_letters]
  congr 1
  have hl : (Multiset.map (letter bs T) Finset.univ.val).toList.map dir =
      (lst X bs T).map (fun p => Pi.single p.1 p.2) := by
    rw [lst, List.map_map]
    rfl
  rw [hl]
  have hg : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (fun z : Vsp X.dim => s k (fun _ => z)) := fun k =>
    (hs k).comp (contDiff_pi.2 fun _ => contDiff_id)
  have h1 := itD_prod hg (lst X bs T) 0
  rw [show tens X s = fun v : Fin n → Vsp X.dim => ∏ k, s k (fun _ => v k) from rfl, h1]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Pi.zero_apply, itD_col (hs k)]
  rfl

open Classical in

theorem colL_coe (T : Choice bs) (k : Fin n) :
    ((colL (lst X bs T) k : List (Vsp X.dim)) : Multiset (Vsp X.dim)) =
      ((Multiset.map (letter bs T) Finset.univ.val).filter (fun l => l.1 = k)).map
        (fun l => EuclideanSpace.single l.2 (1 : ℂ)) := by
  rw [colL, lst, List.filter_map, List.map_map, ← Multiset.map_coe]
  conv_rhs => rw [← Multiset.coe_toList (Multiset.map (letter bs T) Finset.univ.val),
    Multiset.filter_coe, Multiset.map_coe]
  rfl

end PD

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section
namespace ReciprocityTheory.ChartRestriction.G.I2

noncomputable section

variable {E : Type} [Field E] [NumberField E] {n nb : ℕ}

section Cols
variable {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim)

def colB (p : Σ j : Fin nb, Fin (bs j).i) : Fin n := (bs p.1).col p.2

variable {bs}

theorem colB_inj (hD : Disj bs) : Function.Injective (colB bs) := by
  rintro ⟨j, a⟩ ⟨j', a'⟩ h
  by_cases hj : j = j'
  · subst hj
    have ha : a = a' := (bs j).col_inj h
    subst ha
    rfl
  · exact absurd h (hD j j' hj a a')

variable (bs)

open Classical in

def owner (k : Fin n) : Option (Σ j : Fin nb, Fin (bs j).i) :=
  if h : ∃ p, colB bs p = k then some h.choose else none

variable {bs}

theorem owner_colB (hD : Disj bs) (p : Σ j : Fin nb, Fin (bs j).i) : owner bs (colB bs p) = some p := by
  have h' : ∃ q, colB bs q = colB bs p := ⟨p, rfl⟩
  rw [owner, dif_pos h']
  exact congrArg some (colB_inj hD h'.choose_spec)

theorem colB_of_owner {k : Fin n} {p : Σ j : Fin nb, Fin (bs j).i} (h : owner bs k = some p) :
    colB bs p = k := by
  by_cases h' : ∃ q, colB bs q = k
  · rw [owner, dif_pos h'] at h
    obtain rfl := Option.some_injective _ h
    exact h'.choose_spec
  · rw [owner, dif_neg h'] at h
    cases h

theorem owner_eq_none {k : Fin n} (h : ∀ p, colB bs p ≠ k) : owner bs k = none := by
  rw [owner, dif_neg (show ¬∃ q, colB bs q = k from fun ⟨q, hq⟩ => h q hq)]

theorem owner_none_iff (hD : Disj bs) (k : Fin n) : owner bs k = none ↔ ∀ p, colB bs p ≠ k := by
  refine ⟨fun h p hp => ?_, owner_eq_none⟩
  subst hp
  rw [owner_colB hD] at h
  cases h

theorem prod_cols {M : Type*} [CommMonoid M] (hD : Disj bs) (f : Fin n → M) :
    ∏ k, f k = (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), f k) * ∏ p, f (colB bs p) := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => owner bs k = none)]
  congr 1
  rw [← Finset.prod_image (s := Finset.univ) (g := colB bs) (by
    intro a _ b _ h
    exact colB_inj hD h)]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, owner_none_iff hD,
    not_forall, ne_eq, not_not]

end Cols

section Letters
variable (X : PT E) {bs : Fin nb → Block E n X.dim}

theorem filter_positions (hD : Disj bs) (T : Choice bs) (p : Σ j : Fin nb, Fin (bs j).i) :
    (Multiset.map (letter bs T) Finset.univ.val).filter (fun l => l.1 = colB bs p) =
      Multiset.map (fun r : Fin (bs p.1).c => letter bs T ⟨p.1, (r, p.2)⟩) Finset.univ.val := by
  obtain ⟨j0, a0⟩ := p
  rw [Multiset.filter_map]
  calc _ = Multiset.map (letter bs T)
        (Multiset.map (fun r : Fin (bs j0).c => (⟨j0, (r, a0)⟩ : Slot bs)) Finset.univ.val) := by
        congr 1
        refine (Multiset.Nodup.ext (Finset.univ.nodup.filter _)
          (Finset.univ.nodup.map (fun r r' h => by simpa using h))).2 ?_
        rintro ⟨j, r, a⟩
        simp only [Multiset.mem_filter, Finset.mem_val, Finset.mem_univ, true_and, Function.comp,
          Multiset.mem_map]
        constructor
        · intro h
          have hja : (⟨j, a⟩ : Σ j : Fin nb, Fin (bs j).i) = ⟨j0, a0⟩ := colB_inj hD h
          cases hja
          exact ⟨r, rfl⟩
        · rintro ⟨r', h⟩
          cases h
          rfl
    _ = _ := by rw [Multiset.map_map]; rfl

open Classical in
theorem colL_block (hD : Disj bs) (T : Choice bs) (p : Σ j : Fin nb, Fin (bs j).i) :
    ((colL (lst X bs T) (colB bs p) : List (Vsp X.dim)) : Multiset (Vsp X.dim)) =
      Multiset.map (fun r : Fin (bs p.1).c => EuclideanSpace.single
        (⟨(bs p.1).τ, Fin.castLE (bs p.1).hi (T p.1 r p.2)⟩ : Idx X.dim) (1 : ℂ)) Finset.univ.val := by
  have hc : ∀ (L : List (Fin n × Vsp X.dim)) (k : Fin n),
      ((colL L k : List (Vsp X.dim)) : Multiset (Vsp X.dim)) =
        Multiset.map Prod.snd (Multiset.filter (fun x => x.1 = k) (L : Multiset _)) := by
    intro L k
    simp [colL]
  rw [hc, lst, ← Multiset.map_coe, Multiset.coe_toList, Multiset.filter_map, Multiset.map_map]
  have h2 := congrArg (Multiset.map (fun l : Letter n X.dim => EuclideanSpace.single l.2 (1 : ℂ)))
    (filter_positions X hD T p)
  rw [Multiset.map_map] at h2
  convert h2 using 2
  all_goals first
    | rfl
    | exact Multiset.filter_congr fun _ _ => Iff.rfl

theorem colL_empty (hD : Disj bs) (T : Choice bs) {k : Fin n} (hk : owner bs k = none) :
    colL (lst X bs T) k = [] := by
  rw [owner_none_iff hD] at hk
  unfold colL
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro x hx
  unfold lst at hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  obtain ⟨t, -, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_toList.1 hl)
  intro h
  exact hk ⟨t.1, t.2.2⟩ (of_decide_eq_true h)

end Letters

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section
namespace ReciprocityTheory.ChartRestriction.G.I2

noncomputable section

variable {E : Type} [Field E] [NumberField E] {n nb : ℕ}

section Col
variable {dim : (E →+* ℂ) → ℕ}


theorem iteratedDeriv_list_bound (s : (Fin 1 → Vsp dim) → ℂ) (c : ℕ) (μ : ℂ) (y : Vsp dim) (ε : ℝ)
    (σ : E →+* ℂ)
    (hbd : ∀ xs : Fin c → Vsp dim, (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
      ‖d1 s c xs - μ * ∏ k, Hf (xs k) y‖ ≤ ε)
    (l : List (Vsp dim)) (g : Fin c → Vsp dim)
    (hl : (l : Multiset (Vsp dim)) = Multiset.map g Finset.univ.val)
    (hg : ∀ r, InPart σ (g r) ∧ ‖g r‖ = 1) :
    ‖d1 s l.length (fun j => l.get j) - μ * ∏ r, Hf (g r) y‖ ≤ ε := by
  have hlen : l.length = c := by
    have := congrArg Multiset.card hl
    simpa using this
  subst hlen
  have hmem : ∀ j : Fin l.length, InPart σ (l.get j) ∧ ‖l.get j‖ = 1 := by
    intro j
    have : l.get j ∈ Multiset.map g Finset.univ.val := by
      rw [← hl]; exact Multiset.mem_coe.2 (List.get_mem l j)
    obtain ⟨r, -, hr⟩ := Multiset.mem_map.1 this
    rw [← hr]; exact hg r
  have hm : Finset.univ.val.map (fun j : Fin l.length => l.get j) = (l : Multiset (Vsp dim)) := by
    rw [Fin.univ_val_map]
    congr 1
    first
    | exact List.ofFn_get l
    | exact List.ofFn_getElem l
    | simp
  have hprod : ∏ j : Fin l.length, Hf (l.get j) y = ∏ r, Hf (g r) y := by
    calc ∏ j : Fin l.length, Hf (l.get j) y
        = ((Finset.univ.val.map (fun j : Fin l.length => l.get j)).map (fun x => Hf x y)).prod := by
          rw [Multiset.map_map]; rfl
      _ = ∏ r, Hf (g r) y := by
          rw [hm, hl, Multiset.map_map]; rfl
  have := hbd (fun j => l.get j) hmem
  rw [hprod] at this
  exact this

theorem d1_zero (s : (Fin 1 → Vsp dim) → ℂ) (v : Fin 0 → Vsp dim) : d1 s 0 v = s 0 := by
  unfold d1
  exact iteratedFDeriv_zero_apply _

end Col

section Main
variable {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim)

open Classical in

def eU (j : Fin nb) (a : Fin (bs j).i) : Vsp dim :=
  EuclideanSpace.single (⟨(bs j).τ, Fin.castLE (bs j).hi a⟩ : Idx dim) (1 : ℂ)

def idealA (μ : (Σ j : Fin nb, Fin (bs j).i) → ℂ) (y : (Σ j : Fin nb, Fin (bs j).i) → Vsp dim)
    (ee : Fin n → ℂ) (T : Choice bs) (k : Fin n) : ℂ :=
  match owner bs k with
  | some p => μ p * ∏ r, Hf (eU bs p.1 (T p.1 r p.2)) (y p)
  | none => ee k

def blockM (y : (Σ j : Fin nb, Fin (bs j).i) → Vsp dim) (j : Fin nb) :
    Matrix (Fin (bs j).i) (Fin (bs j).i) ℂ :=
  Matrix.of fun a b => Hf (eU bs j a) (y ⟨j, b⟩)

theorem main_term (hD : Disj bs) (μ : (Σ j : Fin nb, Fin (bs j).i) → ℂ)
    (y : (Σ j : Fin nb, Fin (bs j).i) → Vsp dim) (ee : Fin n → ℂ) :
    ∑ T : Choice bs, sgnT bs T * ∏ k, idealA bs μ y ee T k =
      (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ee k) * (∏ p, μ p) *
        ∏ j, (blockM bs y j).det ^ (bs j).c := by
  have hinj : Function.Injective (colB bs) := by
    rintro ⟨j, a⟩ ⟨j', a'⟩ h
    simp only [colB] at h
    by_cases hj : j = j'
    · subst hj
      have := (bs j).col_inj h
      subst this
      rfl
    · exact absurd h (hD j j' hj a a')
  have hown : ∀ p, owner bs (colB bs p) = some p := by
    intro p
    have hex : ∃ p', colB bs p' = colB bs p := ⟨p, rfl⟩
    unfold owner
    rw [dif_pos hex]
    exact congrArg some (hinj hex.choose_spec)
  have hnone : ∀ k, owner bs k = none ↔ k ∉ Finset.univ.image (colB bs) := by
    intro k
    constructor
    · intro h hk
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hk
      rw [hown] at h
      exact Option.some_ne_none _ h
    · intro h
      unfold owner
      rw [dif_neg]
      rintro ⟨p, rfl⟩
      exact h (Finset.mem_image_of_mem _ (Finset.mem_univ p))
  have hT : ∀ T : Choice bs, ∏ k, idealA bs μ y ee T k =
      (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ee k) *
        ∏ p, (μ p * ∏ r, Hf (eU bs p.1 (T p.1 r p.2)) (y p)) := by
    intro T
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => owner bs k = none)]
    congr 1
    · refine Finset.prod_congr rfl fun k hk => ?_
      have h := (Finset.mem_filter.mp hk).2
      simp only [idealA, h]
    · have hset : Finset.univ.filter (fun k => ¬ owner bs k = none) = Finset.univ.image (colB bs) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hnone]
        exact not_not
      rw [hset, Finset.prod_image (fun p _ q _ h => hinj h)]
      refine Finset.prod_congr rfl fun p _ => ?_
      simp only [idealA, hown]
  have hdet : ∀ j, (blockM bs y j).det ^ (bs j).c =
      ∏ r : Fin (bs j).c, ∑ σ : Equiv.Perm (Fin (bs j).i),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ b, Hf (eU bs j (σ b)) (y ⟨j, b⟩) := by
    intro j
    rw [Fin.prod_const, Matrix.det_apply]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    rfl
  have hsum : ∑ T : Choice bs, sgnT bs T * ∏ p, ∏ r, Hf (eU bs p.1 (T p.1 r p.2)) (y p) =
      ∏ j, (blockM bs y j).det ^ (bs j).c := by
    simp_rw [hdet]
    first
    | simp_rw [Fintype.prod_sum]
    | simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [Finset.prod_mul_distrib, sgnT]
    congr 1
    first
    | rw [Fintype.prod_sigma]
    | rw [← Finset.univ_sigma_univ, Finset.prod_sigma]
    refine Finset.prod_congr rfl fun j _ => ?_
    first
    | rw [Finset.prod_comm]
    | exact Finset.prod_comm.symm
  calc ∑ T, sgnT bs T * ∏ k, idealA bs μ y ee T k
      = ∑ T : Choice bs, ((∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ee k) * ∏ p, μ p) *
          (sgnT bs T * ∏ p, ∏ r, Hf (eU bs p.1 (T p.1 r p.2)) (y p)) := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [hT, Finset.prod_mul_distrib]
        ring
    _ = _ := by rw [← Finset.mul_sum, hsum]

end Main

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section
namespace ReciprocityTheory.ChartRestriction.G.I2

theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (x y : ι → ℂ) (β δ : ι → ℝ)
    (hy : ∀ i, ‖y i‖ ≤ β i) (hxy : ∀ i, ‖x i - y i‖ ≤ δ i) :
    ‖∏ i ∈ s, x i - ∏ i ∈ s, y i‖ ≤ ∏ i ∈ s, (β i + δ i) - ∏ i ∈ s, β i := by
  classical
  have hβ : ∀ i, 0 ≤ β i := fun i => (norm_nonneg _).trans (hy i)
  have hδ : ∀ i, 0 ≤ δ i := fun i => (norm_nonneg _).trans (hxy i)
  have hx : ∀ i, ‖x i‖ ≤ β i + δ i := fun i => by
    calc ‖x i‖ = ‖y i + (x i - y i)‖ := by ring_nf
      _ ≤ ‖y i‖ + ‖x i - y i‖ := norm_add_le _ _
      _ ≤ β i + δ i := add_le_add (hy i) (hxy i)
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    have hX : ‖∏ i ∈ s, x i‖ ≤ ∏ i ∈ s, (β i + δ i) := by
      rw [norm_prod]
      exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hx i)
    have hP : ∏ i ∈ s, β i ≤ ∏ i ∈ s, (β i + δ i) :=
      Finset.prod_le_prod (fun i _ => hβ i) (fun i _ => le_add_of_nonneg_right (hδ i))
    calc ‖x a * ∏ i ∈ s, x i - y a * ∏ i ∈ s, y i‖
        = ‖(x a - y a) * ∏ i ∈ s, x i + y a * (∏ i ∈ s, x i - ∏ i ∈ s, y i)‖ := by ring_nf
      _ ≤ ‖(x a - y a) * ∏ i ∈ s, x i‖ + ‖y a * (∏ i ∈ s, x i - ∏ i ∈ s, y i)‖ := norm_add_le _ _
      _ = ‖x a - y a‖ * ‖∏ i ∈ s, x i‖ + ‖y a‖ * ‖∏ i ∈ s, x i - ∏ i ∈ s, y i‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ δ a * ∏ i ∈ s, (β i + δ i) + β a * (∏ i ∈ s, (β i + δ i) - ∏ i ∈ s, β i) := by
          exact add_le_add (mul_le_mul (hxy a) hX (norm_nonneg _) (hδ a))
            (mul_le_mul (hy a) ih (norm_nonneg _) (hβ a))
      _ = (β a + δ a) * ∏ i ∈ s, (β i + δ i) - β a * ∏ i ∈ s, β i := by ring

theorem norm_sum_prod_sub_le {τ ι : Type*} [Fintype τ] [Fintype ι] (sg : τ → ℂ)
    (hsg : ∀ T, ‖sg T‖ ≤ 1) (D A : τ → ι → ℂ) (α δ : ι → ℝ) (hA : ∀ T k, ‖A T k‖ ≤ α k)
    (hD : ∀ T k, ‖D T k - A T k‖ ≤ δ k) :
    ‖∑ T, sg T * ∏ k, D T k - ∑ T, sg T * ∏ k, A T k‖ ≤
      Fintype.card τ * (∏ k, (α k + δ k) - ∏ k, α k) := by
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ T, (sg T * ∏ k, D T k - sg T * ∏ k, A T k)‖
      ≤ ∑ T, ‖sg T * ∏ k, D T k - sg T * ∏ k, A T k‖ := norm_sum_le _ _
    _ ≤ ∑ _T : τ, (∏ k, (α k + δ k) - ∏ k, α k) := by
        refine Finset.sum_le_sum fun T _ => ?_
        rw [← mul_sub, norm_mul]
        have h := norm_prod_sub_prod_le Finset.univ (D T) (A T) α δ (hA T) (hD T)
        calc ‖sg T‖ * ‖∏ k, D T k - ∏ k, A T k‖ ≤ 1 * ‖∏ k, D T k - ∏ k, A T k‖ := by
              gcongr
              exact hsg T
          _ ≤ _ := by rw [one_mul]; exact h
    _ = Fintype.card τ * (∏ k, (α k + δ k) - ∏ k, α k) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem one_add_pow_sub_one_le (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    (1 + x) ^ m - 1 ≤ m * x * (1 + x) ^ m := by
  induction m with
  | zero => simp
  | succ n ih =>
    have h1 : (1 : ℝ) ≤ (1 + x) ^ n := by
      have h : (1 : ℝ) ^ n ≤ (1 + x) ^ n := by gcongr; linarith
      simpa using h
    have h2 : (1 : ℝ) ≤ (1 + x) ^ n * (1 + x) := by nlinarith
    have h3 := mul_le_mul_of_nonneg_right ih (by linarith : (0 : ℝ) ≤ 1 + x)
    push_cast
    rw [pow_succ]
    nlinarith [mul_nonneg hx (sub_nonneg.2 h2)]

theorem num_bound (r D : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ Real.exp (-((D + 1) * (r * Real.log r + 3 * r + 3)))) :
    2 * D * (4 * r) ^ D * Real.exp ((r / 2 + 1) * D) * ε ≤ 1 := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]; nlinarith
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have h2D : 2 * (D : ℝ) ≤ Real.exp (2 * D) := by linarith [Real.add_one_le_exp (2 * (D : ℝ))]
  have hpow : ((4 : ℝ) * r) ^ D = Real.exp (D * Real.log (4 * r)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hlog : Real.log (4 * r) = Real.log 4 + Real.log r :=
    Real.log_mul (by norm_num) (by positivity)
  have hP : 2 * (D : ℝ) * (4 * r) ^ D * Real.exp ((r / 2 + 1) * D) ≤
      Real.exp ((D + 1) * (r * Real.log r + 3 * r + 3)) := by
    rw [hpow]
    calc 2 * (D : ℝ) * Real.exp (D * Real.log (4 * r)) * Real.exp ((r / 2 + 1) * D)
        ≤ Real.exp (2 * D) * Real.exp (D * Real.log (4 * r)) * Real.exp ((r / 2 + 1) * D) := by
          gcongr
      _ = Real.exp (2 * D + D * Real.log (4 * r) + (r / 2 + 1) * D) := by
          rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp ((D + 1) * (r * Real.log r + 3 * r + 3)) := by
          apply Real.exp_le_exp.2
          rw [hlog]
          nlinarith [mul_nonneg hD0 (mul_nonneg (sub_nonneg.2 hr1) hlogr),
            mul_nonneg hD0 (sub_nonneg.2 hlog4), mul_nonneg hD0 (sub_nonneg.2 hr1),
            mul_nonneg hr0.le hlogr]
  calc 2 * (D : ℝ) * (4 * r) ^ D * Real.exp ((r / 2 + 1) * D) * ε
      ≤ Real.exp ((D + 1) * (r * Real.log r + 3 * r + 3)) *
          Real.exp (-((D + 1) * (r * Real.log r + 3 * r + 3))) :=
        mul_le_mul hP hε hε0 (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

theorem eps_bound (g d : ℕ) (t K : ℝ) (h : g * Real.log 2 + 2 * d + 3 + K ≤ t) :
    7 * 2 ^ g * (4.3 : ℝ) ^ d * Real.exp (-t) ≤ Real.exp (-K) := by
  have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h7 : (7 : ℝ) ≤ Real.exp 3 := by
    have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc (7 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
      _ ≤ Real.exp 1 ^ 3 := by gcongr
  have h43 : (4.3 : ℝ) ≤ Real.exp 2 := by
    have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc (4.3 : ℝ) ≤ 2.7182818283 ^ 2 := by norm_num
      _ ≤ Real.exp 1 ^ 2 := by gcongr
  have h2g : (2 : ℝ) ^ g = Real.exp (g * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have h43d : (4.3 : ℝ) ^ d ≤ Real.exp (d * 2) := by
    rw [Real.exp_nat_mul]
    gcongr
  calc 7 * 2 ^ g * (4.3 : ℝ) ^ d * Real.exp (-t)
      ≤ Real.exp 3 * Real.exp (g * Real.log 2) * Real.exp (d * 2) * Real.exp (-t) := by
        rw [h2g]; gcongr
    _ = Real.exp (3 + g * Real.log 2 + d * 2 + -t) := by simp only [Real.exp_add]
    _ ≤ Real.exp (-K) := Real.exp_le_exp.2 (by linarith)

end ReciprocityTheory.ChartRestriction.G.I2
end

section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

def VP {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : Submodule ℂ (Vsp dim) where
  carrier := {v | InPart σ v}
  add_mem' := fun {a b} ha hb j hj => by simp [ha j hj, hb j hj]
  zero_mem' := fun j _ => rfl
  smul_mem' := fun c v hv j hj => by simp [hv j hj]

open Classical in

def prj {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) : Vsp dim :=
  WithLp.toLp 2 fun j => if j.1 = σ then v j else 0

def mulc {dim : (E →+* ℂ) → ℕ} (c : (E →+* ℂ) → ℂ) (v : Vsp dim) : Vsp dim :=
  WithLp.toLp 2 fun j => c j.1 * v j

theorem emb_sep {σ τ : E →+* ℂ} (h : σ ≠ τ) : ∃ α : 𝓞 E, σ (α : E) ≠ τ (α : E) := by
  by_contra hc
  push Not at hc
  apply h
  exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => hc x)

theorem mulc_mem {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim))
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (σ : E →+* ℂ) :
    ∀ v ∈ Submodule.span ℂ (I : Set (Vsp dim)), prj σ v ∈ Submodule.span ℂ (I : Set (Vsp dim)) := by
  classical
  set S := Submodule.span ℂ (I : Set (Vsp dim)) with hS

  have hact : ∀ (α : 𝓞 E), ∀ v ∈ S, act α v ∈ S := by
    intro α
    let A : Vsp dim →ₗ[ℂ] Vsp dim :=
      { toFun := act α
        map_add' := fun x y => by ext j; simp [act]; ring
        map_smul' := fun c x => by ext j; simp [act]; ring }
    have hle : S.map A ≤ S := by
      rw [hS, Submodule.map_span]
      apply Submodule.span_le.2
      rintro _ ⟨x, hx, rfl⟩
      exact Submodule.subset_span (hst α x hx)
    intro v hv
    exact hle ⟨v, hv, rfl⟩

  have hα : ∀ τ : E →+* ℂ, ∃ α : 𝓞 E, τ ≠ σ → σ (α : E) ≠ τ (α : E) := by
    intro τ
    by_cases h : τ = σ
    · exact ⟨0, fun h' => (h' h).elim⟩
    · obtain ⟨α, hα⟩ := emb_sep (Ne.symm h)
      exact ⟨α, fun _ => hα⟩
  choose α hα using hα
  let c : (E →+* ℂ) → (E →+* ℂ) → ℂ := fun τ τ' =>
    (τ' (α τ : E) - τ (α τ : E)) * (σ (α τ : E) - τ (α τ : E))⁻¹
  have hstep : ∀ τ, ∀ v ∈ S, mulc (c τ) v ∈ S := by
    intro τ v hv
    have : mulc (c τ) v = (σ (α τ : E) - τ (α τ : E))⁻¹ • (act (α τ) v - (τ (α τ : E)) • v) := by
      ext j; simp [mulc, act, c]; ring
    rw [this]
    exact S.smul_mem _ (S.sub_mem (hact _ v hv) (S.smul_mem _ hv))
  have hprod : ∀ T : Finset (E →+* ℂ), ∀ v ∈ S, mulc (fun τ' => ∏ τ ∈ T, c τ τ') v ∈ S := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro v hv
      have : mulc (fun τ' => ∏ τ ∈ (∅ : Finset (E →+* ℂ)), c τ τ') v = v := by ext j; simp [mulc]
      rw [this]; exact hv
    | insert τ T hτ ih =>
      intro v hv
      have : mulc (fun τ' => ∏ t ∈ insert τ T, c t τ') v = mulc (c τ) (mulc (fun τ' => ∏ t ∈ T, c t τ') v) := by
        ext j; simp [mulc, Finset.prod_insert hτ]; ring
      rw [this]
      exact hstep τ _ (ih v hv)
  intro v hv
  have : prj σ v = mulc (fun τ' => ∏ τ ∈ Finset.univ.erase σ, c τ τ') v := by
    ext j
    simp only [prj, mulc, PiLp.toLp_apply]
    by_cases hj : j.1 = σ
    · rw [if_pos hj, hj, Finset.prod_eq_one, one_mul]
      intro τ hτ
      have hne := hα τ (Finset.ne_of_mem_erase hτ)
      simp only [c]
      exact mul_inv_cancel₀ (sub_ne_zero.2 hne)
    · rw [if_neg hj, Finset.prod_eq_zero (i := j.1) (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩), zero_mul]
      simp [c]
  rw [this]
  exact hprod _ v hv

theorem Hf_prj {dim : (E →+* ℂ) → ℕ} {σ : E →+* ℂ} {ξ : Vsp dim} (hξ : InPart σ ξ) (a : Vsp dim) :
    Hf ξ a = Hf ξ (prj σ a) := by
  unfold Hf
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [prj, PiLp.toLp_apply]
  by_cases hj : j.1 = σ
  · rw [if_pos hj]
  · rw [if_neg hj, hξ j hj]; simp

theorem Hf_eq_inner' {ι : Type} [Fintype ι] (w v : EuclideanSpace ℂ ι) : Hf w v = inner ℂ v w :=
  lemS_Hf_eq_inner w v

theorem prj_inpart {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (a : Vsp dim) : InPart σ (prj σ a) := by
  intro j hj; simp [prj, hj]

theorem onb_data (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (σ : E →+* ℂ) (ρ : ℕ)
    (hρ : Module.finrank ℂ (Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ VP σ : Submodule ℂ _) = ρ)
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I)
    (w : Fin ρ → Vsp X.dim) (hw : ∀ s, InPart σ (w s) ∧ w s ∈ Submodule.span ℂ (I : Set (Vsp X.dim)))
    (hon : ∀ s s', Hf (w s) (w s') = if s = s' then 1 else 0) :
    ∃ (N : ℕ) (b : Fin N → Vsp X.dim), N ≤ X.r ∧ ρ ≤ N ∧
      (∀ k (h : k.val < ρ), b k = w ⟨k, h⟩) ∧
      (∀ k, InPart σ (b k)) ∧
      (∀ k, ρ ≤ k.val → ‖b k‖ = 1 ∧ ∀ a ∈ I, Hf (b k) a = 0) ∧
      (∀ x y : Vsp X.dim, InPart σ x → InPart σ y → ∑ k, Hf x (b k) * Hf (b k) y = Hf x y) := by
  classical
  set N := Module.finrank ℂ (VP (dim := X.dim) σ) with hN
  have hw_inner : ∀ s s', inner ℂ (w s) (w s') = if s = s' then (1 : ℂ) else 0 := by
    intro s s'
    rw [← Hf_eq_inner', hon s' s]
    by_cases h : s = s' <;> simp [h, eq_comm]
  have hwo : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite]; exact hw_inner
  have hρN : ρ ≤ N := hρ ▸ Submodule.finrank_mono inf_le_right
  have hNr : N ≤ X.r := by
    let f : VP (dim := X.dim) σ →ₗ[ℂ] (Fin (X.dim σ) → ℂ) :=
      { toFun := fun v a => (v : Vsp X.dim) ⟨σ, a⟩
        map_add' := fun x y => by funext a; simp
        map_smul' := fun c x => by funext a; simp }
    have hinj : Function.Injective f := by
      intro v v' h
      apply Subtype.ext
      ext j
      obtain ⟨τ, a⟩ := j
      by_cases hτ : τ = σ
      · subst hτ; exact congrFun h a
      · rw [(v.2 : InPart σ (v : Vsp X.dim)) ⟨τ, a⟩ hτ, (v'.2 : InPart σ (v' : Vsp X.dim)) ⟨τ, a⟩ hτ]
    have h1 := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fin_fun] at h1
    have h2 := X.dim_conj σ
    omega
  let vv : Fin N → VP (dim := X.dim) σ := fun k =>
    if h : k.val < ρ then ⟨w ⟨k, h⟩, (hw _).1⟩ else 0
  have hon' : Orthonormal ℂ (Set.domRestrict {k : Fin N | k.val < ρ} vv) := by
    rw [orthonormal_iff_ite]
    rintro ⟨k, hk⟩ ⟨k', hk'⟩
    have hk0 : k.val < ρ := hk
    have hk0' : k'.val < ρ := hk'
    show inner ℂ (vv k) (vv k') = if (⟨k, hk⟩ : {k : Fin N | k.val < ρ}) = ⟨k', hk'⟩ then 1 else 0
    simp only [vv, dif_pos hk0, dif_pos hk0', Submodule.coe_inner, hw_inner]
    simp [Fin.ext_iff, Subtype.ext_iff]
  obtain ⟨bb, hbb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ)
    (E := VP (dim := X.dim) σ) (ι := Fin N) (by simp [hN]) hon'
  have hbw : ∀ k (h : k.val < ρ), (bb k : Vsp X.dim) = w ⟨k, h⟩ := by
    intro k h
    rw [hbb k h]
    simp [vv, h]
  refine ⟨N, fun k => (bb k : Vsp X.dim), hNr, hρN, hbw, fun k => (bb k).2, ?_, ?_⟩
  · intro k hk
    constructor
    · exact bb.orthonormal.1 k
    · intro a ha
      rw [Hf_prj ((bb k).2 : InPart σ (bb k : Vsp X.dim)) a]
      have hpa : prj σ a ∈ (Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ VP σ : Submodule ℂ _) :=
        ⟨mulc_mem I hst σ a (Submodule.subset_span ha), prj_inpart σ a⟩
      have hspan : Submodule.span ℂ (Set.range w) =
          (Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ VP σ : Submodule ℂ _) := by
        apply Submodule.eq_of_le_of_finrank_eq
        · rw [Submodule.span_le]; rintro _ ⟨s, rfl⟩; exact ⟨(hw s).2, (hw s).1⟩
        · rw [finrank_span_eq_card hwo.linearIndependent, Fintype.card_fin, hρ]
      rw [← hspan] at hpa
      rw [Hf_eq_inner']
      refine Submodule.span_induction (p := fun z _ => inner ℂ z (bb k : Vsp X.dim) = 0) ?_ ?_ ?_ ?_ hpa
      · rintro _ ⟨s, rfl⟩
        have hs : (⟨s.val, lt_of_lt_of_le s.2 hρN⟩ : Fin N).val < ρ := s.2
        have e1 : w s = (bb ⟨s.val, lt_of_lt_of_le s.2 hρN⟩ : Vsp X.dim) := by
          rw [hbw _ hs]
        rw [e1, ← Submodule.coe_inner]
        refine bb.orthonormal.2 ?_
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      · simp
      · intro x y _ _ hx hy; rw [inner_add_left, hx, hy, add_zero]
      · intro c x _ hx; rw [inner_smul_left, hx, mul_zero]
  · intro x y hx hy
    have := bb.sum_inner_mul_inner (⟨y, hy⟩ : VP (dim := X.dim) σ) ⟨x, hx⟩
    simp only [Submodule.coe_inner] at this
    rw [Hf_eq_inner', ← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Hf_eq_inner', Hf_eq_inner', mul_comm]

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

theorem jof_Hf_smul_right {ι : Type} [Fintype ι] (x u : EuclideanSpace ℂ ι) (c : ℂ) :
    Hf x (c • u) = (starRingEnd ℂ) c * Hf x u := by
  simp only [Hf, PiLp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem jof_Hf_conj {ι : Type} [Fintype ι] (v w : EuclideanSpace ℂ ι) : star (Hf v w) = Hf w v := by
  simp only [Hf, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.star_def, mul_comm]

theorem Hf_single {ι : Type} [Fintype ι] [DecidableEq ι] (j j' : ι) :
    Hf (EuclideanSpace.single j (1 : ℂ)) (EuclideanSpace.single j' 1) = if j = j' then 1 else 0 := by
  simp only [Hf, EuclideanSpace.single_apply]
  by_cases h : j = j'
  · subst h
    simp [Finset.sum_ite_eq']
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h1 : i = j
    · subst h1
      simp [h]
    · simp [h1]

theorem sum_fin_le {M : Type*} [AddCommMonoid M] {ρ N : ℕ} (h : ρ ≤ N) (f : Fin ρ → M) :
    ∑ k : Fin N, (if h' : k.val < ρ then f ⟨k, h'⟩ else 0) = ∑ s, f s := by
  have key : ∀ M, ∑ k : Fin M, (if h' : k.val < ρ then f ⟨k, h'⟩ else 0) =
      ∑ k ∈ Finset.range M, (if h' : k < ρ then f ⟨k, h'⟩ else 0) :=
    fun M => Fin.sum_univ_eq_sum_range (fun k => if h' : k < ρ then f ⟨k, h'⟩ else 0) M
  rw [key N]
  have hρ : ∑ s, f s = ∑ k ∈ Finset.range ρ, (if h' : k < ρ then f ⟨k, h'⟩ else 0) := by
    rw [← key ρ]
    exact Finset.sum_congr rfl fun s _ => by simp [s.isLt]
  rw [hρ]
  symm
  apply Finset.sum_subset (Finset.range_mono h)
  intro k _ hk'
  simp only [Finset.mem_range] at hk'
  simp [hk']

variable {E : Type} [Field E] [NumberField E]

theorem l2NormSq_nonneg_gaussianTorus (X : PT E) (q : ℕ) {n : ℕ} (F : (Fin n → Vsp X.dim) → ℂ) : 0 ≤ X.l2 q F := by
  unfold PT.l2
  rw [MeasureTheory.setAverage_eq]
  exact smul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
    (MeasureTheory.integral_nonneg fun v => by unfold PT.ptN2; positivity)

theorem rd_nonneg : 0 ≤ PT.rd E := by
  unfold PT.rd
  positivity

theorem ph_nonneg {X : PT E} {DF : ℕ} (P : Par X DF) : 0 ≤ P.ph := by
  unfold Par.ph PT.ph
  have := rd_nonneg (E := E)
  split_ifs
  · positivity
  · exact le_rfl

theorem Cchi_nonneg (m : ℕ) : 0 ≤ Cchi (E := E) m := by
  unfold Cchi RR
  have := rd_nonneg (E := E)
  positivity

theorem inv_constant_nonneg {X : PT E} {DF : ℕ} (P : Par X DF) : 0 ≤ P.K6⁻¹ := by
  unfold Par.K6
  positivity

open Classical in
theorem block_data (hx : Ext.All) (hc : CharStatement) (ht : ColTorusStatement)
    (ha : ColAbelStatement) [IsCMField E] (X : PT E) {DF : ℕ} (P : Par X DF)
    (I : Submodule ℤ (Vsp X.dim)) (hI : IsSplit P I) (σ : E →+* ℂ) (i : ℕ) (hi : i ≤ X.dim σ)
    (c : ℕ) (hcD : c ≤ DF) :
    ∃ (y : Fin i → Vsp X.dim) (s : Fin i → (Fin 1 → Vsp X.dim) → ℂ) (μ : Fin i → ℂ),
      (∀ b, s b ∈ X.Sec P.q 1) ∧
      (∀ b (xs : Fin c → Vsp X.dim), (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 (s b) c xs - μ b * ∏ k, Hf (xs k) (y b)‖ ≤ P.eps1 * ‖μ b‖) ∧
      (∀ b, P.K6⁻¹ * Real.exp (-(2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q)) * X.l2 P.q (s b) ≤
        ‖μ b‖ ^ 2) ∧
      (∀ b, ‖y b‖ ≤ 2) ∧
      (2 : ℝ) ^ (-(X.r : ℝ) / 2) / 2 ≤
        ‖(Matrix.of fun a b => Hf (EuclideanSpace.single (⟨σ, Fin.castLE hi a⟩ : Idx X.dim) (1 : ℂ))
          (y b)).det‖ ∧
      (∀ b, μ b ≠ 0) := by
  classical
  obtain ⟨ρ, hρ⟩ : ∃ ρ, Module.finrank ℂ
      (Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ VP σ : Submodule ℂ (Vsp X.dim)) = ρ := ⟨_, rfl⟩
  obtain ⟨w, xx, u, R, ε, hw, hon, hxu, -, hεb, hc4, hc5, hc6, hc7⟩ := hc E X DF P I hI σ ρ hρ
  obtain ⟨N, bb, hNr, hρN, hbw, hin, hperp, hpars⟩ := onb_data X I σ ρ hρ hI.stable w hw hon
  set e : Fin i → Vsp X.dim := fun a => EuclideanSpace.single (⟨σ, Fin.castLE hi a⟩ : Idx X.dim) (1 : ℂ)
    with he
  have he_in : ∀ a, InPart σ (e a) := by
    intro a j hj
    simp only [he, PiLp.single_apply]
    rw [if_neg]
    rintro rfl
    exact hj rfl
  have hee : ∀ a a', Hf (e a) (e a') = if a = a' then 1 else 0 := by
    intro a a'
    simp only [he]
    rw [Hf_single]
    by_cases h : a = a'
    · simp [h]
    · rw [if_neg, if_neg h]
      intro h2
      rw [Sigma.mk.inj_iff] at h2
      exact h (Fin.castLE_injective hi (eq_of_heq h2.2))
  let M : Matrix (Fin i) (Fin N) ℂ := Matrix.of fun a k => Hf (e a) (bb k)
  have hMM : M * M.conjTranspose = 1 := by
    ext a a'
    simp only [M, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply, jof_Hf_conj]
    rw [hpars (e a) (e a') (he_in a) (he_in a'), hee]
  obtain ⟨s1, -, hs1⟩ := hx.2.2.2.2.2.1 i N X.r M hMM hNr
  haveI : Nonempty (Fin i → Fin N) := ⟨s1⟩
  obtain ⟨s0, hs0⟩ := Finite.exists_max (fun s : Fin i → Fin N => ‖(M.submatrix id s).det‖)
  set Δ := ‖(M.submatrix id s0).det‖ with hΔ
  have hΔr : (2 : ℝ) ^ (-(X.r : ℝ) / 2) ≤ Δ := hs1.trans (hs0 s1)
  have hΔpos : 0 < Δ := lt_of_lt_of_le (by positivity) hΔr
  have hinj : Function.Injective s0 := by
    intro j j' h
    by_contra hne
    have h0 : (M.submatrix id s0).det = 0 := Matrix.det_zero_of_column_eq hne (by intro a; simp [h])
    rw [hΔ, h0, norm_zero] at hΔpos
    exact lt_irrefl 0 hΔpos
  have hRpos : ∀ t, 0 < R t := by
    intro t
    have h1 := (hc5 t).2
    have hp := Real.pi_pos
    by_contra h
    push Not at h
    nlinarith
  have hT : ∀ t : Fin ρ, ∃ s' ∈ X.Sec P.q 1, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
      (∀ xs : Fin c → Vsp X.dim, (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 s' c xs - ζ * (2 * Real.pi) ^ c * ∏ k, Hf (xs k) (u t)‖ ≤ P.eps1 * (2 * Real.pi * R t) ^ c) ∧
      P.K6⁻¹ * Real.exp (-(2 * Real.pi * ‖u t‖ ^ 2 / P.q)) * X.l2 P.q s' ≤ (2 * Real.pi * R t) ^ (2 * c) :=
    fun t => ht E X DF P I hI c hcD σ (xx t) (u t) (hxu t).1 (hxu t).2 (2 * Real.pi * R t) (hc5 t).2
      (by have h1 := (hc5 t).1; have hp := Real.pi_pos; nlinarith) (hc6 t)
  choose sT hsT ζ hζ hζb hζl using hT
  have hA : ∀ k : Fin N, ρ ≤ k.val → ∃ s' ∈ X.Sec P.q 1,
      (∀ xs : Fin c → Vsp X.dim, (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 s' c xs - (c.factorial : ℂ) * ∏ k', Hf (xs k') (bb k)‖ ≤ P.eps1 * c.factorial) ∧
      P.K6⁻¹ * X.l2 P.q s' ≤ (c.factorial : ℝ) ^ 2 :=
    fun k hk => ha E X DF P I hI c hcD σ (bb k) (hin k) (hperp k hk).1 (hperp k hk).2
  choose sA hsA hAb hAl using hA
  have hK6 := inv_constant_nonneg P
  have hexp1 : Real.exp (-(2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    have := Cchi_nonneg (E := E) P.m
    have := ph_nonneg P
    have := Real.pi_pos
    positivity
  have hexp : ∀ t, Real.exp (-(2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q)) ≤
      Real.exp (-(2 * Real.pi * ‖u t‖ ^ 2 / P.q)) := by
    intro t
    rw [Real.exp_le_exp, neg_le_neg_iff]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have := hc7 t
    have := Real.pi_pos
    nlinarith
  let y : Fin i → Vsp X.dim := fun j =>
    if h : (s0 j).val < ρ then ((R ⟨_, h⟩ : ℂ))⁻¹ • u ⟨_, h⟩ else bb (s0 j)
  let s : Fin i → (Fin 1 → Vsp X.dim) → ℂ := fun j =>
    if h : (s0 j).val < ρ then sT ⟨_, h⟩ else sA (s0 j) (not_lt.1 h)
  let μ : Fin i → ℂ := fun j =>
    if h : (s0 j).val < ρ then ζ ⟨_, h⟩ * (((2 * Real.pi * R ⟨_, h⟩ : ℝ)) : ℂ) ^ c
    else (c.factorial : ℂ)
  have hnμ : ∀ t, ‖ζ t * (((2 * Real.pi * R t : ℝ)) : ℂ) ^ c‖ = (2 * Real.pi * R t) ^ c := by
    intro t
    have := hRpos t
    rw [norm_mul, hζ t, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  refine ⟨y, s, μ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases h : (s0 j).val < ρ
    · simp only [s, dif_pos h]; exact hsT _
    · simp only [s, dif_neg h]; exact hsA _ _
  · intro j xs hxs
    by_cases h : (s0 j).val < ρ
    · simp only [s, μ, y, dif_pos h]
      have hR := hRpos ⟨_, h⟩
      have e1 : ζ ⟨_, h⟩ * (((2 * Real.pi * R ⟨_, h⟩ : ℝ)) : ℂ) ^ c *
          ∏ k, Hf (xs k) (((R ⟨_, h⟩ : ℂ))⁻¹ • u ⟨_, h⟩) =
          ζ ⟨_, h⟩ * (2 * Real.pi) ^ c * ∏ k, Hf (xs k) (u ⟨_, h⟩) := by
        simp only [jof_Hf_smul_right, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, map_inv₀, Complex.conj_ofReal]
        have hR' : (R ⟨_, h⟩ : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
        push_cast
        have key : (2 * (Real.pi : ℂ) * (R ⟨_, h⟩ : ℂ)) ^ c * (1 / (R ⟨_, h⟩ : ℂ)) ^ c =
            (2 * Real.pi) ^ c := by
          rw [← mul_pow]; congr 1; field_simp
        linear_combination (ζ ⟨_, h⟩ * ∏ x, Hf (xs x) (u ⟨_, h⟩)) * key
      rw [e1, hnμ]
      exact hζb _ xs hxs
    · simp only [s, μ, y, dif_neg h]
      rw [Complex.norm_natCast]
      exact hAb _ _ xs hxs
  · intro j
    by_cases h : (s0 j).val < ρ
    · simp only [s, μ, dif_pos h]
      rw [hnμ]
      have hl := l2NormSq_nonneg_gaussianTorus X P.q (sT ⟨_, h⟩)
      calc P.K6⁻¹ * Real.exp (-(2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q)) * X.l2 P.q (sT ⟨_, h⟩)
          ≤ P.K6⁻¹ * Real.exp (-(2 * Real.pi * ‖u ⟨_, h⟩‖ ^ 2 / P.q)) * X.l2 P.q (sT ⟨_, h⟩) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hexp _) hK6) hl
        _ ≤ (2 * Real.pi * R ⟨_, h⟩) ^ (2 * c) := hζl _
        _ = ((2 * Real.pi * R ⟨_, h⟩) ^ c) ^ 2 := by ring
    · simp only [s, μ, dif_neg h]
      rw [Complex.norm_natCast]
      have hl := l2NormSq_nonneg_gaussianTorus X P.q (sA (s0 j) (not_lt.1 h))
      calc P.K6⁻¹ * Real.exp (-(2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q)) *
            X.l2 P.q (sA (s0 j) (not_lt.1 h))
          ≤ P.K6⁻¹ * X.l2 P.q (sA (s0 j) (not_lt.1 h)) :=
            mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hK6 hexp1) hl
        _ ≤ (c.factorial : ℝ) ^ 2 := hAl _ _
  · intro j
    by_cases h : (s0 j).val < ρ
    · simp only [y, dif_pos h]
      have hR := hRpos ⟨_, h⟩
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, inv_mul_le_iff₀ hR]
      have := (hc5 ⟨_, h⟩).1
      linarith
    · simp only [y, dif_neg h]
      rw [(hperp _ (not_lt.1 h)).1]
      norm_num
  ·
    have hDP := hx.2.2.2.2.2.2.1
    have hDN := hx.2.2.2.2.2.2.2.1
    let wv : Fin N → Fin i → ℂ := fun k a => Hf (e a) (bb k)
    let εc : Fin i → Fin N → ℂ := fun j k =>
      if h : (s0 j).val < ρ then (if hk : k.val < ρ then ε ⟨_, h⟩ ⟨_, hk⟩ else 0) else 0
    have hentry : ∀ a j, Hf (e a) (y j) = wv (s0 j) a + ∑ k, εc j k * wv k a := by
      intro a j
      by_cases h : (s0 j).val < ρ
      · simp only [y, dif_pos h, jof_Hf_smul_right, map_inv₀, Complex.conj_ofReal]
        have hR := hRpos ⟨_, h⟩
        have hR' : (R ⟨_, h⟩ : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
        have h4 := hc4 ⟨_, h⟩ (e a) (he_in a)
        have hws : w ⟨_, h⟩ = bb (s0 j) := (hbw (s0 j) h).symm
        have hsum : ∑ s', ε ⟨_, h⟩ s' * Hf (e a) (w s') = ∑ k, εc j k * wv k a := by
          rw [← sum_fin_le hρN (fun s' => ε ⟨_, h⟩ s' * Hf (e a) (w s'))]
          refine Finset.sum_congr rfl fun k _ => ?_
          by_cases hk : k.val < ρ
          · simp only [εc, wv, dif_pos h, dif_pos hk]
            rw [hbw k hk]
          · simp only [εc, dif_pos h, dif_neg hk, zero_mul]
        rw [← hsum]
        simp only [wv]
        rw [← hws, ← h4, div_eq_inv_mul]
      · simp only [y, dif_neg h, εc, wv, zero_mul, Finset.sum_const_zero, add_zero]
    have hmat : (Matrix.of fun a b => Hf (EuclideanSpace.single (⟨σ, Fin.castLE hi a⟩ : Idx X.dim) (1 : ℂ))
        (y b)) = Matrix.of fun a j => (wv (s0 j) + ∑ k, εc j k • wv k) a := by
      ext a j
      simp only [Matrix.of_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact hentry a j
    have hold : (Matrix.of fun a j => wv (s0 j) a).det = (M.submatrix id s0).det := rfl
    have hmax : ∀ σ' : Fin i → Fin N, ‖(Matrix.of fun a j => wv (σ' j) a).det‖ ≤ Δ :=
      fun σ' => hs0 σ'
    have hpert := hDP ℂ i (Fin N) wv s0 εc Δ hmax

    set B : ℝ := Real.sqrt ρ / (30 * ρ ^ 2) with hB
    have hB0 : 0 ≤ B := by positivity
    have hrow : ∀ j, ∑ k, ‖εc j k‖ ≤ if (s0 j).val < ρ then B else 0 := by
      intro j
      by_cases h : (s0 j).val < ρ
      · rw [if_pos h]
        have := (hεb ⟨_, h⟩).2
        rw [← sum_fin_le hρN (fun s' => ‖ε ⟨_, h⟩ s'‖)] at this
        refine le_of_eq_of_le ?_ this
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : k.val < ρ
        · simp [εc, dif_pos h, dif_pos hk]
        · simp [εc, dif_pos h, dif_neg hk]
      · rw [if_neg h]
        simp [εc, dif_neg h]
    have hprod : ∏ j, (1 + ∑ k, ‖εc j k‖) ≤ (1 + B) ^ ρ := by
      calc ∏ j, (1 + ∑ k, ‖εc j k‖)
          ≤ ∏ j, (if (s0 j).val < ρ then 1 + B else 1) := by
            refine Finset.prod_le_prod (fun j _ => by positivity) fun j _ => ?_
            have := hrow j
            by_cases h : (s0 j).val < ρ
            · simp only [h, if_true] at this ⊢; linarith
            · simp only [h, if_false] at this ⊢; linarith
        _ = (1 + B) ^ (Finset.univ.filter fun j => (s0 j).val < ρ).card := by
            rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
        _ ≤ (1 + B) ^ ρ := by
            apply pow_le_pow_right₀ (by linarith)
            have : (Finset.univ.filter fun j => (s0 j).val < ρ).card ≤ (Finset.range ρ).card := by
              apply Finset.card_le_card_of_injOn (fun j => (s0 j).val)
              · intro j hj
                simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj
                simpa using hj
              · intro j _ j' _ hjj
                exact hinj (Fin.ext hjj)
            simpa using this
    have hhalf : (1 + B) ^ ρ - 1 ≤ 1 / 2 := by
      rcases Nat.eq_zero_or_pos ρ with h0 | hpos
      · subst h0; norm_num
      · have hρ1 : (1 : ℝ) ≤ ρ := by exact_mod_cast hpos
        have hnum := hDN ρ hpos
        have hBle : B ≤ (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10 := by
          have hsq : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt (by positivity)
          have hsp : 0 < Real.sqrt ρ := Real.sqrt_pos.2 (by linarith)
          have hr : (ρ : ℝ) ^ (-(3 : ℝ) / 2) = 1 / (ρ * Real.sqrt ρ) := by
            rw [show (-(3 : ℝ) / 2) = -((1 : ℝ) + 1 / 2) by norm_num, Real.rpow_neg (by positivity),
              Real.rpow_add (by linarith), Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]
          have hBeq : B = (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 30 := by
            rw [hr, hB, div_div, div_eq_div_iff (by positivity) (by positivity)]
            linear_combination (30 * (ρ : ℝ)) * hsq
          have h0 : 0 ≤ (ρ : ℝ) ^ (-(3 : ℝ) / 2) := by positivity
          rw [hBeq]
          linarith
        have : (1 + B) ^ ρ ≤ (1 + (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10) ^ ρ :=
          pow_le_pow_left₀ (by linarith) (by linarith) ρ
        linarith
    have hfac : ((∏ j, (1 + ∑ k, ‖εc j k‖)) - 1) * Δ ≤ Δ / 2 := by
      have := hΔpos.le
      nlinarith [hprod, hhalf]
    rw [hmat]
    have h2 : ‖(Matrix.of fun a j => wv (s0 j) a).det‖ = Δ := by rw [hold]
    have h4 : Δ - ‖(Matrix.of fun a j => (wv (s0 j) + ∑ k, εc j k • wv k) a).det -
        (Matrix.of fun a j => wv (s0 j) a).det‖ ≤
        ‖(Matrix.of fun a j => (wv (s0 j) + ∑ k, εc j k • wv k) a).det‖ := by
      have := norm_sub_norm_le (Matrix.of fun a j => wv (s0 j) a).det
        (Matrix.of fun a j => (wv (s0 j) + ∑ k, εc j k • wv k) a).det
      rw [h2, norm_sub_rev] at this
      linarith
    linarith [hpert, hfac, h4, hΔr]
  · intro j
    by_cases h : (s0 j).val < ρ
    · simp only [μ, dif_pos h]
      rw [← norm_ne_zero_iff, hnμ]
      have := hRpos ⟨_, h⟩
      positivity
    · simp only [μ, dif_neg h]
      exact_mod_cast Nat.factorial_ne_zero c

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField

noncomputable section

variable {E : Type} [Field E] [NumberField E] {n nb : ℕ}

section Count
variable {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim)

theorem c_le_DF (j : Fin nb) (hi : 1 ≤ (bs j).i) : (bs j).c ≤ DF bs := by
  unfold DF
  exact le_trans (Nat.le_mul_of_pos_left _ hi)
    (Finset.single_le_sum (f := fun j => (bs j).i * (bs j).c) (fun j _ => Nat.zero_le _) (Finset.mem_univ j))

theorem card_choice_le (r : ℕ) (hr : ∀ j, (bs j).i ≤ r) :
    Fintype.card (Choice bs) ≤ r ^ DF bs := by
  unfold DF
  rw [Fintype.card_pi, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
  intro j _
  rw [Fintype.card_fun, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin, pow_mul]
  exact Nat.pow_le_pow_left (le_trans (Nat.factorial_le_pow _) (Nat.pow_le_pow_left (hr j) _)) _

theorem prod_two_pow :
    ∏ p : (Σ j : Fin nb, Fin (bs j).i), (2 : ℝ) ^ (bs p.1).c = 2 ^ DF bs := by
  rw [Fintype.prod_sigma]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  unfold DF
  congr 1
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem card_pos_le : Fintype.card (Σ j : Fin nb, Fin (bs j).i) ≤ DF bs := by
  rw [Fintype.card_sigma]
  unfold DF
  exact Finset.sum_le_sum (fun j _ => by rw [Fintype.card_fin]; exact Nat.le_mul_of_pos_right _ (bs j).hc)

theorem card_pos_pos (h : 1 ≤ DF bs) : 1 ≤ Fintype.card (Σ j : Fin nb, Fin (bs j).i) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  by_contra hc
  push_neg at hc
  have h0 : ∀ j, (bs j).i = 0 := by
    intro j
    have := Finset.single_le_sum (f := fun j => (bs j).i) (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  unfold DF at h
  simp [h0] at h

theorem prod_det_ge (d : ∀ j : Fin nb, ℝ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hd : ∀ j, 1 ≤ (bs j).i → δ ≤ d j) (hd1 : ∀ j, (bs j).i = 0 → d j = 1) :
    δ ^ DF bs ≤ ∏ j, d j ^ (bs j).c := by
  unfold DF
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod (fun j _ => pow_nonneg hδ0 _)
  intro j _
  by_cases hi : (bs j).i = 0
  · rw [hi, zero_mul, pow_zero, hd1 j hi, one_pow]
  · have hi1 : 1 ≤ (bs j).i := Nat.one_le_iff_ne_zero.mpr hi
    calc δ ^ ((bs j).i * (bs j).c) ≤ δ ^ (bs j).c :=
          pow_le_pow_of_le_one hδ0 hδ1 (Nat.le_mul_of_pos_left _ hi1)
      _ ≤ d j ^ (bs j).c := pow_le_pow_left₀ hδ0 (hd j hi1) _

end Count

section Data
variable [IsCMField E] (X : PT E) (bs : Fin nb → Block E n X.dim)

open Classical in
theorem block_data_all (hx : Ext.All) (hc : CharStatement) (ht : ColTorusStatement)
    (ha : ColAbelStatement) (P : Par X (DF bs)) (I : Submodule ℤ (Vsp X.dim)) (hI : IsSplit P I)
    (j : Fin nb) :
    ∃ (y : Fin (bs j).i → Vsp X.dim) (s : Fin (bs j).i → (Fin 1 → Vsp X.dim) → ℂ)
      (μ : Fin (bs j).i → ℂ),
      (∀ b, s b ∈ X.Sec P.q 1) ∧
      (∀ b (xs : Fin (bs j).c → Vsp X.dim), (∀ k, InPart (bs j).τ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 (s b) (bs j).c xs - μ b * ∏ k, Hf (xs k) (y b)‖ ≤ P.eps1 * ‖μ b‖) ∧
      (∀ b, P.K6⁻¹ * Real.exp (-(2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q)) * X.l2 P.q (s b) ≤
        ‖μ b‖ ^ 2) ∧
      (∀ b, ‖y b‖ ≤ 2) ∧
      (2 : ℝ) ^ (-(X.r : ℝ) / 2) / 2 ≤
        ‖(Matrix.of fun a b => Hf (EuclideanSpace.single
          (⟨(bs j).τ, Fin.castLE (bs j).hi a⟩ : Idx X.dim) (1 : ℂ)) (y b)).det‖ ∧
      (∀ b, μ b ≠ 0) := by
  rcases Nat.eq_zero_or_pos (bs j).i with h0 | hpos
  · haveI : IsEmpty (Fin (bs j).i) := by rw [h0]; infer_instance
    refine ⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim, fun b => isEmptyElim b,
      isEmptyElim, isEmptyElim, ?_, isEmptyElim⟩
    rw [Matrix.det_isEmpty, norm_one]
    have h1 : (2 : ℝ) ^ (-(X.r : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
        have := Nat.cast_nonneg (α := ℝ) X.r; linarith)
    linarith
  · exact block_data hx hc ht ha X P I hI (bs j).τ (bs j).i (bs j).hi (bs j).c (c_le_DF bs j hpos)

end Data

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex NumberField

section Core

variable {E : Type} [Field E] [NumberField E]

theorem Hf_norm_le_two {dim : (E →+* ℂ) → ℕ} (e y : Vsp dim) (he : ‖e‖ = 1) (hy : ‖y‖ ≤ 2) :
    ‖Hf e y‖ ≤ 2 := by
  rw [Hf_eq_inner']
  calc ‖inner ℂ y e‖ ≤ ‖y‖ * ‖e‖ := norm_inner_le_norm y e
    _ ≤ 2 := by rw [he, mul_one]; exact hy

open Classical in
theorem eU_props {dim : (E →+* ℂ) → ℕ} {n nb : ℕ} (bs : Fin nb → Block E n dim) (j : Fin nb)
    (a : Fin (bs j).i) : InPart (bs j).τ (eU bs j a) ∧ ‖eU bs j a‖ = 1 := by
  refine ⟨fun k hk => ?_, by simp [eU]⟩
  simp only [eU, PiLp.single_apply]
  rw [if_neg]
  rintro rfl
  exact hk rfl

theorem norm_sgnT {dim : (E →+* ℂ) → ℕ} {n nb : ℕ} (bs : Fin nb → Block E n dim) (T : Choice bs) :
    ‖sgnT bs T‖ ≤ 1 := by
  unfold sgnT
  rw [norm_prod]
  refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun j _ => ?_
  rw [norm_prod]
  refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun r _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign (T j r)) with h | h <;> simp [h]

set_option maxHeartbeats 1000000 in
open Classical in
theorem jof_core (hx : Ext.All) (hs : SplitStatement) (hc : CharStatement) (ht : ColTorusStatement)
    (ha : ColAbelStatement) (he : ColEmptyStatement) [IsCMField E] (X : PT E) {n nb : ℕ}
    (bs : Fin nb → Block E n X.dim) (hD : Disj bs) (P : Par X (DF bs)) :
    ∃ F ∈ X.Sec P.q n, X.l2 P.q F = 1 ∧ P.Jbound n ≤ ‖polyDeriv (P1 bs) dir F 0‖ ^ 2 := by
  obtain ⟨I, hI⟩ := hs E X (DF bs) P
  choose yB sB μB hsB hbd hl2 hyB hdet hμ using block_data_all X bs hx hc ht ha P I hI
  obtain ⟨se, hse, hse0, hsel⟩ := he E X (DF bs) P I hI
  set y : (Σ j : Fin nb, Fin (bs j).i) → Vsp X.dim := fun p => yB p.1 p.2 with hydef
  set μ : (Σ j : Fin nb, Fin (bs j).i) → ℂ := fun p => μB p.1 p.2 with hμdef
  set sc : Fin n → (Fin 1 → Vsp X.dim) → ℂ := fun k =>
    match owner bs k with
    | some p => sB p.1 p.2
    | none => se with hscdef
  have hsc_col : ∀ p, sc (colB bs p) = sB p.1 p.2 := fun p => by
    simp only [hscdef, owner_colB hD p]
  have hsc_none : ∀ k, owner bs k = none → sc k = se := fun k hk => by
    simp only [hscdef, hk]
  have hsc : ∀ k, sc k ∈ X.Sec P.q 1 := by
    intro k
    rcases hk : owner bs k with _ | p
    · rw [hsc_none k hk]; exact hse
    · rw [← colB_of_owner hk, hsc_col]; exact hsB _ _
  have hcd : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (sc k) := fun k => sec_contDiff X (hsc k)
  set F₀ := tens X sc with hF₀def
  have hF₀ : F₀ ∈ X.Sec P.q n := tens_mem X hsc
  set V0 := polyDeriv (P1 bs) dir F₀ 0 with hV0def
  have hV0 := polyDeriv_determinantPoly_tensor X bs sc hcd
  set ε := P.eps1 with hεdef
  set ee : Fin n → ℂ := fun _ => se 0 with heedef
  set A := idealA bs μ y ee with hAdef
  set D : Choice bs → Fin n → ℂ := fun T k =>
    d1 (sc k) (colL (lst X bs T) k).length (fun j => (colL (lst X bs T) k).get j) with hDdef
  set α : Fin n → ℝ := fun k =>
    match owner bs k with
    | some p => ‖μ p‖ * 2 ^ (bs p.1).c
    | none => ‖se 0‖ with hαdef
  set δ : Fin n → ℝ := fun k =>
    match owner bs k with
    | some p => ε * ‖μ p‖
    | none => 0 with hδdef
  have hε0 : 0 ≤ ε := by
    rw [hεdef, Par.eps1]; positivity

  have hAb : ∀ T k, ‖A T k‖ ≤ α k := by
    intro T k
    rcases hk : owner bs k with _ | p
    · simp only [hAdef, idealA, hk, hαdef, heedef, le_refl]
    · simp only [hAdef, idealA, hk, hαdef]
      rw [norm_mul, norm_prod]
      gcongr
      calc ∏ r, ‖Hf (eU bs p.1 (T p.1 r p.2)) (y p)‖ ≤ ∏ _r : Fin (bs p.1).c, (2 : ℝ) :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun r _ =>
              Hf_norm_le_two _ _ (eU_props bs p.1 _).2 (hyB p.1 p.2)
        _ = 2 ^ (bs p.1).c := by simp
  have hDb : ∀ T k, ‖D T k - A T k‖ ≤ δ k := by
    intro T k
    rcases hk : owner bs k with _ | p
    · simp only [hAdef, idealA, hk, hδdef, hDdef, heedef]
      rw [colL_empty X hD T hk, hsc_none k hk]
      simp [d1_zero]
    · have hkp := colB_of_owner hk
      subst hkp
      simp only [hAdef, idealA, hk, hδdef, hDdef]
      rw [hsc_col]
      exact iteratedDeriv_list_bound (sB p.1 p.2) (bs p.1).c (μ p) (y p) (ε * ‖μ p‖) (bs p.1).τ
        (hbd p.1 p.2) _ (fun r => eU bs p.1 (T p.1 r p.2)) (colL_block X hD T p)
        (fun r => eU_props bs p.1 _)
  have herr := norm_sum_prod_sub_le (sgnT bs) (norm_sgnT bs) D A α δ hAb hDb
  rw [main_term bs hD μ y ee] at herr
  have hV0e : V0 = ∑ T, sgnT bs T * ∏ k, D T k := hV0
  rw [← hV0e] at herr
  set N := Fintype.card (Choice bs) with hNdef

  set Ce : ℝ := ∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ‖se 0‖ with hCedef
  set Mμ : ℝ := ∏ p, ‖μ p‖ with hMμdef
  set Dt : ℝ := ∏ j, ‖(blockM bs y j).det‖ ^ (bs j).c with hDtdef
  set A1 : ℝ := ∏ p : (Σ j : Fin nb, Fin (bs j).i), ((2 : ℝ) ^ (bs p.1).c + ε) with hA1def
  have hCe0 : 0 ≤ Ce := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hMμ0 : 0 ≤ Mμ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hCm : ‖(∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ee k) * (∏ p, μ p) *
      ∏ j, (blockM bs y j).det ^ (bs j).c‖ = Ce * Mμ * Dt := by
    simp only [norm_mul, norm_prod, norm_pow, hCedef, hMμdef, hDtdef, heedef]
  have hα : ∏ k, α k = Ce * (Mμ * 2 ^ DF bs) := by
    rw [prod_cols hD]
    congr 1
    · refine Finset.prod_congr rfl fun k hk => ?_
      rw [Finset.mem_filter] at hk
      simp only [hαdef, hk.2]
    · rw [hMμdef, ← prod_two_pow bs, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p _ => ?_
      simp only [hαdef, owner_colB hD p]
  have hαδ : ∏ k, (α k + δ k) = Ce * (Mμ * A1) := by
    rw [prod_cols hD]
    congr 1
    · refine Finset.prod_congr rfl fun k hk => ?_
      rw [Finset.mem_filter] at hk
      simp only [hαdef, hδdef, hk.2, add_zero]
    · rw [hMμdef, hA1def, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p _ => ?_
      simp only [hαdef, hδdef, owner_colB hD p]
      ring

  have hr1 : 1 ≤ X.r := by
    have := P.hfr
    rcases Nat.eq_zero_or_pos X.r with h | h
    · rw [h, mul_zero] at this; omega
    · exact h
  have hir : ∀ j, (bs j).i ≤ X.r := fun j => by
    have h1 := (bs j).hi
    have h2 := X.dim_conj (bs j).τ
    omega
  have hcard := card_choice_le bs X.r hir
  have hm := card_pos_le bs
  have hK : ε ≤ Real.exp (-(((DF bs : ℝ) + 1) * ((X.r : ℝ) * Real.log X.r + 3 * X.r + 3))) := by
    have h6 := P.C6
    rw [hεdef, Par.eps1]
    exact eps_bound X.gA (dstar (E := E) P.m) (t0 (E := E) P.q P.R0) _ (by push_cast at h6 ⊢; linarith)
  have hε1 : ε ≤ 1 := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ X.r by exact_mod_cast hr1)
    have hr0 : (0 : ℝ) ≤ X.r := Nat.cast_nonneg _
    have h1 : 0 ≤ ((DF bs : ℝ) + 1) * ((X.r : ℝ) * Real.log X.r + 3 * X.r + 3) :=
      mul_nonneg (by positivity) (by have := mul_nonneg hr0 hlog; linarith)
    exact hK.trans (Real.exp_le_one_iff.2 (by linarith))
  have hnum := num_bound X.r (DF bs) hr1 ε hε0 hK
  set m := Fintype.card (Σ j : Fin nb, Fin (bs j).i) with hmdef
  have hA1le : A1 - 2 ^ DF bs ≤ 2 ^ DF bs * (m * ε * 2 ^ DF bs) := by
    have h1 : A1 ≤ 2 ^ DF bs * (1 + ε) ^ m := by
      rw [hA1def, ← prod_two_pow bs, hmdef, ← Finset.card_univ, ← Finset.prod_const,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun _ _ => by positivity) fun p _ => ?_
      have : (1 : ℝ) ≤ 2 ^ (bs p.1).c := one_le_pow₀ (by norm_num)
      nlinarith
    have h2 := one_add_pow_sub_one_le ε hε0 m
    have h3 : (1 + ε) ^ m ≤ 2 ^ DF bs :=
      (pow_le_pow_left₀ (by linarith) (by linarith) m).trans (pow_le_pow_right₀ (by norm_num) hm)
    have h4 : (0 : ℝ) ≤ 2 ^ DF bs := by positivity
    have h5 : (0 : ℝ) ≤ m * ε := by positivity
    calc A1 - 2 ^ DF bs ≤ 2 ^ DF bs * ((1 + ε) ^ m - 1) := by nlinarith
      _ ≤ 2 ^ DF bs * (m * ε * (1 + ε) ^ m) := mul_le_mul_of_nonneg_left h2 h4
      _ ≤ 2 ^ DF bs * (m * ε * 2 ^ DF bs) := by gcongr
  set δ0 : ℝ := (2 : ℝ) ^ (-(X.r : ℝ) / 2) / 2 with hδ0def
  have hδ0pos : 0 < δ0 := by positivity
  have hδ01 : δ0 ≤ 1 := by
    have : (2 : ℝ) ^ (-(X.r : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
        have := Nat.cast_nonneg (α := ℝ) X.r; linarith)
    rw [hδ0def]; linarith
  have hDt : δ0 ^ DF bs ≤ Dt := by
    rw [hDtdef]
    refine prod_det_ge bs _ δ0 hδ0pos.le hδ01 (fun j hj => hdet j) (fun j hj => ?_)
    haveI : IsEmpty (Fin (bs j).i) := by rw [hj]; infer_instance
    rw [Matrix.det_isEmpty, norm_one]
  have hδ0exp : Real.exp (-((X.r : ℝ) / 2 + 1)) ≤ δ0 := by
    rw [hδ0def, Real.rpow_def_of_pos (by norm_num)]
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have hl2' : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have he1 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, one_div]
      have := Real.add_one_le_exp (1 : ℝ)
      exact inv_anti₀ (by norm_num) (by linarith)
    have hr0 : (0 : ℝ) ≤ X.r := Nat.cast_nonneg _
    calc Real.exp (-((X.r : ℝ) / 2 + 1)) = Real.exp (-((X.r : ℝ) / 2)) * Real.exp (-1) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (Real.log 2 * (-(X.r : ℝ) / 2)) * (1 / 2) := by
          gcongr
          nlinarith
      _ = Real.exp (Real.log 2 * (-(X.r : ℝ) / 2)) / 2 := by ring
  have hnum2 : (N : ℝ) * (A1 - 2 ^ DF bs) ≤ Dt / 2 := by
    have hc : (N : ℝ) ≤ (X.r : ℝ) ^ DF bs := by exact_mod_cast hcard
    have hm' : (m : ℝ) ≤ DF bs := by exact_mod_cast hm
    have hA0 : 0 ≤ A1 - 2 ^ DF bs := by
      rw [hA1def, ← prod_two_pow bs, sub_nonneg]
      exact Finset.prod_le_prod (fun _ _ => by positivity) fun p _ => le_add_of_nonneg_right hε0
    have hexp : Real.exp (-((X.r : ℝ) / 2 + 1)) ^ DF bs = Real.exp (-(((X.r : ℝ) / 2 + 1) * DF bs)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hE : 0 < Real.exp ((X.r / 2 + 1) * DF bs) := Real.exp_pos _
    have hfin : (DF bs : ℝ) * ε * (4 * X.r) ^ DF bs ≤ Real.exp (-(((X.r : ℝ) / 2 + 1) * DF bs)) / 2 := by
      rw [Real.exp_neg, ← one_div, div_div, le_div_iff₀ (by positivity)]
      calc (DF bs : ℝ) * ε * (4 * X.r) ^ DF bs * (Real.exp ((X.r / 2 + 1) * DF bs) * 2)
          = 2 * (DF bs : ℝ) * (4 * X.r) ^ DF bs * Real.exp ((X.r / 2 + 1) * DF bs) * ε := by ring
        _ ≤ 1 := hnum
    have h4r : ((4 : ℝ) * X.r) ^ DF bs = 2 ^ DF bs * 2 ^ DF bs * (X.r : ℝ) ^ DF bs := by
      rw [← mul_pow, ← mul_pow]; norm_num
    have hmε : (m : ℝ) * ε * 2 ^ DF bs ≤ (DF bs : ℝ) * ε * 2 ^ DF bs :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm' hε0) (by positivity)
    have hr0 : (0 : ℝ) ≤ (X.r : ℝ) ^ DF bs := by positivity
    have h20 : (0 : ℝ) ≤ 2 ^ DF bs := by positivity
    calc (N : ℝ) * (A1 - 2 ^ DF bs)
        ≤ (X.r : ℝ) ^ DF bs * (2 ^ DF bs * (m * ε * 2 ^ DF bs)) :=
          mul_le_mul hc hA1le hA0 hr0
      _ ≤ (X.r : ℝ) ^ DF bs * (2 ^ DF bs * (DF bs * ε * 2 ^ DF bs)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmε h20) hr0
      _ = (DF bs : ℝ) * ε * (4 * X.r) ^ DF bs := by rw [h4r]; ring
      _ ≤ Real.exp (-(((X.r : ℝ) / 2 + 1) * DF bs)) / 2 := hfin
      _ ≤ Dt / 2 := by
          rw [← hexp]
          have := pow_le_pow_left₀ (Real.exp_pos _).le hδ0exp (DF bs)
          linarith
  have herr2 : ‖V0 - (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ee k) * (∏ p, μ p) *
      ∏ j, (blockM bs y j).det ^ (bs j).c‖ ≤ Ce * Mμ * Dt / 2 := by
    refine herr.trans ?_
    rw [hαδ, hα]
    calc (N : ℝ) * (Ce * (Mμ * A1) - Ce * (Mμ * 2 ^ DF bs))
        = Ce * Mμ * ((N : ℝ) * (A1 - 2 ^ DF bs)) := by ring
      _ ≤ Ce * Mμ * (Dt / 2) := mul_le_mul_of_nonneg_left hnum2 (mul_nonneg hCe0 hMμ0)
      _ = Ce * Mμ * Dt / 2 := by ring
  have hV0ge : Ce * Mμ * Dt / 2 ≤ ‖V0‖ := by
    have := norm_sub_norm_le ((∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ee k) *
      (∏ p, μ p) * ∏ j, (blockM bs y j).det ^ (bs j).c) V0
    rw [hCm, norm_sub_rev] at this
    linarith

  have hCepos : 0 < Ce := Finset.prod_pos fun _ _ => by
    have := hse0; linarith
  have hMμpos : 0 < Mμ := Finset.prod_pos fun p _ => norm_pos_iff.2 (hμ p.1 p.2)
  have hDtpos : 0 < Dt := lt_of_lt_of_le (pow_pos hδ0pos _) hDt
  have hV0pos : 0 < ‖V0‖ := lt_of_lt_of_le (by positivity) hV0ge
  have hl2F : X.l2 P.q F₀ = ∏ k, X.l2 P.q (sc k) := l2_tens_eq_prod X P.q sc
  have hl2pos : 0 < X.l2 P.q F₀ := by
    rcases (l2NormSq_nonneg_gaussianTorus X P.q F₀).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [hl2F] at h
      obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h.symm
      have hz := eq_zero_of_l2_eq_zero X hx.1 P.hq (hsc k) hk
      have hF0 : F₀ = 0 := by
        funext v
        rw [hF₀def, tens]
        exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hz]; rfl)
      have : V0 = 0 := by rw [hV0def, hF0]; exact polyDeriv_zero_fun _ _ _
      rw [this, norm_zero] at hV0pos
      exact lt_irrefl 0 hV0pos

  set a : ℝ := 2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q with hadef
  have ha0 : 0 ≤ a := by
    have := Cchi_nonneg (E := E) P.m; have := ph_nonneg P; have := Real.pi_pos
    rw [hadef]; positivity
  set w : ℝ := 4⁻¹ * P.K6⁻¹ * Real.exp (-a) with hwdef
  have hK6 := inv_constant_nonneg P
  have hJ : P.Jbound n = (∏ _k : Fin n, w) * (2 : ℝ)⁻¹ ^ ((X.r + 2) * DF bs) := by
    have hwn : w ^ n = (4 : ℝ)⁻¹ ^ n * P.K6⁻¹ ^ n *
        Real.exp (-(2 * Real.pi * n * Cchi (E := E) P.m * P.ph / P.q)) := by
      rw [hwdef, mul_pow, mul_pow, ← Real.exp_nat_mul]
      congr 2
      rw [hadef]
      ring
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hwn, Par.Jbound, Par.K6]
    ring
  have hmain : P.Jbound n * X.l2 P.q F₀ ≤ ‖V0‖ ^ 2 := by
    have hsq : (Ce * Mμ * Dt / 2) ^ 2 ≤ ‖V0‖ ^ 2 := pow_le_pow_left₀ (by positivity) hV0ge 2
    refine le_trans ?_ hsq
    rw [hJ, hl2F, prod_cols hD (fun _ => w), prod_cols hD (fun k => X.l2 P.q (sc k))]
    have he1 : (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), w) *
        (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), X.l2 P.q (sc k)) ≤ Ce ^ 2 := by
      rw [← Finset.prod_mul_distrib, hCedef, ← Finset.prod_pow]
      refine Finset.prod_le_prod (fun k _ => mul_nonneg (by positivity) (l2NormSq_nonneg_gaussianTorus X P.q _))
        fun k hk => ?_
      rw [Finset.mem_filter] at hk
      rw [hsc_none k hk.2, hwdef]
      have h1 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      have h2 := hsel
      have h3 : (1 : ℝ) / 4 ≤ ‖se 0‖ ^ 2 := by nlinarith
      have h4 := l2NormSq_nonneg_gaussianTorus X P.q se
      have h5 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
      nlinarith [mul_nonneg hK6 h4, mul_le_mul_of_nonneg_left h1 (mul_nonneg hK6 h4)]
    have he2 : (∏ p : (Σ j : Fin nb, Fin (bs j).i), w) *
        (∏ p : (Σ j : Fin nb, Fin (bs j).i), X.l2 P.q (sc (colB bs p))) ≤ 4⁻¹ * Mμ ^ 2 := by
      rw [← Finset.prod_mul_distrib]
      calc ∏ p : (Σ j : Fin nb, Fin (bs j).i), (w * X.l2 P.q (sc (colB bs p)))
          ≤ ∏ p : (Σ j : Fin nb, Fin (bs j).i), (4⁻¹ * ‖μ p‖ ^ 2) := by
            refine Finset.prod_le_prod (fun p _ => mul_nonneg (by positivity) (l2NormSq_nonneg_gaussianTorus X P.q _))
              fun p _ => ?_
            rw [hsc_col, hwdef]
            have := hl2 p.1 p.2
            nlinarith
        _ = (4⁻¹) ^ m * Mμ ^ 2 := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hMμdef, Finset.prod_pow]
        _ ≤ 4⁻¹ * Mμ ^ 2 := by
            have hm1 : 1 ≤ m := card_pos_pos bs P.hDF
            have : ((4 : ℝ)⁻¹) ^ m ≤ 4⁻¹ := by
              calc ((4 : ℝ)⁻¹) ^ m ≤ (4⁻¹) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm1
                _ = 4⁻¹ := pow_one _
            gcongr
    have he3 : (2 : ℝ)⁻¹ ^ ((X.r + 2) * DF bs) ≤ Dt ^ 2 := by
      have hδsq : δ0 ^ 2 = (2 : ℝ)⁻¹ ^ (X.r + 2) := by
        rw [hδ0def, div_pow, ← Real.rpow_natCast ((2 : ℝ) ^ (-(X.r : ℝ) / 2)) 2,
          ← Real.rpow_mul (by norm_num)]
        have h2 : (-(X.r : ℝ) / 2 * ((2 : ℕ) : ℝ)) = -(X.r : ℝ) := by push_cast; ring
        rw [h2, Real.rpow_neg (by norm_num), Real.rpow_natCast, pow_add, inv_pow, inv_pow]
        ring
      have h1 : (2 : ℝ)⁻¹ ^ ((X.r + 2) * DF bs) = (δ0 ^ DF bs) ^ 2 := by
        rw [pow_mul, ← hδsq, ← pow_mul, ← pow_mul, mul_comm]
      rw [h1]
      exact pow_le_pow_left₀ (by positivity) hDt 2
    have hA : 0 ≤ (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), w) *
        (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), X.l2 P.q (sc k)) :=
      mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
        (Finset.prod_nonneg fun _ _ => l2NormSq_nonneg_gaussianTorus X P.q _)
    have hB : 0 ≤ (∏ p : (Σ j : Fin nb, Fin (bs j).i), w) *
        (∏ p : (Σ j : Fin nb, Fin (bs j).i), X.l2 P.q (sc (colB bs p))) :=
      mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
        (Finset.prod_nonneg fun _ _ => l2NormSq_nonneg_gaussianTorus X P.q _)
    calc (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), w) *
          (∏ p : (Σ j : Fin nb, Fin (bs j).i), w) * (2 : ℝ)⁻¹ ^ ((X.r + 2) * DF bs) *
          ((∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), X.l2 P.q (sc k)) *
            ∏ p : (Σ j : Fin nb, Fin (bs j).i), X.l2 P.q (sc (colB bs p)))
        = ((∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), w) *
            (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), X.l2 P.q (sc k))) *
          ((∏ p : (Σ j : Fin nb, Fin (bs j).i), w) *
            (∏ p : (Σ j : Fin nb, Fin (bs j).i), X.l2 P.q (sc (colB bs p)))) *
          (2 : ℝ)⁻¹ ^ ((X.r + 2) * DF bs) := by ring
      _ ≤ Ce ^ 2 * (4⁻¹ * Mμ ^ 2) * Dt ^ 2 := by
          gcongr
      _ = (Ce * Mμ * Dt / 2) ^ 2 := by ring

  set c : ℂ := (((Real.sqrt (X.l2 P.q F₀))⁻¹ : ℝ) : ℂ) with hcdef
  have hsq : 0 < Real.sqrt (X.l2 P.q F₀) := Real.sqrt_pos.2 hl2pos
  refine ⟨c • F₀, Submodule.smul_mem _ _ hF₀, ?_, ?_⟩
  · rw [l2_smul, hcdef, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hsq, inv_pow,
      Real.sq_sqrt hl2pos.le, inv_mul_cancel₀ hl2pos.ne']
  · rw [polyDeriv_smul_fun _ _ (sec_contDiff X hF₀), ← hV0def, norm_mul, mul_pow, hcdef,
      Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hsq, inv_pow, Real.sq_sqrt hl2pos.le,
      inv_mul_eq_div, le_div_iff₀ hl2pos]
    exact hmain

end Core

theorem jOf (hx : Ext.All) (hs : SplitStatement) (hc : CharStatement) (ht : ColTorusStatement)
    (ha : ColAbelStatement) (he : ColEmptyStatement) : JStatement := by
  intro E _ _ _ X n nb bs hD P
  exact jof_core hx hs hc ht ha he X bs hD P

end ReciprocityTheory.ChartRestriction.G.I2
end
