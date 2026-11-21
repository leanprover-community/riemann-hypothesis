import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr

section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

abbrev WTZ (E : Type) [Field E] : Type := ((E →+* ℂ) × ℕ → ℤ) × ℤ

def wtZ {E : Type} [Field E] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : WTZ E := (fun x => (a x : ℤ), (n : ℤ))

theorem wtZ_add {E : Type} [Field E] (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) :
    wtZ (a + a') (n + n') = wtZ a n + wtZ a' n' := by
  unfold wtZ
  ext <;> simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

abbrev AC (Z : Comp Xo c) : Type := AddMonoidAlgebra (Om Z) (WTZ E)

example (Z : Comp Xo c) : Algebra (𝓞 c.F) (AC Z) := inferInstance

example (Z : Comp Xo c) : IsScalarTower (𝓞 c.F) c.F (AC Z) := inferInstance

instance towKAC (Z : Comp Xo c) : IsScalarTower c.F (Om Z) (AC Z) := inferInstance

def AG (Z : Comp Xo c) (G : WTZ E) : Submodule (Om Z) (AC Z) :=
  Submodule.span (Om Z) {AddMonoidAlgebra.single G 1}

theorem mem_AG {Z : Comp Xo c} {G : WTZ E} {f : AC Z} : f ∈ AG Z G ↔ ∃ r : Om Z, f = AddMonoidAlgebra.single G r := by
  unfold AG
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, by rw [AddMonoidAlgebra.smul_single', mul_one]⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, by rw [AddMonoidAlgebra.smul_single', mul_one]⟩

instance gradedAG (Z : Comp Xo c) : SetLike.GradedMonoid (AG Z) where
  one_mem := mem_AG.2 ⟨1, rfl⟩
  mul_mem := by
    intro G G' f g hf hg
    obtain ⟨r, rfl⟩ := mem_AG.1 hf
    obtain ⟨s, rfl⟩ := mem_AG.1 hg
    exact mem_AG.2 ⟨r * s, by rw [AddMonoidAlgebra.single_mul_single]⟩

theorem finrank_AG (Z : Comp Xo c) (G : WTZ E) : Module.finrank (Om Z) (AG Z G) = 1 :=
  finrank_span_singleton (by simp)

theorem mul_ne_zero_AG {Z : Comp Xo c} {G G' : WTZ E} {f g : AC Z} (hf : f ∈ AG Z G) (hg : g ∈ AG Z G')
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) : f * g ≠ 0 := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  obtain ⟨s, rfl⟩ := mem_AG.1 hg
  have hr : r ≠ 0 := by
    rintro rfl
    exact hf0 (by simp)
  have hs : s ≠ 0 := by
    rintro rfl
    exact hg0 (by simp)
  rw [AddMonoidAlgebra.single_mul_single]
  simp [hr, hs]

def valC (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) : ∀ Z : Comp Xo c, AC Z :=
  fun Z => AddMonoidAlgebra.single (wtZ a n) (evC h Z f)

theorem valC_mem (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) (Z : Comp Xo c) :
    valC h a n f Z ∈ AG Z (wtZ a n) := mem_AG.2 ⟨_, rfl⟩

end Formalism.L2.Pj
end
end

section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def exZ (Dw : Datum H) (G : WTZ E) : Ix Dw → ℤ
  | none => G.2
  | some x => G.1 (x.1, x.2)

theorem exZ_add (G G' : WTZ E) (i : Ix Dw) : exZ Dw (G + G') i = exZ Dw G i + exZ Dw G' i := by
  cases i <;> rfl

def frW (δ : Ix Dw → ℤ) (G : WTZ E) : ℤ := ∑ i, exZ Dw G i * δ i

theorem frW_add (δ : Ix Dw → ℤ) (G G' : WTZ E) : frW δ (G + G') = frW δ G + frW δ G' := by
  simp only [frW, exZ_add, add_mul, Finset.sum_add_distrib]

variable {Z : Comp Xo c}

def ordC (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) (G : WTZ E) (x : AC Z) : ℤ :=
  WithTop.untopD 0 (v (x.coeff G)) + frW δ G

theorem ordC_single (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) (G : WTZ E) {r : Om Z} (hr : r ≠ 0) :
    ((ordC δ v G (AddMonoidAlgebra.single G r) : ℤ) : WithTop ℤ) = v r + (frW δ G : WithTop ℤ) := by
  have hv : v r ≠ ⊤ := fun h => hr ((AddValuation.top_iff v).1 h)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hv
  simp only [ordC, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, ← hn, WithTop.untopD_coe]
  push_cast; rfl

theorem ordC_mul (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) {G G' : WTZ E} {f g : AC Z}
    (hf : f ∈ AG Z G) (hg : g ∈ AG Z G') (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    ordC δ v (G + G') (f * g) = ordC δ v G f + ordC δ v G' g := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  obtain ⟨s, rfl⟩ := mem_AG.1 hg
  have hr : r ≠ 0 := fun h => hf0 (by simp [h])
  have hs : s ≠ 0 := fun h => hg0 (by simp [h])
  rw [AddMonoidAlgebra.single_mul_single]
  apply WithTop.coe_injective
  rw [ordC_single δ v _ (mul_ne_zero hr hs)]
  push_cast
  rw [ordC_single δ v _ hr, ordC_single δ v _ hs, AddValuation.map_mul, frW_add]
  push_cast
  ac_rfl

theorem ordC_smul (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) {G : WTZ E} {f : AC Z} (a : Om Z)
    (hf : f ∈ AG Z G) (hf0 : f ≠ 0) (ha : a ≠ 0) :
    ((ordC δ v G (a • f) : ℤ) : WithTop ℤ) = v a + (ordC δ v G f : WithTop ℤ) := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  have hr : r ≠ 0 := fun h => hf0 (by simp [h])
  rw [AddMonoidAlgebra.smul_single', ordC_single δ v _ (mul_ne_zero ha hr), ordC_single δ v _ hr,
    AddValuation.map_mul, add_assoc]

abbrev sgOf (P : Om Z →+* ℂ) : c.F →+* ℂ := P.comp (algebraMap c.F (Om Z))

def PAlg (P : Om Z →+* ℂ) : Om Z →ₐ[c.F] CAt (sgOf P) :=
  { P with commutes' := fun _ => rfl }

def CBase (h : GenFrEx Xo c) (Z : Comp Xo c) (yP : ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) : Prop :=
  ∀ P, FrMap (PAlg P) (genFr h Z) (yP P)

def nrmC (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) (G : WTZ E) (x : AC Z) (P : Om Z →+* ℂ) : ℝ :=
  ‖P (x.coeff G)‖ * ∏ i, |fn _ (yP P) i| ^ (-exZ Dw G i)

variable (Xo c) in

def FnNe (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) : Prop := ∀ σ y i, fn σ y i ≠ 0

section nrm

variable (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
  (yP : ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))

theorem nrmC_zero (G : WTZ E) (P : Om Z →+* ℂ) : nrmC fn yP G 0 P = 0 := by
  simp only [nrmC, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, map_zero, norm_zero, zero_mul]

theorem nrmC_single (G : WTZ E) (r : Om Z) (P : Om Z →+* ℂ) :
    nrmC fn yP G (AddMonoidAlgebra.single G r) P = ‖P r‖ * ∏ i, |fn _ (yP P) i| ^ (-exZ Dw G i) := by
  simp only [nrmC, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]

theorem nrmC_pos (hfn : FnNe Xo c fn) {G : WTZ E} {f : AC Z} (P : Om Z →+* ℂ) (hf : f ∈ AG Z G) (hf0 : f ≠ 0) :
    0 < nrmC fn yP G f P := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  have hr : r ≠ 0 := fun h => hf0 (by simp [h])
  rw [nrmC_single]
  refine mul_pos (norm_pos_iff.2 ((map_ne_zero P).2 hr)) (Finset.prod_pos fun i _ => ?_)
  exact zpow_pos (abs_pos.2 (hfn _ _ i)) _

theorem nrmC_mul (hfn : FnNe Xo c fn) {G G' : WTZ E} {f g : AC Z} (P : Om Z →+* ℂ) (hf : f ∈ AG Z G)
    (hg : g ∈ AG Z G') : nrmC fn yP (G + G') (f * g) P = nrmC fn yP G f P * nrmC fn yP G' g P := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  obtain ⟨s, rfl⟩ := mem_AG.1 hg
  rw [AddMonoidAlgebra.single_mul_single, nrmC_single, nrmC_single, nrmC_single, map_mul, norm_mul]
  have : ∏ i, |fn _ (yP P) i| ^ (-exZ Dw (G + G') i) =
      (∏ i, |fn _ (yP P) i| ^ (-exZ Dw G i)) * ∏ i, |fn _ (yP P) i| ^ (-exZ Dw G' i) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [exZ_add, neg_add, zpow_add₀ (abs_ne_zero.2 (hfn _ _ i))]
  rw [this]; ring

theorem nrmC_smul {G : WTZ E} {f : AC Z} (P : Om Z →+* ℂ) (a : Om Z) (hf : f ∈ AG Z G) :
    nrmC fn yP G (a • f) P = ‖P a‖ * nrmC fn yP G f P := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  rw [AddMonoidAlgebra.smul_single', nrmC_single, nrmC_single, map_mul, norm_mul, mul_assoc]

end nrm

variable (Xo c) in

def FnConj (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) : Prop :=
  ∀ Z (G : WTZ E) (x : AC Z) (P : Om Z →+* ℂ),
    nrmC fn (yP Z) G x ((starRingEnd ℂ).comp P) = nrmC fn (yP Z) G x P

end Formalism.L2.Pj
end
end
