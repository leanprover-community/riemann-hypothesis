import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G]

def ExpIdent (U : UnifPre I D A G) (e k : ℕ)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (S : Finset D.toPre.X) : Prop :=
  ∀ (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι)) (j₁ : Fin 1 → U.LG.L.ι)
      (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι),
      j₁ 0 = p.2 PUnit.unit →
      CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
        (Sum.elim (fun _ => p.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) →
      (res (inf_le_left.trans inf_le_left :
          U.expW e p j₁ S jf jt ≤ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left)
            (U.LG.L.pull (fstG I e G).left)).U p) ((U.w e).s p)).val ^ k *
        ((thickObj R I e G).left.presheaf.map (homOfLE (inf_le_left.trans inf_le_right :
          U.expW e p j₁ S jf jt ≤
            (fstG I e G).left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁)).op).hom
          (((fstG I e G).left.app _).hom (σ.f j₁)) =
      ∑ α ∈ S.attach,
        ((thickObj R I e G).left.presheaf.map
            (homOfLE (U.expW_le_f e p j₁ jf jt α.2)).op).hom
            (((U.gt e).pG.left.app _).hom ((f α.1).f (jf α.1))) *
          (res (U.expWeight_le_chart_weight e p j₁ jf jt α.2) (((U.gt e).t α.1).s (jt α.1))).val

lemma sum_attach_mono {X β : Type} [AddCommMonoid β] {S S' : Finset X} (hSS : S ⊆ S')
    (T : S' → β) (h0 : ∀ α : S', α.1 ∉ S → T α = 0) :
    ∑ α ∈ S'.attach, T α = ∑ α ∈ S.attach, T ⟨α.1, hSS α.2⟩ := by
  classical
  set g : X → β := fun α => if h : α ∈ S' then T ⟨α, h⟩ else 0 with hg
  have h1 : ∑ α ∈ S'.attach, T α = ∑ α ∈ S', g α := by
    rw [← Finset.sum_attach S' g]
    exact Finset.sum_congr rfl fun α _ => by simp only [hg, dif_pos α.2]
  have h2 : ∑ α ∈ S.attach, T ⟨α.1, hSS α.2⟩ = ∑ α ∈ S, g α := by
    rw [← Finset.sum_attach S g]
    exact Finset.sum_congr rfl fun α _ => by simp only [hg, dif_pos (hSS α.2)]
  rw [h1, h2]
  exact (Finset.sum_subset hSS fun α hα' hα => by
    simp only [hg, dif_pos hα']
    exact h0 ⟨α, hα'⟩ hα).symm

theorem expIdent_mono (U : UnifPre I D A G) (e k : ℕ)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) {S S' : Finset D.toPre.X} (hSS : S ⊆ S')
    (hvan : ∀ α ∉ S, ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt e).pG.left.app _).hom ((f α).f j) = 0)
    (h : ExpIdent U e k σ f S) : ExpIdent U e k σ f S' := by
  classical
  intro p j₁ jf jt hj hcoh'
  set m : PUnit.{1} ⊕ ((S × Fin 4) ⊕ (S × Fin 4)) → PUnit.{1} ⊕ ((S' × Fin 4) ⊕ (S' × Fin 4)) :=
    Sum.map id (Sum.map (fun a => (⟨a.1.1, hSS a.1.2⟩, a.2)) (fun a => (⟨a.1.1, hSS a.1.2⟩, a.2)))
    with hm
  have hcoh : CohAll D.toPre.P.L
      (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
        (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
          (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
      (Sum.elim (fun _ => p.1 PUnit.unit)
        (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) := by
    intro a b hab
    have h1 := hcoh' (m a) (m b) (by
      rcases a with a | a | a <;> rcases b with b | b | b <;> exact hab)
    rcases a with a | a | a <;> rcases b with b | b | b <;> exact h1
  have hS := h p j₁ jf jt hj hcoh
  have hle : U.expW e p j₁ S' jf jt ≤ U.expW e p j₁ S jf jt :=
    inf_le_inf_left _ (Finset.inf_mono hSS)
  have key := congrArg (rs hle) hS
  simp only [rs, res, Units.coe_map, MonoidHom.coe_coe, map_mul, map_pow, map_sum] at key
  rw [sum_attach_mono hSS _ (fun α hα => by
    have h0 := hvan α.1 hα (jf α.1)
    erw [h0, map_zero, zero_mul])]
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  simp only [← CommRingCat.comp_apply, ← Functor.map_comp] at key
  convert key using 4
  all_goals first | rfl | exact Subsingleton.elim _ _ | skip
  all_goals (erw [Units.coe_map, Units.coe_map]; exact (rs_rs _ hle _).symm)

lemma map_map_hom {Z : Scheme.{0}} {U W V : Z.Opens} (h : W ≤ U) (h' : V ≤ W) (x : Γ(Z, U)) :
    (Z.presheaf.map (homOfLE h').op).hom ((Z.presheaf.map (homOfLE h).op).hom x) =
      (Z.presheaf.map (homOfLE (h'.trans h)).op).hom x := rs_rs h h' x

lemma sum_attach_dite {X β : Type} [DecidableEq X] [AddCommMonoid β] (S : Finset X) (g : S → β) :
    ∑ x ∈ S.attach, g x = ∑ x ∈ S, (if h : x ∈ S then g ⟨x, h⟩ else 0) := by
  rw [← Finset.sum_attach S (fun x => if h : x ∈ S then g ⟨x, h⟩ else 0)]
  exact Finset.sum_congr rfl fun x _ => by simp only [dif_pos x.2]

theorem expIdent_restrict [DecidableEq D.toPre.X] (U : UnifPre I D A G) (e k : ℕ)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (S : Finset D.toPre.X) (h : ExpIdent U e k σ f S)
    (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι)) (j₁ : Fin 1 → U.LG.L.ι)
    (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι) (hj : j₁ 0 = p.2 PUnit.unit)
    (hcoh : CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
        (Sum.elim (fun _ => p.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))))
    {O : (thickObj R I e G).left.Opens} (hO : O ≤ U.expW e p j₁ S jf jt) :
    (res (hO.trans (inf_le_left.trans inf_le_left)) ((U.w e).s p)).val ^ k *
        rs (hO.trans (inf_le_left.trans inf_le_right)) (((fstG I e G).left.app _).hom (σ.f j₁)) =
      ∑ α ∈ S, (if hα : α ∈ S then rs (hO.trans (U.expW_le_f e p j₁ jf jt hα))
          (((U.gt e).pG.left.app _).hom ((f α).f (jf α))) *
        (res (hO.trans (U.expWeight_le_chart_weight e p j₁ jf jt hα)) (((U.gt e).t α).s (jt α))).val else 0) := by
  have key := congrArg (rs hO) (h p j₁ jf jt hj hcoh)
  simp only [rs, res, Units.coe_map, MonoidHom.coe_coe, map_mul, map_pow, map_sum, map_map_hom] at key
  rw [sum_attach_dite] at key
  refine key.trans (Finset.sum_congr rfl fun α hα => ?_)
  simp only [dif_pos hα]
  congr 1
  erw [Units.coe_map, map_map_hom]
  rfl

theorem expIdent_pull [DecidableEq D.toPre.X] (U : UnifPre I D A G) (e k : ℕ)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (S : Finset D.toPre.X) (h : ExpIdent U e k σ f S)
    (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι)) (j₁ : Fin 1 → U.LG.L.ι)
    (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι) (hj : j₁ 0 = p.2 PUnit.unit)
    (hcoh : CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
        (Sum.elim (fun _ => p.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))))
    {Z : Scheme.{0}} (hh : Z ⟶ (thickObj R I e G).left) {O : Z.Opens}
    (hO : O ≤ hh ⁻¹ᵁ U.expW e p j₁ S jf jt) :
    rs hO ((hh.app _).hom (res (inf_le_left.trans inf_le_left :
        U.expW e p j₁ S jf jt ≤ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left)
          (U.LG.L.pull (fstG I e G).left)).U p) ((U.w e).s p)).val) ^ k *
      rs hO ((hh.app _).hom (rs (inf_le_left.trans inf_le_right : U.expW e p j₁ S jf jt ≤
        (fstG I e G).left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁)
        (((fstG I e G).left.app _).hom (σ.f j₁)))) =
      ∑ α ∈ S, (if hα : α ∈ S then
        rs hO ((hh.app _).hom (rs (U.expW_le_f e p j₁ jf jt hα)
          (((U.gt e).pG.left.app _).hom ((f α).f (jf α))))) *
        rs hO ((hh.app _).hom (res (U.expWeight_le_chart_weight e p j₁ jf jt hα) (((U.gt e).t α).s (jt α))).val)
        else 0) := by
  have key := expIdent_restrict U e k σ f S h p j₁ jf jt hj hcoh (le_refl _)
  have key2 := congrArg (fun x => rs hO ((hh.app _).hom x)) key
  simp only [map_mul, map_pow, map_sum] at key2
  refine key2.trans (Finset.sum_congr rfl fun α hα => ?_)
  simp only [dif_pos hα, map_mul]

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

variable {X Y Y' Z : Scheme.{0}} (L : LB X) {K₁ K₂ K₃ K K' : Type} [Fintype K₁] [Fintype K₂] [Fintype K₃]
  [Fintype K] [Fintype K']

theorem secRel_pull (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ) (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁))
    (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)) (h : Y' ⟶ Y)
    (φ₃ : K₃ → (Y' ⟶ X)) (ε₃ : K₃ → ℤ) (u : LB.Gen (LB.LinComb L φ₃ ε₃))
    (hrel : GeneratorPullback.SecRel L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h φ₃ ε₃ u)
    (j₁ : K₁ → L.ι) (j₂ : K₂ → L.ι) (j₃ : K₃ → L.ι)
    (hcoh : LB.Coh L (Sum.elim φ₁ (Sum.elim (fun k => h ≫ φ₂ k) φ₃)) (Sum.elim j₁ (Sum.elim j₂ j₃)))
    (q : Z ⟶ Y') {O : Z.Opens}
    (h₁ : O ≤ q ⁻¹ᵁ LB.wchart L φ₁ j₁) (h₂ : O ≤ (q ≫ h) ⁻¹ᵁ LB.wchart L φ₂ j₂)
    (h₃ : O ≤ q ⁻¹ᵁ LB.wchart L φ₃ j₃) :
    rs h₁ ((q.app _).hom (s₁.f j₁)) =
      rs h₂ (((q ≫ h).app _).hom (s₂.f j₂)) * rs h₃ ((q.app _).hom (u.s j₃).val) := by
  have hOb : O ≤ q ⁻¹ᵁ (LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ⊓ LB.wchart L φ₃ j₃) := by
    intro z hz
    refine ⟨⟨h₁ hz, Set.mem_iInter.2 fun k => ?_⟩, h₃ hz⟩
    have := Set.mem_iInter.1 (h₂ hz) k
    simpa [Scheme.Hom.comp_apply] using this
  have key : rs (inf_le_left.trans inf_le_left : _ ≤ LB.wchart L φ₁ j₁) (s₁.f j₁) =
      rs ((inf_le_left.trans inf_le_right).trans (wchart_comp_le φ₂ h j₂)) ((h.app _).hom (s₂.f j₂)) *
      rs (inf_le_right : _ ≤ LB.wchart L φ₃ j₃) (u.s j₃).val := hrel j₁ j₂ j₃ hcoh
  have ha : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤ LB.wchart L φ₁ j₁ :=
    inf_le_left.trans inf_le_left
  have hb : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤
      h ⁻¹ᵁ LB.wchart L φ₂ j₂ := (inf_le_left.trans inf_le_right).trans (wchart_comp_le φ₂ h j₂)
  have hc : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤
      LB.wchart L φ₃ j₃ := inf_le_right
  have e1 : rs hOb ((q.app _).hom (rs ha (s₁.f j₁))) = rs h₁ ((q.app _).hom (s₁.f j₁)) :=
    (congrArg (rs hOb) (app_rs q ha (s₁.f j₁))).trans (rs_rs _ _ _)
  have e2 : rs hOb ((q.app _).hom (rs hb ((h.app _).hom (s₂.f j₂)))) =
      rs h₂ (((q ≫ h).app _).hom (s₂.f j₂)) := by
    rw [app_rs, rs_rs]
    rfl
  have e3 : rs hOb ((q.app _).hom (rs hc (u.s j₃).val)) = rs h₃ ((q.app _).hom (u.s j₃).val) :=
    (congrArg (rs hOb) (app_rs q hc (u.s j₃).val)).trans (rs_rs _ _ _)
  rw [← e1, ← e2, ← e3, ← rs_mul, ← map_mul]
  exact congrArg (fun x => rs hOb ((q.app _).hom x)) key

theorem corr_pull (φ : K → (Y' ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y' ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (hc : LB.Gen.Corr L φ ε φ' ε' t t') (j : K → L.ι) (j' : K' → L.ι) (hj : LB.Coh L φ j)
    (hj' : LB.Coh L φ' j') (hjj : ∀ k k', φ k = φ' k' → j k = j' k')
    (q : Z ⟶ Y') {O : Z.Opens} (h₁ : O ≤ q ⁻¹ᵁ LB.wchart L φ j) (h₂ : O ≤ q ⁻¹ᵁ LB.wchart L φ' j') :
    rs h₁ ((q.app _).hom (t.s j).val) = rs h₂ ((q.app _).hom (t'.s j').val) := by
  have hO : O ≤ q ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ' j') := fun z hz => ⟨h₁ hz, h₂ hz⟩
  have key : rs (inf_le_left : _ ≤ LB.wchart L φ j) (t.s j).val =
      rs (inf_le_right : _ ≤ LB.wchart L φ' j') (t'.s j').val := by
    exact congrArg Units.val (hc j j' hj hj' hjj)
  have e1 : rs hO ((q.app _).hom (rs (inf_le_left : _ ≤ LB.wchart L φ j) (t.s j).val)) =
      rs h₁ ((q.app _).hom (t.s j).val) :=
    (congrArg (rs hO) (app_rs q (inf_le_left : _ ≤ LB.wchart L φ j) (t.s j).val)).trans (rs_rs _ _ _)
  have e2 : rs hO ((q.app _).hom (rs (inf_le_right : _ ≤ LB.wchart L φ' j') (t'.s j').val)) =
      rs h₂ ((q.app _).hom (t'.s j').val) :=
    (congrArg (rs hO) (app_rs q (inf_le_right : _ ≤ LB.wchart L φ' j') (t'.s j').val)).trans (rs_rs _ _ _)
  rw [← e1, ← e2]
  exact congrArg (fun x => rs hO ((q.app _).hom x)) key

lemma rs_app_comp' {Z Y X : Scheme.{0}} (h : Z ⟶ Y) (ψ : Y ⟶ X) {U : X.Opens} {W : Y.Opens}
    {V : Z.Opens} (hW : W ≤ ψ ⁻¹ᵁ U) (hV : V ≤ h ⁻¹ᵁ W) (hV' : V ≤ (h ≫ ψ) ⁻¹ᵁ U) (x : Γ(X, U)) :
    rs hV ((h.app W).hom (rs hW ((ψ.app U).hom x))) = rs hV' (((h ≫ ψ).app U).hom x) := by
  rw [app_rs, rs_rs, Scheme.Hom.comp_app]
  rfl

theorem rs_app_mulGen (φ : K → (Y' ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y' ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (j : K ⊕ K' → L.ι)
    (q : Z ⟶ Y') {O : Z.Opens} (h : O ≤ q ⁻¹ᵁ LB.wchart L (Sum.elim φ φ') j)
    (h₁ : O ≤ q ⁻¹ᵁ LB.wchart L φ (j ∘ Sum.inl)) (h₂ : O ≤ q ⁻¹ᵁ LB.wchart L φ' (j ∘ Sum.inr)) :
    rs h ((q.app _).hom ((LB.mulGen L φ ε φ' ε' t t').s j).val) =
      rs h₁ ((q.app _).hom (t.s (j ∘ Sum.inl)).val) * rs h₂ ((q.app _).hom (t'.s (j ∘ Sum.inr)).val) := by
  simp only [LB.mulGen, Units.val_mul, map_mul, rs_mul]
  congr 1
  · exact (congrArg (rs h) (app_rs q _ (t.s (j ∘ Sum.inl)).val)).trans (rs_rs _ _ _)
  · exact (congrArg (rs h) (app_rs q _ (t'.s (j ∘ Sum.inr)).val)).trans (rs_rs _ _ _)

theorem rs_app_pullGen {W : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε))
    (g : W ⟶ Y) (j : K → L.ι) (q : Z ⟶ W) {O : Z.Opens}
    (h : O ≤ q ⁻¹ᵁ LB.wchart L (fun k => g ≫ φ k) j) (h' : O ≤ (q ≫ g) ⁻¹ᵁ LB.wchart L φ j) :
    rs h ((q.app _).hom ((LB.pullGen L φ ε c g).s j).val) = rs h' (((q ≫ g).app _).hom (c.s j).val) :=
  (congrArg (rs h) (app_rs q (wchart_comp_le φ g j) ((g.app _).hom (c.s j).val))).trans (rs_rs _ _ _)

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

def subSec {Y : Scheme.{0}} {M : LB Y} (s s' : LB.Sec M) : LB.Sec M where
  f j := s.f j - s'.f j
  compat i j := by rw [map_sub, map_sub, s.compat, s'.compat, mul_sub]

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

def pullφB {D : DegPre V} {O : Type} [Ring O] [StarRing O] [Module O D.X] (oa : D.OAct O) (a : O)
    (χ : D.X) : Fin 4 ⊕ Fin 4 → (D.P.A.left ⟶ D.P.A.left) :=
  Sum.elim (DegPre.famφB D (star a • χ)) (fun i => (oa.onB.act a).left ≫ DegPre.famφB D χ i)

lemma cross_alg {Γ : Type} [CommRing Γ] {Jx Xc : Type} [DecidableEq Xc] (S : Finset Jx) (S'' : Finset Xc)
    (g : Jx → Xc) (hg : Set.InjOn g S) (hS : S.image g ⊆ S'') (W W' : Γˣ) (m n : ℕ) (Z Y : Fin 2 → Γ)
    (P1 : Fin 2 → Xc → Γ) (P2 A : Fin 2 → Jx → Γ) (c : Jx → Γ) (ξ : Γ)
    (E1 : ∀ i, (W : Γ) ^ m * Z i = ∑ β ∈ S'', P1 i β)
    (E2 : ∀ i, (W' : Γ) ^ n * Y i = ∑ α ∈ S, P2 i α)
    (E1' : ∀ i, ∀ χ ∈ S, P1 i (g χ) = A i χ * ξ * c χ)
    (E2' : ∀ i, ∀ α ∈ S, P2 i α = A i α * c α)
    (E5 : ∀ i, ∀ β ∈ S'', β ∉ S.image g → P1 i β = 0) :
    Z 0 * Y 1 - Z 1 * Y 0 = 0 := by
  have key : ∀ i, (W : Γ) ^ m * Z i = ξ * ((W' : Γ) ^ n * Y i) := by
    intro i
    rw [E1 i, E2 i, ← Finset.sum_subset hS (fun β hβ hn => E5 i β hβ hn), Finset.sum_image hg, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun χ hχ => ?_)
    rw [E1' i χ hχ, E2' i χ hχ]
    ring
  have hu : IsUnit ((W : Γ) ^ m) := (Units.isUnit W).pow m
  refine hu.mul_right_eq_zero.mp ?_
  linear_combination (Y 1) * key 0 - (Y 0) * key 1

lemma rs_app_of_eq {Z X : Scheme.{0}} {f g : Z ⟶ X} (e : f = g) {U : X.Opens} {V : Z.Opens}
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) (x : Γ(X, U)) :
    rs hf ((f.app U).hom x) = rs hg ((g.app U).hom x) := by
  subst e
  rfl

lemma rs_app_comp {Z Y X : Scheme.{0}} (h : Z ⟶ Y) (ψ : Y ⟶ X) {U : X.Opens} {W : Y.Opens}
    {V : Z.Opens} (hW : W ≤ ψ ⁻¹ᵁ U) (hV : V ≤ h ⁻¹ᵁ W) (hV' : V ≤ (h ≫ ψ) ⁻¹ᵁ U) (x : Γ(X, U)) :
    rs hV ((h.app W).hom (rs hW ((ψ.app U).hom x))) = rs hV' (((h ≫ ψ).app U).hom x) := by
  change (ψ.appLE U W hW ≫ h.appLE W V hV).hom x = ((h ≫ ψ).appLE U V hV').hom x
  first
    | rw [Scheme.Hom.appLE_comp_appLE]
    | rw [Scheme.Hom.appLE, Category.assoc, Scheme.Hom.map_appLE, Scheme.Hom.comp_appLE]

lemma fstG_act {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ) {G : Over (Spec (CommRingCat.of R))}
    (f : G ⟶ G) :
    ((Over.pullback (thick R I e)).map f).left ≫ (fstG I e G).left = (fstG I e G).left ≫ f.left := by
  simp only [fstG]
  simp
  first
    | exact pullback.lift_fst _ _ _
    | erw [pullback.lift_fst]

lemma pG_act {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) {O : Type} [Ring O] [StarRing O]
    [Module O D.toPre.X] {ιD : D.OAct O} {ιA : A.OAct O} {ιG : RingAct G O} (hlin : U.OLinear O ιD ιA ιG)
    (e : ℕ) (a : O) :
    ((Over.pullback (thick R I e)).map (ιG.act a)).left ≫ (U.gt e).pG.left =
      (U.gt e).pG.left ≫ (ιD.onB.act a).left := by
  have hq := congrArg (fun φ => φ.left) (hlin.q_lin e a)
  simp only [Over.comp_left] at hq
  unfold GtCoord.pG
  simp only [Over.comp_left, Over.map_map_left, Category.assoc]
  rw [← Category.assoc, hq, Category.assoc]
  congr 1
  first
    | exact fstG_act I e (ιD.onB.act a)
    | (unfold DegPre.prBe; simp; done)
    | (unfold DegPre.prBe; simp; exact pullback.lift_fst _ _ _)

lemma mem_finset_inf' {Y : Scheme.{0}} {κ : Type} (s : Finset κ) (F : κ → Y.Opens) (y : Y)
    (h : ∀ i ∈ s, y ∈ F i) : y ∈ s.inf F := by
  exact Finset.inf_induction (p := fun O : Y.Opens => y ∈ O) (by simp) (fun a ha b hb => ⟨ha, hb⟩) h

lemma le_finset_inf' {Y : Scheme.{0}} {κ : Type} {s : Finset κ} {F : κ → Y.Opens} {i : κ} (hi : i ∈ s) :
    s.inf F ≤ F i := Finset.inf_le hi

lemma pG_lift {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ) (χ : D.toPre.X) :
    (U.gt e).pG.left ≫ (lift (toUnit D.toPre.P.A ≫ D.toPre.c χ) (𝟙 D.toPre.P.A)).left =
      (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left := by
  first
    | rw [← Over.comp_left, comp_lift, comp_toUnit_assoc, Category.comp_id]
    | simp [← Over.comp_left]

lemma le_comp_of_eq {Z Y Y' X : Scheme.{0}} {f : Z ⟶ Y} {g : Y ⟶ X} {f' : Z ⟶ Y'} {g' : Y' ⟶ X}
    (h : f ≫ g = f' ≫ g') {U : X.Opens} {O : Z.Opens} (hO : O ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U)) :
    O ≤ (f' ≫ g') ⁻¹ᵁ U := by
  rw [← h]
  exact hO

lemma rs_zero' {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) : rs h (0 : Γ(Z, U)) = 0 := map_zero _

lemma rs_sub' {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (x y : Γ(Z, U)) : rs h (x - y) = rs h x - rs h y := map_sub _ x y

set_option maxHeartbeats 4000000 in

theorem cross_vanish (hL4 : Laws4) {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {H : Geo.Tor.Host E} {t : Geo.Tor.SAB H (Spec (CommRingCat.of V))}
    (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (k N : ℕ) (e : ℕ)
    (X : letI := H.starRing; LB.Gen (LB.LinComb P.D.toPre.P.L
      ![𝟙 P.D.toPre.P.A.left, (P.oD.onB.act a).left] ![((k * N : ℕ) : ℤ), -(k : ℤ)]))
    (hX : X.IsGen)
    (uR : letI := H.starRing; LB.Gen (LB.LinComb P.D.toPre.P.L
      (rosatiφ P.D.toPre.P.A (P.oD.onB.act (star a)) (P.oD.onB.act a)) rosatiε))
    (huR : uR.IsGen)
    (huR0 : LB.Gen.Corr P.D.toPre.P.L _ _ _ _
      (LB.pullGen P.D.toPre.P.L _ _ uR (zero2 P.D.toPre.P.A)) (LB.oneGen P.D.toPre.P.L))
    (hinj : letI := H.starRing; Function.Injective fun χ : P.D.toPre.X => star a • χ)
    (σ'' : Fin 2 → LB.Sec (LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => 𝟙 t.G.left)
      (fun _ => ((k * N : ℕ) : ℤ))))
    (τ : Fin 2 → LB.Sec (LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ))))
    (f'' : Fin 2 → ∀ α : P.D.toPre.X, P.D.toPre.SecB (k * N) α)
    (f : Fin 2 → ∀ α : P.D.toPre.X, P.D.toPre.SecB k α)
    (h'' : ∀ i, P.U.ExpandsAt e (k * N) (σ'' i) (f'' i))
    (hf : ∀ i, P.U.ExpandsAt e k (τ i) (f i))
    (hrel : letI := H.starRing; ∀ i χ, ∃ u : LB.Gen (LB.LinComb P.D.toPre.P.L (pullφB P.oD a χ) (pullε k N)),
      u.IsGen ∧
      LB.Gen.Corr P.D.toPre.P.L _ _ _ _ u (LB.mulGen P.D.toPre.P.L _ _ _ _ X
        (LB.pullGen P.D.toPre.P.L _ _ uR (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c χ) (𝟙 P.D.toPre.P.A)).left)) ∧
      GeneratorPullback.SecRel P.D.toPre.P.L (DegPre.famφB P.D.toPre (star a • χ)) (DegPre.famε (k * N))
        (f'' i (star a • χ)) (DegPre.famφB P.D.toPre χ) (DegPre.famε k) (f i χ) (P.oD.onB.act a).left
        (pullφB P.oD a χ) (pullε k N) u)
    (hoff : letI := H.starRing; ∀ i β, (∀ χ, β ≠ star a • χ) → ∀ j, (f'' i β).f j = 0) :
    ∀ j, ((fstG (maximalIdeal V) e t.G).left.app _).hom
      ((subSec
        (mulSec P.U.LG.L _ _ _ _ (σ'' 0) (pullSec P.U.LG.L _ _ (τ 1) (t.act.act a).left))
        (mulSec P.U.LG.L _ _ _ _ (σ'' 1) (pullSec P.U.LG.L _ _ (τ 0) (t.act.act a).left))).f j) = 0 := by
  classical
  intro j
  set W := (fstG (maximalIdeal V) e t.G).left ⁻¹ᵁ LB.wchart P.U.LG.L
    (Sum.elim (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ : Fin 1 => (t.act.act a).left ≫ 𝟙 t.G.left)) j with hWdef
  set z := ((fstG (maximalIdeal V) e t.G).left.app _).hom
      ((subSec
        (mulSec P.U.LG.L _ _ _ _ (σ'' 0) (pullSec P.U.LG.L _ _ (τ 1) (t.act.act a).left))
        (mulSec P.U.LG.L _ _ _ _ (σ'' 1) (pullSec P.U.LG.L _ _ (τ 0) (t.act.act a).left))).f j) with hzdef
  have hloc : ∀ y : W, ∃ O : (thickObj V (maximalIdeal V) e t.G).left.Opens, y.1 ∈ O ∧
      ∃ hOW : O ≤ W, rs hOW z = 0 := by
    intro y
    letI := H.starRing
    have hch : ∀ ψ : (thickObj V (maximalIdeal V) e t.G).left ⟶ P.D.toPre.P.A.left,
        ∃ i, ψ.base y.1 ∈ (P.D.toPre.P.L.U i : Set _) := by
      intro ψ
      have h1 : ψ.base y.1 ∈
          ((⨆ i, P.D.toPre.P.L.U i : P.D.toPre.P.A.left.Opens) : Set _) := by
        rw [P.D.toPre.P.isLB.cover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 h1
    choose cB hcB using hch
    obtain ⟨S''₀, hv''₀, hE''₀⟩ := h'' 0
    obtain ⟨S''₁, hv''₁, hE''₁⟩ := h'' 1
    obtain ⟨S₀, hv₀, hE₀⟩ := hf 0
    obtain ⟨S₁, hv₁, hE₁⟩ := hf 1
    obtain ⟨S, hSdef⟩ : ∃ S : Finset P.D.toPre.X,
        S = S₀ ∪ S₁ ∪ (S''₀ ∪ S''₁).preimage (fun χ => star a • χ) hinj.injOn := ⟨_, rfl⟩
    obtain ⟨S'', hS''def⟩ : ∃ S'' : Finset P.D.toPre.X, S'' = S''₀ ∪ S''₁ ∪ S.image (fun χ => star a • χ) :=
      ⟨_, rfl⟩
    have hvS : ∀ i, ∀ α ∉ S, ∀ jj : Fin 4 → P.D.toPre.P.L.ι,
        (((P.U.gt e).pG.left.app _).hom ((f i α).f jj)) = 0 := by
      intro i α hα jj
      fin_cases i
      · exact hv₀ α (fun h => hα (hSdef ▸ Finset.mem_union_left _ (Finset.mem_union_left _ h))) jj
      · exact hv₁ α (fun h => hα (hSdef ▸ Finset.mem_union_left _ (Finset.mem_union_right _ h))) jj
    have hE'' : ∀ i, ExpIdent P.U.toUnifPre e (k * N) (σ'' i) (f'' i) S'' := by
      intro i
      fin_cases i
      · exact expIdent_mono _ _ _ _ _ (fun x hx => hS''def ▸ Finset.mem_union_left _ (Finset.mem_union_left _ hx)) hv''₀ hE''₀
      · exact expIdent_mono _ _ _ _ _ (fun x hx => hS''def ▸ Finset.mem_union_left _ (Finset.mem_union_right _ hx)) hv''₁ hE''₁
    have hEτ : ∀ i, ExpIdent P.U.toUnifPre e k (τ i) (f i) S := by
      intro i
      fin_cases i
      · exact expIdent_mono _ _ _ _ _ (fun x hx => hSdef ▸ Finset.mem_union_left _ (Finset.mem_union_left _ hx)) hv₀ hE₀
      · exact expIdent_mono _ _ _ _ _ (fun x hx => hSdef ▸ Finset.mem_union_left _ (Finset.mem_union_right _ hx)) hv₁ hE₁
    have hF1 : ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left ≫ (fstG (maximalIdeal V) e t.G).left = (fstG (maximalIdeal V) e t.G).left ≫ (t.act.act a).left := fstG_act _ e _
    have hF2 : ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left ≫ (P.U.gt e).pG.left = (P.U.gt e).pG.left ≫ (P.oD.onB.act a).left := pG_act P.U.toUnifPre P.lin e a
    let p : (PUnit.{1} → P.D.toPre.P.L.ι) × (PUnit.{1} → P.U.LG.L.ι) :=
      (fun _ => cB (P.U.gt e).pG.left, fun _ => j (Sum.inl 0))
    let p' : (PUnit.{1} → P.D.toPre.P.L.ι) × (PUnit.{1} → P.U.LG.L.ι) :=
      (fun _ => cB (((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left ≫ (P.U.gt e).pG.left), fun _ => j (Sum.inr 0))
    let jf'' : P.D.toPre.X → Fin 4 → P.D.toPre.P.L.ι := fun β i => cB ((P.U.gt e).pG.left ≫ P.D.toPre.famφB β i)

    let jt'' : P.D.toPre.X → Fin 4 → P.D.toPre.P.L.ι := fun β i => cB (P.D.toPre.Oφ (P.U.gt e).pG β i)

    let jfτ : P.D.toPre.X → Fin 4 → P.D.toPre.P.L.ι := fun α i => cB (((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left ≫ (P.U.gt e).pG.left ≫ P.D.toPre.famφB α i)

    let jtτ : P.D.toPre.X → Fin 4 → P.D.toPre.P.L.ι := fun α i => cB (((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left ≫ P.D.toPre.Oφ (P.U.gt e).pG α i)

    have hcoh₁ : CohAll P.D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (P.U.gt e).pG.left)
          (Sum.elim (fun x : S'' × Fin 4 => (P.U.gt e).pG.left ≫ P.D.toPre.famφB x.1.1 x.2)
            (fun x : S'' × Fin 4 => P.D.toPre.Oφ (P.U.gt e).pG x.1.1 x.2)))
        (Sum.elim (fun _ => p.1 PUnit.unit)
          (Sum.elim (fun x : S'' × Fin 4 => jf'' x.1.1 x.2) (fun x : S'' × Fin 4 => jt'' x.1.1 x.2))) := by
      intro x x' hx
      rcases x with x | x | x <;> rcases x' with x' | x' | x' <;> exact congrArg cB hx
    have hcoh₂ : CohAll P.D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (P.U.gt e).pG.left)
          (Sum.elim (fun x : S × Fin 4 => (P.U.gt e).pG.left ≫ P.D.toPre.famφB x.1.1 x.2)
            (fun x : S × Fin 4 => P.D.toPre.Oφ (P.U.gt e).pG x.1.1 x.2)))
        (Sum.elim (fun _ => p'.1 PUnit.unit)
          (Sum.elim (fun x : S × Fin 4 => jfτ x.1.1 x.2) (fun x : S × Fin 4 => jtτ x.1.1 x.2))) := by
      intro x x' hx
      rcases x with x | x | x <;> rcases x' with x' | x' | x' <;> exact congrArg (fun ψ => cB (((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left ≫ ψ)) hx
    let O₁ := P.U.expW e p (j ∘ Sum.inl) S'' jf'' jt''
    let O₂ := ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left ⁻¹ᵁ P.U.expW e p' (j ∘ Sum.inr) S jfτ jtτ
    have hyW : y.1 ∈ W := y.2
    have hyL : ∀ b : Fin 1 ⊕ Fin 1, ((Sum.elim (fun _ : Fin 1 => 𝟙 t.G.left)
        (fun _ : Fin 1 => (t.act.act a).left ≫ 𝟙 t.G.left) b).base ((fstG (maximalIdeal V) e t.G).left.base y.1)) ∈
          (P.U.LG.L.U (j b) : Set _) := fun b => Set.mem_iInter.1 hyW b
    have hy₁ : y.1 ∈ O₁ := by
      refine ⟨⟨⟨Set.mem_iInter.2 fun _ => hcB (P.U.gt e).pG.left, Set.mem_iInter.2 fun _ => hyL (Sum.inl 0)⟩,
        Set.mem_iInter.2 fun b => hyL (Sum.inl b)⟩, mem_finset_inf' _ _ _ fun β _ =>
          ⟨Set.mem_iInter.2 fun i => ?_, Set.mem_iInter.2 fun i => hcB _⟩⟩
      have := hcB ((P.U.gt e).pG.left ≫ P.D.toPre.famφB β i)
      rwa [Scheme.Hom.comp_apply] at this
    have hfy : ((fstG (maximalIdeal V) e t.G).left).base (((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left.base y.1) = (t.act.act a).left.base (((fstG (maximalIdeal V) e t.G).left).base y.1) := by
      rw [← Scheme.Hom.comp_apply, hF1, Scheme.Hom.comp_apply]
    have hyLl : ∀ b : Fin 1, ((fstG (maximalIdeal V) e t.G).left).base y.1 ∈ (P.U.LG.L.U (j (Sum.inl b)) : Set _) := fun b => by
      have := Set.mem_iInter.1 hyW (Sum.inl b)
      simpa using this
    have hyR : ∀ b : Fin 1, (t.act.act a).left.base (((fstG (maximalIdeal V) e t.G).left).base y.1) ∈ (P.U.LG.L.U (j (Sum.inr b)) : Set _) :=
      fun b => by
        have := Set.mem_iInter.1 hyW (Sum.inr b)
        simpa using this
    have hy₂ : y.1 ∈ O₂ := by
      refine ⟨⟨⟨Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩, Set.mem_iInter.2 fun b => ?_⟩,
        mem_finset_inf' _ _ _ fun α _ => ⟨Set.mem_iInter.2 fun i => ?_, Set.mem_iInter.2 fun i => ?_⟩⟩
      · have := hcB (((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left ≫ (P.U.gt e).pG.left)
        rwa [Scheme.Hom.comp_apply] at this
      · exact (show ((fstG (maximalIdeal V) e t.G).left).base (((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left.base y.1) ∈ (P.U.LG.L.U (j (Sum.inr 0)) : Set _) by
          rw [hfy]; exact hyR 0)
      · exact (show ((fstG (maximalIdeal V) e t.G).left).base (((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left.base y.1) ∈ (P.U.LG.L.U (j (Sum.inr b)) : Set _) by
          rw [hfy]; exact hyR b)
      · have := hcB (((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left ≫ (P.U.gt e).pG.left ≫ P.D.toPre.famφB α i)
        rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this
      · have := hcB (((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left ≫ P.D.toPre.Oφ (P.U.gt e).pG α i)
        rwa [Scheme.Hom.comp_apply] at this

    let liftG : P.D.toPre.X → ((thickObj V (maximalIdeal V) e t.G).left ⟶ (P.D.toPre.P.A ⊗ P.D.toPre.P.A).left) :=
      fun χ => (lift (toUnit _ ≫ P.D.toPre.c χ) (P.U.gt e).pG).left
    let liftB : P.D.toPre.X → (P.D.toPre.P.A.left ⟶ (P.D.toPre.P.A ⊗ P.D.toPre.P.A).left) :=
      fun χ => (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c χ) (𝟙 P.D.toPre.P.A)).left
    have hlift : ∀ χ, (P.U.gt e).pG.left ≫ liftB χ = liftG χ := fun χ => pG_lift P.U.toUnifPre e χ

    let rosφ := rosatiφ P.D.toPre.P.A (P.oD.onB.act (star a)) (P.oD.onB.act a)
    let jR : P.D.toPre.X → Fin 6 → P.D.toPre.P.L.ι := fun χ k => cB (liftG χ ≫ rosφ k)
    let jB3 : P.D.toPre.X → Fin 4 ⊕ Fin 4 → P.D.toPre.P.L.ι := fun χ k => cB ((P.U.gt e).pG.left ≫ pullφB P.oD a χ k)
    let φX : Fin 2 → (P.D.toPre.P.A.left ⟶ P.D.toPre.P.A.left) := ![𝟙 P.D.toPre.P.A.left, (P.oD.onB.act a).left]
    let jX : Fin 2 → P.D.toPre.P.L.ι := fun k => cB ((P.U.gt e).pG.left ≫ φX k)

    let φT : P.D.toPre.X → (Fin 4 ⊕ Fin 6) → ((thickObj V (maximalIdeal V) e t.G).left ⟶ P.D.toPre.P.A.left) := fun χ =>
      Sum.elim (P.D.toPre.Oφ (P.U.gt e).pG (star a • χ)) (fun k => liftG χ ≫ rosφ k)
    let jT : P.D.toPre.X → (Fin 4 ⊕ Fin 6) → P.D.toPre.P.L.ι := fun χ => Sum.elim (jt'' (star a • χ)) (jR χ)
    let φT' : P.D.toPre.X → Fin 4 → ((thickObj V (maximalIdeal V) e t.G).left ⟶ P.D.toPre.P.A.left) := fun χ k => ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left ≫ P.D.toPre.Oφ (P.U.gt e).pG χ k
    let O₃ : (thickObj V (maximalIdeal V) e t.G).left.Opens := S.inf fun χ => LB.wchart P.D.toPre.P.L (φT χ) (jT χ) ⊓ LB.wchart P.D.toPre.P.L (φT' χ) (jtτ χ)

    let φM : P.D.toPre.X → (Fin 2 ⊕ Fin 6) → (P.D.toPre.P.A.left ⟶ P.D.toPre.P.A.left) := fun χ =>
      Sum.elim φX (fun k => liftB χ ≫ rosφ k)
    let jM : P.D.toPre.X → (Fin 2 ⊕ Fin 6) → P.D.toPre.P.L.ι := fun χ => Sum.elim jX (jR χ)
    let O₄ : (thickObj V (maximalIdeal V) e t.G).left.Opens := S.inf fun χ => (P.U.gt e).pG.left ⁻¹ᵁ (LB.wchart P.D.toPre.P.L (P.D.toPre.famφB (star a • χ)) (jf'' (star a • χ)) ⊓
        LB.wchart P.D.toPre.P.L (fun k => (P.oD.onB.act a).left ≫ P.D.toPre.famφB χ k) (jfτ χ) ⊓
        LB.wchart P.D.toPre.P.L (pullφB P.oD a χ) (jB3 χ) ⊓ LB.wchart P.D.toPre.P.L (φM χ) (jM χ))
    have hy₃ : y.1 ∈ O₃ := by
      refine mem_finset_inf' _ _ _ fun χ _ => ⟨Set.mem_iInter.2 fun k => ?_, Set.mem_iInter.2 fun k => ?_⟩
      · rcases k with k | k
        · exact hcB _
        · exact hcB _
      · exact hcB _
    have hy₄ : y.1 ∈ O₄ := by
      refine mem_finset_inf' _ _ _ fun χ _ => ⟨⟨⟨Set.mem_iInter.2 fun k => ?_, Set.mem_iInter.2 fun k => ?_⟩,
        Set.mem_iInter.2 fun k => ?_⟩, Set.mem_iInter.2 fun k => ?_⟩
      · have := hcB ((P.U.gt e).pG.left ≫ P.D.toPre.famφB (star a • χ) k)
        rwa [Scheme.Hom.comp_apply] at this
      · have e1 : ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left ≫ (P.U.gt e).pG.left ≫ P.D.toPre.famφB χ k =
            (P.U.gt e).pG.left ≫ (P.oD.onB.act a).left ≫ P.D.toPre.famφB χ k := by
          rw [← Category.assoc, hF2, Category.assoc]
        have := hcB (((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left ≫ (P.U.gt e).pG.left ≫ P.D.toPre.famφB χ k)
        have e2 := congrArg (fun g => g.base y.1) e1
        simp only [Scheme.Hom.comp_apply] at e2 this
        show ((P.oD.onB.act a).left ≫ P.D.toPre.famφB χ k).base ((P.U.gt e).pG.left.base y.1) ∈
          (P.D.toPre.P.L.U (jfτ χ k) : Set _)
        rw [Scheme.Hom.comp_apply, ← e2]
        exact this
      · have := hcB ((P.U.gt e).pG.left ≫ pullφB P.oD a χ k)
        rwa [Scheme.Hom.comp_apply] at this
      · rcases k with k | k
        · have := hcB ((P.U.gt e).pG.left ≫ φX k)
          rwa [Scheme.Hom.comp_apply] at this
        · have := hcB (liftG χ ≫ rosφ k)
          have e2 : (liftB χ ≫ rosφ k).base ((P.U.gt e).pG.left.base y.1) = (liftG χ ≫ rosφ k).base y.1 := by
            rw [← Scheme.Hom.comp_apply, ← Category.assoc, hlift χ]
          show (liftB χ ≫ rosφ k).base ((P.U.gt e).pG.left.base y.1) ∈ (P.D.toPre.P.L.U (jR χ k) : Set _)
          rw [e2]
          exact this
    let O₅ : (thickObj V (maximalIdeal V) e t.G).left.Opens := (P.U.gt e).pG.left ⁻¹ᵁ LB.wchart P.D.toPre.P.L φX jX
    have hy₅ : y.1 ∈ O₅ := Set.mem_iInter.2 fun k => by
      have := hcB ((P.U.gt e).pG.left ≫ φX k)
      rwa [Scheme.Hom.comp_apply] at this
    let O : (thickObj V (maximalIdeal V) e t.G).left.Opens := W ⊓ O₁ ⊓ O₂ ⊓ O₃ ⊓ O₄ ⊓ O₅
    have hOW : O ≤ W := fun _ h => h.1.1.1.1.1
    have hO₁ : O ≤ O₁ := fun _ h => h.1.1.1.1.2
    have hO₂ : O ≤ O₂ := fun _ h => h.1.1.1.2
    have hO₃ : O ≤ O₃ := fun _ h => h.1.1.2
    have hO₄ : O ≤ O₄ := fun _ h => h.1.2
    have hO₅ : O ≤ O₅ := fun _ h => h.2
    have hyO : y.1 ∈ O := ⟨⟨⟨⟨⟨hyW, hy₁⟩, hy₂⟩, hy₃⟩, hy₄⟩, hy₅⟩
    refine ⟨O, hyO, hOW, ?_⟩
    have E1 := fun i => expIdent_restrict P.U.toUnifPre e (k * N) (σ'' i) (f'' i) S'' (hE'' i) p
      (j ∘ Sum.inl) jf'' jt'' rfl hcoh₁ hO₁
    have E2 := fun i => expIdent_pull P.U.toUnifPre e k (τ i) (f i) S (hEτ i) p' (j ∘ Sum.inr) jfτ jtτ rfl
      hcoh₂ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left hO₂
    have hSim : S.image (fun χ => star a • χ) ⊆ S'' := by
      rw [hS''def]; exact Finset.subset_union_right
    let Wu := res (hO₁.trans (inf_le_left.trans inf_le_left)) ((P.U.w e).s p)
    let W'u := res hO₂ (pullU ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left _ (res (inf_le_left.trans inf_le_left :
      P.U.expW e p' (j ∘ Sum.inr) S jfτ jtτ ≤ _) ((P.U.w e).s p')))
    let Z : Fin 2 → Γ((thickObj V (maximalIdeal V) e t.G).left, O) := fun i => rs (hO₁.trans (inf_le_left.trans inf_le_right))
      (((fstG (maximalIdeal V) e t.G).left.app _).hom ((σ'' i).f (j ∘ Sum.inl)))
    let Y : Fin 2 → Γ((thickObj V (maximalIdeal V) e t.G).left, O) := fun i => rs hO₂ ((((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left.app _).hom (rs (inf_le_left.trans inf_le_right :
      P.U.expW e p' (j ∘ Sum.inr) S jfτ jtτ ≤ _) (((fstG (maximalIdeal V) e t.G).left.app _).hom ((τ i).f (j ∘ Sum.inr)))))
    let P1 : Fin 2 → P.D.toPre.X → Γ((thickObj V (maximalIdeal V) e t.G).left, O) := fun i β => if hβ : β ∈ S'' then
      rs (hO₁.trans (P.U.expW_le_f e p (j ∘ Sum.inl) jf'' jt'' hβ)) (((P.U.gt e).pG.left.app _).hom ((f'' i β).f (jf'' β))) *
        (res (hO₁.trans (P.U.expWeight_le_chart_weight e p (j ∘ Sum.inl) jf'' jt'' hβ)) (((P.U.gt e).t β).s (jt'' β))).val
      else 0
    let P2 : Fin 2 → P.D.toPre.X → Γ((thickObj V (maximalIdeal V) e t.G).left, O) := fun i α => if hα : α ∈ S then
      rs hO₂ ((((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left.app _).hom (rs (P.U.expW_le_f e p' (j ∘ Sum.inr) jfτ jtτ hα)
        (((P.U.gt e).pG.left.app _).hom ((f i α).f (jfτ α))))) *
      rs hO₂ ((((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left.app _).hom (res (P.U.expWeight_le_chart_weight e p' (j ∘ Sum.inr) jfτ jtτ hα)
        (((P.U.gt e).t α).s (jtτ α))).val)
      else 0
    have hA : ∀ α ∈ S, O ≤ ((P.U.gt e).pG.left ≫ (P.oD.onB.act a).left) ⁻¹ᵁ
        LB.wchart P.D.toPre.P.L (P.D.toPre.famφB α) (jfτ α) := fun α hα =>
      le_comp_of_eq hF2 (hO₂.trans fun y' hy' => P.U.expW_le_f e p' (j ∘ Sum.inr) jfτ jtτ hα hy')
    let A : Fin 2 → P.D.toPre.X → Γ((thickObj V (maximalIdeal V) e t.G).left, O) := fun i α => if hα : α ∈ S then
      rs (hA α hα) ((((P.U.gt e).pG.left ≫ (P.oD.onB.act a).left).app _).hom ((f i α).f (jfτ α))) else 0
    have hcT : ∀ α ∈ S, O ≤ LB.wchart P.D.toPre.P.L (P.D.toPre.Oφ (P.U.gt e).pG (star a • α))
        (jt'' (star a • α)) := fun α hα =>
      hO₁.trans (P.U.expWeight_le_chart_weight e p (j ∘ Sum.inl) jf'' jt'' (hSim (Finset.mem_image_of_mem _ hα)))
    have hcR : ∀ α ∈ S, O ≤ liftG α ⁻¹ᵁ LB.wchart P.D.toPre.P.L rosφ (jR α) := fun α hα y' hy' => by
      have h3 := le_finset_inf' hα (hO₃ hy')
      exact wchart_comp_le rosφ (liftG α) (jR α) (Set.mem_iInter.2 fun k' => Set.mem_iInter.1 h3.1 (Sum.inr k'))
    let c : P.D.toPre.X → Γ((thickObj V (maximalIdeal V) e t.G).left, O) := fun α => if hα : α ∈ S then
      (res (hcT α hα) (((P.U.gt e).t (star a • α)).s (jt'' (star a • α)))).val *
        rs (hcR α hα) (((liftG α).app _).hom (uR.s (jR α)).val) else 0
    let ξ : Γ((thickObj V (maximalIdeal V) e t.G).left, O) := rs hO₅ (((P.U.gt e).pG.left.app _).hom (X.s jX).val)
    have E1' : ∀ i, ∀ χ ∈ S, P1 i (star a • χ) = A i χ * ξ * c χ := by
      intro i χ hχ
      have hmem : star a • χ ∈ S'' := hSim (Finset.mem_image_of_mem _ hχ)
      obtain ⟨u, hu, hcorr, hsec⟩ := hrel i χ
      have hidx : ∀ kk, (Sum.elim (jf'' (star a • χ)) (Sum.elim (jfτ χ) (jB3 χ))) kk =
          cB ((P.U.gt e).pG.left ≫ (Sum.elim (P.D.toPre.famφB (star a • χ)) (Sum.elim
            (fun k => (P.oD.onB.act a).left ≫ P.D.toPre.famφB χ k) (pullφB P.oD a χ))) kk) := by
        intro kk
        rcases kk with kk | kk | kk
        · rfl
        · show cB (((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left ≫ (P.U.gt e).pG.left ≫ P.D.toPre.famφB χ kk) = cB ((P.U.gt e).pG.left ≫ (P.oD.onB.act a).left ≫ P.D.toPre.famφB χ kk)
          rw [← Category.assoc, hF2, Category.assoc]
        · rfl
      have h₃ : O ≤ (P.U.gt e).pG.left ⁻¹ᵁ LB.wchart P.D.toPre.P.L (pullφB P.oD a χ) (jB3 χ) :=
        fun y' hy' => (le_finset_inf' hχ (hO₄ hy')).1.2
      have h₄ : O ≤ (P.U.gt e).pG.left ⁻¹ᵁ LB.wchart P.D.toPre.P.L (φM χ) (jM χ) :=
        fun y' hy' => (le_finset_inf' hχ (hO₄ hy')).2
      have hs := secRel_pull P.D.toPre.P.L _ _ _ _ _ _ _ _ _ _ hsec (jf'' (star a • χ)) (jfτ χ) (jB3 χ)
        (fun a₁ b₁ hab => by rw [hidx a₁, hidx b₁]; exact congrArg (fun ψ => cB ((P.U.gt e).pG.left ≫ ψ)) hab)
        (P.U.gt e).pG.left (hO₁.trans (P.U.expW_le_f e p (j ∘ Sum.inl) jf'' jt'' hmem)) (hA χ hχ) h₃
      have hjM : ∀ kk, jM χ kk = cB ((P.U.gt e).pG.left ≫ φM χ kk) := by
        intro kk
        rcases kk with kk | kk
        · rfl
        · show cB (liftG χ ≫ rosφ kk) = cB ((P.U.gt e).pG.left ≫ liftB χ ≫ rosφ kk)
          rw [← Category.assoc, hlift χ]
      have hu2 := corr_pull P.D.toPre.P.L _ _ _ _ _ _ hcorr (jB3 χ) (jM χ)
        (fun k₁ k₂ hk => congrArg (fun ψ => cB ((P.U.gt e).pG.left ≫ ψ)) hk)
        (fun k₁ k₂ hk => by rw [hjM k₁, hjM k₂]; exact congrArg (fun ψ => cB ((P.U.gt e).pG.left ≫ ψ)) hk)
        (fun k₁ k₂ hk => by rw [hjM k₂]; exact congrArg (fun ψ => cB ((P.U.gt e).pG.left ≫ ψ)) hk)
        (P.U.gt e).pG.left h₃ h₄
      have hR' : O ≤ (P.U.gt e).pG.left ⁻¹ᵁ LB.wchart P.D.toPre.P.L (fun k => liftB χ ≫ rosφ k) (jM χ ∘ Sum.inr) :=
        fun y' hy' => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h₄ hy') (Sum.inr k)
      have h'' : O ≤ ((P.U.gt e).pG.left ≫ liftB χ) ⁻¹ᵁ LB.wchart P.D.toPre.P.L rosφ (jR χ) := by
        rw [hlift χ]; exact hcR χ hχ
      have hX2 := rs_app_mulGen P.D.toPre.P.L _ _ _ _ X (LB.pullGen P.D.toPre.P.L _ _ uR (liftB χ)) (jM χ) (P.U.gt e).pG.left h₄ hO₅ hR'
      have hP2 := rs_app_pullGen P.D.toPre.P.L _ _ uR (liftB χ) (jM χ ∘ Sum.inr) (P.U.gt e).pG.left hR' h''
      have hE2 := rs_app_of_eq (hlift χ) h'' (hcR χ hχ) (uR.s (jR χ)).val
      have key := hs.trans (congrArg (fun x => _ * x) (hu2.trans (hX2.trans (congrArg (fun x => _ * x)
        (hP2.trans hE2)))))
      simp only [P1, A, c, dif_pos hmem, dif_pos hχ]
      refine (congrArg (fun x : Γ((thickObj V (maximalIdeal V) e t.G).left, O) => x * _) key).trans ?_
      rw [show ∀ a b c d : Γ((thickObj V (maximalIdeal V) e t.G).left, O), a * (b * c) * d = a * b * (d * c) from
        fun a b c d => by ring]
      rfl
    have E2' : ∀ i, ∀ α ∈ S, P2 i α = A i α * c α := by
      intro i α hα
      have hAE : O ≤ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left ⁻¹ᵁ LB.wchart P.D.toPre.P.L (P.D.toPre.Oφ (P.U.gt e).pG α) (jtτ α) :=
        fun y' hy' => P.U.expWeight_le_chart_weight e p' (j ∘ Sum.inr) jfτ jtτ hα (hO₂ hy')
      have e1 : rs hO₂ ((((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left.app _).hom (rs (P.U.expW_le_f e p' (j ∘ Sum.inr) jfτ jtτ hα)
          (((P.U.gt e).pG.left.app _).hom ((f i α).f (jfτ α))))) =
          rs (hA α hα) ((((P.U.gt e).pG.left ≫ (P.oD.onB.act a).left).app _).hom ((f i α).f (jfτ α))) :=
        (rs_app_comp ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left (P.U.gt e).pG.left (P.U.expW_le_f e p' (j ∘ Sum.inr) jfτ jtτ hα) hO₂
          (fun y' hy' => P.U.expW_le_f e p' (j ∘ Sum.inr) jfτ jtτ hα (hO₂ hy')) _).trans
          (rs_app_of_eq hF2 _ _ _)
      have e2 : rs hO₂ ((((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left.app _).hom (res (P.U.expWeight_le_chart_weight e p' (j ∘ Sum.inr) jfτ jtτ hα)
          (((P.U.gt e).t α).s (jtτ α))).val) = rs hAE ((((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left.app _).hom (((P.U.gt e).t α).s (jtτ α)).val) :=
        (congrArg (rs hO₂) (app_rs ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left (P.U.expWeight_le_chart_weight e p' (j ∘ Sum.inr) jfτ jtτ hα)
          (((P.U.gt e).t α).s (jtτ α)).val)).trans (rs_rs _ _ _)
      have hT := hL4.tLin V (maximalIdeal V) (NumberField.RingOfIntegers E) P.D P.A t.G P.U.toUnifPre P.oD P.oA
        t.act.toRingAct P.lin e a uR huR huR0 α
      have hjT : ∀ kk, jT α kk = cB (φT α kk) := fun kk => by rcases kk with kk | kk <;> rfl
      have hc := corr_pull P.D.toPre.P.L _ _ _ _ _ _ hT (jT α) (jtτ α)
        (fun k₁ k₂ hk => by rw [hjT k₁, hjT k₂]; exact congrArg cB hk)
        (fun k₁ k₂ hk => congrArg cB hk)
        (fun k₁ k₂ hk => by rw [hjT k₁]; exact congrArg cB hk)
        (𝟙 _) (fun y' hy' => (le_finset_inf' hα (hO₃ hy')).1) (fun y' hy' => (le_finset_inf' hα (hO₃ hy')).2)
      simp only [P2, A, c, dif_pos hα]
      rw [e1, e2]
      congr 1
      refine (Eq.trans ?_ hc.symm).trans ?_
      · exact (rs_rs _ _ _).symm
      · simp only [LB.mulGen, Units.val_mul, map_mul, rs_mul]
        congr 1
        · exact rs_rs _ _ _
        · exact (congrArg (rs _) (rs_rs _ _ _)).trans (rs_rs _ _ _)
    have E5 : ∀ i, ∀ β ∈ S'', β ∉ S.image (fun χ => star a • χ) → P1 i β = 0 := by
      intro i β hβ hβ'
      have hne : ∀ χ, β ≠ star a • χ := by
        intro χ hχ
        apply hβ'
        have hβ2 := hβ
        rw [hS''def] at hβ2
        rcases Finset.mem_union.1 hβ2 with h | h
        · have hχS : χ ∈ S := by
            rw [hSdef]
            exact Finset.mem_union_right _ (Finset.mem_preimage.2 (hχ ▸ h))
          exact Finset.mem_image.2 ⟨χ, hχS, hχ.symm⟩
        · exact h
      have h0 := hoff i β hne (jf'' β)
      simp only [P1, dif_pos hβ]
      rw [h0]
      erw [map_zero, rs_zero', zero_mul]
    have hmain := cross_alg S S'' (fun χ => star a • χ) hinj.injOn hSim Wu W'u (k * N) k Z Y P1 P2 A c ξ
      (fun i => E1 i) (fun i => E2 i) E1' E2' E5
    have hz : rs hOW z = Z 0 * Y 1 - Z 1 * Y 0 := by
      have hWτ : P.U.expW e p' (j ∘ Sum.inr) S jfτ jtτ ≤ (fstG (maximalIdeal V) e t.G).left ⁻¹ᵁ LB.wchart P.U.LG.L
          (fun _ : Fin 1 => 𝟙 t.G.left) (j ∘ Sum.inr) := inf_le_left.trans inf_le_right
      have h1 : O ≤ (((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left ≫ (fstG (maximalIdeal V) e t.G).left) ⁻¹ᵁ LB.wchart P.U.LG.L (fun _ : Fin 1 => 𝟙 t.G.left) (j ∘ Sum.inr) :=
        fun y' hy' => hWτ (hO₂ hy')
      have hYO : O ≤ ((fstG (maximalIdeal V) e t.G).left ≫ (t.act.act a).left) ⁻¹ᵁ LB.wchart P.U.LG.L (fun _ : Fin 1 => 𝟙 t.G.left)
          (j ∘ Sum.inr) := le_comp_of_eq hF1 h1
      have hY : ∀ i, Y i = rs hYO ((((fstG (maximalIdeal V) e t.G).left ≫ (t.act.act a).left).app _).hom ((τ i).f (j ∘ Sum.inr))) := fun i =>
        (rs_app_comp' ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left (fstG (maximalIdeal V) e t.G).left hWτ hO₂ h1 _).trans (rs_app_of_eq hF1 h1 hYO _)
      have hprod : ∀ i i' : Fin 2, rs hOW (((fstG (maximalIdeal V) e t.G).left.app _).hom ((mulSec P.U.LG.L _ _ _ _ (σ'' i)
          (pullSec P.U.LG.L _ _ (τ i') (t.act.act a).left)).f j)) = Z i * Y i' := by
        intro i i'
        rw [hY i']
        simp only [mulSec, map_mul, rs_mul]
        congr 1
        · exact (congrArg (rs hOW) (app_rs (fstG (maximalIdeal V) e t.G).left _ _)).trans (rs_rs _ _ _)
        · simp only [pullSec]
          exact (congrArg (rs hOW) (app_rs (fstG (maximalIdeal V) e t.G).left _ _)).trans ((rs_rs _ _ _).trans (rs_app_comp' (fstG (maximalIdeal V) e t.G).left (t.act.act a).left _ _ _ _))
      rw [hzdef]
      show rs hOW (((fstG (maximalIdeal V) e t.G).left.app _).hom ((mulSec P.U.LG.L _ _ _ _ (σ'' 0)
          (pullSec P.U.LG.L _ _ (τ 1) (t.act.act a).left)).f j - (mulSec P.U.LG.L _ _ _ _ (σ'' 1)
          (pullSec P.U.LG.L _ _ (τ 0) (t.act.act a).left)).f j)) = _
      exact ((congrArg (rs hOW) (map_sub _ _ _)).trans (rs_sub' _ _ _)).trans
        (congrArg₂ (· - ·) (hprod 0 1) (hprod 1 0))
    rw [hz, hmain]
  choose O hyO hOW hz0 using hloc
  refine sec_ext_cover W O hOW (fun y hy => ?_) z 0 (fun y => (hz0 y).trans (map_zero _).symm)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyO ⟨y, hy⟩⟩

end ReciprocityTheory.ChartRestriction.G.DVR
end
end
