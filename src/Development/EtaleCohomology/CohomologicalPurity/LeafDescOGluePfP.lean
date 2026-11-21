import Development.EtaleCohomology.CohomologicalPurity.LeafDescPf

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl

theorem le_of_comp {Y Z X : Scheme.{0}} {W : Y.Opens} {V : Z.Opens} (f : Y ⟶ Z) (g : Z ⟶ X) (U : X.Opens)
    (hV : V = g ⁻¹ᵁ U) (k : Y ⟶ X) (hk : f ≫ g = k) (hW : W ≤ k ⁻¹ᵁ U) : W ≤ f ⁻¹ᵁ V := by
  subst hV hk; intro w hw; exact hW hw

theorem pre_comp {Y Z X : Scheme.{0}} (f : Y ⟶ Z) (g : Z ⟶ X) (V : Z.Opens) (U : X.Opens) (hV : V = g ⁻¹ᵁ U) :
    f ⁻¹ᵁ V = (f ≫ g) ⁻¹ᵁ U := by
  subst hV; ext; rfl

theorem LeafPcGlue_pf : LeafPcGlue := by
  intro q X U m i hG A p s hcov H
  let E := fun a => Equiv.ofBijective _ (pc_bij (q := q) (p a) m i)
  obtain ⟨c, hc⟩ := hG A (fun a => (p a).j.opensRange) (fun a => (E a).symm (s a)) (fun x hx => hcov x hx) (by
    intro a b x hxa hxb hxU
    obtain ⟨y, rfl⟩ : x ∈ Set.range (p a).j := hxa
    obtain ⟨t, u, h, hcomm, ⟨z, rfl⟩, heq⟩ := H a b y hxU hxb
    let P : Pc U := ⟨t.Y, t.j ≫ (p a).j, inferInstance, t.V, t.hV.trans (pre_comp _ _ _ U (p a).hV)⟩
    have ha : P.j.opensRange ≤ (p a).j.opensRange := by rintro _ ⟨w, rfl⟩; exact ⟨t.j w, rfl⟩
    have hb : P.j.opensRange ≤ (p b).j.opensRange := by
      rintro _ ⟨w, rfl⟩
      refine ⟨u w, ?_⟩
      change (u ≫ (p b).j) w = (t.j ≫ (p a).j) w
      rw [hcomm]
    have ea : P.j.isoOpensRange.hom ≫ X.homOfLE ha = t.j ≫ (p a).j.isoOpensRange.hom := by
      rw [← cancel_mono ((p a).j.opensRange.ι)]
      simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoOpensRange_hom_ι]; rfl
    have eb : P.j.isoOpensRange.hom ≫ X.homOfLE hb = u ≫ (p b).j.isoOpensRange.hom := by
      rw [← cancel_mono ((p b).j.opensRange.ι)]
      simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoOpensRange_hom_ι]
      exact hcomm
    have hPV : P.V ≤ P.j ⁻¹ᵁ U := P.hV.le
    have ha' : P.j.opensRange.ι ⁻¹ᵁ U ≤ X.homOfLE ha ⁻¹ᵁ ((p a).j.opensRange.ι ⁻¹ᵁ U) :=
      le_of_comp _ _ U rfl _ (Scheme.homOfLE_ι _ _) le_rfl
    have hb' : P.j.opensRange.ι ⁻¹ᵁ U ≤ X.homOfLE hb ⁻¹ᵁ ((p b).j.opensRange.ι ⁻¹ᵁ U) :=
      le_of_comp _ _ U rfl _ (Scheme.homOfLE_ι _ _) le_rfl
    refine ⟨P.j.opensRange, ha, hb, ha', hb', ⟨z, rfl⟩, ?_⟩
    apply (pc_bij P m i).1
    have k1 : P.V ≤ (t.j ≫ (p a).j.isoOpensRange.hom) ⁻¹ᵁ ((p a).j.opensRange.ι ⁻¹ᵁ U) :=
      le_of_comp _ _ U rfl _ (by rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]) hPV
    have k2 : P.V ≤ (u ≫ (p b).j.isoOpensRange.hom) ⁻¹ᵁ ((p b).j.opensRange.ι ⁻¹ᵁ U) :=
      le_of_comp _ _ U rfl _ (by rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, ← hcomm]) hPV
    rw [pull_pull _ _ ea _ _ _ _ _ k1, pull_pull _ _ eb _ _ _ _ _ k2,
      ← pull_pull t.j _ rfl _ _ _ t.hV.le (pc_le (p a)) k1, ← pull_pull u _ rfl _ _ _ h (pc_le (p b)) k2]
    change Hs.pull q _ m i (E a ((E a).symm (s a))) = Hs.pull q _ m i (E b ((E b).symm (s b)))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact heq)
  refine ⟨c, fun a => ?_⟩
  rw [pc_res, hc a]
  exact (E a).apply_symm_apply (s a)

theorem LeafDesc_of' (hD : LeafDict) (hF : LeafFlq) (hS : LeafDescOSep) (hG : LeafDescOGlue) : LeafDesc :=
  LeafDesc_of hD hF hS hG LeafPcGlue_pf

end LateralTheory.CohomologicalPurity.Cl
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl

def LeafResK : Prop := ∀ (q : ℕ) (i : ℤ),
  (∀ s, Injective ((res _ (tw q i)).X s)) ∧ ∀ s < 0, IsZero ((res _ (tw q i)).X s)

def LeafZcPull : Prop := ∀ {R : Type} [CommRing R] (K : Cx R) {X' X : Scheme.{0}} (f : X' ⟶ X) (U' : X'.Opens)
  (U : X.Opens), U' ≤ f ⁻¹ᵁ U → ∀ (n : ℤ) (a : Sec (K.X n) X), a ∈ Zc K U n → Sec.res f a ∈ Zc K U' n

def LeafZcIn : Prop := ∀ {R : Type} [CommRing R] (K : Cx R) {X : Scheme.{0}} (U W V : X.Opens) (h : V ≤ W), V ≤ U →
  ∀ (n : ℤ) (a : Sec (K.X n) W.toScheme), a ∈ Zc K (W.ι ⁻¹ᵁ U) n → rs h a = 0

private theorem sres_zero {R : Type} [CommRing R] {G : Shv R} {X Y : Scheme.{0}} (f : Y ⟶ X) :
    Sec.res f (0 : Sec G X) = 0 := by
  show (G.obj.map f.op).hom 0 = 0
  exact map_zero _

private theorem smap_zero {R : Type} [CommRing R] {G H : Shv R} (φ : G ⟶ H) {X : Scheme.{0}} :
    Sec.map φ (0 : Sec G X) = 0 := by
  show (φ.hom.app (op X)).hom 0 = 0
  exact map_zero _

private theorem Bd_zero {R : Type} [CommRing R] (K : Cx R) {X : Scheme.{0}} (U : X.Opens) (n : ℤ) : Bd K U n 0 :=
  ⟨0, sres_zero _, smap_zero _⟩

private theorem leι {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) (U : X.Opens) :
    V.ι ⁻¹ᵁ U ≤ X.homOfLE h ⁻¹ᵁ (W.ι ⁻¹ᵁ U) :=
  le_of_comp _ _ U rfl _ (Scheme.homOfLE_ι _ _) le_rfl

private theorem descent_glue_of_residue_pullback_inclusion (hK : LeafResK) (hP : LeafZcPull) (hI : LeafZcIn) : LeafDescOGlue := by
  intro hD hF q X U m i hL A V s hcov H
  obtain ⟨cls, hon, hker, hnat⟩ := hD q m i
  have H1 : ∀ n < m, ∀ (W : X.Opens), ∀ a ∈ Zc (res _ (tw q i)) (W.ι ⁻¹ᵁ U) n, ∀ x ∈ W,
      ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ Bd (res _ (tw q i)) (V.ι ⁻¹ᵁ U) n (rs h a) := by
    intro n hn W a ha x hx
    by_cases hxU : x ∈ U
    · refine ⟨W ⊓ U, inf_le_left, ⟨hx, hxU⟩, ?_⟩
      rw [hI _ U W (W ⊓ U) _ inf_le_right n a ha]
      exact Bd_zero _ _ _
    · obtain ⟨V', hV'W, hxV', hsub⟩ := hL x W hx
      refine ⟨V', hV'W, hxV', ?_⟩
      obtain ⟨cn, -, hkern, -⟩ := hD q n i
      have hz := hP _ (X.homOfLE hV'W) (V'.ι ⁻¹ᵁ U) (W.ι ⁻¹ᵁ U) (leι hV'W U) n a ha
      have := hsub n hn
      exact (hkern (V'.ι ⁻¹ᵁ U) ⟨_, hz⟩).1 (Subsingleton.elim _ _)
  obtain ⟨-, hglue⟩ := hF _ (res _ (tw q i)) (hK q i).1 (hK q i).2 X U m H1
  choose l hl using fun a => hon ((V a).ι ⁻¹ᵁ U) (s a)
  let V' : Option A → X.Opens := fun o => Option.elim o U V
  let a' : ∀ k, Sec ((res _ (tw q i)).X m) (V' k).toScheme := fun
    | none => 0
    | some a => (l a).1
  have hmem : ∀ k, a' k ∈ Zc (res _ (tw q i)) ((V' k).ι ⁻¹ᵁ U) m := by
    rintro (_ | a)
    · exact zero_mem _
    · exact (l a).2
  have hcv : ∀ x : X, ∃ k, x ∈ V' k := by
    intro x
    by_cases hx : x ∈ U
    · exact ⟨none, hx⟩
    · obtain ⟨a, ha⟩ := hcov x hx
      exact ⟨some a, ha⟩
  have hcmp : ∀ k l', ∀ x ∈ V' k, x ∈ V' l' → ∃ (T : X.Opens) (hk : T ≤ V' k) (hl : T ≤ V' l'), x ∈ T ∧
      Bd (res _ (tw q i)) (T.ι ⁻¹ᵁ U) m (rs hk (a' k) - rs hl (a' l')) := by
    intro k l' x hk hl'
    by_cases hxU : x ∈ U
    · refine ⟨V' k ⊓ V' l' ⊓ U, inf_le_left.trans inf_le_left, inf_le_left.trans inf_le_right, ⟨⟨hk, hl'⟩, hxU⟩, ?_⟩
      rw [hI _ U (V' k) _ _ inf_le_right m (a' k) (hmem k), hI _ U (V' l') _ _ inf_le_right m (a' l') (hmem l'),
        sub_zero]
      exact Bd_zero _ _ _
    · rcases k with _ | a
      · exact absurd hk hxU
      rcases l' with _ | b
      · exact absurd hl' hxU
      obtain ⟨T, ha, hb, ha', hb', hxT, heq⟩ := H a b x hk hl' hxU
      refine ⟨T, ha, hb, hxT, ?_⟩
      have za := hP _ (X.homOfLE ha) (T.ι ⁻¹ᵁ U) ((V a).ι ⁻¹ᵁ U) ha' m (l a).1 (l a).2
      have zb := hP _ (X.homOfLE hb) (T.ι ⁻¹ᵁ U) ((V b).ι ⁻¹ᵁ U) hb' m (l b).1 (l b).2
      have e1 := hnat (X.homOfLE ha) (T.ι ⁻¹ᵁ U) ((V a).ι ⁻¹ᵁ U) ha' (l a) ⟨_, za⟩ rfl
      have e2 := hnat (X.homOfLE hb) (T.ι ⁻¹ᵁ U) ((V b).ι ⁻¹ᵁ U) hb' (l b) ⟨_, zb⟩ rfl
      rw [hl a] at e1
      rw [hl b] at e2
      have h0 : cls (T.ι ⁻¹ᵁ U) (⟨_, za⟩ - ⟨_, zb⟩) = 0 := by
        rw [map_sub, ← e1, ← e2, heq, sub_self]
      exact (hker _ _).1 h0
  obtain ⟨c, hc, hcb⟩ := hglue (Option A) V' a' hmem hcv hcmp
  refine ⟨cls U ⟨c, hc⟩, fun a => ?_⟩
  have zc := hP _ (V a).ι ((V a).ι ⁻¹ᵁ U) U le_rfl m c hc
  show Hs.pull q (opnMap (V a).ι ((V a).ι ⁻¹ᵁ U) U le_rfl) m i (cls U ⟨c, hc⟩) = s a
  rw [hnat (V a).ι ((V a).ι ⁻¹ᵁ U) U le_rfl ⟨c, hc⟩ ⟨_, zc⟩ rfl, ← hl a, ← sub_eq_zero, ← map_sub]
  exact (hker _ _).2 (hcb (some a))

private theorem sres_comp {R : Type} [CommRing R] {G : Shv R} {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (a : Sec G X) :
    Sec.res g (Sec.res f a) = Sec.res (g ≫ f) a := by
  show (G.obj.map g.op).hom ((G.obj.map f.op).hom a) = (G.obj.map (g ≫ f).op).hom a
  rw [op_comp, Functor.map_comp]; rfl

private theorem sres_id {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (a : Sec G X) : Sec.res (𝟙 X) a = a := by
  show (G.obj.map (𝟙 X).op).hom a = a
  rw [op_id, CategoryTheory.Functor.map_id]; rfl

private theorem smap_res {R : Type} [CommRing R] {G H : Shv R} (φ : G ⟶ H) {X Y : Scheme.{0}} (f : Y ⟶ X) (a : Sec G X) :
    Sec.map φ (Sec.res f a) = Sec.res f (Sec.map φ a) := by
  show (φ.hom.app (op Y)).hom ((G.obj.map f.op).hom a) = (H.obj.map f.op).hom ((φ.hom.app (op X)).hom a)
  have h := φ.hom.naturality f.op
  exact congrArg (fun t => t.hom a) h

private theorem LeafZcPull_pf : LeafZcPull := by
  intro R _ K X' X f U' U h n a ha
  obtain ⟨h1, h2⟩ := (mem_Zc a).1 ha
  refine (mem_Zc _).2 ⟨?_, ?_⟩
  · rw [sres_comp, ← Scheme.Hom.resLE_comp_ι f h, ← sres_comp, h1, sres_zero]
  · rw [smap_res, h2, sres_zero]

private theorem LeafZcIn_pf : LeafZcIn := by
  intro R _ K X U W V h hU n a ha
  obtain ⟨h1, -⟩ := (mem_Zc a).1 ha
  have e : (⊤ : V.toScheme.Opens) ≤ X.homOfLE h ⁻¹ᵁ (W.ι ⁻¹ᵁ U) :=
    le_of_comp _ _ U rfl _ (Scheme.homOfLE_ι _ _) ((Scheme.Opens.ι_preimage_self V).symm.le.trans (fun y hy => hU hy))
  have h0 : Sec.res (⊤ : V.toScheme.Opens).ι (rs h a) = 0 := by
    rw [sres_comp, ← Scheme.Hom.resLE_comp_ι (X.homOfLE h) e, ← sres_comp, h1, sres_zero]
  rw [← sres_id (rs h a), ← Scheme.toIso_inv_ι, ← sres_comp, h0, sres_zero]

private theorem resK_inj (q : ℕ) (i : ℤ) (s : ℤ) : Injective ((res _ (tw q i)).X s) := by unfold GlobalTheory.EtC.res; infer_instance
private theorem LeafResK_pf : LeafResK := fun q i => ⟨resK_inj q i, fun s hs => by
  have : (res _ (tw q i)).IsStrictlyGE 0 := by unfold GlobalTheory.EtC.res; infer_instance
  exact CochainComplex.isZero_of_isStrictlyGE (res _ (tw q i)) 0 s hs⟩

theorem LeafDescOGlue_of : LeafDescOGlue := descent_glue_of_residue_pullback_inclusion LeafResK_pf LeafZcPull_pf LeafZcIn_pf

end LateralTheory.CohomologicalPurity.Cl
end
end
