import Development.EtaleCohomology.WeilConjectures.GysinSeqCut

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.Gys.LV
open LateralTheory.EWeil LateralTheory.EWeil.Gys

def LowVan : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (P : SPair l r) (c : ℕ) (i n : ℤ), n < 2 * r →
  ∀ x : HZ (l ^ c) i P.j n, x = 0

def PointVan : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (P : SPair l r) (c : ℕ) (i n : ℤ), 2 * r < n →
  ∀ (x : HZ (l ^ c) i P.j n) (t : P.X), ∃ (P' : SPair l r) (f : P'.Hom P),
    t ∈ Set.range f.fX ∧ pullZ _ i f.fX f.fU f.sqU n x = 0

def Glue : Prop := ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (P : SPair l r) (c : ℕ) (i n : ℤ) (x : HZ (l ^ c) i P.j n),
  (∀ t : P.X, ∃ (P' : SPair l r) (f : P'.Hom P), t ∈ Set.range f.fX ∧ pullZ _ i f.fX f.fU f.sqU n x = 0) →
  ∃ (P' : SPair l r) (f : P'.Hom P), Surjective f.fX ∧ pullZ _ i f.fX f.fU f.sqU n x = 0

def SPair.idHom {l r : ℕ} (P : SPair l r) : P.Hom P where
  fX := 𝟙 _
  fZ := 𝟙 _
  fU := 𝟙 _
  etale := inferInstance
  sqZ := IsPullback.of_horiz_isIso ⟨by simp⟩
  sqU := by simp

theorem goal_of (hL : LowVan) (hP : PointVan) (hG : Glue) : Gys.LocalVan := by
  intro hB l _ r P c i n hn x
  rcases lt_or_gt_of_ne hn with h | h
  · refine ⟨P, SPair.idHom P, show Surjective (𝟙 P.X) from inferInstance, ?_⟩
    rw [hL hB l r P c i n h x, map_zero]
  · exact hG l r P c i n x (fun t => hP hB l r P c i n h x t)

end LateralTheory.EWeil.Gys.LV
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.Gys.LV.GluePf
open LateralTheory.EWeil LateralTheory.EWeil.Gys LateralTheory.EWeil.Gys.LV

def Sig : Prop := ∀ (l r : ℕ) (P : SPair l r) {T : Type} (Q : T → SPair l r) (g : ∀ t, (Q t).Hom P),
  ∃ (P' : SPair l r) (f : P'.Hom P) (a : ∀ t, (Q t).Hom P'), (∀ t, (a t).fX ≫ f.fX = (g t).fX) ∧
    Nonempty (IsColimit (Cofan.mk P'.X fun t => (a t).fX)) ∧ Nonempty (IsColimit (Cofan.mk P'.U fun t => (a t).fU)) ∧
    ((∀ x : P.X, ∃ t, x ∈ Set.range (g t).fX) → Surjective f.fX)

def ShvSigma : Prop := ∀ (R : Type) [CommRing R] (F : GlobalTheory.EtC.Shv R) {T : Type} {Y : T → Scheme.{0}} (c : Cofan Y), IsColimit c →
  Function.Bijective (fun (s : GlobalTheory.EtC.Sec F c.pt) (t : T) => GlobalTheory.EtC.Sec.res (c.inj t) s)

theorem glue_of (hS : Sig) (hF : ShvSigma) : Glue := by
  intro l _ r P c i n x hx
  choose Q g ht hz using hx
  obtain ⟨P', f, a, hfa, ⟨hX⟩, ⟨hU⟩, hsurj⟩ := hS l r P Q g
  refine ⟨P', f, hsurj fun t => ⟨t, ht t⟩, ?_⟩
  induction x using QuotientAddGroup.induction_on with
  | H z => ?_
  have key : ∀ t, ∃ y : SecI (l ^ c) i (Q t).X (n - 1), resA (l ^ c) i (Q t).j (n - 1) y = 0 ∧
      dA (l ^ c) i (Q t).X (n - 1) n y = resA (l ^ c) i (g t).fX n z.1 := by
    intro t
    have h := hz t
    unfold pullZ at h
    rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h
    obtain ⟨y, hy, e⟩ := h
    exact ⟨y, hy, e⟩
  choose y hy hd using key
  obtain ⟨Y, hY⟩ := (hF _ ((res _ (tw (l ^ c) i)).X (n - 1)) _ hX).2 y
  have hYt : ∀ t, resA (l ^ c) i (a t).fX (n - 1) Y = y t := fun t => congrFun hY t
  unfold pullZ
  rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  refine ⟨Y, ?_, ?_⟩
  · show resA (l ^ c) i P'.j (n - 1) Y = 0
    apply (hF _ ((res _ (tw (l ^ c) i)).X (n - 1)) _ hU).1
    funext t
    change resA (l ^ c) i (a t).fU (n - 1) (resA (l ^ c) i P'.j (n - 1) Y) = resA (l ^ c) i (a t).fU (n - 1) 0
    rw [map_zero, ← resA_comp, (a t).sqU, resA_comp, hYt, hy]
  · show dA (l ^ c) i P'.X (n - 1) n Y = resA (l ^ c) i f.fX n z.1
    apply (hF _ ((res _ (tw (l ^ c) i)).X n) _ hX).1
    funext t
    change resA (l ^ c) i (a t).fX n (dA (l ^ c) i P'.X (n - 1) n Y) = resA (l ^ c) i (a t).fX n (resA (l ^ c) i f.fX n z.1)
    rw [resA_dA, hYt, hd, ← resA_comp, hfa]

end LateralTheory.EWeil.Gys.LV.GluePf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.EWeil.Gys.LV.GluePf

theorem shvSigma : ShvSigma := by
  intro R _ F T Y c hc
  let G : Scheme.{0}ᵒᵖ ⥤ Type 1 := F.obj ⋙ forget _
  have hG : Presieve.IsSheaf Scheme.zariskiTopology G :=
    Presieve.isSheaf_of_le G Scheme.zariskiTopology_le_etaleTopology
      ((isSheaf_iff_isSheaf_of_type _ G).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget _)).1 F.property))
  have : PreservesLimitsOfShape (Discrete T) G := preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hG
  let hL : IsLimit (G.mapCone c.op) := isLimitOfPreserves G (Cofan.IsColimit.op hc)
  let e := Types.isLimitEquivSections hL
  have he : ∀ s t, (e s).1 ⟨t⟩ = GlobalTheory.EtC.Sec.res (c.inj t) s := fun s t => rfl
  constructor
  · intro s₁ s₂ h
    apply e.injective
    apply Subtype.ext
    funext ⟨t⟩
    rw [he, he]
    exact congrFun h t
  · intro y
    let sec : (Discrete.functor (fun a => op (Y a)) ⋙ G).sections :=
      ⟨fun j => y j.as, by
        rintro ⟨j⟩ ⟨j'⟩ ⟨⟨h⟩⟩
        cases h
        show G.map (𝟙 _) _ = _
        rw [G.map_id]; rfl⟩
    refine ⟨e.symm sec, ?_⟩
    funext t
    show GlobalTheory.EtC.Sec.res (c.inj t) (e.symm sec) = y t
    rw [← he, e.apply_symm_apply]

end LateralTheory.EWeil.Gys.LV.GluePf
end
end
