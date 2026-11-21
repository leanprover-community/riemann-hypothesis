import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaDisj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SectionExt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatNat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatUnique
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaLocal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GlueSection
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.KerRes
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatNat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatOne

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem map_restrict {V : Scheme.{0}} {d : ℕ} (M : Matrix (Fin d) (Fin d) Γ(V, ⊤))
    {U P : V.Opens} (s : (P : Scheme.{0}) ⟶ U) (hs : s ≫ U.ι = P.ι) :
    (M.map U.ι.appTop.hom).map s.appTop.hom = M.map P.ι.appTop.hom := by
  ext m l
  simp only [Matrix.map_apply, ← hs, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gMatUnique :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (a b : V ⟶ WP B) (M M' : Matrix (Fin d) (Fin d) Γ(V, ⊤)), GMat B a b M → GMat B a b M' → M = M' := by
  intro K _ W Z Y q i π D d B V a b M M' hM hM'
  ext m l
  refine sectionExt _ _ fun x => ?_
  obtain ⟨U, α, β, a₁, b₁, hx, ha, hb, hL⟩ := hM x
  obtain ⟨U', α', β', a₁', b₁', hx', ha', hb', hL'⟩ := hM' x
  have hs : V.homOfLE (inf_le_left : U ⊓ U' ≤ U) ≫ U.ι = (U ⊓ U').ι := Scheme.homOfLE_ι _ _
  have hs' : V.homOfLE (inf_le_right : U ⊓ U' ≤ U') ≫ U'.ι = (U ⊓ U').ι := Scheme.homOfLE_ι _ _
  generalize V.homOfLE (inf_le_left : U ⊓ U' ≤ U) = s at hs
  generalize V.homOfLE (inf_le_right : U ⊓ U' ≤ U') = s' at hs'
  have pt : ((U ⊓ U' : V.Opens) : Scheme.{0}) := ⟨x, hx, hx'⟩
  have eα : α = α' := by
    refine sigmaDisj (fun α : B.ι => (oW B α : Scheme.{0})) (s ≫ a₁) (s' ≫ a₁') pt ?_
    change (s ≫ a₁) ≫ wI B α = (s' ≫ a₁') ≫ wI B α'
    rw [Category.assoc, Category.assoc, ← ha, ← ha', ← Category.assoc, ← Category.assoc, hs, hs']
  have eβ : β = β' := by
    refine sigmaDisj (fun α : B.ι => (oW B α : Scheme.{0})) (s ≫ b₁) (s' ≫ b₁') pt ?_
    change (s ≫ b₁) ≫ wI B β = (s' ≫ b₁') ≫ wI B β'
    rw [Category.assoc, Category.assoc, ← hb, ← hb', ← Category.assoc, ← Category.assoc, hs, hs']
  subst eα eβ
  have h₁ := locMatNat B α β s _ _ hL
  have h₂ := locMatNat B α β s' _ _ hL'
  rw [map_restrict M s hs, ← Category.assoc, hs] at h₁
  rw [map_restrict M' s' hs', ← Category.assoc, hs'] at h₂
  have e := locMatUnique B α β _ _ _ h₁ h₂
  exact ⟨U ⊓ U', ⟨hx, hx'⟩, congrFun (congrFun e m) l⟩
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.trExists :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {N : Z.Opens} (_ : IsAffineOpen N) (h₁ : N ≤ B.V α) (h₂ : N ≤ B.V β), ∃ G : Matrix (Fin d) (Fin d) Γ(Z, N), IsTr B α β h₁ h₂ G := by
  intro K _ W Z Y q i π D d B α β N hN h₁ h₂
  have key : ∀ m, ∃ c : Fin d → Γ(Z, N), ∑ l, c l * tN B α h₁ l = tN B β h₂ m := by
    intro m
    have hm : tN B β h₂ m ∈ Ideal.span (Set.range (tN B α h₁)) := by
      rw [← kerRes B α hN h₁, kerRes B β hN h₂]
      exact Ideal.subset_span ⟨m, rfl⟩
    exact Ideal.mem_span_range_iff_exists_fun.1 hm
  choose G hG using key
  exact ⟨Matrix.of G, fun m => (hG m).symm⟩
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private lemma appTop_appLE {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (h : f ≫ g = k)
    (N : C.Opens) (e₁ : ⊤ ≤ g ⁻¹ᵁ N) (e₂ : ⊤ ≤ k ⁻¹ᵁ N) (s : Γ(C, N)) :
    f.appTop.hom ((g.appLE N ⊤ e₁).hom s) = (k.appLE N ⊤ e₂).hom s := by
  subst h
  have e₀ : (⊤ : A.Opens) ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have h₀ : f.appLE ⊤ ⊤ e₀ = f.appTop := Scheme.Hom.appLE_eq_app (f := f) (U := ⊤)
  have h := Scheme.Hom.appLE_comp_appLE f g N ⊤ ⊤ e₁ e₀
  rw [h₀] at h
  rw [← h]
  rfl

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatExists :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {V : Scheme.{0}} (p : V ⟶ W), (∀ x : V, (p ≫ i) x ∈ B.V α ⊓ B.V β) → ∃ M : Matrix (Fin d) (Fin d) Γ(V, ⊤), LocMat B α β p M := by
  intro K _ W Z Y q i π D d B α β V p hp
  have hN : ∀ x : V, ∃ N : Z.Opens, IsAffineOpen N ∧ (p ≫ i) x ∈ N ∧ N ≤ B.V α ⊓ B.V β := fun x => by
    obtain ⟨N, h1, h2, h3⟩ := exists_isAffineOpen_mem_and_subset (hp x)
    exact ⟨N, h1, h2, h3⟩
  choose N hNa hNx hNle using hN
  have h₁ : ∀ x, N x ≤ B.V α := fun x => (hNle x).trans inf_le_left
  have h₂ : ∀ x, N x ≤ B.V β := fun x => (hNle x).trans inf_le_right
  choose G hG using fun x => trExists B α β (hNa x) (h₁ x) (h₂ x)
  let U : V → V.Opens := fun x => (p ≫ i) ⁻¹ᵁ N x
  have hxU : ∀ x, x ∈ U x := hNx
  have hU : ∀ x, ⊤ ≤ ((U x).ι ≫ p ≫ i) ⁻¹ᵁ N x := by
    intro x y _
    exact y.2
  let Mx : ∀ x, Matrix (Fin d) (Fin d) Γ((U x : Scheme.{0}), ⊤) := fun x =>
    (G x).map (((U x).ι ≫ p ≫ i).appLE (N x) ⊤ (hU x)).hom
  have hL : ∀ x, LocMat B α β ((U x).ι ≫ p) (Mx x) := by
    intro x y
    have hT : ⊤ ≤ ((⊤ : (U x : Scheme.{0}).Opens).ι ≫ ((U x).ι ≫ p) ≫ i) ⁻¹ᵁ N x := by
      intro z _
      exact z.1.2
    refine ⟨⊤, N x, trivial, hNa x, h₁ x, h₂ x, hT, G x, hG x, ?_⟩
    ext a b
    exact appTop_appLE _ _ _ (by simp) _ _ _ _
  have hglue : ∀ a b, ∃ s₀ : Γ(V, ⊤), ∀ x, (U x).ι.appTop.hom s₀ = Mx x a b := by
    intro a b
    refine glueSection U hxU (fun x => Mx x a b) ?_
    intro x y S f f' hff
    have n1 := locMatNat B α β f ((U x).ι ≫ p) (Mx x) (hL x)
    have n2 := locMatNat B α β f' ((U y).ι ≫ p) (Mx y) (hL y)
    have e : f ≫ (U x).ι ≫ p = f' ≫ (U y).ι ≫ p := by
      rw [← Category.assoc, hff, Category.assoc]
    rw [e] at n1
    have := locMatUnique B α β _ _ _ n1 n2
    exact congrFun (congrFun this a) b
  choose M hM using hglue
  refine ⟨Matrix.of M, fun x => ⟨U x, N x, hxU x, hNa x, h₁ x, h₂ x, hU x, G x, hG x, ?_⟩⟩
  ext a b
  exact hM a b x
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

namespace UpperTheory.Gal.KunnethLefschetz.G.PX

variable {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
  {D : E.LineData Y} {d : ℕ}

private theorem wI_cP (B : Blow q i π D d) (α : B.ι) : wI B α ≫ cP B = (oW B α).ι := by
  unfold wI cP
  exact Sigma.ι_desc _ _

private theorem mem_V (B : Blow q i π D d) {U : Scheme.{0}} {p : U ⟶ W} {α : B.ι}
    (c : U ⟶ (oW B α : Scheme.{0})) (h : p = c ≫ (oW B α).ι) (y : U) : (p ≫ i) y ∈ B.V α := by
  subst h
  have h₁ : (c y).1 ∈ oW B α := (c y).2
  have h₂ : i (c y).1 ∈ B.V α := h₁
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact h₂

private theorem exists_loc (B : Blow q i π D d) {V : Scheme.{0}} (a b : V ⟶ WP B)
    (h : a ≫ cP B = b ≫ cP B) (x : V) :
    ∃ (U : V.Opens) (α β : B.ι) (a₁ : (U : Scheme.{0}) ⟶ oW B α) (b₁ : (U : Scheme.{0}) ⟶ oW B β)
      (M : Matrix (Fin d) (Fin d) Γ((U : Scheme.{0}), ⊤)), x ∈ U ∧
      U.ι ≫ a = a₁ ≫ wI B α ∧ U.ι ≫ b = b₁ ≫ wI B β ∧ LocMat B α β (U.ι ≫ a ≫ cP B) M := by
  obtain ⟨U₁, α, a₀, hx₁, ha⟩ := sigmaLocal (fun α : B.ι => (oW B α : Scheme.{0})) a x
  obtain ⟨U₂, β, b₀, hx₂, hb⟩ := sigmaLocal (fun α : B.ι => (oW B α : Scheme.{0})) b x
  have ha' : (U₁ ⊓ U₂).ι ≫ a = (V.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≫ a₀) ≫ wI B α := by
    have ha₀ : U₁.ι ≫ a = a₀ ≫ wI B α := ha
    rw [Category.assoc, ← ha₀, ← Category.assoc, Scheme.homOfLE_ι]
  have hb' : (U₁ ⊓ U₂).ι ≫ b = (V.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂) ≫ b₀) ≫ wI B β := by
    have hb₀ : U₂.ι ≫ b = b₀ ≫ wI B β := hb
    rw [Category.assoc, ← hb₀, ← Category.assoc, Scheme.homOfLE_ι]
  have e₁ : (U₁ ⊓ U₂).ι ≫ a ≫ cP B = (V.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≫ a₀) ≫ (oW B α).ι := by
    rw [← Category.assoc, ha', Category.assoc, wI_cP]
  have e₂ : (U₁ ⊓ U₂).ι ≫ a ≫ cP B = (V.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂) ≫ b₀) ≫ (oW B β).ι := by
    rw [h, ← Category.assoc, hb', Category.assoc, wI_cP]
  obtain ⟨M, hM⟩ := locMatExists B α β ((U₁ ⊓ U₂).ι ≫ a ≫ cP B)
    (fun y => ⟨mem_V B _ e₁ y, mem_V B _ e₂ y⟩)
  exact ⟨U₁ ⊓ U₂, α, β, _, _, M, ⟨hx₁, hx₂⟩, ha', hb', hM⟩

private theorem compat (B : Blow q i π D d) {V S : Scheme.{0}} (a b : V ⟶ WP B) {U U' : V.Opens}
    (f : S ⟶ (U : Scheme.{0})) (f' : S ⟶ (U' : Scheme.{0})) (e : f ≫ U.ι = f' ≫ U'.ι)
    {α β α' β' : B.ι} (a₁ : (U : Scheme.{0}) ⟶ oW B α) (b₁ : (U : Scheme.{0}) ⟶ oW B β)
    (a₁' : (U' : Scheme.{0}) ⟶ oW B α') (b₁' : (U' : Scheme.{0}) ⟶ oW B β')
    (ha : U.ι ≫ a = a₁ ≫ wI B α) (hb : U.ι ≫ b = b₁ ≫ wI B β)
    (ha' : U'.ι ≫ a = a₁' ≫ wI B α') (hb' : U'.ι ≫ b = b₁' ≫ wI B β')
    (M : Matrix (Fin d) (Fin d) Γ((U : Scheme.{0}), ⊤)) (M' : Matrix (Fin d) (Fin d) Γ((U' : Scheme.{0}), ⊤))
    (hM : LocMat B α β (U.ι ≫ a ≫ cP B) M) (hM' : LocMat B α' β' (U'.ι ≫ a ≫ cP B) M') :
    M.map f.appTop.hom = M'.map f'.appTop.hom := by
  by_cases hS : Nonempty S
  · obtain ⟨s⟩ := hS
    have ea : (f ≫ a₁) ≫ wI B α = (f' ≫ a₁') ≫ wI B α' := by
      rw [Category.assoc, Category.assoc, ← ha, ← ha', ← Category.assoc, ← Category.assoc, e]
    have eb : (f ≫ b₁) ≫ wI B β = (f' ≫ b₁') ≫ wI B β' := by
      rw [Category.assoc, Category.assoc, ← hb, ← hb', ← Category.assoc, ← Category.assoc, e]
    obtain rfl : α = α' := sigmaDisj (fun α : B.ι => (oW B α : Scheme.{0})) _ _ s ea
    obtain rfl : β = β' := sigmaDisj (fun α : B.ι => (oW B α : Scheme.{0})) _ _ s eb
    have n₁ := locMatNat B α β f _ M hM
    have n₂ := locMatNat B α β f' _ M' hM'
    have ep : f ≫ U.ι ≫ a ≫ cP B = f' ≫ U'.ι ≫ a ≫ cP B := by
      rw [← Category.assoc, e, Category.assoc]
    rw [ep] at n₁
    exact locMatUnique B α β _ _ _ n₁ n₂
  · have : IsEmpty S := not_nonempty_iff.mp hS
    ext r c
    exact sectionExt _ _ (fun x => isEmptyElim x)

end UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gMatExists :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (a b : V ⟶ WP B), a ≫ cP B = b ≫ cP B → ∃ M : Matrix (Fin d) (Fin d) Γ(V, ⊤), GMat B a b M := by
  intro K _ W Z Y q i π D d B V a b h
  choose U α β a₁ b₁ M hx ha hb hM using exists_loc B a b h
  have hg : ∀ r c, ∃ s₀ : Γ(V, ⊤), ∀ x, (U x).ι.appTop.hom s₀ = M x r c := fun r c =>
    glueSection U hx (fun x => M x r c) (fun x y S f f' e => by
      have h₁ := compat B a b f f' e (a₁ x) (b₁ x) (a₁ y) (b₁ y) (ha x) (hb x) (ha y) (hb y)
        (M x) (M y) (hM x) (hM y)
      exact congrFun (congrFun h₁ r) c)
  choose G hG using hg
  refine ⟨Matrix.of G, fun x => ⟨U x, α x, β x, a₁ x, b₁ x, hx x, ha x, hb x, ?_⟩⟩
  have e : (Matrix.of G).map (U x).ι.appTop.hom = M x := by
    ext r c
    exact hG r c x
  rw [e]
  exact hM x
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

namespace UpperTheory.Gal.KunnethLefschetz.G.PX

private lemma restr_sec {V Z : Scheme.{0}} (f : V ⟶ Z) {U U₂ : V.Opens} {N N₂ : Z.Opens}
    (hN : N₂ ≤ N) (hUU : U₂ ≤ U) (hU : ⊤ ≤ (U.ι ≫ f) ⁻¹ᵁ N) (hU₂ : ⊤ ≤ (U₂.ι ≫ f) ⁻¹ᵁ N₂)
    (s : Γ(V, ⊤)) (g : Γ(Z, N))
    (h : U.ι.appTop.hom s = ((U.ι ≫ f).appLE N ⊤ hU).hom g) :
    U₂.ι.appTop.hom s =
      ((U₂.ι ≫ f).appLE N₂ ⊤ hU₂).hom ((Z.presheaf.map (homOfLE hN).op).hom g) := by
  have e1 : U₂.ι.appTop = U.ι.appTop ≫ (V.homOfLE hUU).appTop := by
    rw [← Scheme.Hom.comp_appTop, Scheme.homOfLE_ι]
  have hT : (⊤ : (U₂ : Scheme.{0}).Opens) ≤ (V.homOfLE hUU) ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have e0 : (V.homOfLE hUU).appLE ⊤ ⊤ hT = (V.homOfLE hUU).appTop :=
    (Scheme.Hom.app_eq_appLE (V.homOfLE hUU)).symm
  have e2 : Z.presheaf.map (homOfLE hN).op ≫ (U₂.ι ≫ f).appLE N₂ ⊤ hU₂ =
      (U.ι ≫ f).appLE N ⊤ hU ≫ (V.homOfLE hUU).appTop := by
    rw [← e0, Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE]
    simp only [← Category.assoc, Scheme.homOfLE_ι]
  have e3 := congrArg (fun φ => φ.hom g) e2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e3
  rw [e1, CommRingCat.hom_comp, RingHom.comp_apply, h, ← e3]

variable {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)}
  {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ}

private lemma tN_res (B : Blow q i π D d) (α : B.ι) {N N₂ : Z.Opens} (h : N ≤ B.V α)
    (hN : N₂ ≤ N) (m : Fin d) :
    tN B α (hN.trans h) m = (Z.presheaf.map (homOfLE hN).op).hom (tN B α h m) := by
  simp only [tN]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private lemma isTr_res (B : Blow q i π D d) (α β : B.ι) {N N₂ : Z.Opens} (h₁ : N ≤ B.V α)
    (h₂ : N ≤ B.V β) (hN : N₂ ≤ N) (G : Matrix (Fin d) (Fin d) Γ(Z, N))
    (hG : IsTr B α β h₁ h₂ G) :
    IsTr B α β (hN.trans h₁) (hN.trans h₂) (G.map (Z.presheaf.map (homOfLE hN).op).hom) := by
  intro m
  rw [tN_res B β h₂ hN, hG m, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, tN_res B α h₁ hN]
  rfl

private lemma isTr_comp (B : Blow q i π D d) (α β γ : B.ι) {N : Z.Opens} (h₁ : N ≤ B.V α)
    (h₂ : N ≤ B.V β) (h₃ : N ≤ B.V γ) (G G' : Matrix (Fin d) (Fin d) Γ(Z, N))
    (hG : IsTr B α β h₁ h₂ G) (hG' : IsTr B β γ h₂ h₃ G') :
    IsTr B α γ h₁ h₃ (G' * G) := by
  intro m
  rw [hG' m]
  simp only [hG _, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatComp :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β γ : B.ι) {V : Scheme.{0}} (p : V ⟶ W) (M M' : Matrix (Fin d) (Fin d) Γ(V, ⊤)), LocMat B α β p M → LocMat B β γ p M' → LocMat B α γ p (M' * M) := by
  intro K _ W Z Y q i π D d B α β γ V p M M' h h' x
  obtain ⟨U, N, hx, hNa, h₁, h₂, hU, G, hG, hM⟩ := h x
  obtain ⟨U', N', hx', hNa', h₁', h₂', hU', G', hG', hM'⟩ := h' x
  have hxN : (p ≫ i) x ∈ N := hU (Set.mem_univ (⟨x, hx⟩ : (U : Scheme.{0})))
  have hxN' : (p ≫ i) x ∈ N' := hU' (Set.mem_univ (⟨x, hx'⟩ : (U' : Scheme.{0})))
  obtain ⟨N₂, hA, hxN₂, hle⟩ := exists_isAffineOpen_mem_and_subset (U := N ⊓ N') ⟨hxN, hxN'⟩
  have hl₁ : N₂ ≤ N := fun y hy => (hle hy).1
  have hl₂ : N₂ ≤ N' := fun y hy => (hle hy).2
  let U₂ : V.Opens := U ⊓ U' ⊓ (p ≫ i) ⁻¹ᵁ N₂
  have hUl : U₂ ≤ U := fun y hy => hy.1.1
  have hUl' : U₂ ≤ U' := fun y hy => hy.1.2
  have hU₂ : ⊤ ≤ (U₂.ι ≫ p ≫ i) ⁻¹ᵁ N₂ := by
    intro y _
    exact y.2.2
  refine ⟨U₂, N₂, ⟨⟨hx, hx'⟩, hxN₂⟩, hA, hl₁.trans h₁, hl₂.trans h₂', hU₂,
    G'.map (Z.presheaf.map (homOfLE hl₂).op).hom * G.map (Z.presheaf.map (homOfLE hl₁).op).hom,
    ?_, ?_⟩
  · exact isTr_comp B α β γ _ (hl₁.trans h₂) _ _ _ (isTr_res B α β h₁ h₂ hl₁ G hG)
      (isTr_res B β γ h₁' h₂' hl₂ G' hG')
  · rw [Matrix.map_mul, Matrix.map_mul]
    congr 1
    · ext a b
      exact restr_sec (p ≫ i) hl₂ hUl' hU' hU₂ _ _ (congrFun (congrFun hM' a) b)
    · ext a b
      exact restr_sec (p ≫ i) hl₁ hUl hU hU₂ _ _ (congrFun (congrFun hM a) b)
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem map_map_appTop {A B C : Scheme.{0}} {d : ℕ} (f : A ⟶ B) (g : B ⟶ C)
    (M : Matrix (Fin d) (Fin d) Γ(C, ⊤)) :
    (M.map g.appTop.hom).map f.appTop.hom = M.map (f ≫ g).appTop.hom := by
  ext m n
  simp only [Matrix.map_apply, Scheme.Hom.comp_appTop]
  rfl

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gMatComp :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (a b k : V ⟶ WP B) (M M' : Matrix (Fin d) (Fin d) Γ(V, ⊤)), a ≫ cP B = b ≫ cP B → GMat B a b M → GMat B b k M' → GMat B a k (M' * M) := by
  intro K _ W Z Y q i π D d B V a b k M M' hab h₁ h₂ x
  obtain ⟨U, α, β, a₁, b₁, hx, ha, hb, hL⟩ := h₁ x
  obtain ⟨U', β', γ, b₂, k₂, hx', hb', hk', hL'⟩ := h₂ x
  let e : ((U ⊓ U' : V.Opens) : Scheme.{0}) ⟶ U := V.homOfLE inf_le_left
  let e' : ((U ⊓ U' : V.Opens) : Scheme.{0}) ⟶ U' := V.homOfLE inf_le_right
  have he : e ≫ U.ι = (U ⊓ U').ι := V.homOfLE_ι _
  have he' : e' ≫ U'.ι = (U ⊓ U').ι := V.homOfLE_ι _
  have hβ : β = β' := by
    refine UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaDisj (fun α : B.ι => (oW B α : Scheme.{0})) (e ≫ b₁) (e' ≫ b₂)
      (⟨x, hx, hx'⟩ : ((U ⊓ U' : V.Opens) : Scheme.{0})) ?_
    change (e ≫ b₁) ≫ wI B β = (e' ≫ b₂) ≫ wI B β'
    rw [Category.assoc, Category.assoc, ← hb, ← hb', ← Category.assoc, ← Category.assoc, he, he']
  subst hβ
  refine ⟨U ⊓ U', α, γ, e ≫ a₁, e' ≫ k₂, ⟨hx, hx'⟩, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← ha, ← Category.assoc, he]
  · rw [Category.assoc, ← hk', ← Category.assoc, he']
  · have n₁ := UpperTheory.Gal.KunnethLefschetz.G.PX.locMatNat B α β e _ _ hL
    have n₂ := UpperTheory.Gal.KunnethLefschetz.G.PX.locMatNat B β γ e' _ _ hL'
    rw [map_map_appTop, he, ← Category.assoc, he] at n₁
    rw [map_map_appTop, he', ← Category.assoc, he', ← hab] at n₂
    have := UpperTheory.Gal.KunnethLefschetz.G.PX.locMatComp B α β γ _ _ _ n₁ n₂
    rwa [← Matrix.map_mul] at this
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gMatOne :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (a : V ⟶ WP B), GMat B a a 1 := by
  intro K _ W Z Y q i π D d B V a x
  obtain ⟨U, α, a₁, hx, ha⟩ := sigmaLocal (fun α : B.ι => (oW B α : Scheme.{0})) a x
  refine ⟨U, α, α, a₁, a₁, hx, ha, ha, ?_⟩
  have hc : U.ι ≫ a ≫ cP B = a₁ ≫ (oW B α).ι := by
    have h : wI B α ≫ cP B = (oW B α).ι := by
      simp [wI, cP]
    rw [← Category.assoc, show U.ι ≫ a = a₁ ≫ wI B α from ha, Category.assoc, h]
  have h1 : (1 : Matrix (Fin d) (Fin d) Γ(V, ⊤)).map U.ι.appTop.hom = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  rw [h1]
  refine locMatOne B α _ fun y => ?_
  rw [hc, Category.assoc, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact (a₁ y).2
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.existsG :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d), ∃ g : ∀ {V : Scheme.{0}} (a b : V ⟶ WP B), a ≫ cP B = b ≫ cP B → GL (Fin d) Γ(V, ⊤), (∀ {V' V : Scheme.{0}} (s : V' ⟶ V) (a b : V ⟶ WP B) (h : a ≫ cP B = b ≫ cP B), g (s ≫ a) (s ≫ b) (by rw [Category.assoc, h, Category.assoc]) = Matrix.GeneralLinearGroup.map s.appTop.hom (g a b h)) ∧ (∀ {V : Scheme.{0}} (a b k : V ⟶ WP B) (h : a ≫ cP B = b ≫ cP B) (h' : b ≫ cP B = k ≫ cP B), g b k h' * g a b h = g a k (h.trans h')) ∧ ∀ {V : Scheme.{0}} (a b : V ⟶ WP B) (h : a ≫ cP B = b ≫ cP B), GMat B a b (g a b h : Matrix (Fin d) (Fin d) Γ(V, ⊤)) := by
  intro K _ W Z Y q i π D d B
  have hinv : ∀ {V : Scheme.{0}} (a b : V ⟶ WP B) (h : a ≫ cP B = b ≫ cP B),
      (gMatExists B b a h.symm).choose * (gMatExists B a b h).choose = 1 := fun a b h =>
    gMatUnique B a a _ _
      (gMatComp B a b a _ _ h (gMatExists B a b h).choose_spec (gMatExists B b a h.symm).choose_spec)
      (gMatOne B a)
  refine ⟨fun {V} a b h => ⟨(gMatExists B a b h).choose, (gMatExists B b a h.symm).choose,
    hinv b a h.symm, hinv a b h⟩, ?_, ?_, ?_⟩
  · intro V' V s a b h
    apply Units.ext
    exact gMatUnique B (s ≫ a) (s ≫ b) _ _ (gMatExists B (s ≫ a) (s ≫ b) (by rw [Category.assoc, h, Category.assoc])).choose_spec
      (gMatNat B s a b _ (gMatExists B a b h).choose_spec)
  · intro V a b k h h'
    apply Units.ext
    exact gMatUnique B a k _ _
      (gMatComp B a b k _ _ h (gMatExists B a b h).choose_spec (gMatExists B b k h').choose_spec)
      (gMatExists B a k (h.trans h')).choose_spec
  · intro V a b h
    exact (gMatExists B a b h).choose_spec
end
