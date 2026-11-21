import Development.EtaleCohomology.EtaleSheaves.StalkGerm
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf

namespace LateralTheory.E.StalkGermPf

abbrev toO {X S : Scheme.{0}} (p : X ⟶ S) (s : S) (U : S.Opens) (hs : s ∈ U) :
    pullback p (S.fromSpecStalk s) ⟶ overO p U :=
  pullback.map p (S.fromSpecStalk s) p U.ι (𝟙 _) (U.fromSpecStalkOfMem s hs) (𝟙 _) (by simp) (by simp)

def StalkCont : Prop := Cont → Hyp → ∀ (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
  [QuasiCompact p] [QuasiSeparated p], IsUnit (q : Γ(S, ⊤)) → ∀ (i n : ℤ) (s : S),
  (∀ (U : S.Opens) (hs : s ∈ U) (x : Ht q (sch.obj (overO p U)) n i), pull _ (sch.map (toO p s U hs)) _ _ x = 0 →
    ∃ (V : S.Opens) (h : V ≤ U), s ∈ V ∧ pull _ (sch.map (resO p h)) _ _ x = 0) ∧
  (∀ z : Ht q (sch.obj (pullback p (S.fromSpecStalk s))) n i, ∃ (U : S.Opens) (hs : s ∈ U) (x : Ht q (sch.obj (overO p U)) n i),
    pull _ (sch.map (toO p s U hs)) _ _ x = z)

variable {Y X S : Scheme.{0}}

theorem pull_mc {q : ℕ} {n i : ℤ} {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C) (x : Ht q (sch.obj C) n i) :
    pull _ (sch.map (a ≫ b)) (tw q i) n x = pull _ (sch.map a) _ _ (pull _ (sch.map b) _ _ x) := by
  rw [Functor.map_comp, pull_comp]

theorem toO_res (p : X ⟶ S) (s : S) {V U : S.Opens} (h : V ≤ U) (hV : s ∈ V) :
    toO p s V hV ≫ resO p h = toO p s U (h hV) := by
  have e : V.fromSpecStalkOfMem s hV ≫ S.homOfLE h = U.fromSpecStalkOfMem s (h hV) := by
    rw [← cancel_mono U.ι]; simp
  simp only [toO, resO]; rw [pullback.map_comp]; congr 1 <;> simp [e]

theorem toO_f (f : Y ⟶ X) (p : X ⟶ S) (s : S) (U : S.Opens) (hs : s ∈ U) :
    pullback.map (f ≫ p) (S.fromSpecStalk s) p (S.fromSpecStalk s) f (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ toO p s U hs =
      toO (f ≫ p) s U hs ≫ fO f p U := by
  simp only [toO, resO, fO]; rw [pullback.map_comp]; try rw [pullback.map_comp]
  all_goals (try congr 1) <;> simp

theorem res_f (f : Y ⟶ X) (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO (f ≫ p) h ≫ fO f p U = fO f p V ≫ resO p h := by
  simp only [toO, resO, fO]; rw [pullback.map_comp]; try rw [pullback.map_comp]
  all_goals (try congr 1) <;> simp

theorem res_res (p : X ⟶ S) {W V U : S.Opens} (h1 : W ≤ V) (h2 : V ≤ U) :
    resO p h1 ≫ resO p h2 = resO p (h1.trans h2) := by
  simp only [toO, resO, fO]; rw [pullback.map_comp]; try rw [pullback.map_comp]
  all_goals (try congr 1) <;> simp

theorem StalkGerm_of (hS : StalkCont) : StalkGerm := by
  intro hC hH q Y X S f p _ _ _ _ _ _ hq i s he n
  obtain ⟨ia, sa⟩ := hS hC hH q p hq i n s
  obtain ⟨ib, -⟩ := hS hC hH q (f ≫ p) hq i n s
  have hb := he n
  constructor
  · intro U hs x hx
    apply ia U hs x
    apply hb.1
    rw [map_zero, ← pull_mc, toO_f, pull_mc, hx, map_zero]
  · intro U hs y
    obtain ⟨w, hw⟩ := hb.2 (pull _ (sch.map (toO (f ≫ p) s U hs)) _ _ y)
    obtain ⟨U1, hs1, x1, hx1⟩ := sa w
    have hs2 : s ∈ U ⊓ U1 := ⟨hs, hs1⟩
    have hx2' : pull (ZMod q) (sch.map (toO p s (U ⊓ U1) hs2)) (tw q i) n
        (pull (ZMod q) (sch.map (resO p (inf_le_right : U ⊓ U1 ≤ U1))) (tw q i) n x1) = w := by
      rw [← pull_mc, toO_res]; exact hx1
    obtain ⟨x2, hx2⟩ : ∃ x2 : H (ZMod q) (sch.obj (overO p (U ⊓ U1))) (tw q i) n,
        pull (ZMod q) (sch.map (toO p s (U ⊓ U1) hs2)) (tw q i) n x2 = w := ⟨_, hx2'⟩
    have e1 : pull _ (sch.map (toO (f ≫ p) s (U ⊓ U1) hs2)) _ _ (pull _ (sch.map (fO f p (U ⊓ U1))) _ _ x2) =
        pull _ (sch.map (pullback.map (f ≫ p) (S.fromSpecStalk s) p (S.fromSpecStalk s) f (𝟙 _) (𝟙 _)
          (by simp) (by simp))) (tw q i) n (pull _ (sch.map (toO p s (U ⊓ U1) hs2)) _ _ x2) := by
      rw [← pull_mc, ← pull_mc, toO_f]
    have e2 : pull _ (sch.map (toO (f ≫ p) s (U ⊓ U1) hs2)) _ _
        (pull _ (sch.map (resO (f ≫ p) (inf_le_left : U ⊓ U1 ≤ U))) _ _ y) =
        pull _ (sch.map (toO (f ≫ p) s U hs)) (tw q i) n y := by
      rw [← pull_mc, toO_res]
    have h0 : pull _ (sch.map (toO (f ≫ p) s (U ⊓ U1) hs2)) _ _
        (pull _ (sch.map (fO f p (U ⊓ U1))) _ _ x2 -
          pull _ (sch.map (resO (f ≫ p) (inf_le_left : U ⊓ U1 ≤ U))) _ _ y) = 0 := by
      rw [map_sub, e1, e2, hx2, hw, sub_self]
    obtain ⟨V, hV, hsV, hd⟩ := ib _ hs2 _ h0
    refine ⟨V, hV.trans inf_le_left, hsV, pull _ (sch.map (resO p hV)) _ _ x2, ?_⟩
    rw [map_sub, sub_eq_zero] at hd
    have g1 : pull _ (sch.map (fO f p V)) _ _ (pull _ (sch.map (resO p hV)) _ _ x2) =
        pull _ (sch.map (resO (f ≫ p) hV)) (tw q i) n (pull _ (sch.map (fO f p (U ⊓ U1))) _ _ x2) := by
      rw [← pull_mc, ← pull_mc, res_f]
    have g2 : pull _ (sch.map (resO (f ≫ p) hV)) (tw q i) n
        (pull _ (sch.map (resO (f ≫ p) (inf_le_left : U ⊓ U1 ≤ U))) _ _ y) =
        pull _ (sch.map (resO (f ≫ p) (hV.trans inf_le_left))) (tw q i) n y := by
      rw [← pull_mc, res_res]
    rw [g1, hd, g2]

end LateralTheory.E.StalkGermPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf LateralTheory.E.StalkGermPf GlobalTheory.StalkLimit

namespace LateralTheory.E.StalkContPf

set_option backward.isDefEq.respectTransparency false

variable {X S : Scheme.{0}}

theorem diagram_map_eq (p : X ⟶ S) (s : S) {V W : AffNhd s} (i : V ⟶ W) :
    (diagram s p).map i = resO p i.le := by
  apply pullback.hom_ext <;> simp [diagram, resO]

theorem cone_app_eq (p : X ⟶ S) (s : S) (V : AffNhd s) :
    (cone (IsPullback.of_hasPullback p (S.fromSpecStalk s))).π.app V = toO p s V.1 V.2.1 := by
  apply pullback.hom_ext <;> simp [cone, toO]

theorem pull_cone {q : ℕ} {n i : ℤ} (p : X ⟶ S) (s : S) (V : AffNhd s) (y : Ht q (sch.obj (overO p V.1)) n i) :
    pull _ (sch.map ((cone (IsPullback.of_hasPullback p (S.fromSpecStalk s))).π.app V)) (tw q i) n y =
      pull _ (sch.map (toO p s V.1 V.2.1)) (tw q i) n y := by
  rw [cone_app_eq]; rfl

theorem pull_diag {q : ℕ} {n i : ℤ} (p : X ⟶ S) (s : S) {V W : AffNhd s} (f : V ⟶ W)
    (y : Ht q (sch.obj (overO p W.1)) n i) :
    pull _ (sch.map ((diagram s p).map f)) (tw q i) n y = pull _ (sch.map (resO p f.le)) (tw q i) n y := by
  rw [diagram_map_eq]; rfl

theorem exists_aff (s : S) (U : S.Opens) (hs : s ∈ U) : ∃ V : AffNhd s, V.1 ≤ U := by
  obtain ⟨W, h₁, h₂, h₃⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hs
  exact ⟨⟨W, h₂, h₁⟩, h₃⟩

theorem StalkCont_of : StalkCont := by
  intro hC hH q X S p _ _ _ _ hq i n s
  have hc := (nonempty_isLimit (IsPullback.of_hasPullback p (S.fromSpecStalk s))).some
  have hcpt : ∀ V : AffNhd s, CompactSpace ((diagram s p).obj V) := fun V => by
    have : IsAffine V.1.toScheme := V.2.2
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd p V.1.ι)
  have hqs : ∀ V : AffNhd s, QuasiSeparatedSpace ((diagram s p).obj V) := fun V => by
    have : IsAffine V.1.toScheme := V.2.2
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd p V.1.ι)
  have hu : ∀ V : AffNhd s, IsUnit (q : Γ((diagram s p).obj V, ⊤)) := fun V => by
    have := hq.map ((pullback.fst p V.1.ι ≫ p).appTop).hom
    simp only [map_natCast] at this
    exact this
  obtain ⟨hsurj, hkill⟩ := hC hH q (diagram s p) _ hc (fun f => inferInstance) hcpt hqs hu n i
  constructor
  · intro U hs x hx
    obtain ⟨V0, hV0⟩ := exists_aff s U hs
    have h0 : pull _ (sch.map ((cone (IsPullback.of_hasPullback p (S.fromSpecStalk s))).π.app V0)) _ _
        (pull _ (sch.map (resO p hV0)) _ _ x) = 0 := by
      rw [pull_cone, ← pull_mc, toO_res]; exact hx
    obtain ⟨k, f, hf⟩ := hkill V0 _ h0
    have hkV : k.1 ≤ V0.1 := f.le
    refine ⟨k.1, hkV.trans hV0, k.2.1, ?_⟩
    rw [pull_diag, ← pull_mc, res_res] at hf
    exact hf
  · intro z
    obtain ⟨j, y, hy⟩ := hsurj z
    exact ⟨j.1, j.2.1, y, (pull_cone p s j y).symm.trans hy⟩

end LateralTheory.E.StalkContPf
end
end
