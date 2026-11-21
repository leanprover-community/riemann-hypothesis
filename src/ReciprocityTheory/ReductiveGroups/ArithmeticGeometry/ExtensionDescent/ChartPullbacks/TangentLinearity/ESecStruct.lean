import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.PairProp

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf

open Semi

section SlopeTestRemainingChoices

variable {Y Z : Scheme.{0}} (L : LB Y) {K K' : Type} [Fintype K] [Fintype K']

lemma wchart_inl_le (φ : K → (Z ⟶ Y)) (φ' : K' → (Z ⟶ Y)) (j : K ⊕ K' → L.ι) :
    LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ (j ∘ Sum.inl) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)

lemma wchart_inr_le (φ : K → (Z ⟶ Y)) (φ' : K' → (Z ⟶ Y)) (j : K ⊕ K' → L.ι) :
    LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ' (j ∘ Sum.inr) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)

private lemma appLE_res_lemma {T₀ Z₀ : Scheme.{0}} (f : T₀ ⟶ Z₀) {V₀ U₀ : Z₀.Opens} (hVU : V₀ ≤ U₀)
    (W₀ : T₀.Opens) (h : W₀ ≤ f ⁻¹ᵁ V₀) (h' : W₀ ≤ f ⁻¹ᵁ U₀) (x : Γ(Z₀, U₀)ˣ) :
    (f.appLE V₀ W₀ h).hom (res hVU x).val = (f.appLE U₀ W₀ h').hom x.val := by
  rw [← Scheme.Hom.map_appLE f h (homOfLE hVU).op]
  rfl

lemma appLE_mulGen {T : Scheme.{0}} (f : T ⟶ Z) (φ : K → (Z ⟶ Y)) (ε : K → ℤ) (φ' : K' → (Z ⟶ Y))
    (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (j : K ⊕ K' → L.ι) (W' : T.Opens) (h : W' ≤ f ⁻¹ᵁ LB.wchart L (Sum.elim φ φ') j) :
    (f.appLE _ W' h).hom ((LB.mulGen L φ ε φ' ε' t t').s j).val =
      (f.appLE (LB.wchart L φ (j ∘ Sum.inl)) W' (fun _ hz => wchart_inl_le L φ φ' j (h hz))).hom (t.s (j ∘ Sum.inl)).val *
      (f.appLE (LB.wchart L φ' (j ∘ Sum.inr)) W' (fun _ hz => wchart_inr_le L φ φ' j (h hz))).hom (t'.s (j ∘ Sum.inr)).val := by
  simp only [LB.mulGen, Units.val_mul, map_mul]
  congr 1 <;> exact appLE_res_lemma _ _ _ _ _ _

lemma appLE_pullGen {T X : Scheme.{0}} (f : T ⟶ Z) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (L : LB X)
    (c : LB.Gen (LB.LinComb L φ ε)) (hh : Z ⟶ Y) (j : K → L.ι) (W' : T.Opens)
    (h : W' ≤ f ⁻¹ᵁ LB.wchart L (fun k => hh ≫ φ k) j) :
    (f.appLE _ W' h).hom ((LB.pullGen L φ ε c hh).s j).val =
      ((f ≫ hh).appLE (LB.wchart L φ j) W'
        (fun _ hz => Semi.LBVal.wchart_pull_le L φ hh j (h hz))).hom (c.s j).val := by
  simp only [LB.pullGen]
  refine (appLE_res_lemma f _ W' h ?_ _).trans ?_
  · exact fun _ hz => Semi.LBVal.wchart_pull_le L φ hh j (h hz)
  · first
      | rfl
      | (rw [Scheme.Hom.appLE, Scheme.Hom.appLE, Scheme.comp_app]; rfl)
      | simp [pullU, Scheme.Hom.appLE, Scheme.comp_app]

end SlopeTestRemainingChoices

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))

private lemma q_act_lemma :
    (Over.map (thick R I e)).map (WeightPf.act (U.gt e)) ≫ (Over.map (thick R I e)).map (U.gt e).q =
      (Over.map (thick R I e)).map (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)) ≫
        (Over.map (thick R I e)).map (U.gt e).q := by
  rw [← Functor.map_comp, WeightPf.act_q, Functor.map_comp]

private lemma pG_act_lemma :
    (Over.map (thick R I e)).map (WeightPf.act (U.gt e)) ≫ (U.gt e).pG =
      (Over.map (thick R I e)).map (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)) ≫
        (U.gt e).pG := by
  first
    | (simp only [GtCoord.pG]
       rw [← Category.assoc, ← Functor.map_comp, WeightPf.act_q, Functor.map_comp, Category.assoc])
    | simp [GtCoord.pG, ← Functor.map_comp_assoc, WeightPf.act_q]

private lemma unit_act_lemma :
    (Over.map (thick R I e)).map (WeightPf.act (U.gt e)) ≫
        toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) =
      (Over.map (thick R I e)).map (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)) ≫
        toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) :=
  toUnit_unique _ _

private lemma left_act_lemma {A' : Over (Spec (CommRingCat.of R))}
    (p : (Over.map (thick R I e)).obj (thickObj R I e G) ⟶ A')
    (hp : (Over.map (thick R I e)).map (WeightPf.act (U.gt e)) ≫ p =
      (Over.map (thick R I e)).map (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)) ≫ p) :
    (WeightPf.act (U.gt e)).left ≫ p.left =
      (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ p.left := by
  simpa using congrArg CommaMorphism.left hp

lemma act_lift_xc :
    (WeightPf.act (U.gt e)).left ≫ (lift (xc e χ (G := G)) (U.gt e).pG).left =
      (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫
        (lift (xc e χ (G := G)) (U.gt e).pG).left := by
  refine left_act_lemma (U := U) (e := e) _ ?_
  first
    | (rw [comp_lift, comp_lift, pG_act_lemma]
       simp only [xc, ← Category.assoc, unit_act_lemma])
    | simp [xc, pG_act_lemma, unit_act_lemma]

theorem hA_act (k : Fin 4 ⊕ Fin 6) :
    (WeightPf.act (U.gt e)).left ≫ φA U ιD e a χ k =
      (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ φA U ιD e a χ k := by
  rcases k with k | k
  · simp only [φA, Sum.elim_inl]
    fin_cases k
    · exact left_act_lemma (U := U) (e := e)
        (padd D.toPre.P.A (U.gt e).pG (toUnit _ ≫ D.toPre.c (star a • χ)))
        (by simp only [padd, ← Category.assoc, comp_lift, pG_act_lemma, q_act_lemma, unit_act_lemma])
    · exact left_act_lemma (U := U) (e := e) (toUnit _ ≫ D.toPre.c (star a • χ))
        (by simp only [← Category.assoc, unit_act_lemma])
    · exact left_act_lemma (U := U) (e := e) (U.gt e).pG (pG_act_lemma U e)
    · exact left_act_lemma (U := U) (e := e) (toUnit _ ≫ η[D.toPre.P.A])
        (by simp only [← Category.assoc, unit_act_lemma])
  · simp only [φA, Sum.elim_inr, ← Category.assoc, act_lift_xc]

private lemma res_val_lemma {X₀ : Scheme.{0}} {U₀ V₀ W₀ : X₀.Opens} (e₀ : V₀ ≤ U₀) (hW : W₀ ≤ V₀)
    (x : Γ(X₀, U₀)ˣ) :
    (X₀.presheaf.map (homOfLE hW).op).hom (res e₀ x).val =
      (X₀.presheaf.map (homOfLE (hW.trans e₀)).op).hom x.val := by
  show (X₀.presheaf.map (homOfLE e₀).op ≫ X₀.presheaf.map (homOfLE hW).op).hom x.val = _
  rw [← Functor.map_comp]
  rfl

private lemma pull_val_lemma {X₀ Y₀ : Scheme.{0}} (g : Y₀ ⟶ X₀) (U₀ : X₀.Opens) {W₀ : Y₀.Opens}
    (hW : W₀ ≤ g ⁻¹ᵁ U₀) (x : Γ(X₀, U₀)ˣ) :
    (Y₀.presheaf.map (homOfLE hW).op).hom (pullU g U₀ x).val = (g.appLE U₀ W₀ hW).hom x.val :=
  rfl

private lemma corr_val_lemma {X₀ : Scheme.{0}} {V₀ V₁ V₂ W₀ : X₀.Opens} (h₁ : V₀ ≤ V₁) (h₂ : V₀ ≤ V₂)
    (x : Γ(X₀, V₁)ˣ) (y : Γ(X₀, V₂)ˣ) (hE : res h₁ x = res h₂ y) (hW₁ : W₀ ≤ V₁) (hW₂ : W₀ ≤ V₂)
    (hW : W₀ ≤ V₀) :
    (X₀.presheaf.map (homOfLE hW₁).op).hom x.val = (X₀.presheaf.map (homOfLE hW₂).op).hom y.val := by
  have h3 := congrArg (fun z => (X₀.presheaf.map (homOfLE hW).op).hom (Units.val z)) hE
  simp only [res_val_lemma] at h3
  exact h3

private lemma mulGen_val_lemma {X₀ Y₀ : Scheme.{0}} (L₀ : LB X₀) {K₀ K₁ : Type} [Fintype K₀]
    [Fintype K₁] (φ : K₀ → (Y₀ ⟶ X₀)) (ε : K₀ → ℤ) (φ' : K₁ → (Y₀ ⟶ X₀)) (ε' : K₁ → ℤ)
    (t : LB.Gen (LB.LinComb L₀ φ ε)) (t' : LB.Gen (LB.LinComb L₀ φ' ε')) (j : K₀ ⊕ K₁ → L₀.ι)
    {W₀ : Y₀.Opens} (hW : W₀ ≤ LB.wchart L₀ (Sum.elim φ φ') j) :
    (Y₀.presheaf.map (homOfLE hW).op).hom ((LB.mulGen L₀ φ ε φ' ε' t t').s j).val =
      (Y₀.presheaf.map (homOfLE (hW.trans (wchart_inl_le L₀ φ φ' j))).op).hom
          (t.s (j ∘ Sum.inl)).val *
        (Y₀.presheaf.map (homOfLE (hW.trans (wchart_inr_le L₀ φ φ' j))).op).hom
          (t'.s (j ∘ Sum.inr)).val := by
  simp only [LB.mulGen, Units.val_mul, map_mul]
  congr 1 <;> exact res_val_lemma _ _ _

private lemma pullGen_val_lemma {X₀ Y₀ Z₀ : Scheme.{0}} (L₀ : LB X₀) {K₀ : Type} [Fintype K₀]
    (φ : K₀ → (Y₀ ⟶ X₀)) (ε : K₀ → ℤ) (c : LB.Gen (LB.LinComb L₀ φ ε)) (h : Z₀ ⟶ Y₀)
    (j : K₀ → L₀.ι) {W₀ : Z₀.Opens} (hW : W₀ ≤ LB.wchart L₀ (fun k => h ≫ φ k) j) :
    (Z₀.presheaf.map (homOfLE hW).op).hom ((LB.pullGen L₀ φ ε c h).s j).val =
      (h.appLE (LB.wchart L₀ φ j) W₀ (hW.trans (Semi.LBVal.wchart_pull_le L₀ φ h j))).hom
        (c.s j).val :=
  (res_val_lemma _ _ _).trans (pull_val_lemma _ _ _ _)

private lemma charGen_val_lemma {S₀ : Scheme.{0}} (X₁ : Type) [AddCommGroup X₁] (G₀ : Over S₀)
    {Z₀ : Scheme.{0}} (L₀ : LB Z₀) (χ₀ : X₁) (j : PEmpty → L₀.ι)
    {W₀ : (splitTorus S₀ X₁ ⊗ G₀).left.Opens}
    (hW : W₀ ≤ LB.wchart L₀ (Y := (splitTorus S₀ X₁ ⊗ G₀).left) (K := PEmpty) PEmpty.elim j) :
    ((splitTorus S₀ X₁ ⊗ G₀).left.presheaf.map (homOfLE hW).op).hom
        ((charGen X₁ G₀ L₀ χ₀).s j).val =
      ((splitTorus S₀ X₁ ⊗ G₀).left.presheaf.map (homOfLE (le_top : W₀ ≤ ⊤)).op).hom
        (Semi.TorusInj.chiP X₁ G₀ χ₀) :=
  (res_val_lemma _ _ _).trans rfl

private lemma appLE_congr_lemma {X₀ Y₀ : Scheme.{0}} {f g : Y₀ ⟶ X₀} (hfg : f = g) {U₀ : X₀.Opens}
    {W₀ : Y₀.Opens} (h₁ : W₀ ≤ f ⁻¹ᵁ U₀) (h₂ : W₀ ≤ g ⁻¹ᵁ U₀) (x : Γ(X₀, U₀)) :
    (f.appLE U₀ W₀ h₁).hom x = (g.appLE U₀ W₀ h₂).hom x := by
  subst hfg
  rfl

private lemma snd_cancel_lemma {Z₀ : Scheme.{0}} (x y : (thickObj R I e G).left ⟶ Z₀)
    (h : (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ x =
      (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ y) : x = y := by
  have h2 := congrArg ((lift (toUnit (thickObj R I e G) ≫ η[WeightPf.Te D.toPre I e])
    (𝟙 (thickObj R I e G))).left ≫ ·) h
  simpa only [← Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.id_comp] using h2

theorem lhs_act (jA : Fin 4 ⊕ Fin 6 → D.toPre.P.L.ι) (cA : LB.Coh D.toPre.P.L (φA U ιD e a χ) jA)
    (W' : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.Opens)
    (hs : W' ≤ (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ
      LB.wchart D.toPre.P.L (φA U ιD e a χ) jA)
    (ha : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) :
    ((WeightPf.act (U.gt e)).left.appLE _ W' ha).hom ((lhs U ιD e a χ u).s jA).val =
      ((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom
        (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) (star a • χ)) *
      ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE _ W' hs).hom
        ((lhs U ιD e a χ u).s jA).val := by
  simp only [lhs]
  rw [appLE_mulGen, appLE_mulGen, ← _root_.mul_assoc]
  congr 1
  · have hact : ∀ k : Fin 4, (WeightPf.act (U.gt e)).left ≫ D.toPre.Oφ (U.gt e).pG (star a • χ) k =
        (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫
          D.toPre.Oφ (U.gt e).pG (star a • χ) k :=
      fun k => hA_act (U := U) (ιD := ιD) (e := e) (a := a) (χ := χ) (Sum.inl k)
    have key : ∀ k₁ k₂ : Fin 4,
        (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫
            D.toPre.Oφ (U.gt e).pG (star a • χ) k₁ =
          (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫
            D.toPre.Oφ (U.gt e).pG (star a • χ) k₂ →
        jA (Sum.inl k₁) = jA (Sum.inl k₂) :=
      fun k₁ k₂ h => cA (Sum.inl k₁) (Sum.inl k₂) (snd_cancel_lemma (e := e) _ _ h)
    have E := (U.gt e).t_weight (star a • χ) (jA ∘ Sum.inl)
      (Sum.elim (fun x => x.elim) (jA ∘ Sum.inl))
      (fun k₁ k₂ h => key k₁ k₂ ((hact k₁).symm.trans (h.trans (hact k₂))))
      (by
        rintro (k₁ | k₁) (k₂ | k₂) h <;>
          first | exact k₁.elim | exact k₂.elim | exact key k₁ k₂ h)
      (by
        rintro k (k' | k') h <;>
          first | exact k'.elim | exact key k k' ((hact k).symm.trans h))
    have h1 : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ
        LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG (star a • χ)) (jA ∘ Sum.inl) :=
      fun _ hz => wchart_inl_le D.toPre.P.L _ _ jA (ha hz)
    have h2 : W' ≤ (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ
        LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG (star a • χ)) (jA ∘ Sum.inl) :=
      fun _ hz => wchart_inl_le D.toPre.P.L _ _ jA (hs hz)
    have hWa : W' ≤ LB.wchart D.toPre.P.L
        (fun k => (WeightPf.act (U.gt e)).left ≫ D.toPre.Oφ (U.gt e).pG (star a • χ) k)
        (jA ∘ Sum.inl) :=
      fun _ hz => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h1 hz) k
    have hWb : W' ≤ LB.wchart D.toPre.P.L
        (Sum.elim (PEmpty.elim : PEmpty → _) (fun k => (snd (WeightPf.Te D.toPre I e)
          (thickObj R I e G)).left ≫ D.toPre.Oφ (U.gt e).pG (star a • χ) k))
        (Sum.elim (fun x => x.elim) (jA ∘ Sum.inl)) := by
      intro z hz
      refine Set.mem_iInter.2 ?_
      rintro (k | k)
      · exact k.elim
      · exact Set.mem_iInter.1 (h2 hz) k
    have E' := corr_val_lemma _ _ _ _ E hWa hWb (le_inf hWa hWb)
    exact (pullGen_val_lemma ..).symm.trans (E'.trans ((mulGen_val_lemma ..).trans
      (congrArg₂ (· * ·) (charGen_val_lemma ..) (pullGen_val_lemma ..))))
  · exact (appLE_pullGen ..).trans ((appLE_congr_lemma (act_lift_xc (U := U) (e := e) (χ := χ)) ..).trans
      (appLE_pullGen ..).symm)

end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf

open Semi

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))

include hO in

theorem hB_act (k : Fin 4) :
    (WeightPf.act (U.gt e)).left ≫ φB U ιG e a χ k =
      (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ φB U ιG e a χ k := by

  have hq0 : WeightPf.act (U.gt e) ≫ (U.gt e).q =
      snd (WeightPf.Te D.toPre I e) (thickObj R I e G) ≫ (U.gt e).q := by
    haveI := (U.gt e).q_hom
    have hiq := (U.gt e).isKernel.w
    simp only [WeightPf.act, Category.assoc, IsMonHom.mul_hom, lift_map_assoc, hiq,
      comp_toUnit_assoc, MonObj.lift_comp_one_left]
  have hq : (WeightPf.act (U.gt e) ≫ (Over.pullback (thick R I e)).map (ιG.act a)) ≫ (U.gt e).q =
      (snd (WeightPf.Te D.toPre I e) (thickObj R I e G) ≫
        (Over.pullback (thick R I e)).map (ιG.act a)) ≫ (U.gt e).q := by
    rw [Category.assoc, Category.assoc, hO, reassoc_of% hq0]

  have gen : ∀ {f g : WeightPf.Te D.toPre I e ⊗ thickObj R I e G ⟶ thickObj R I e G},
      f ≫ (U.gt e).q = g ≫ (U.gt e).q → ∀ k : Fin 4,
      f.left ≫ D.toPre.Oφ (U.gt e).pG χ k = g.left ≫ D.toPre.Oφ (U.gt e).pG χ k := by
    intro f g hfg k
    have h2 : (Over.map (thick R I e)).map f ≫ (U.gt e).pG =
        (Over.map (thick R I e)).map g ≫ (U.gt e).pG := by
      simp only [GtCoord.pG, ← Functor.map_comp_assoc, hfg]
    fin_cases k
    · exact congrArg CommaMorphism.left
        (show (Over.map (thick R I e)).map f ≫
            padd D.toPre.P.A (U.gt e).pG (toUnit _ ≫ D.toPre.c χ) =
          (Over.map (thick R I e)).map g ≫
            padd D.toPre.P.A (U.gt e).pG (toUnit _ ≫ D.toPre.c χ) by
          simp only [padd, comp_lift_assoc, h2, comp_toUnit_assoc])
    · exact congrArg CommaMorphism.left
        (show (Over.map (thick R I e)).map f ≫ (toUnit _ ≫ D.toPre.c χ) =
          (Over.map (thick R I e)).map g ≫ (toUnit _ ≫ D.toPre.c χ) by
          simp only [comp_toUnit_assoc])
    · exact congrArg CommaMorphism.left h2
    · exact congrArg CommaMorphism.left
        (show (Over.map (thick R I e)).map f ≫ (toUnit _ ≫ η[D.toPre.P.A]) =
          (Over.map (thick R I e)).map g ≫ (toUnit _ ≫ η[D.toPre.P.A]) by
          simp only [comp_toUnit_assoc])
  simpa only [Over.comp_left, Category.assoc, φB] using gen hq k

section Rhs

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιG : RingAct G O) (e : ℕ) (a : O)

abbrev actA : thickObj R I e G ⟶ thickObj R I e G := (Over.pullback (thick R I e)).map (ιG.act a)

def mA (ta : WeightPf.Te D.toPre I e ⟶ WeightPf.Te D.toPre I e) :
    WeightPf.Te D.toPre I e ⊗ thickObj R I e G ⟶ WeightPf.Te D.toPre I e ⊗ thickObj R I e G :=
  lift (fst _ _ ≫ ta) (snd _ _ ≫ actA ιG e a)

theorem mA_fst (ta : WeightPf.Te D.toPre I e ⟶ WeightPf.Te D.toPre I e) :
    mA ιG e a ta ≫ fst _ _ = fst _ _ ≫ ta := by
  simp only [mA, lift_fst]

theorem mA_snd (ta : WeightPf.Te D.toPre I e ⟶ WeightPf.Te D.toPre I e) :
    mA ιG e a ta ≫ snd _ _ = snd _ _ ≫ actA ιG e a := by
  simp only [mA, lift_snd]

theorem act_actA (ta : WeightPf.Te D.toPre I e ⟶ WeightPf.Te D.toPre I e)
    (hia : (U.gt e).i ≫ actA ιG e a = ta ≫ (U.gt e).i) :
    WeightPf.act (U.gt e) ≫ actA ιG e a = mA ιG e a ta ≫ WeightPf.act (U.gt e) := by
  haveI := ιG.hom a
  have hμ : μ[thickObj R I e G] ≫ actA ιG e a =
      (actA ιG e a ⊗ₘ actA ιG e a) ≫ μ[thickObj R I e G] := IsMonHom.mul_hom _
  simp only [WeightPf.act, mA, Category.assoc, hμ, lift_map_assoc, comp_lift_assoc,
    lift_fst_assoc, lift_snd, hia]

set_option maxHeartbeats 800000 in

theorem mA_chiP (ta : WeightPf.Te D.toPre I e ⟶ WeightPf.Te D.toPre I e)
    (hta : TorusEndOf D.toPre.X (fun χ => star a • χ) ta) (χ : D.toPre.X)
    (W2 W' : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.Opens)
    (hm : W' ≤ (mA ιG e a ta).left ⁻¹ᵁ W2) :
    ((mA ιG e a ta).left.appLE W2 W' hm).hom
        (((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom
          (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) χ)) =
      ((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom
        (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) (star a • χ)) := by
  have hF : (mA ιG e a ta).left ≫ (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left =
      (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ ta.left := by
    rw [← Over.comp_left, mA_fst, Over.comp_left]
  have hTop : (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appTop ≫
      (mA ιG e a ta).left.appTop =
      ta.left.appTop ≫ (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appTop := by
    rw [← Scheme.Hom.comp_appTop, hF, Scheme.Hom.comp_appTop]
  have hval := congrArg Units.val (hta χ)
  simp only [Semi.res, Semi.pullU, Units.coe_map, MonoidHom.coe_coe] at hval
  simp only [Semi.TorusInj.chiP, ← hval]
  simp only [Scheme.Hom.appLE]
  have hTop' : (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appTop ≫ (mA ιG e a ta).left.app ⊤ = ta.left.app ⊤ ≫ (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.app ⊤ := hTop

  have key : (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appTop ≫
      (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE (le_top : W2 ≤ ⊤)).op ≫
      (mA ιG e a ta).left.app W2 ≫
      (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE hm).op =
      ta.left.app ⊤ ≫
      (WeightPf.Te D.toPre I e).left.presheaf.map
        (homOfLE (fun _ _ => trivial : (⊤ : (WeightPf.Te D.toPre I e).left.Opens) ≤ ta.left ⁻¹ᵁ ⊤)).op ≫
      (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.app ⊤ ≫
      (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE (fun _ _ => trivial : W' ≤ (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ ⊤)).op := by
    rw [Scheme.Hom.naturality_assoc, Scheme.Hom.naturality_assoc, reassoc_of% hTop']
    simp only [← Functor.map_comp]
    rfl
  have hk := congrArg (fun φ => φ.hom (charUnit _ D.toPre.X χ).val) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hk ⊢
  exact hk

end Rhs

include hO in

theorem rhs_act
    (hi : ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X,
      TorusEndOf D.toPre.X (fun χ => star a • χ) t ∧
        (U.gt e).i ≫ (Over.pullback (thick R I e)).map (ιG.act a) = t ≫ (U.gt e).i)
    (jB : Fin 4 → D.toPre.P.L.ι) (cB : LB.Coh D.toPre.P.L (φB U ιG e a χ) jB)
    (W' : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.Opens)
    (hs : W' ≤ (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ
      LB.wchart D.toPre.P.L (φB U ιG e a χ) jB)
    (ha : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) :
    ((WeightPf.act (U.gt e)).left.appLE _ W' ha).hom ((rhs U ιG e a χ).s jB).val =
      ((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom
        (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) (star a • χ)) *
      ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE _ W' hs).hom
        ((rhs U ιG e a χ).s jB).val := by
  obtain ⟨ta, hta, hia⟩ := hi
  set hL := (actA ιG e a).left with hhL
  set actL := (WeightPf.act (U.gt e)).left with hactL
  set sndL := (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left with hsndL
  set mL := (mA ιG e a ta).left with hmL
  set Wt := LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG χ) jB with hWt
  have hWb : LB.wchart D.toPre.P.L (φB U ιG e a χ) jB ≤ hL ⁻¹ᵁ Wt :=
    Semi.LBVal.wchart_pull_le D.toPre.P.L (D.toPre.Oφ (U.gt e).pG χ) hL jB
  have eqA : actL ≫ hL = mL ≫ actL := by
    rw [hactL, hhL, hmL, ← Over.comp_left, act_actA U ιG e a ta hia, Over.comp_left]
  have eqS : mL ≫ sndL = sndL ≫ hL := by
    rw [hsndL, hhL, hmL, ← Over.comp_left, mA_snd, Over.comp_left]
  let W2 : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.Opens := sndL ⁻¹ᵁ Wt ⊓ actL ⁻¹ᵁ Wt
  have hs2 : W2 ≤ sndL ⁻¹ᵁ Wt := inf_le_left
  have ha2 : W2 ≤ actL ⁻¹ᵁ Wt := inf_le_right
  have hm : W' ≤ mL ⁻¹ᵁ W2 := by
    intro z hz
    refine ⟨?_, ?_⟩
    · show sndL (mL z) ∈ Wt
      rw [← Scheme.Hom.comp_apply, eqS, Scheme.Hom.comp_apply]
      exact hWb (hs hz)
    · show actL (mL z) ∈ Wt
      rw [← Scheme.Hom.comp_apply, ← eqA, Scheme.Hom.comp_apply]
      exact hWb (ha hz)
  have hjt : LB.Coh D.toPre.P.L (D.toPre.Oφ (U.gt e).pG χ) jB :=
    fun k1 k2 h => cB k1 k2 (congrArg (hL ≫ ·) h)
  have T := WeightPf.t_act (U.gt e) χ jB hjt W2 hs2 ha2
  have M1 : hL.appLE Wt _ hWb ≫ actL.appLE _ W' ha =
      actL.appLE Wt W2 ha2 ≫ mL.appLE W2 W' hm := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, Semi.TorusInj.appLE_of_eq eqA]
  have M3 : sndL.appLE Wt W2 hs2 ≫ mL.appLE W2 W' hm =
      hL.appLE Wt _ hWb ≫ sndL.appLE _ W' hs := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, Semi.TorusInj.appLE_of_eq eqS]
  have C := mA_chiP ιG e a ta hta χ W2 W' hm
  set x := (((U.gt e).t χ).s jB).val with hx
  calc ((WeightPf.act (U.gt e)).left.appLE _ W' ha).hom ((rhs U ιG e a χ).s jB).val
      = (hL.appLE Wt _ hWb ≫ actL.appLE _ W' ha).hom x := rfl
    _ = (mL.appLE W2 W' hm).hom ((actL.appLE Wt W2 ha2).hom x) :=
        congrArg (fun φ => φ.hom x) M1
    _ = (mL.appLE W2 W' hm).hom
          (((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom
            (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) χ)) *
        (mL.appLE W2 W' hm).hom ((sndL.appLE Wt W2 hs2).hom x) := by
        rw [T, map_mul]
    _ = _ := by
        rw [C]
        congr 1
        exact congrArg (fun φ => φ.hom x) M3

end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf

open Semi

lemma appLE_res {A B : Scheme.{0}} (f : A ⟶ B) {U V : B.Opens} (hVU : V ≤ U) {W : A.Opens}
    (e : W ≤ f ⁻¹ᵁ V) (x : Γ(B, U)) :
    (f.appLE V W e).hom ((B.presheaf.map (homOfLE hVU).op).hom x) =
      (f.appLE U W (e.trans (f.preimage_mono hVU))).hom x :=
  congrArg (fun φ => φ.hom x) (Scheme.Hom.map_appLE f e (homOfLE hVU).op)

lemma res_appTop {A B : Scheme.{0}} (f : A ⟶ B) {W : A.Opens} (hW : W ≤ f ⁻¹ᵁ ⊤) (x : Γ(B, ⊤)) :
    (A.presheaf.map (homOfLE hW).op).hom (f.appTop.hom x) = (f.appLE ⊤ W hW).hom x := by
  have : f.app ⊤ ≫ A.presheaf.map (homOfLE hW).op = f.appLE ⊤ W hW := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  exact congrArg (fun φ => φ.hom x) this

theorem comp_base_eq' {A B C : Scheme.{0}} {a b : A ⟶ B} {ψ : B ⟶ C} (h : a ≫ ψ = b ≫ ψ) (z : A) :
    ψ (a z) = ψ (b z) := by
  rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))

lemma act_mem_of {K : Type} [Fintype K] (φ : K → ((thickObj R I e G).left ⟶ D.toPre.P.A.left))
    (hφ : ∀ k, (WeightPf.act (U.gt e)).left ≫ φ k =
      (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ φ k) (j : K → D.toPre.P.L.ι)
    (W' : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.Opens)
    (hs : W' ≤ (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ
      LB.wchart D.toPre.P.L φ j) :
    W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ LB.wchart D.toPre.P.L φ j := by
  intro z hz
  refine Set.mem_iInter.2 fun k => ?_
  have h1 := Set.mem_iInter.1 (hs hz) k
  simp only [Set.mem_preimage] at h1 ⊢
  rw [comp_base_eq' (hφ k) z]
  exact h1

include hO in

theorem rho_inv_loc
    (hi : ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X,
      TorusEndOf D.toPre.X (fun χ => star a • χ) t ∧
        (U.gt e).i ≫ (Over.pullback (thick R I e)).map (ιG.act a) = t ≫ (U.gt e).i)
    (ρ : Γ((thickObj R I e G).left, ⊤)ˣ) (hρ : PairProp U ιD ιG e a χ u ρ)
    (jA : Fin 4 ⊕ Fin 6 → D.toPre.P.L.ι) (jB : Fin 4 → D.toPre.P.L.ι)
    (cA : LB.Coh D.toPre.P.L (φA U ιD e a χ) jA) (cB : LB.Coh D.toPre.P.L (φB U ιG e a χ) jB)
    (cAB : ∀ k k', φB U ιG e a χ k = φA U ιD e a χ k' → jB k = jA k')
    (W' : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.Opens)
    (hsV : W' ≤ (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ
      (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB ⊓ LB.wchart D.toPre.P.L (φA U ιD e a χ) jA))
    (ht1 : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ ⊤)
    (ht2 : W' ≤ (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ ⊤) :
    ((WeightPf.act (U.gt e)).left.appLE ⊤ W' ht1).hom ρ.val =
      ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE ⊤ W' ht2).hom ρ.val := by
  have hsA : W' ≤ (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) := hsV.trans ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.preimage_mono inf_le_right)
  have hsB : W' ≤ (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) := hsV.trans ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.preimage_mono inf_le_left)
  have haA : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) := act_mem_of U e _ (hA_act U ιD e a χ) jA W' hsA
  have haB : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) := act_mem_of U e _ (hB_act U ιD ιG e a χ hO) jB W' hsB
  have haV : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ ((LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) ⊓ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA)) := fun z hz => ⟨haB hz, haA hz⟩
  have hP : (res (inf_le_right : (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) ⊓ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) ≤ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA)) ((lhs U ιD e a χ u).s jA)).val =
      (res (le_top : (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) ⊓ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) ≤ ⊤) ρ).val * (res (inf_le_left : (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) ⊓ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) ≤ (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB)) ((rhs U ιG e a χ).s jB)).val := by
    rw [← Units.val_mul]
    exact congrArg Units.val (hρ jA jB cA cB cAB)

  have hA1 := congrArg ((WeightPf.act (U.gt e)).left.appLE _ W' haV).hom hP
  rw [map_mul] at hA1
  have e1 : ((WeightPf.act (U.gt e)).left.appLE _ W' haV).hom (res (inf_le_right : (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) ⊓ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) ≤ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA)) ((lhs U ιD e a χ u).s jA)).val =
      ((WeightPf.act (U.gt e)).left.appLE (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) W' haA).hom ((lhs U ιD e a χ u).s jA).val :=
    appLE_res (WeightPf.act (U.gt e)).left inf_le_right haV _
  have e2 : ((WeightPf.act (U.gt e)).left.appLE _ W' haV).hom (res (le_top : (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) ⊓ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) ≤ ⊤) ρ).val =
      ((WeightPf.act (U.gt e)).left.appLE ⊤ W' ht1).hom ρ.val :=
    appLE_res (WeightPf.act (U.gt e)).left le_top haV _
  have e3 : ((WeightPf.act (U.gt e)).left.appLE _ W' haV).hom (res (inf_le_left : (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) ⊓ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) ≤ (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB)) ((rhs U ιG e a χ).s jB)).val =
      ((WeightPf.act (U.gt e)).left.appLE (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) W' haB).hom ((rhs U ιG e a χ).s jB).val :=
    appLE_res (WeightPf.act (U.gt e)).left inf_le_left haV _
  rw [e1, e2, e3, lhs_act U ιD e a χ u jA cA W' hsA haA,
    rhs_act U ιD ιG e a χ hO hi jB cB W' hsB haB] at hA1

  have hS1 := congrArg ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE _ W' hsV).hom hP
  rw [map_mul] at hS1
  have f1 : ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE _ W' hsV).hom (res (inf_le_right : (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) ⊓ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) ≤ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA)) ((lhs U ιD e a χ u).s jA)).val =
      ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) W' hsA).hom ((lhs U ιD e a χ u).s jA).val :=
    appLE_res (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left inf_le_right hsV _
  have f2 : ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE _ W' hsV).hom (res (le_top : (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) ⊓ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) ≤ ⊤) ρ).val =
      ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE ⊤ W' ht2).hom ρ.val :=
    appLE_res (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left le_top hsV _
  have f3 : ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE _ W' hsV).hom (res (inf_le_left : (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) ⊓ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) ≤ (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB)) ((rhs U ιG e a χ).s jB)).val =
      ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) W' hsB).hom ((rhs U ιG e a χ).s jB).val :=
    appLE_res (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left inf_le_left hsV _
  rw [f1, f2, f3] at hS1

  have hchi : IsUnit (((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op).hom
      (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) (star a • χ))) := by
    unfold Semi.TorusInj.chiP
    exact ((charUnit _ _ _).isUnit.map _).map _
  have hR : IsUnit (((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) W' hsB).hom ((rhs U ιG e a χ).s jB).val) :=
    ((rhs U ιG e a χ).s jB).isUnit.map _
  rw [hS1] at hA1
  have key : ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE ⊤ W' ht2).hom ρ.val * (((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op).hom
      (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) (star a • χ)) * ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) W' hsB).hom ((rhs U ιG e a χ).s jB).val) =
      ((WeightPf.act (U.gt e)).left.appLE ⊤ W' ht1).hom ρ.val * (((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op).hom
      (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) (star a • χ)) * ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) W' hsB).hom ((rhs U ιG e a χ).s jB).val) := by
    rw [← hA1]; ring
  exact ((hchi.mul hR).mul_right_cancel key).symm

include hO in

theorem rho_inv
    (hi : ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X,
      TorusEndOf D.toPre.X (fun χ => star a • χ) t ∧
        (U.gt e).i ≫ (Over.pullback (thick R I e)).map (ιG.act a) = t ≫ (U.gt e).i)
    (ρ : Γ((thickObj R I e G).left, ⊤)ˣ) (hρ : PairProp U ιD ιG e a χ u ρ) :
    (WeightPf.act (U.gt e)).left.appTop.hom ρ.val =
      (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appTop.hom ρ.val := by
  classical
  choose idx hidx using fun w : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left =>
    idx_exists D.toPre.P.L D.toPre.P.isLB
      ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left w)
  let W : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left →
      (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.Opens := fun w =>
    (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ
      (LB.wchart D.toPre.P.L (φB U ιG e a χ) (fun k => idx w (φB U ιG e a χ k)) ⊓
        LB.wchart D.toPre.P.L (φA U ιD e a χ) (fun k => idx w (φA U ιD e a χ k)))
  have hc : ⨆ w, W w = ⊤ := by
    refine eq_top_iff.2 fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, ?_⟩
    exact ⟨Set.mem_iInter.2 fun k => hidx z _, Set.mem_iInter.2 fun k => hidx z _⟩
  refine eq_local W hc _ _ (fun w => ?_)
  have r1 := res_appTop (WeightPf.act (U.gt e)).left (W := W w) (fun _ _ => trivial) ρ.val
  have r2 := res_appTop (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left (W := W w)
    (fun _ _ => trivial) ρ.val
  exact r1.trans ((rho_inv_loc U ιD ιG e a χ hO u hi ρ hρ _ _ (fun k1 k2 h => congrArg (idx w) h)
    (fun k1 k2 h => congrArg (idx w) h) (fun k k' h => congrArg (idx w) h) (W w) le_rfl
    (fun _ _ => trivial) (fun _ _ => trivial)).trans r2.symm)

end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf

open Semi

namespace ZeroLinearity

section SlopeTestRemainingChoices

variable {X Y Z W : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]

lemma map_rfl' {V : Y.Opens} (x : Γ(Y, V)) :
    (Y.presheaf.map (homOfLE (le_rfl : V ≤ V)).op).hom x = x := by
  simp

lemma pullGen_s_val {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (j : K → L.ι) :
    ((LB.pullGen L φ ε c h).s j).val =
      (h.appLE (LB.wchart L φ j) (LB.wchart L (fun k => h ≫ φ k) j)
        (LBVal.wchart_pull_le L φ h j)).hom (c.s j).val := by
  rfl

lemma res_eq_of_res_eq' {U V W : Y.Opens} (a : Γ(Y, U)ˣ) (b : Γ(Y, V)ˣ) (h1 : W ≤ U) (h2 : W ≤ V)
    (h : res (inf_le_left : U ⊓ V ≤ U) a = res (inf_le_right : U ⊓ V ≤ V) b) :
    res h1 a = res h2 b := by
  have hW : W ≤ U ⊓ V := le_inf h1 h2
  have key : ∀ {P : Y.Opens} (hP : U ⊓ V ≤ P) (hQ : W ≤ P) (c : Γ(Y, P)ˣ),
      res hQ c = res hW (res hP c) := by
    intro P hP hQ c
    have e : Y.presheaf.map (homOfLE hQ).op =
        Y.presheaf.map (homOfLE hP).op ≫ Y.presheaf.map (homOfLE hW).op := by
      rw [← Functor.map_comp]
      rfl
    ext
    exact congrArg (fun φ => φ.hom c.val) e
  rw [key inf_le_left h1 a, key inf_le_right h2 b, h]

lemma corr_symm' {K' : Type} [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)}
    {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : LB.Gen.Corr L φ ε φ' ε' t t') : LB.Gen.Corr L φ' ε' φ ε t' t := by
  intro j j' hj hj' hjj
  exact (res_eq_of_res_eq' _ _ _ _
    (h j' j hj' hj fun k k' hk => (hjj k' k hk.symm).symm)).symm

private lemma res_one_lemma {U V : Y.Opens} (h : V ≤ U) : res h (1 : Γ(Y, U)ˣ) = 1 :=
  Units.ext (map_one _)

lemma corr_one_alt {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    (h : LB.Gen.Corr L φ ε PEmpty.elim PEmpty.elim t (LB.oneGen L)) (j : K → L.ι)
    (hj : LB.Coh L φ j) : t.s j = 1 := by
  have hC : LB.Coh L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun k => k.elim
  have h2 : (L.LinComb φ ε).U j ≤
      (L.LinComb (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim).U PEmpty.elim := by
    delta LB.LinComb
    simp [LB.wchart]
  have key := res_eq_of_res_eq' _ _ le_rfl h2 (h j PEmpty.elim hj hC fun _ k' _ => k'.elim)
  change res _ (t.s j) = res _ 1 at key
  rw [res_one_lemma] at key
  have e : res (le_refl _) (t.s j) = t.s j := Units.ext (map_rfl' _)
  rw [← e]
  exact key

private lemma appLE_res_lemma_3 (f : W ⟶ Y) {C : Y.Opens} {B T : W.Opens} (e : B ≤ f ⁻¹ᵁ C)
    (hT : T ≤ B) (x : Γ(Y, C)) :
    (W.presheaf.map (homOfLE hT).op).hom ((f.appLE C B e).hom x) = (f.appLE C T (hT.trans e)).hom x := by
  change (f.appLE C B e ≫ W.presheaf.map (homOfLE hT).op).hom x = _
  rw [Scheme.Hom.appLE_map]

private lemma appLE_appLE_lemma_2 {B T : W.Opens} {C : Y.Opens} {D : Z.Opens} (g1 : Z ⟶ Y)
    (g2 : W ⟶ Z) (e1 : D ≤ g1 ⁻¹ᵁ C) (e2 : B ≤ g2 ⁻¹ᵁ D) (hT : T ≤ B) (x : Γ(Y, C)) :
    (W.presheaf.map (homOfLE hT).op).hom ((g2.appLE D B e2).hom ((g1.appLE C D e1).hom x)) =
      ((g2 ≫ g1).appLE C T (hT.trans (e2.trans (g2.preimage_mono e1)))).hom x := by
  change (g1.app C ≫ Z.presheaf.map (homOfLE e1).op ≫ g2.appLE D B e2 ≫
    W.presheaf.map (homOfLE hT).op).hom x = _
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  first
  | rfl
  | simp only [Scheme.Hom.appLE, Scheme.comp_app, Category.assoc]
  | simp only [Scheme.Hom.appLE, Scheme.Hom.comp_app, Category.assoc]

lemma corr_pull_comp {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : LB.Gen (LB.LinComb L φ ε)) (g1 : Z ⟶ Y)
    (g2 : W ⟶ Z) (g : W ⟶ Y) (hg : g2 ≫ g1 = g) :
    LB.Gen.Corr L _ ε _ ε (LB.pullGen L _ ε (LB.pullGen L φ ε c g1) g2) (LB.pullGen L φ ε c g) := by
  subst hg
  intro j j' _ _ hjj
  obtain rfl : j = j' := funext fun k => hjj k k (by simp)
  ext
  change (W.presheaf.map (homOfLE _).op).hom
      ((LB.pullGen L _ ε (LB.pullGen L φ ε c g1) g2).s j).val =
    (W.presheaf.map (homOfLE _).op).hom ((LB.pullGen L φ ε c (g2 ≫ g1)).s j).val
  rw [pullGen_s_val, pullGen_s_val, pullGen_s_val]
  exact (appLE_appLE_lemma_2 g1 g2 _ _ _ _).trans (appLE_res_lemma_3 (g2 ≫ g1) _ _ _).symm


lemma appLE_one {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (hC : LB.Gen.Corr L _ ε PEmpty.elim PEmpty.elim (LB.pullGen L φ ε t h) (LB.oneGen L))
    (j : K → L.ι) (hj : LB.Coh L (fun k => h ≫ φ k) j) (V : Z.Opens)
    (hV : V ≤ LB.wchart L (fun k => h ≫ φ k) j) :
    (h.appLE (LB.wchart L φ j) V (hV.trans (LBVal.wchart_pull_le L φ h j))).hom (t.s j).val = 1 := by
  have e2 := congrArg Units.val (corr_one_alt L hC j hj)
  rw [pullGen_s_val, Units.val_one] at e2
  exact (appLE_res_lemma_3 h (LBVal.wchart_pull_le L φ h j) hV _).symm.trans
    ((congrArg (fun y => (Z.presheaf.map (homOfLE hV).op).hom y) e2).trans (map_one _))

lemma appLE_res (f : Z ⟶ Y) {U V : Y.Opens} (hUV : V ≤ U) {W' : Z.Opens} (hW : W' ≤ f ⁻¹ᵁ V)
    (x : Γ(Y, U)ˣ) :
    (f.appLE V W' hW).hom (res hUV x).val =
      (f.appLE U W' (hW.trans (f.preimage_mono hUV))).hom x.val := by
  change (Y.presheaf.map (homOfLE hUV).op ≫ f.appLE V W' hW).hom x.val = _
  rw [Scheme.Hom.map_appLE]

lemma corr_one_pull {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    (hC : LB.Gen.Corr L φ ε PEmpty.elim PEmpty.elim t (LB.oneGen L)) (h : Z ⟶ Y) :
    LB.Gen.Corr L _ ε PEmpty.elim PEmpty.elim (LB.pullGen L φ ε t h) (LB.oneGen L) := by
  intro j j' hj _ _
  have hj0 : LB.Coh L φ j := fun k₁ k₂ hk => hj k₁ k₂ (by simp only [hk])
  have e := corr_one_alt L hC j hj0
  delta LB.pullGen LB.oneGen
  simp only [e, map_one]
  exact (res_one_lemma _).trans (res_one_lemma _).symm

end SlopeTestRemainingChoices

section Z

variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (f g : B ⟶ B) [IsMonHom g]

abbrev zz : B ⟶ B ⊗ B := lift (𝟙 B) (toUnit B ≫ η[B])

lemma zz_0 : zz B ≫ padd B (fst B B ≫ f) (snd B B) = f := by
  rw [zz, padd, ← Category.assoc, comp_lift]
  simpa using MonObj.lift_comp_one_right f

lemma zz_1 : zz B ≫ fst B B ≫ f = f := by
  simp [zz]

lemma zz_2 : zz B ≫ snd B B = toUnit B ≫ η[B] := by
  simp [zz]

lemma zz_5 : zz B ≫ snd B B ≫ g = toUnit B ≫ η[B] := by
  simp [zz]

lemma zz_3 : zz B ≫ padd B (fst B B) (snd B B ≫ g) = 𝟙 B := by
  rw [zz, padd, ← Category.assoc, comp_lift]
  simpa using MonObj.lift_comp_one_right (𝟙 B)

lemma zz_4 : zz B ≫ fst B B = 𝟙 B := by
  simp [zz]

lemma zz_sameSum : LB.SameSum (Y := B.left) (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun k => (zz B).left ≫ rosatiφ B f g k) rosatiε := by
  intro ψ
  have h0 : (zz B).left ≫ (padd B (fst B B ≫ f) (snd B B)).left = f.left := by
    rw [← Over.comp_left, zz_0]
  have h1 : (zz B).left ≫ (fst B B ≫ f).left = f.left := by
    rw [← Over.comp_left, zz_1]
  have h2 : (zz B).left ≫ (snd B B).left = (toUnit B ≫ η[B]).left := by
    rw [← Over.comp_left, zz_2]
  have h3 : (zz B).left ≫ (padd B (fst B B) (snd B B ≫ g)).left = Over.Hom.left (𝟙 B) := by
    rw [← Over.comp_left, zz_3]
  have h4 : (zz B).left ≫ (fst B B).left = Over.Hom.left (𝟙 B) := by
    rw [← Over.comp_left, zz_4]
  have h5 : (zz B).left ≫ (snd B B ≫ g).left = (toUnit B ≫ η[B]).left := by
    rw [← Over.comp_left, zz_5]
  have e0 : (zz B).left ≫ rosatiφ B f g 0 = f.left := h0
  have e1 : (zz B).left ≫ rosatiφ B f g 1 = f.left := h1
  have e2 : (zz B).left ≫ rosatiφ B f g 2 = (toUnit B ≫ η[B]).left := h2
  have e3 : (zz B).left ≫ rosatiφ B f g 3 = Over.Hom.left (𝟙 B) := h3
  have e4 : (zz B).left ≫ rosatiφ B f g 4 = Over.Hom.left (𝟙 B) := h4
  have e5 : (zz B).left ≫ rosatiφ B f g 5 = (toUnit B ≫ η[B]).left := h5
  rw [Fin.sum_univ_six]
  beta_reduce
  erw [e0, e1, e2, e3, e4, e5]
  by_cases hf : Over.Hom.left f = ψ <;> by_cases hu : (toUnit B ≫ η[B]).left = ψ <;>
    by_cases hi : Over.Hom.left (𝟙 B) = ψ <;>
    first
    | (simp only [hf, hu, hi, eq_self_iff_true, ↓reduceIte]; simp [rosatiε]; done)
    | simp [hf, hu, hi, rosatiε]

end Z

section Unit

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιG : RingAct G O) (e : ℕ) (a : O)

lemma eSec_h : eSec (thickObj R I e G) ≫ ((Over.pullback (thick R I e)).map (ιG.act a)).left =
    eSec (thickObj R I e G) := by
  haveI := ιG.hom a
  delta eSec
  rw [← Over.comp_left, IsMonHom.one_hom]

lemma eSec_pG : (Over.map (thick R I e)).map η[thickObj R I e G] ≫ (U.gt e).pG =
    toUnit _ ≫ η[D.toPre.P.A] := by
  have := (U.gt e).q_hom
  ext1
  have h1 : (η[thickObj R I e G] ≫ (U.gt e).q) = η[thickObj R I e D.toPre.P.A] := IsMonHom.one_hom _
  have h2 := congrArg Over.Hom.left h1
  simp only [GtCoord.pG, DegPre.prBe, Over.comp_left, Over.map_map_left, Over.homMk_left] at h2 ⊢
  rw [← Category.assoc, h2, Functor.obj.η_def]
  simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_fst]
  have h3 := Over.w (toUnit ((Over.map (thick R I e)).obj (𝟙_ _)))
  have h4 := Over.w (Functor.LaxMonoidal.ε (Over.pullback (thick R I e)))
  have h5 := pullback.condition (f := (𝟙_ (Over (Spec (CommRingCat.of R)))).hom) (g := thick R I e)
  simp only [Over.map_obj_hom, Functor.id_obj, Over.pullback_obj_hom] at h3 h4 h5
  have h5' : pullback.fst (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (thick R I e) =
      pullback.snd (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (thick R I e) ≫ thick R I e :=
    (Category.comp_id _).symm.trans h5
  have h3' : Over.Hom.left (toUnit ((Over.map (thick R I e)).obj
      (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))))) = thick R I e :=
    (Category.comp_id _).symm.trans (h3.trans (Category.id_comp _))
  have key : Over.Hom.left (Functor.LaxMonoidal.ε (Over.pullback (thick R I e))) ≫
      pullback.fst (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (thick R I e) =
      Over.Hom.left (toUnit ((Over.map (thick R I e)).obj
        (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))))) := by
    rw [h5', ← Category.assoc, h4, h3']
    exact Category.id_comp _
  rw [← Category.assoc, key]

lemma eSec_lift (χ : D.toPre.X) :
    eSec (thickObj R I e G) ≫ (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left =
      ((Over.map (thick R I e)).map η[thickObj R I e G] ≫ toUnit _ ≫ D.toPre.c χ).left ≫
        (zz D.toPre.P.A).left := by
  show ((Over.map (thick R I e)).map η[thickObj R I e G]).left ≫ _ = _
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  rw [comp_lift, eSec_pG, comp_lift, Category.comp_id, ← Category.assoc _ (toUnit D.toPre.P.A),
    toUnit_unique (_ ≫ toUnit D.toPre.P.A) (toUnit _)]

end Unit

end ZeroLinearity

open ZeroLinearity

section Main

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))

theorem u_zero (hGF : GlobalFnsSt) (hu : u.IsGen)
    (hu0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (zero2 D.toPre.P.A))
      (LB.oneGen D.toPre.P.L)) :
    LB.Gen.Corr D.toPre.P.L _ _ _ _
      (LB.pullGen D.toPre.P.L _ _ u (lift (𝟙 D.toPre.P.A) (toUnit D.toPre.P.A ≫ η[D.toPre.P.A])).left)
      (LB.oneGen D.toPre.P.L) := by
  classical
  have hL := D.toPre.P.isLB
  have hg : IsMonHom (ιD.onB.act a) := ιD.onB.hom a
  let ψ : Fin 6 → (D.toPre.P.A.left ⟶ D.toPre.P.A.left) := fun k =>
    (zz D.toPre.P.A).left ≫ rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k
  have hs := zz_sameSum D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)
  let canon := Canon.canonGen D.toPre.P.L (Y := D.toPre.P.A.left) (K := PEmpty) PEmpty.elim
    PEmpty.elim ψ rosatiε (fun k => k.elim) (LB.oneGen D.toPre.P.L)
  have hcan : canon.IsGen :=
    Canon.canonGen_isGen hL _ _ _ _ hs _ _ (LB.isGen_oneGen D.toPre.P.L)
  have hcc := Canon.canonGen_corr hL (Y := D.toPre.P.A.left) (K := PEmpty) PEmpty.elim PEmpty.elim
    ψ rosatiε (fun k => k.elim) (LB.oneGen D.toPre.P.L)
  let v := LB.pullGen D.toPre.P.L _ _ u (zz D.toPre.P.A).left
  have hv : v.IsGen := LB.isGen_pullGen (L := D.toPre.P.L) _ _ _ hu _
  obtain ⟨κ, hκ⟩ := ratio_glue _ (linComb_cover _ hL ψ rosatiε) v canon hv hcan

  let ηA := (η[D.toPre.P.A]).left
  have hz : ηA ≫ (zz D.toPre.P.A).left = zero2 D.toPre.P.A := by
    rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc,
      toUnit_unique (η[D.toPre.P.A] ≫ toUnit D.toPre.P.A) (𝟙 _), Category.id_comp]
  have hψz : ∀ k, ηA ≫ ψ k = zero2 D.toPre.P.A ≫
      rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k := fun k => by
    rw [← hz, Category.assoc]
  choose idx hidx using fun s : (𝟙_ (Over (Spec (CommRingCat.of R)))).left =>
    idx_exists D.toPre.P.L hL s
  let js : (𝟙_ (Over (Spec (CommRingCat.of R)))).left → Fin 6 → D.toPre.P.L.ι :=
    fun s k => idx s (ηA ≫ ψ k)
  let Us : (𝟙_ (Over (Spec (CommRingCat.of R)))).left → (𝟙_ (Over (Spec (CommRingCat.of R)))).left.Opens :=
    fun s => LB.wchart D.toPre.P.L (fun k => ηA ≫ ψ k) (js s)
  have hUs : ∀ s, s ∈ Us s := fun s => Set.mem_iInter.2 fun k => hidx s _
  have hcov : ⨆ s, Us s = ⊤ :=
    top_unique fun s _ => TopologicalSpace.Opens.mem_iSup.2 ⟨s, hUs s⟩
  have key : ∀ s, res (fun _ _ => trivial : Us s ≤ ηA ⁻¹ᵁ ⊤) (pullU ηA ⊤ κ) = 1 := by
    intro s

    have coh1 : LB.Coh D.toPre.P.L (fun k => ηA ≫ ψ k) (js s) := fun k1 k2 h => congrArg (idx s) h
    have coh2 : LB.Coh D.toPre.P.L (fun k => zero2 D.toPre.P.A ≫
        rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k) (js s) :=
      fun k1 k2 h => congrArg (idx s) (((hψz k1).trans h).trans (hψz k2).symm)
    have cross : ∀ k k', ηA ≫ ψ k = zero2 D.toPre.P.A ≫
        rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k' → js s k = js s k' :=
      fun k k' h => congrArg (idx s) (h.trans (hψz k').symm)
    have e := corr_pull_comp D.toPre.P.L u (zz D.toPre.P.A).left ηA (zero2 D.toPre.P.A) hz
      (js s) (js s) coh1 coh2 cross
    have one := corr_one_alt D.toPre.P.L hu0 (js s) coh2
    have h2 : Us s ≤ LB.wchart D.toPre.P.L (fun k => zero2 D.toPre.P.A ≫
        rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k) (js s) :=
      fun x hx => Set.mem_iInter.2 fun k => by
        have := Set.mem_iInter.1 hx k
        beta_reduce at this ⊢
        rwa [hψz k] at this
    have e' := res_eq_of_res_eq' _ _ (le_rfl : Us s ≤ Us s) h2 e
    have e'' := (Canon.res_refl _ _).symm.trans (e'.trans ((congrArg (res h2) one).trans (map_one _)))

    have cohψ : LB.Coh D.toPre.P.L ψ (js s) := fun k1 k2 h => congrArg (idx s) (congrArg (ηA ≫ ·) h)
    have cone := corr_one_alt D.toPre.P.L (corr_symm' D.toPre.P.L hcc) (js s) cohψ

    have hh : Us s ≤ ηA ⁻¹ᵁ LB.wchart D.toPre.P.L ψ (js s) := LBVal.wchart_pull_le _ ψ ηA (js s)
    have e5 : v.s (js s) = res le_top κ :=
      (hκ (js s)).trans ((congrArg (res le_top κ * ·) cone).trans (_root_.mul_one _))
    have e4 : res hh (pullU ηA _ (v.s (js s))) = res (fun _ _ => trivial : Us s ≤ ηA ⁻¹ᵁ ⊤)
        (pullU ηA ⊤ κ) :=
      (congrArg (fun x => res hh (pullU ηA _ x)) e5).trans
        (Canon.res_pullU_eq ηA le_top (fun _ _ => trivial) hh κ).symm
    exact e4.symm.trans e''
  have hκe : ηA.appTop.hom κ.val = 1 := by
    refine eq_local Us hcov _ _ fun s => ?_
    exact (congrArg Units.val (key s)).trans (map_one _).symm

  obtain ⟨c, hc⟩ := (hGF _ D.toPre.P.A D.toPre.P.isAb).2 κ.val
  have hηA : ηA ≫ D.toPre.P.A.hom = 𝟙 _ := Over.w η[D.toPre.P.A]
  have hc1 : c = 1 := by
    have m : (ηA ≫ D.toPre.P.A.hom).appTop.hom c = c := by rw [hηA]; rfl
    rw [Scheme.Hom.comp_appTop] at m
    exact m.symm.trans ((congrArg ηA.appTop.hom hc).trans hκe)
  have hκ1 : κ = 1 := Units.ext (hc.symm.trans (by rw [hc1, map_one]; rfl))

  intro j j' hj hj' hm
  have h1 : v.s j = canon.s j := (hκ j).trans (by rw [hκ1, map_one, _root_.one_mul])
  exact (congrArg (res _) h1).trans ((corr_symm' D.toPre.P.L hcc) j j' hj hj' hm)

include hO in

theorem rho_e (hGF : GlobalFnsSt) (hu : u.IsGen)
    (hu0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (zero2 D.toPre.P.A))
      (LB.oneGen D.toPre.P.L))
    (ρ : Γ((thickObj R I e G).left, ⊤)ˣ) (hρ : PairProp U ιD ιG e a χ u ρ) :
    (eSec (thickObj R I e G)).appTop.hom ρ.val = 1 := by
  classical
  have hL := D.toPre.P.isLB
  have hz0 := u_zero ιD a u hGF hu hu0
  have F1 := eSec_h (I := I) ιG e a
  have F2 := eSec_lift U e χ
  let ε := eSec (thickObj R I e G)
  let cS := ((Over.map (thick R I e)).map η[thickObj R I e G] ≫ toUnit _ ≫ D.toPre.c χ).left
  let S' := (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left
  choose idx hidx using fun s : S' => idx_exists D.toPre.P.L hL s
  let jA : S' → Fin 4 ⊕ Fin 6 → D.toPre.P.L.ι := fun s k => idx s (ε ≫ φA U ιD e a χ k)
  let jB : S' → Fin 4 → D.toPre.P.L.ι := fun s k => idx s (ε ≫ φB U ιG e a χ k)
  let Us : S' → S'.Opens := fun s =>
    LB.wchart D.toPre.P.L (fun k => ε ≫ φB U ιG e a χ k) (jB s) ⊓
      LB.wchart D.toPre.P.L (fun k => ε ≫ φA U ιD e a χ k) (jA s)
  have hUs : ∀ s, s ∈ Us s := fun s =>
    ⟨Set.mem_iInter.2 fun k => hidx s _, Set.mem_iInter.2 fun k => hidx s _⟩
  have hcov : ⨆ s, Us s = ⊤ :=
    top_unique fun s _ => TopologicalSpace.Opens.mem_iSup.2 ⟨s, hUs s⟩
  have key : ∀ s, (ε.appLE ⊤ (Us s) (fun _ _ => trivial)).hom ρ.val = 1 := by
    intro s
    have cA : LB.Coh D.toPre.P.L (φA U ιD e a χ) (jA s) :=
      fun k1 k2 h => congrArg (idx s) (congrArg (ε ≫ ·) h)
    have cB : LB.Coh D.toPre.P.L (φB U ιG e a χ) (jB s) :=
      fun k1 k2 h => congrArg (idx s) (congrArg (ε ≫ ·) h)
    have cross : ∀ k k', φB U ιG e a χ k = φA U ιD e a χ k' → jB s k = jA s k' :=
      fun k k' h => congrArg (idx s) (congrArg (ε ≫ ·) h)
    have P := hρ (jA s) (jB s) cA cB cross
    have hU : Us s ≤ ε ⁻¹ᵁ (LB.wchart D.toPre.P.L (φB U ιG e a χ) (jB s) ⊓
        LB.wchart D.toPre.P.L (φA U ιD e a χ) (jA s)) :=
      fun x hx => ⟨LBVal.wchart_pull_le _ _ ε _ hx.1, LBVal.wchart_pull_le _ _ ε _ hx.2⟩
    have P2 := (congrArg (fun w => (ε.appLE _ (Us s) hU).hom (Units.val w)) P).trans
      (map_mul (ε.appLE _ (Us s) hU).hom _ _)
    have P' := (appLE_res ε _ hU _).symm.trans (P2.trans
      (congrArg₂ (· * ·) (appLE_res ε _ hU ρ) (appLE_res ε _ hU _)))

    have hB : Us s ≤ ε ⁻¹ᵁ LB.wchart D.toPre.P.L (φB U ιG e a χ) (jB s) :=
      fun x hx => LBVal.wchart_pull_le _ _ ε _ hx.1
    have hBO : ∀ k, ε ≫ φB U ιG e a χ k = ε ≫ D.toPre.Oφ (U.gt e).pG χ k := fun k => by
      show ε ≫ ((Over.pullback (thick R I e)).map (ιG.act a)).left ≫ _ = _
      rw [← Category.assoc, F1]
    have R1 : (ε.appLE _ (Us s) hB).hom ((rhs U ιG e a χ).s (jB s)).val = 1 := by
      refine (congrArg (ε.appLE _ (Us s) hB).hom (pullGen_s_val D.toPre.P.L _ _ (jB s))).trans ?_
      have cohB : LB.Coh D.toPre.P.L (fun k => ε ≫ D.toPre.Oφ (U.gt e).pG χ k) (jB s) :=
        fun k1 k2 h => congrArg (idx s) (((hBO k1).trans h).trans (hBO k2).symm)
      have hV : Us s ≤ LB.wchart D.toPre.P.L (fun k => ε ≫ D.toPre.Oφ (U.gt e).pG χ k) (jB s) :=
        fun x hx => Set.mem_iInter.2 fun k => by
          have := Set.mem_iInter.1 hx.1 k
          beta_reduce at this ⊢
          rwa [hBO k] at this
      have m : ((Over.pullback (thick R I e)).map (ιG.act a)).left.appLE _ _
          (LBVal.wchart_pull_le _ _ _ (jB s)) ≫ ε.appLE _ (Us s) hB =
          ε.appLE _ (Us s) (hV.trans (LBVal.wchart_pull_le _ _ ε (jB s))) := by
        rw [Scheme.Hom.appLE_comp_appLE]
        exact Semi.TorusInj.appLE_of_eq F1 _
      rw [← appLE_one D.toPre.P.L ((U.gt e).t χ) ε ((U.gt e).t_unit χ) (jB s) cohB (Us s) hV, ← m]
      rfl

    have hA : Us s ≤ ε ⁻¹ᵁ LB.wchart D.toPre.P.L (φA U ιD e a χ) (jA s) :=
      fun x hx => LBVal.wchart_pull_le _ _ ε _ hx.2
    have M := LBVal.mulGen_val D.toPre.P.L _ _ _ _ ((U.gt e).t (star a • χ))
      (LB.pullGen D.toPre.P.L _ _ u (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left) (jA s) _ le_rfl
    have L1 := (congrArg (ε.appLE _ (Us s) hA).hom ((map_rfl' _).symm.trans M)).trans
      (map_mul (ε.appLE _ (Us s) hA).hom _ _)

    have coh1 : LB.Coh D.toPre.P.L (fun k => ε ≫ D.toPre.Oφ (U.gt e).pG (star a • χ) k)
        (jA s ∘ Sum.inl) := fun k1 k2 h => congrArg (idx s) h
    have hV1 : Us s ≤ LB.wchart D.toPre.P.L (fun k => ε ≫ D.toPre.Oφ (U.gt e).pG (star a • χ) k)
        (jA s ∘ Sum.inl) := fun x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.2 (Sum.inl k)
    have T1 := appLE_one D.toPre.P.L ((U.gt e).t (star a • χ)) ε ((U.gt e).t_unit _) (jA s ∘ Sum.inl)
      coh1 (Us s) hV1
    have m1 := congrArg (fun ψ => ψ.hom (((U.gt e).t (star a • χ)).s (jA s ∘ Sum.inl)).val)
      (Scheme.Hom.map_appLE ε hA (homOfLE (fun x hx =>
        Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (Sum.inl k) :
          LB.wchart D.toPre.P.L (φA U ιD e a χ) (jA s) ≤ _)).op)

    have hF2k : ∀ k, ε ≫ φA U ιD e a χ (Sum.inr k) = cS ≫ ((zz D.toPre.P.A).left ≫
        rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k) := fun k => by
      show ε ≫ (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left ≫ _ = _
      rw [← Category.assoc, F2, Category.assoc]
    have coh2 : LB.Coh D.toPre.P.L (fun k => cS ≫ ((zz D.toPre.P.A).left ≫
        rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k)) (jA s ∘ Sum.inr) :=
      fun k1 k2 h => congrArg (idx s) (((hF2k k1).trans h).trans (hF2k k2).symm)
    have hV2' : Us s ≤ LB.wchart D.toPre.P.L (fun k => cS ≫ ((zz D.toPre.P.A).left ≫
        rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k)) (jA s ∘ Sum.inr) :=
      fun x hx => Set.mem_iInter.2 fun k => by
        have := Set.mem_iInter.1 hx.2 (Sum.inr k)
        beta_reduce at this ⊢
        rwa [hF2k k] at this
    have T2 := appLE_one D.toPre.P.L (LB.pullGen D.toPre.P.L _ _ u (zz D.toPre.P.A).left) cS
      (corr_one_pull D.toPre.P.L hz0 cS) (jA s ∘ Sum.inr) coh2 (Us s) hV2'
    have hW2 : Us s ≤ ε ⁻¹ᵁ LB.wchart D.toPre.P.L (fun k =>
        (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left ≫
          rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k) (jA s ∘ Sum.inr) :=
      fun x hx => LBVal.wchart_pull_le _ _ ε _ (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.2 (Sum.inr k))
    have m2 : (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left.appLE _ _
        (LBVal.wchart_pull_le _ _ _ (jA s ∘ Sum.inr)) ≫ ε.appLE _ (Us s) hW2 =
        (zz D.toPre.P.A).left.appLE _ _ (LBVal.wchart_pull_le _ _ _ (jA s ∘ Sum.inr)) ≫
          cS.appLE _ (Us s) (hV2'.trans (LBVal.wchart_pull_le _ _ cS _)) := by
      rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      exact Semi.TorusInj.appLE_of_eq F2 _
    have V2 : (ε.appLE _ (Us s) hW2).hom ((LB.pullGen D.toPre.P.L _ _ u
        (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left).s (jA s ∘ Sum.inr)).val = 1 := by
      refine (congrArg (ε.appLE _ (Us s) hW2).hom (pullGen_s_val D.toPre.P.L _ _ _)).trans ?_
      refine (congrArg (fun ψ => ψ.hom (u.s (jA s ∘ Sum.inr)).val) m2).trans ?_
      refine Eq.trans ?_ T2
      exact congrArg (cS.appLE _ (Us s) _).hom (pullGen_s_val D.toPre.P.L _ _ _).symm
    have m3 := congrArg (fun ψ => ψ.hom ((LB.pullGen D.toPre.P.L _ _ u
        (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left).s (jA s ∘ Sum.inr)).val)
      (Scheme.Hom.map_appLE ε hA (homOfLE (fun x hx =>
        Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (Sum.inr k) :
          LB.wchart D.toPre.P.L (φA U ιD e a χ) (jA s) ≤ _)).op)
    have LHS1 : (ε.appLE _ (Us s) hA).hom ((lhs U ιD e a χ u).s (jA s)).val = 1 :=
      L1.trans ((congrArg₂ (· * ·) (m1.trans T1) (m3.trans V2)).trans (_root_.mul_one _))
    exact (_root_.mul_one _).symm.trans ((congrArg _ R1).symm.trans (P'.symm.trans LHS1))
  refine eq_local Us hcov _ _ fun s => ?_
  exact (key s).trans (map_one _).symm

end Main

end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf

open Semi

lemma eSec_struct {S : Scheme.{0}} (H : Over S) [GrpObj H] (κ : Γ((𝟙_ (Over S)).left, ⊤)) :
    (eSec H).appTop.hom (H.hom.appTop.hom κ) = κ := by

  have key : eSec H ≫ H.hom = 𝟙 _ := by
    first
    | simp [eSec]
    | (have h := Over.w (η[H]); simpa [eSec] using h)
  calc (eSec H).appTop.hom (H.hom.appTop.hom κ)
      = (eSec H ≫ H.hom).appTop.hom κ := by first | rfl | simp
    _ = κ := by rw [key]; simp

set_option backward.isDefEq.respectTransparency false in

theorem tLin_of (hGF : GlobalFnsSt) : TLinSt := by
  intro R _ _ I O _ _ D _ A G _ _ U ιD ιA ιG hlin e a u hu hu0 χ
  have hO := hlin.q_lin e
  have hi := hlin.i_lin e a
  obtain ⟨ρ, hρ⟩ := pair U ιD ιG e a χ hO u hu
  have hinv := rho_inv U ιD ιG e a χ hO u hi ρ hρ
  obtain ⟨v, hv⟩ := descend (U.gt e) ρ.val hinv
  obtain ⟨κ, hκ⟩ := const_pullback hGF (thick R I e) D.toPre.P.A D.toPre.P.isAb v
  have hq : (U.gt e).q.left ≫ (thickObj R I e D.toPre.P.A).hom = (thickObj R I e G).hom :=
    Over.w (U.gt e).q
  have hρκ : ρ.val = (thickObj R I e G).hom.appTop.hom κ := by
    rw [← hv, ← hκ]
    have := congrArg (fun φ : (thickObj R I e G).left ⟶ _ => φ.appTop.hom κ) hq
    rw [Scheme.Hom.comp_appTop] at this
    exact this
  have he := rho_e U ιD ιG e a χ hO u hGF hu hu0 ρ hρ
  have hκ1 : κ = 1 := by
    rw [hρκ, eSec_struct] at he
    exact he
  have hρ1 : ρ = 1 := Units.ext (by rw [hρκ, hκ1, map_one]; rfl)
  intro j j' cj cj' cjj'
  have h1 := hρ j j' cj cj' (fun k k' h => (cjj' k' k h.symm).symm)
  rw [hρ1, map_one] at h1
  have h1' := h1.trans (_root_.one_mul _)
  have h2 := congrArg (res (le_of_eq (inf_comm _ _) : LB.wchart D.toPre.P.L (φA U ιD e a χ) j ⊓
      LB.wchart D.toPre.P.L (φB U ιG e a χ) j' ≤
      LB.wchart D.toPre.P.L (φB U ιG e a χ) j' ⊓ LB.wchart D.toPre.P.L (φA U ιD e a χ) j)) h1'
  exact (Canon.res_res' _ _ _).symm.trans (h2.trans (Canon.res_res' _ _ _))

end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
end
end
