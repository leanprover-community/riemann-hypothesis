import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdNeg

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TWM

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation

theorem appTop_specMap {R S : CommRingCat} (g : R ⟶ S) (r : Γ(Spec R, ⊤)) :
    (Spec.map g).appTop.hom r = (Scheme.ΓSpecIso S).inv.hom (g.hom ((Scheme.ΓSpecIso R).hom.hom r)) := by
  have e := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_naturality g)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [← e]
  simp

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

abbrev TO : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom (fO v hϖ hv)))

abbrev ιS : TF (R := V) F ⟶ TO hϖ hv :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F))) (by
    show Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ Spec.map (CommRingCat.ofHom (fO v hϖ hv)) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F)) ≫ Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, fO_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp])

abbrev jO : DegPre.BF D.toPre F ⟶ TO hϖ hv ⊗ D.toPre.P.A := ιS hϖ hv ▷ D.toPre.P.A

theorem jO_snd : (jO hϖ hv (D := D)).left ≫ (snd (TO hϖ hv) D.toPre.P.A).left = (DegPre.prB D.toPre F).left := by
  rw [← Over.comp_left, whiskerRight_snd]

theorem jO_fst : (jO hϖ hv (D := D)).left ≫ (fst (TO hϖ hv) D.toPre.P.A).left =
    (fst (TF (R := V) F) D.toPre.P.A).left ≫ (ιS hϖ hv).left := by
  rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]

abbrev ιr (r : Γ(Spec (CommRingCat.of (Ov v)), ⊤)) : F :=
  algebraMap (Ov v) F ((Scheme.ΓSpecIso (CommRingCat.of (Ov v))).hom.hom r)

theorem v_ιr (r : Γ(Spec (CommRingCat.of (Ov v)), ⊤)) : (0 : WithTop ℚ) ≤ v (ιr (v := v) r) := v_nonneg v _

theorem gs_jO {Z : Scheme.{0}} (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (r : Γ(Spec (CommRingCat.of (Ov v)), ⊤)) :
    gs (ρ ≫ (jO hϖ hv (D := D)).left) z ⊤ ((fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom r) =
      gs ρ z ⊤ (gF D.toPre F (ιr (v := v) r)) := by
  have e1 : gs (ρ ≫ (jO hϖ hv (D := D)).left) z ⊤ ((fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom r) =
      gs ((ρ ≫ (jO hϖ hv (D := D)).left) ≫ (fst (TO hϖ hv) D.toPre.P.A).left) z ⊤ r := gs_pull _ _ z ⊤ trivial r
  rw [e1, Category.assoc, jO_fst, ← Category.assoc]
  have e2 : gs ((ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) ≫ (ιS hϖ hv).left) z ⊤ r =
      gs (ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z ⊤ ((ιS hϖ hv).left.appTop.hom r) := (gs_pull _ _ z ⊤ trivial r).symm
  have e3 : gs ρ z ⊤ (gF D.toPre F (ιr (v := v) r)) = gs (ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (ιr (v := v) r)) := gs_pull _ _ z ⊤ trivial _
  rw [e2, e3, show (ιS hϖ hv).left = Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) from rfl, appTop_specMap]
  rfl

theorem vge_moveO (hTW : TwistBCSpanStatement) {k : ℕ} (hk : 1 ≤ k) {α χ : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))}
    {s' : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))}
    {h : (DegPre.BF D.toPre F).left ⟶ (DegPre.BF D.toPre F).left}
    (hfst : h ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left)
    {H : (TO hϖ hv ⊗ D.toPre.P.A).left ⟶ (TO hϖ hv ⊗ D.toPre.P.A).left}
    (hh : h ≫ (jO hϖ hv (D := D)).left = (jO hϖ hv).left ≫ H)
    {K₃ K₄ : Type} [Fintype K₃] [Fintype K₄]
    {φ₃ : K₃ → ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb D.toPre.P.L φ₃ ε₃))
    (hrel : GeneratorPullback.SecRel D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k) s'
      (DegPre.famφ D.toPre F α) (DegPre.famε k) s h φ₃ ε₃ u)
    {ψ : K₄ → ((TO hϖ hv ⊗ D.toPre.P.A).left ⟶ D.toPre.P.A.left)} {δ : K₄ → ℤ}
    (eO : LB.Gen (LB.LinComb D.toPre.P.L ψ δ)) (heO : eO.IsGen)
    (hform : FormEq (Sum.elim (fun i => (H ≫ (snd (TO hϖ hv) D.toPre.P.A).left) ≫ D.toPre.famφB α i) ψ)
      (Sum.elim (DegPre.famε k) δ) (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB χ i) (DegPre.famε k))
    (c : F)
    (hc : ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      (val u (𝟙 _) y J).val = gs (𝟙 _) y ⊤ (gF D.toPre F c) * (val eO (jO hϖ hv).left y J).val)
    {r q : ℚ} (hq : ((q : ℚ) : WithTop ℚ) ≤ v c) (hs : VGe D F v k α s r) : VGe D F v k χ s' (r + q) := by
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨n, a, σ, σF, hscal, hva, hsum⟩ := hs
  have e1 : ∀ i, ∃ t : LB.Sec (LB.LinComb D.toPre.P.L
      (fun j => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB χ j) (DegPre.famε k)),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (TO hϖ hv ⊗ D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval t ρ z J = sval (σ i) (ρ ≫ H ≫ (snd (TO hϖ hv) D.toPre.P.A).left) z J * (val eO ρ z J).val := fun i => by
    obtain ⟨t, ht⟩ := exists_sec hL hform (pullMulSec (σ i) (H ≫ (snd (TO hϖ hv) D.toPre.P.A).left) eO heO)
    exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (sval_pullMulSec _ _ _ heO ρ z hJ)⟩
  choose S hS using e1
  have e2 := fun i => hTW V D.toPre k hk χ (Ov v) (fO v hϖ hv) inferInstance (S i)
  choose m rr σ' hsp using e2
  have hformF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB χ i) (DegPre.famε k)
      (DegPre.famφ D.toPre F χ) (DegPre.famε k) := fun U _ g =>
    Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]
  have e3 : ∀ (i : Fin n) (l : Fin (m i)), ∃ t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k)),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval t ρ z J = sval (σ' i l) (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun i l => by
    obtain ⟨t, ht⟩ := exists_sec hL hformF (pullSec D.toPre.P.L _ _ (σ' i l) (DegPre.prB D.toPre F).left)
    exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (sval_pullSec _ _ _ _ ρ z hJ)⟩
  choose σ'F hσ'F using e3
  let eqv := (finSigmaFinEquiv (n := m)).symm
  let co : Fin (∑ i, m i) → F := fun t => c * a (eqv t).1 * ιr (v := v) (rr (eqv t).1 (eqv t).2)
  have hprB : h ≫ (DegPre.prB D.toPre F).left = (jO hϖ hv).left ≫ H ≫ (snd (TO hϖ hv) D.toPre.P.A).left := by
    rw [← jO_snd hϖ hv, ← Category.assoc, hh, Category.assoc]

  have CORE : ∀ (y : (DegPre.BF D.toPre F).left) (I), Good D.toPre.P.L y I →
      sval s' (𝟙 _) y I = ∑ t, gs (𝟙 _) y ⊤ (gF D.toPre F (co t)) * sval (σ'F (eqv t).1 (eqv t).2) (𝟙 _) y I := by
    intro y I hIy
    have H1 := (secRel_iff hL _ _ s' _ _ s h _ _ u).1 hrel _ (𝟙 _) y I hIy
    have H2 := sval_lin (fun i => gF D.toPre F (a i)) σF (fun j => hsum j) (𝟙 _ ≫ h) y hIy
    rw [H1, H2, hc y I hIy, Finset.sum_mul]
    rw [← (Equiv.sum_comp eqv.symm _), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    have A1 : gs (𝟙 _ ≫ h) y ⊤ (gF D.toPre F (a i)) = gs (𝟙 _) y ⊤ (gF D.toPre F (a i)) := by
      rw [Category.id_comp]; exact gs_gF_comp hfst y (a i)
    have A2 : sval (σF i) (𝟙 _ ≫ h) y I = sval (σ i) ((jO hϖ hv).left ≫ H ≫ (snd (TO hϖ hv) D.toPre.P.A).left) y I := by
      rw [← secScal_sval (hscal i) (𝟙 _ ≫ h) y hIy, Category.assoc, hprB, Category.id_comp]
    have A3 := hS i _ (jO hϖ hv).left y I hIy
    have A4 := sval_lin (fun l => (fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom (rr i l))
      (fun l => pullSec D.toPre.P.L _ _ (σ' i l) (snd (TO hϖ hv) D.toPre.P.A).left) (fun j => hsp i j)
      (jO hϖ hv).left y hIy
    rw [A1, A2]
    have A5 : sval (σ i) ((jO hϖ hv).left ≫ H ≫ (snd (TO hϖ hv) D.toPre.P.A).left) y I *
        (val eO (jO hϖ hv).left y I).val = ∑ l, gs (𝟙 _) y ⊤ (gF D.toPre F (ιr (v := v) (rr i l))) *
          sval (σ'F i l) (𝟙 _) y I := by
      rw [← A3, A4]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [sval_pullSec _ _ _ _ _ y hIy, jO_snd, hσ'F i l _ (𝟙 _) y I hIy, Category.id_comp]
      congr 1
      have := gs_jO hϖ hv (D := D) (𝟙 _) y (rr i l)
      rwa [Category.id_comp] at this
    calc _ = gs (𝟙 _) y ⊤ (gF D.toPre F (a i)) * gs (𝟙 _) y ⊤ (gF D.toPre F c) *
          (sval (σ i) ((jO hϖ hv).left ≫ H ≫ (snd (TO hϖ hv) D.toPre.P.A).left) y I *
            (val eO (jO hϖ hv).left y I).val) := by ring
      _ = _ := by
        rw [A5, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [co, eqv, Equiv.symm_symm, map_mul]
        rw [show finSigmaFinEquiv.symm (finSigmaFinEquiv (⟨i, l⟩ : (i : Fin n) × Fin (m i))) = ⟨i, l⟩ from
          Equiv.symm_apply_apply _ _, gs_mul _ y ⊤ trivial, gs_mul _ y ⊤ trivial]
        ring
  refine ⟨∑ i, m i, co, fun t => σ' (eqv t).1 (eqv t).2, fun t => σ'F (eqv t).1 (eqv t).2, fun t => ?_, fun t => ?_,
    fun j => ?_⟩
  · exact secScal_of_sval hL fun y J hJ => (hσ'F _ _ _ (𝟙 _) y J hJ).symm
  · show ((r + q : ℚ) : WithTop ℚ) ≤ v (c * a (eqv t).1 * ιr (v := v) (rr (eqv t).1 (eqv t).2))
    rw [AddValuation.map_mul, AddValuation.map_mul, WithTop.coe_add]
    calc ((r : ℚ) : WithTop ℚ) + (q : WithTop ℚ) = (q : WithTop ℚ) + (r : WithTop ℚ) + 0 := by
          rw [add_zero, add_comm]
      _ ≤ _ := add_le_add (add_le_add hq (hva _)) (v_ιr _)
  · show s'.f j = ∑ t, resTop _ (gF D.toPre F (co t)) * (σ'F (eqv t).1 (eqv t).2).f j
    refine fn_ext fun y hy => ?_
    choose I hI using fun ψ : (DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left =>
      Geo.Tor.exists_chart hL (ψ y)
    have hIy : Good D.toPre.P.L y I := hI
    have mm := hIy.mem (DegPre.famφ D.toPre F χ) (𝟙 _)
    have hy' : y ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j := hy
    have T0 := sec_trans s' (𝟙 _) y hy' mm
    set τ := (Geo.Tor.trF (DegPre.famφ D.toPre F χ) (DegPre.famε k) (𝟙 _) y j
      (fun k => I (𝟙 _ ≫ DegPre.famφ D.toPre F χ k))).val with hτ
    have RHS : gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
        (∑ t, resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (co t)) *
          (show Γ((DegPre.BF D.toPre F).left, LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) from
            (σ'F (eqv t).1 (eqv t).2).f j)) =
        τ * ∑ t, gs (𝟙 _) y ⊤ (gF D.toPre F (co t)) * sval (σ'F (eqv t).1 (eqv t).2) (𝟙 _) y I := by
      rw [gs_sum _ y _ hy', Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      have S1 : gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
          (resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (co t))) =
          gs (𝟙 _) y ⊤ (gF D.toPre F (co t)) := gs_res _ y le_top hy' _
      rw [gs_mul _ y _ hy', S1, sec_trans (σ'F (eqv t).1 (eqv t).2) (𝟙 _) y hy' mm, hτ]
      exact mul_left_comm _ _ _
    exact T0.trans ((congrArg (fun x => τ * x) (CORE y I hIy)).trans RHS.symm)

end ReciprocityTheory.ChartRestriction.G.DVR.TWM
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TWM

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem TF_hom : (TF (R := V) F).hom = Spec.map (CommRingCat.ofHom (algVF (F := F) (V := V))) := by
  simp only [TF, jFK, jK]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem exists_liftO (b : TF (R := V) F ⟶ D.toPre.P.A) : ∃ m : TO hϖ hv ⟶ D.toPre.P.A, ιS hϖ hv ≫ m = b := by
  haveI : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  obtain ⟨x', hx'p, hx'⟩ := TWO.exists_lift v hϖ hv D.toPre.P.A.hom b.left (by rw [Over.w b, TF_hom])
  exact ⟨Over.homMk x' hx'p, Over.OverMorphism.ext hx'⟩

theorem liftO_unique (m₁ m₂ : TO hϖ hv ⟶ D.toPre.P.A) (h : ιS hϖ hv ≫ m₁ = ιS hϖ hv ≫ m₂) : m₁ = m₂ := by
  haveI : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  apply Over.OverMorphism.ext
  exact TWO.lift_unique v hϖ hv D.toPre.P.A.hom m₁.left m₂.left (Over.w m₁) (Over.w m₂)
    (congrArg (fun g => g.left) h)

def gtφO (m : TO hϖ hv ⟶ D.toPre.P.A) (χ : D.toPre.X) : Fin 4 → ((TO hϖ hv).left ⟶ D.toPre.P.A.left) :=
  ![(cP D.toPre _ χ * m).left, (cP D.toPre _ χ).left, m.left, (1 : TO hϖ hv ⟶ D.toPre.P.A).left]

def lineφO (m : TO hϖ hv ⟶ D.toPre.P.A) : Fin 2 → ((TO hϖ hv).left ⟶ D.toPre.P.A.left) :=
  ![(1 : TO hϖ hv ⟶ D.toPre.P.A).left, m.left]

def trO (m : TO hϖ hv ⟶ D.toPre.P.A) : TO hϖ hv ⊗ D.toPre.P.A ⟶ TO hϖ hv ⊗ D.toPre.P.A :=
  lift (fst _ _) (padd D.toPre.P.A (snd _ _) (fst _ _ ≫ m))

theorem trO_fst (m : TO hϖ hv ⟶ D.toPre.P.A) : trO hϖ hv m ≫ fst _ _ = fst _ _ := by
  unfold trO
  exact lift_fst _ _

theorem trO_snd (m : TO hϖ hv ⟶ D.toPre.P.A) : trO hϖ hv m ≫ snd _ _ = snd _ _ * (fst _ _ ≫ m) := by
  unfold trO
  rw [lift_snd]
  rfl

theorem jO_trO (b : TF (R := V) F ⟶ D.toPre.P.A) (m : TO hϖ hv ⟶ D.toPre.P.A) (hm : ιS hϖ hv ≫ m = b) :
    jO hϖ hv (D := D) ≫ trO hϖ hv m = DegPre.trPt D.toPre F b ≫ jO hϖ hv := by
  have h1 : jO hϖ hv (D := D) ≫ trO hϖ hv m ≫ snd (TO hϖ hv) D.toPre.P.A =
      snd (TF (R := V) F) D.toPre.P.A * (fst (TF (R := V) F) D.toPre.P.A ≫ b) := by
    rw [trO_snd, MonObj.comp_mul, whiskerRight_snd, ← Category.assoc, whiskerRight_fst, Category.assoc, hm]
  have h2 : DegPre.trPt D.toPre F b ≫ jO hϖ hv (D := D) ≫ snd (TO hϖ hv) D.toPre.P.A =
      snd (TF (R := V) F) D.toPre.P.A * (fst (TF (R := V) F) D.toPre.P.A ≫ b) := by
    rw [whiskerRight_snd]
    unfold DegPre.trPt
    rw [lift_snd]
    rfl
  have h3 : jO hϖ hv (D := D) ≫ trO hϖ hv m ≫ fst (TO hϖ hv) D.toPre.P.A =
      fst (TF (R := V) F) D.toPre.P.A ≫ ιS hϖ hv := by
    rw [trO_fst, whiskerRight_fst]
  have h4 : DegPre.trPt D.toPre F b ≫ jO hϖ hv (D := D) ≫ fst (TO hϖ hv) D.toPre.P.A =
      fst (TF (R := V) F) D.toPre.P.A ≫ ιS hϖ hv := by
    rw [whiskerRight_fst, ← Category.assoc, tr_fst]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc]
    rw [h3, h4]
  · simp only [Category.assoc]
    rw [h1, h2]

theorem gen_uO (k : ℕ) (α α' : D.toPre.X) (m : TO hϖ hv ⟶ D.toPre.P.A)
    (hα : cP D.toPre _ α' = cP D.toPre _ α * m ^ k) {K : Type} [Fintype K]
    {φ : K → ((TO hϖ hv).left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    (vO : LB.Gen (LB.LinComb D.toPre.P.L φ ε)) (hvO : vO.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : ((TO hϖ hv).left ⟶ D.toPre.P.A.left) → U), ∏ i, h (φ i) ^ ε i =
      (h (cP D.toPre _ α * m).left)⁻¹ * h (cP D.toPre _ α).left * h m.left * (h (1 : TO hϖ hv ⟶ D.toPre.P.A).left)⁻¹ *
        (h m.left ^ k)⁻¹ * h (1 : TO hϖ hv ⟶ D.toPre.P.A).left ^ k) :
    ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α' i)
        (fun i => (trO hϖ hv m ≫ snd _ _).left ≫ D.toPre.famφB α i)) (DegPre.deltaε k)), u.IsGen ∧
      ∀ (T : Over (Spec (CommRingCat.of V))) (ρ : T ⟶ TO hϖ hv ⊗ D.toPre.P.A) (z : T.left) (J), Good D.toPre.P.L z J →
        val u ρ.left z J = cubN (th D.toPre z J) k (cP D.toPre T α) (ρ ≫ fst _ _ ≫ m) (ρ ≫ snd _ _) *
          (th D.toPre z J (cP D.toPre T α) (ρ ≫ snd _ _) (ρ ≫ fst _ _ ≫ m))⁻¹ * val vO (ρ ≫ fst _ _).left z J := by
  let a : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A := cP D.toPre _ α
  let mm : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A := fst _ _ ≫ m
  let x : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A := snd _ _
  have hα' : cP D.toPre (TO hϖ hv ⊗ D.toPre.P.A) α' = a * mm ^ k := by
    rw [← comp_cP D.toPre (fst (TO hϖ hv) D.toPre.P.A), hα]
    exact (map_mul (preHom (fst (TO hϖ hv) D.toPre.P.A)) _ _).trans
      (congrArg₂ (· * ·) (comp_cP D.toPre _ α) (map_pow (preHom (fst (TO hϖ hv) D.toPre.P.A)) _ _))
  obtain ⟨N, hN, vN⟩ := exists_cubN D.toPre.cub a mm x k
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_gen D.toPre.P.isLB (φ' := Sum.elim (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α' i)
      (fun i => (trO hϖ hv m ≫ snd _ _).left ≫ D.toPre.famφB α i)) (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub a x mm h
      have p₂ := hF U (fun q => h ((fst (TO hϖ hv) D.toPre.P.A).left ≫ q))
      have p₃ := SectionScalarValuation.prod_famB D.toPre (snd (TO hϖ hv) D.toPre.P.A) α' k h
      have p₄ := SectionScalarValuation.prod_famB D.toPre (trO hϖ hv m ≫ snd _ _) α k h
      have q₁ : (fst (TO hϖ hv) D.toPre.P.A).left ≫ (cP D.toPre _ α * m).left = (a * mm).left :=
        congrArg (fun q : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A => q.left)
          ((MonObj.comp_mul (fst (TO hϖ hv) D.toPre.P.A) (cP D.toPre _ α) m).trans
            (congrArg (· * mm) (comp_cP D.toPre (fst (TO hϖ hv) D.toPre.P.A) α)))
      have q₂ : (fst (TO hϖ hv) D.toPre.P.A).left ≫ (cP D.toPre _ α).left = a.left :=
        congrArg (fun q : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A => q.left) (comp_cP D.toPre (fst (TO hϖ hv) D.toPre.P.A) α)
      have q₃ : (fst (TO hϖ hv) D.toPre.P.A).left ≫ (1 : TO hϖ hv ⟶ D.toPre.P.A).left =
          (1 : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A).left :=
        congrArg (fun q : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A => q.left) (MonObj.comp_one (M := D.toPre.P.A) (fst (TO hϖ hv) D.toPre.P.A))
      have q₄ : (fst (TO hϖ hv) D.toPre.P.A).left ≫ m.left = mm.left := rfl
      rw [q₁, q₂, q₃, q₄] at p₂
      have c₁ : SectionScalarValuation.cQ D.toPre (TO hϖ hv ⊗ D.toPre.P.A) α' = a * mm ^ k := hα'
      have c₂ : SectionScalarValuation.cQ D.toPre (TO hϖ hv ⊗ D.toPre.P.A) α = a := rfl
      rw [c₁] at p₃
      rw [c₂] at p₄
      conv at p₄ => rhs; rw [trO_snd]
      refine Eq.trans (prod_sum₂ (K := Fin 8 ⊕ thK) (K' := K) (U := U) _
        (prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ rfl (prod_neg _ _ p₁)) p₂)
        (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).symm)
      have r1 : x * (a * mm ^ k) = a * mm ^ k * x := mul_comm _ _
      have r2 : x * mm * a = a * x * mm := by rw [mul_comm, ← _root_.mul_assoc]
      have r3 : mm * x = x * mm := mul_comm _ _
      rw [r1, r2, r3]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, a, mm, x]
      module)
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _ N (LB.invGen D.toPre.P.L _ _
      (LB.pullGen D.toPre.P.L (thφ D.toPre.P.A (x3 D.toPre.P.A)) thε D.toPre.cub.t (lift a (lift x mm)).left)))
      (LB.pullGen D.toPre.P.L _ _ vO (fst (TO hϖ hv) D.toPre.P.A).left))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.toPre.cub.isGen _)))
      (pullGen_isGen _ _ _ _ hvO _))
  refine ⟨u₀, hu₀, fun T ρ z J hJ => ?_⟩
  refine (vu₀ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    ((congrArg₂ (· * ·) (vN T ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.toPre.cub ρ hJ _ _ _)))).trans ?_))
    (val_pull hJ _ _ _)))
  rw [← comp_cP D.toPre ρ α]

end ReciprocityTheory.ChartRestriction.G.DVR.TWM
end
end
