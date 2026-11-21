import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.CrossGlobal

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.ValuationAtUnit

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

def ValAtUnit {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {H : Geo.Tor.Host E} {t : Geo.Tor.SAB H (Spec (CommRingCat.of V))}
    (P : Geo.Tor.PELUnif (maximalIdeal V) t) (k : ℕ) (s : P.U.SecK k) (x : FractionRing V) : Prop :=
  ∃ τ : LB.Gen (LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => unitK ≫ gK) (fun _ => (k : ℤ))), τ.IsGen ∧
    LB.Gen.Corr P.U.LG.L _ _ _ _ τ
      (LB.pullGen P.U.LG.L _ _ (GeneratorPullback.powGen P.U.LG.L _ _ P.U.LG.rig k) (jK V)) ∧
    ∀ j, rs (wchart_comp_le (L := P.U.LG.L) (fun _ : Fin 1 => gK) unitK j) ((unitK.app _).hom (s.f j)) =
      ((Spec (CommRingCat.of (FractionRing V))).presheaf.map (homOfLE le_top).op).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom x) * (τ.s j).val

theorem eq_of_gs_eq {F : Type} [Field F] (z : Spec (CommRingCat.of F)) (c c' : F)
    (h : gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) =
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c')) : c = c' := by
  have hz : (𝟙 (Spec (CommRingCat.of F)) : _) z ∈ (⊤ : (Spec (CommRingCat.of F)).Opens) := trivial
  unfold gs at h
  rw [dif_pos hz, dif_pos hz] at h
  have h2 : (Scheme.Hom.app (𝟙 (Spec (CommRingCat.of F))) ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) =
      (Scheme.Hom.app (𝟙 (Spec (CommRingCat.of F))) ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c') := by
    first
    | exact AlgebraicGeometry.germ_injective_of_isIntegral _ _ hz h
    | exact AlgebraicGeometry.germ_injective_of_isIntegral _ _ _ hz h
    | exact AlgebraicGeometry.germ_injective_of_isIntegral _ hz h
    | exact AlgebraicGeometry.germ_injective_of_isIntegral (Spec (CommRingCat.of F)) h
  have h2' : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c = (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c' := by
    first
    | exact h2
    | simpa only [RingHom.id_apply] using h2
    | (simp only [Scheme.Hom.id_app, CommRingCat.hom_id, RingHom.id_apply] at h2; exact h2)
  have h3 := congrArg (fun y => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom y) h2'
  simpa using h3

theorem valueAtZero_unique_of_stalk_reading {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F] {k : ℕ}
    {α : D.toPre.X} {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {c c' : F}
    (h : Val0 D F k α s c) (h' : Val0 D F k α s c') : c = c' := by
  obtain ⟨τ, -, cτ, eτ⟩ := h
  obtain ⟨τ', -, cτ', eτ'⟩ := h'
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of F)) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  choose J hJ using fun χ : Spec (CommRingCat.of F) ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ z)
  have hm := Good.mem hJ (fun i => (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i) (𝟙 _)
  have e := congrArg (gs (𝟙 _) z _)
    ((eτ (fun i => J (𝟙 _ ≫ (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i))).symm.trans
      (eτ' (fun i => J (𝟙 _ ≫ (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i))))
  have A := (gs_mul (𝟙 _) z _ hm _ _).symm.trans (e.trans (gs_mul (𝟙 _) z _ hm _ _))
  let r0 : Spec (CommRingCat.of F) ⟶ (TF (R := V) F).left := 𝟙 _
  have B : gs (𝟙 (Spec (CommRingCat.of F))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) *
        (val τ r0 z J).val =
      gs (𝟙 (Spec (CommRingCat.of F))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c') *
        (val τ' r0 z J).val := by
    convert A using 2 <;> first
      | exact (gs_res (𝟙 _) z le_top hm _).symm
      | exact (gs_unit (𝟙 _) z _ hm _).symm
  rw [val_corr hJ cτ, val_corr hJ cτ'] at B
  exact eq_of_gs_eq z c c' (mul_right_cancel₀ (Units.ne_zero _) B)


theorem exists_glue_ratio {Y : Scheme.{0}} {M : LB Y} (hc : ⨆ j, M.U j = ⊤) (s : LB.Sec M) (τ : LB.Gen M)
    (hτ : τ.IsGen) : ∃ a : Γ(Y, ⊤), ∀ j, s.f j = (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom a * (τ.s j).val := by
  let r : ∀ j, Γ(Y, M.U j) := fun j => s.f j * ((τ.s j)⁻¹ : Γ(Y, M.U j)ˣ).val
  have compat : ∀ i j, (Y.presheaf.map (homOfLE (inf_le_left : M.U i ⊓ M.U j ≤ M.U i)).op).hom (r i) =
      (Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom (r j) := by
    intro i j
    have hs := s.compat i j
    have hti : (Y.presheaf.map (homOfLE (inf_le_left : M.U i ⊓ M.U j ≤ M.U i)).op).hom ((τ.s i)⁻¹ : Γ(Y, M.U i)ˣ).val =
        (Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom ((τ.s j)⁻¹ : Γ(Y, M.U j)ˣ).val *
          ((M.g i j)⁻¹ : Γ(Y, M.U i ⊓ M.U j)ˣ).val := by
      have := congrArg (fun u => (u⁻¹ : Γ(Y, M.U i ⊓ M.U j)ˣ).val) (hτ i j)
      simp only [mul_inv_rev, Units.val_mul] at this
      exact this
    have hg : (M.g i j : Γ(Y, M.U i ⊓ M.U j)ˣ).val * ((M.g i j)⁻¹ : Γ(Y, M.U i ⊓ M.U j)ˣ).val = 1 := by
      rw [← Units.val_mul, _root_.mul_inv_cancel, Units.val_one]
    simp only [r, map_mul]
    rw [hs, hti]
    linear_combination ((Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom (s.f j) *
      (Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom ((τ.s j)⁻¹ : Γ(Y, M.U j)ˣ).val) * hg
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' M.U ⊤ (fun j => homOfLE le_top) hc.ge r compat
  have ha' : ∀ j, (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom a = r j := ha
  refine ⟨a, fun j => ?_⟩
  rw [ha' j]
  simp only [r]
  rw [_root_.mul_assoc, ← Units.val_mul, _root_.inv_mul_cancel, Units.val_one, _root_.mul_one]


end ReciprocityTheory.ChartRestriction.G.DVR.ValuationAtUnit
