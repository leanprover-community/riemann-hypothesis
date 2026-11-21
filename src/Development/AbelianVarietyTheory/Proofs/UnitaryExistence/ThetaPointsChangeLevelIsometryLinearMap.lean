import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0CompLinear
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecValuesComplexFibreAbelianScheme
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaCharHalfDifferentiableNeZeroFamilies
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.InversionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RatioSqEqDetJAut
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChangeOfNormalisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmUnitPowFourIdempotentModEight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaSqTransformLevelEight
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory

theorem exists_sec_generator_fibre (hT : Out.SecTwistSt) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)
    {K : Type} [Field K] (y : Sp K ⟶ S) :
    ∃ β : (o.t.PP.L.pull (pullback.fst o.t.G.hom y)).Sec, ∀ s : (o.t.PP.L.pull (pullback.fst o.t.G.hom y)).Sec,
      ∃ a : K, ∀ i, s.f i = constFn (pullback.snd o.t.G.hom y) _ a * β.f i := by
  have h := isGrpPullback_pullback o.t.G y
  obtain ⟨hL, hr, -, hs⟩ := Out.CubePf.cubePull _ _ o.t.G _ (cubeMapOf h) o.t.PP o.t.cub
  have semi := IsSemiAbelian.pullback y o.t.G o.t.semi
  have := semi.smooth
  obtain ⟨am, kt⟩ := amplePt _ _ y _ _ _ h _ _ o.t.PP.isLB hL ⟨_, Out.CubePf.idIsoL_isGen hL⟩ o.ample o.ktriv
  have := semi.geomConnected
  have : ConnectedSpace ((Over.pullback y).obj o.t.G).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := ((Over.pullback y).obj o.t.G).hom) (𝟙 _) (𝟙 _)
      ((Over.pullback y).obj o.t.G).hom (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected ((Over.pullback y).obj o.t.G).hom
    (eSec ((Over.pullback y).obj o.t.G) (default : PrimeSpectrum K))
  obtain ⟨-, ws, gs', -⟩ := hs o.t.sym
  obtain ⟨β, hβ⟩ := principalPolarisation_exists_unique_section hT
    { A := (Over.pullback y).obj o.t.G, g := d, smoothDim := hd, L := ((cubeMapOf h).rigLB o.t.PP hL hr).L
      isLB := hL, ample := am, ktriv := kt
      isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) h.1 o.proper, ‹_›⟩
      rigid := ⟨((cubeMapOf h).rigLB o.t.PP hL hr).rig, ((cubeMapOf h).rigLB o.t.PP hL hr).rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  exact ⟨β, fun s => (hβ s).exists⟩

theorem FamilyUnif_isOpen_ex {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) (i : Fin U.n)
    (P : (U.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ty P) (V : Xo.univ.t.G.left.Opens) :
    IsOpen {z | ⊤ ≤ (U.ex i P z).left ⁻¹ᵁ V} := by
  have h := ((U.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun x => differentiableOn_const _⟩).2 V 0).1
  have c : Continuous (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) := by fun_prop
  convert h.preimage c using 1
  ext z
  simp

theorem thetaFrame_ratio : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((U.Di i).La →+ (Fin g → ℂ))) (θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ), (∀ b ∈ B, IsPeriod (U.Di i) ty (P b)) → (∀ j, DifferentiableOn ℂ (fr j) {bz | bz.1 ∈ B ∧ ⊤ ≤ (U.ex i (P bz.1) bz.2).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) → (∀ j b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, z) ≠ 0) → (∀ j j' b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') → fr j (b, z) = valAt' (U.ex i (P b) z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' (b, z)) → (∀ j b, b ∈ B → ⊤ ≤ (U.ex i (P b) 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, 0) = valAt' (U.u i (P b)) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) → (∀ b ∈ B, ∃ s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).Sec, ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (U.u i (P b))), x ≫ pullback.fst _ _ = (U.ex i (P b) z).left → x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).U (fun _ => j)) (s.f (fun _ => j)) = θ b z * fr j (b, z)) → ∀ b ∈ B, ∀ b' ∈ B, ∀ h₀ : Matrix (Fin g) (Fin g) ℂ, θ b ≠ 0 → θ b' ≠ 0 → IsUnit h₀.det → (U.u i (P b)) = (U.u i (P b')) → (∀ z, (U.ex i (P b') (h₀ *ᵥ z)).left = (U.ex i (P b) z).left) → ∃ (ρ : (Fin g → ℂ) → ℂ) (κ : ℂ), Differentiable ℂ ρ ∧ (∀ z, ρ z ≠ 0) ∧ ρ 0 = 1 ∧ κ ≠ 0 ∧ (∀ z, θ b' (h₀ *ᵥ z) * ρ z = κ * θ b z) ∧ ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b', h₀ *ᵥ z) = ρ z * fr j (b, z) := by
  intro hT E _ _ _ H D l Xo σ g ty U i m B P θ fr hP hd hn hc h0 hs b hb b' hb' h₀ hθ hθ' hdet hu hex
  have cover : ∀ z, ∃ j, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z => by
    obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB ((U.ex i (P b) z).left (default : PrimeSpectrum ℂ))
    exact ⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩
  choose J hJ using cover
  have tr : ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      ⊤ ≤ (U.ex i (P b') (h₀ *ᵥ z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j z h => by rw [hex]; exact h
  have key : ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j (b', h₀ *ᵥ z) = fr (J z) (b', h₀ *ᵥ z) / fr (J z) (b, z) * fr j (b, z) := fun j z h => by
    have h1 : ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U (J z)) :=
      (top_le_preimage_inf _ _ _).2 ⟨h, hJ z⟩
    have e1 := hc j (J z) b z hb h1
    have e2 := hc j (J z) b' (h₀ *ᵥ z) hb' (by rw [hex]; exact h1)
    rw [hex] at e2
    have := hn _ _ _ hb (hJ z)
    rw [e1, e2]
    field_simp
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (Fin g → ℂ) → ℂ, ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j (b', h₀ *ᵥ z) = ρ z * fr j (b, z) := ⟨_, key⟩
  clear key
  have hρ0 : ∀ z, ρ z ≠ 0 := fun z h => hn _ _ _ hb' (tr _ _ (hJ z)) (by rw [hρ _ _ (hJ z), h, zero_mul])

  obtain ⟨s, hs1⟩ := hs b hb
  obtain ⟨s', hs2⟩ := hs b' hb'
  have hs3 : ∃ s' : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).Sec,
      ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (U.u i (P b))), x ≫ pullback.fst _ _ = (U.ex i (P b') z).left →
      x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (U.ex i (P b') z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).U (fun _ => j))
        (s'.f (fun _ => j)) = θ b' z * fr j (b', z) := by
    rw [hu]; exact ⟨s', hs2⟩
  clear s' hs2
  obtain ⟨s', hs2⟩ := hs3
  obtain ⟨β, hβ⟩ := exists_sec_generator_fibre hT Xo.univ (U.u i (P b))
  obtain ⟨a, ha⟩ := hβ s
  obtain ⟨a', ha'⟩ := hβ s'
  have val : ∀ z, ∃ v : ℂ, a * v = θ b z * fr (J z) (b, z) ∧
      a' * v = θ b' (h₀ *ᵥ z) * (ρ z * fr (J z) (b, z)) := fun z => by
    have w : (U.ex i (P b) z).left ≫ Xo.univ.t.G.hom = 𝟙 _ ≫ U.u i (P b) :=
      (Over.w (U.ex i (P b) z)).trans (Category.id_comp _).symm
    let x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (U.u i (P b)) := pullback.lift _ _ w
    have x1 : x ≫ pullback.fst _ _ = (U.ex i (P b) z).left := pullback.lift_fst _ _ _
    have x2 : x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hx : ⊤ ≤ x ⁻¹ᵁ (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).U (fun _ => J z) := by
      rw [top_le_preimage_iff_mem, mem_pull]
      have := hJ z
      rw [← x1, top_le_preimage_iff_mem] at this
      exact this
    have e1 := hs1 (J z) z x x1 x2 (hJ z)
    have e2 := hs2 (J z) (h₀ *ᵥ z) x (x1.trans (hex z).symm) x2 (tr _ _ (hJ z))
    rw [hρ _ _ (hJ z)] at e2
    have f1 := (congrArg (valAt' x _) (ha (fun _ => J z))).trans ((valAt'_mul _ _ _ _).trans
      (congrArg (· * _) (valAt'_constFn x _ x2 _ _ hx)))
    have f2 := (congrArg (valAt' x _) (ha' (fun _ => J z))).trans ((valAt'_mul _ _ _ _).trans
      (congrArg (· * _) (valAt'_constFn x _ x2 _ _ hx)))
    exact ⟨_, f1.symm.trans e1, f2.symm.trans e2⟩
  have ha0 : a ≠ 0 := fun h => hθ (funext fun z => by
    obtain ⟨v, e, -⟩ := val z
    rw [h, zero_mul] at e
    exact (mul_eq_zero.1 e.symm).resolve_right (hn _ _ _ hb (hJ z)))
  have ha0' : a' ≠ 0 := fun h => hθ' (funext fun w => by
    obtain ⟨v, -, e⟩ := val (h₀⁻¹ *ᵥ w)
    rw [h, zero_mul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at e
    exact (mul_eq_zero.1 e.symm).resolve_right (mul_ne_zero (hρ0 _) (hn _ _ _ hb (hJ _))))
  refine ⟨ρ, a' / a, fun z => ?_, hρ0, ?_, div_ne_zero ha0' ha0, fun z => ?_, hρ⟩
  · have ho := FamilyUnif_isOpen_ex U i (P b) (hP b hb) (Xo.univ.t.PP.L.U (J z))
    have hz := ho.mem_nhds (hJ z)
    have d1 : DifferentiableOn ℂ (fun z' => fr (J z) (b, z'))
        {z' | ⊤ ≤ (U.ex i (P b) z').left ⁻¹ᵁ Xo.univ.t.PP.L.U (J z)} :=
      (hd (J z)).comp (f := fun z' => (b, z')) (by fun_prop) (fun z' h => ⟨hb, h⟩)
    have dl : Differentiable ℂ (fun z' : Fin g → ℂ => h₀ *ᵥ z') :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin h₀)).differentiable
    have d2 : DifferentiableOn ℂ (fun z' => fr (J z) (b', h₀ *ᵥ z'))
        {z' | ⊤ ≤ (U.ex i (P b) z').left ⁻¹ᵁ Xo.univ.t.PP.L.U (J z)} :=
      (hd (J z)).comp (f := fun z' => (b', h₀ *ᵥ z'))
        ((differentiable_const _).prodMk dl).differentiableOn (fun z' h => ⟨hb', tr _ _ h⟩)
    have d3 := (d2.mul (d1.inv (fun z' h => hn _ _ _ hb h))).congr (f₁ := ρ) (fun z' h => by
      have := hn _ _ _ hb h
      show ρ z' = fr (J z) (b', h₀ *ᵥ z') * (fr (J z) (b, z'))⁻¹
      rw [hρ _ _ h]; field_simp)
    exact d3.differentiableAt hz
  · have e := hρ _ _ (hJ 0)
    have t := tr _ _ (hJ 0)
    rw [Matrix.mulVec_zero] at e t
    have e' : fr (J 0) (b', 0) = fr (J 0) (b, 0) := by rw [h0 _ _ hb (hJ 0), h0 _ _ hb' t, hu]
    rw [e'] at e
    exact ((mul_eq_right₀ (hn _ _ _ hb (hJ 0))).1 e.symm)
  · obtain ⟨v, e1, e2⟩ := val z
    have := hn _ _ _ hb (hJ z)
    apply mul_right_cancel₀ this
    rw [_root_.mul_assoc, ← e2, _root_.mul_assoc, ← e1]
    field_simp

end GlobalTheory
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.GlobalTheory.T.uniformization_period_lattice_change : (∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n → σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P P' : (U.Di i).La →+ (Fin g → ℂ)) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di i).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod (U.Di i) ty P → IsPeriod (U.Di i) ty P' → (∀ a b, (U.Di i).EF (gam a) (gam b) = (U.Di i).EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (U.Di i).La), ∃ e, gam a = a + l.M • e) → (∀ a, ∃ e, gam a = a + l.A • e) → (∀ a, P' (gam a) = h₀ *ᵥ P a) → IsUnit h₀.det ∧ U.u i P = U.u i P' ∧ ∀ z, (U.ex i P' (h₀ *ᵥ z)).left = (U.ex i P z).left := by
  first | exact @GlobalTheory.FamRigid.ex_eq_of_level_group | exact GlobalTheory.FamRigid.ex_eq_of_level_group | (intros; apply GlobalTheory.FamRigid.ex_eq_of_level_group <;> assumption)
end

section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory

theorem thetaFrame_det_mul_sq_invariant : (∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n → σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1) → Out.SecTwistSt → (∀ (g : ℕ) (ga : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), ga ∈ Matrix.symplecticGroup (Fin g) ℤ → (∀ i j, (8 : ℤ) ∣ ga (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ ga (Sum.inr i) (Sum.inl j)) → (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ, theta (halfVec 0) (halfVec 0) (zAct ga τ z) (spAct ga τ) ^ 2 = ((ZMod.χ₄ ((ga.toBlocks₂₂.det : ℤ) : ZMod 4) : ℤ) : ℂ) * (jAut ga τ).det * eC (expArg ga τ z) * theta (halfVec 0) (halfVec 0) z τ ^ 2)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((U.Di i).La →+ (Fin g → ℂ))) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.Di i).La) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ), (∀ b ∈ B, IsPeriod (U.Di i) ty (P b)) → (∀ a a', (U.Di i).EF (bas a) (bas a') = -omegaStd a a') → (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inl k) 1) = bas (Pi.single (Sum.inl k) 1) + (8 : ℕ) • e) ∧ (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inr k) 1) = (8 : ℕ) • e) → (∀ b ∈ B, (∀ k, h b *ᵥ P b (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h b *ᵥ P b (bas (Pi.single (Sum.inr k) 1)) = τ b *ᵥ Pi.single k 1)) → (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → (∀ j, DifferentiableOn ℂ (fr j) {bz | bz.1 ∈ B ∧ ⊤ ≤ (U.ex i (P bz.1) bz.2).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) → (∀ j b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, z) ≠ 0) → (∀ j j' b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') → fr j (b, z) = valAt' (U.ex i (P b) z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' (b, z)) → (∀ j b, b ∈ B → ⊤ ≤ (U.ex i (P b) 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, 0) = valAt' (U.u i (P b)) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) → (∀ b ∈ B, ∃ s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).Sec, ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (U.u i (P b))), x ≫ pullback.fst _ _ = (U.ex i (P b) z).left → x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).U (fun _ => j)) (s.f (fun _ => j)) = thetaChar (τ b) c₁ c₂ (h b *ᵥ z) * fr j (b, z)) → ∀ b ∈ B, ∀ b' ∈ B, ∀ (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di i).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), (∀ a b, (U.Di i).EF (gam a) (gam b) = (U.Di i).EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (U.Di i).La), ∃ e, gam a = a + l.M • e) → (∀ a, ∃ e, gam a = a + l.A • e) → (∀ a, P b' (gam a) = h₀ *ᵥ P b a) → ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → (h b).det * (thetaChar (τ b) c₁ c₂ (h b *ᵥ z) * fr j (b, z)) ^ 2 = (h b').det * h₀.det * (thetaChar (τ b') c₁ c₂ (h b' *ᵥ (h₀ *ᵥ z)) * fr j (b', h₀ *ᵥ z)) ^ 2 := by
  intro hMink hT hlaw E _ _ _ H D l Xo σ g ty U i m B P bas h τ c₁ c₂ fr hP hbas hw hn h₁ h₂ hd hne hc h0 hs
    b hb b' hb' gam h₀ hiso hhalf hA hPP j z hz
  have riem : ∀ b ∈ B, IsUnit (h b).det ∧ τ b ∈ SiegelH (Fin g) := fun b hb => by
    obtain ⟨h', τ', -, hu, hsy, hpos, huniq⟩ :=
      (RiemannRel.riemann_relations E H (U.Di i) g ty bas hbas).1 (P b) (hP b hb)
    obtain ⟨e1, e2⟩ := huniq _ _ (hn b hb)
    rw [e1, e2]
    exact ⟨hu, hsy, hpos⟩
  obtain ⟨hu, hτ⟩ := riem b hb
  obtain ⟨hu', hτ'⟩ := riem b' hb'
  obtain ⟨hu₀, hpt, hex⟩ := GlobalTheory.T.uniformization_period_lattice_change hMink E H D l Xo σ g ty U i (P b) (P b') gam h₀ (hP b hb)
    (hP b' hb') hiso hhalf hA hPP
  have hθ : ∀ b ∈ B, (fun z => thetaChar (τ b) c₁ c₂ (h b *ᵥ z)) ≠ 0 := fun b hb hz => by
    obtain ⟨hu, hτ⟩ := riem b hb
    obtain ⟨n, rfl⟩ := ThetaRatio.exists_eq_halfVec h₁
    obtain ⟨n', rfl⟩ := ThetaRatio.exists_eq_halfVec h₂
    refine theta_ne_zero hτ (halfVec n) (halfVec n') (funext fun w => ?_)
    have := congrFun hz ((h b)⁻¹ *ᵥ w)
    simp only [ThetaRatio.thetaChar_ofRealVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
      Matrix.one_mulVec] at this
    exact this
  obtain ⟨ρ, κ, hρd, hρ0, hρ1, hκ, hrel, hfr⟩ := thetaFrame_ratio hT E H D l Xo σ g ty U i m B P
    (fun b z => thetaChar (τ b) c₁ c₂ (h b *ᵥ z)) fr hP hd hne hc h0 hs b hb b' hb' h₀
    (hθ b hb) (hθ b' hb') hu₀ hpt hex
  have hfull := LevelHalf.trivial_mod_of_trivial_on_half E H (U.Di i) l gam hiso hhalf
  have hiso' : ∀ a b, (U.Di i).EF (gam.symm a) (gam.symm b) = (U.Di i).EF a b := fun a b => by
    rw [← hiso, gam.apply_symm_apply, gam.apply_symm_apply]
  have hfull' : ∀ a, ∃ e, gam.symm a = a + l.M • e := fun a => by
    obtain ⟨e, he⟩ := hfull (gam.symm a)
    rw [gam.apply_symm_apply] at he
    refine ⟨-e, ?_⟩
    rw [smul_neg]
    exact eq_add_neg_of_add_eq he.symm
  let N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
    Matrix.of fun u v => bas.symm (gam.symm (bas (Pi.single v 1))) u
  obtain ⟨h8, hdet⟩ := AdaptedDet.blocks_det_mod_eight E H (U.Di i) g l.M bas gam.symm N hw
    l.three_le hiso' hfull' (fun _ _ => rfl)
  have hcomp : ∀ a, (h b' * h₀) *ᵥ P b (gam.symm a) = h b' *ᵥ P b' a := fun a => by
    rw [← Matrix.mulVec_mulVec, ← hPP, gam.apply_symm_apply]
  obtain ⟨ga, hga, hgae, hτe, hhe, hde⟩ := PeriodChange.period_change E H (U.Di i) g bas gam.symm N
    (P b) ((P b).comp gam.symm.toLinearMap.toAddMonoidHom) (h b) (h b' * h₀) (τ b) (τ b') hbas hiso'
    (fun _ _ => rfl) (fun _ => rfl) (hn b hb)
    (fun k => ⟨(hcomp _).trans (hn b' hb' k).1, (hcomp _).trans (hn b' hb' k).2⟩) hτ hτ' hu
  have h8ga : ∀ i j, (8 : ℤ) ∣ ga (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ ga (Sum.inr i) (Sum.inl j) :=
    fun i j => by
      rw [hgae]
      exact h8 j i
  have hχ : ((ZMod.χ₄ ((ga.toBlocks₂₂.det : ℤ) : ZMod 4) : ℤ) : ℂ) = 1 := by
    have e : ga.toBlocks₂₂.det = N.toBlocks₁₁.det := by
      rw [hgae, Matrix.toBlocks_fromBlocks₂₂, Matrix.det_transpose]
    have e' : ((ga.toBlocks₂₂.det : ℤ) : ZMod 4) = 1 := by
      have h4 : ((4 : ℕ) : ℤ) ∣ N.toBlocks₁₁.det - 1 := Dvd.dvd.trans (by norm_num) hdet
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).2 h4
      rw [Int.cast_sub, Int.cast_one, sub_eq_zero] at this
      rw [e, this]
    rw [e', map_one, Int.cast_one]
  have hl := hlaw g ga hga h8ga
  rw [hχ] at hl
  have dl : Differentiable ℂ (fun w : Fin g → ℂ => (h b)⁻¹ *ᵥ w) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (h b)⁻¹)).differentiable
  have hκ2 := ThetaRatio.ratio_sq_eq_det_jAut g ga hga h8ga hl c₁ c₂ h₁ h₂ (τ b) hτ
    (fun w => ρ ((h b)⁻¹ *ᵥ w)) κ (hρd.comp dl) (fun w => hρ0 _)
    (by simp only [Matrix.mulVec_zero, hρ1]) hκ (fun w => by
      have := hrel ((h b)⁻¹ *ᵥ w)
      simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc] at this
      rw [hhe, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, hτe] at this
      exact this)
  have e := hrel z
  rw [hfr j z hz, hde, Matrix.det_mul, ← hκ2, ← mul_assoc (thetaChar (τ b') c₁ c₂ _), e]
  ring

end GlobalTheory
end
end

section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory

theorem thetaFrame_det_mul_sq_invariant_uncond : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((U.Di i).La →+ (Fin g → ℂ))) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.Di i).La) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ), (∀ b ∈ B, IsPeriod (U.Di i) ty (P b)) → (∀ a a', (U.Di i).EF (bas a) (bas a') = -omegaStd a a') → (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inl k) 1) = bas (Pi.single (Sum.inl k) 1) + (8 : ℕ) • e) ∧ (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inr k) 1) = (8 : ℕ) • e) → (∀ b ∈ B, (∀ k, h b *ᵥ P b (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h b *ᵥ P b (bas (Pi.single (Sum.inr k) 1)) = τ b *ᵥ Pi.single k 1)) → (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → (∀ j, DifferentiableOn ℂ (fr j) {bz | bz.1 ∈ B ∧ ⊤ ≤ (U.ex i (P bz.1) bz.2).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) → (∀ j b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, z) ≠ 0) → (∀ j j' b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') → fr j (b, z) = valAt' (U.ex i (P b) z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' (b, z)) → (∀ j b, b ∈ B → ⊤ ≤ (U.ex i (P b) 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, 0) = valAt' (U.u i (P b)) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) → (∀ b ∈ B, ∃ s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).Sec, ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (U.u i (P b))), x ≫ pullback.fst _ _ = (U.ex i (P b) z).left → x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).U (fun _ => j)) (s.f (fun _ => j)) = thetaChar (τ b) c₁ c₂ (h b *ᵥ z) * fr j (b, z)) → ∀ b ∈ B, ∀ b' ∈ B, ∀ (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di i).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), (∀ a b, (U.Di i).EF (gam a) (gam b) = (U.Di i).EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (U.Di i).La), ∃ e, gam a = a + l.M • e) → (∀ a, ∃ e, gam a = a + l.A • e) → (∀ a, P b' (gam a) = h₀ *ᵥ P b a) → ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → (h b).det * (thetaChar (τ b) c₁ c₂ (h b *ᵥ z) * fr j (b, z)) ^ 2 = (h b').det * h₀.det * (thetaChar (τ b') c₁ c₂ (h b' *ᵥ (h₀ *ᵥ z)) * fr j (b', h₀ *ᵥ z)) ^ 2 :=
  thetaFrame_det_mul_sq_invariant latMinkowski abelianSchemeLaws_all.2.secTwist
    theta_sq_transform_level_eight

end GlobalTheory
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.ThetaPtChg

theorem exists_chart_point {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Sp ℂ ⟶ X) :
    ∃ j, ⊤ ≤ p ⁻¹ᵁ L.U j := by
  let q : Sp ℂ := IsLocalRing.closedPoint ℂ
  have hq : p q ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hq
  refine ⟨j, fun q' _ => ?_⟩
  have : q' = q := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  rw [this]
  exact hj

theorem val_of_secBC (hS : Out.SecTwistSt) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    (x x' : Sp ℂ ⟶ Xo.X) (hx : x' = x) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (a : ℂ)
    (h : SecBC (RingHom.id ℂ) a x x' s s') (p : Over.mk x ⟶ Xo.univ.t.G) (j : Xo.univ.t.PP.L.ι) (v v' : ℂ)
    (hv : ∀ pt : Sp ℂ ⟶ Gx x, pt ≫ gxFst x = p.left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) →
      valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = v)
    (hv' : ∀ pt : Sp ℂ ⟶ Gx x', pt ≫ gxFst x' = p.left → pt ≫ gxSnd x' = 𝟙 (Sp ℂ) →
      valAt' pt ((PPx x').U (fun _ => j)) (s'.f (fun _ => j)) = v') : v' = a * v := by
  subst hx
  have hid : x' = spMap (RingHom.id ℂ) ≫ x' := by
    simp [spMap]
  have h2 := ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo ℂ ℂ ℂ (RingHom.id ℂ) (RingHom.id ℂ) x' x' x' hid hid).2.1
    a s s').1 h
  let pt : Sp ℂ ⟶ Gx x' := (CartesianMonoidalCategory.lift (𝟙 (Over.mk x')) p).left
  have e1 : pt ≫ gxFst x' = p.left := by
    have := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 (Over.mk x')) p)
    exact this
  have e2 : pt ≫ gxSnd x' = 𝟙 (Sp ℂ) := by
    have := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 (Over.mk x')) p)
    exact this
  rw [← hv pt e1 e2, ← hv' pt e1 e2]
  exact (congrArg (valAt' pt ((PPx x').U (fun _ => j))) (h2 (fun _ => j))).trans
    ((GlobalTheory.sec_values_complex_fibre hS E H Dw l Xo x' s).1 a _ pt e2)

theorem thetaPt_change : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ b' ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ κ' : ℂ) (y y' : FrPt Xo c (CAt σ)) (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), IsThetaPt T b κ y → IsThetaPt T b' κ' y' → ((∀ a b, (F.Di k).EF (gam a) (gam b) = (F.Di k).EF a b) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ v, gam a = a + l.M • v) ∧ (∀ a, ∃ v, gam a = a + l.A • v)) → (∀ a, T.Pf (T.co b') (gam a) = h₀ *ᵥ T.Pf (T.co b) a) → y'.x = y.x ∧ (∀ τ i, IsDerivAt0 (fun z => (F.ex k (T.Pf (T.co b)) z).left) (h₀⁻¹ *ᵥ Pi.single (e.symm ⟨τ, i⟩) 1) (y'.u τ i)) ∧ ∃ t₀ : (CAt σ)ˣ, SecBC (RingHom.id (CAt σ)) (t₀ : CAt σ) y.x y'.x y.s y'.s ∧ toC (t₀ : CAt σ) ^ 2 * (κ ^ 2 * (T.h b').det * h₀.det) = κ' ^ 2 * (T.h b).det := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M k T b hb b' hb' κ κ' y y' gam h₀ hy hy' hgam hP
  obtain ⟨hg1, hg2, hg3⟩ := hgam
  have hp := T.isPer _ hb
  have hp' := T.isPer _ hb'
  obtain ⟨hdet, hu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F k
    (T.Pf (T.co b)) (T.Pf (T.co b')) gam h₀ hp hp' hg1 hg2 hg3 hP
  have hx : y'.x = y.x := hy'.1.trans (hu.symm.trans hy.1.symm)
  refine ⟨hx, fun τ i => ?_, ?_⟩
  · refine (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F k (T.Pf (T.co b)) hp k (T.Pf (T.co b')) (Matrix.mulVecLin h₀) hp'
      hex _ _).2 ?_
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    exact hy'.2.1 τ i
  obtain ⟨gm, a, -, -, -, hbc⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) y y').1 hx
  refine ⟨a, hbc, ?_⟩
  obtain ⟨hhd, hsym, hpos, -⟩ := T.norm b hb
  obtain ⟨-, w, hw⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g T.c₁ T.c₂ T.half₁ T.half₂).1 _ hsym hpos
  obtain ⟨z, hz⟩ : ∃ z, T.h b *ᵥ z = w :=
    ⟨(T.h b)⁻¹ *ᵥ w, by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hhd, Matrix.one_mulVec]⟩
  obtain ⟨j, hj⟩ := exists_chart_point Xo.univ.t.PP.isLB (F.ex k (T.Pf (T.co b)) z).left
  have hmult := GlobalTheory.thetaFrame_det_mul_sq_invariant_uncond E H Dw l Xo _ g _ F k T.m (T.co ⁻¹' (M.X k).dom)
    (fun b => T.Pf (T.co b)) T.bas T.h T.ta T.c₁ T.c₂ T.fr (fun b hb => T.isPer _ hb) T.sympl T.adapt
    (fun b hb => (T.norm b hb).2.2.2) T.half₁ T.half₂ T.fr_hol T.fr_ne T.fr_coc T.fr_rig T.fr_sec
    b hb b' hb' gam h₀ hg1 hg2 hg3 hP j z hj
  have hne : thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z) * T.fr j (b, z) ≠ 0 :=
    mul_ne_zero (by rw [hz]; exact hw) (T.fr_ne j b z hb hj)
  have hw0 : (F.ex k (T.Pf (T.co b)) z).left ≫ Xo.univ.t.G.hom = (y.x : Sp ℂ ⟶ Xo.X) :=
    (Over.w (F.ex k (T.Pf (T.co b)) z)).trans hy.1.symm
  have hval := val_of_secBC hS (Xo := Xo) y.x y'.x hx y.s y'.s (toC (a : CAt σ)) hbc
    (Over.homMk (F.ex k (T.Pf (T.co b)) z).left hw0) j _ _
    (fun pt h1 h2 => hy.2.2 j z pt h1 h2 hj)
    (fun pt h1 h2 => hy'.2.2 j (h₀ *ᵥ z) pt (h1.trans (hex z).symm) h2 (by rw [hex z]; exact hj))
  apply mul_right_cancel₀ (pow_ne_zero 2 hne)
  rw [mul_assoc κ', mul_assoc κ] at hval
  generalize thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z) * T.fr j (b, z) = S at *
  generalize thetaChar (T.ta b') T.c₁ T.c₂ (T.h b' *ᵥ (h₀ *ᵥ z)) * T.fr j (b', h₀ *ᵥ z) = S' at *
  linear_combination (-κ' ^ 2) * hmult - (T.h b').det * h₀.det * (κ' * S' + toC (a : CAt σ) * (κ * S)) * hval

end GlobalTheory.ThetaPtChg
end
end
