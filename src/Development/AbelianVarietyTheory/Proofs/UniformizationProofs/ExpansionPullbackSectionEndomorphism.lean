import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DescentPowerIsoEndomorphismAbelianPartUniformizaStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PGAppEqZeroIff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdNeg
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValueAtUnitSection
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import BuildAid.ForwardExisting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.PullInt

theorem oneLeft {S : Scheme.{0}} {X M : Over S} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ eSec M := by
  have h : (toUnit X).left = X.hom := by simpa using Over.w (toUnit X)
  rw [Hom.one_def, Over.comp_left, h]; rfl

theorem exists_zpow {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (a b : ℕ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun i => ((a : ℤ) - b) * ε i)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t' r z J = val t r z J ^ ((a : ℤ) - b) := by
  obtain ⟨t', h₁, h₂⟩ := exists_gen hL (φ' := φ) (ε' := fun i => ((a : ℤ) - b) * ε i) (fun U _ h => by
      rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [← zpow_add]; congr 1; ring)
    (LB.mulGen L _ _ _ _ (GeneratorPullback.powGen L φ ε t a) (LB.invGen L _ _ (GeneratorPullback.powGen L φ ε t b)))
    (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ ht a) (invGen_isGen _ _ _ _ (powGen_isGen _ _ _ _ ht b)))
  refine ⟨t', h₁, fun Z r z J hJ => (h₂ Z r z J hJ).trans ((val_mul hJ _ _ _).trans ?_)⟩
  rw [val_inv, zpow_sub, zpow_natCast, zpow_natCast]
  exact congrArg₂ (fun u v => u * v⁻¹) (map_pow _ _ _) (map_pow _ _ _)

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem rig_val (e : ℕ) {Z : Scheme.{0}} (s : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) {z : Z}
    {N : (Z ⟶ G.left) → U.LG.L.ι} {J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    (hN : Good U.LG.L z N) (hJ : Good D.toPre.P.L z J) (o : Z ⟶ (thickObj R I e G).left)
    (ho : o = s ≫ eSec (thickObj R I e G)) :
    rigV D.toPre (s ≫ thick R I e) z J =
      wv U e o z (J (o ≫ pGl U e)) (N (o ≫ fGl I G e)) *
        val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (s ≫ thick R I e) z N := by
  subst ho
  have hp : (s ≫ eSec (thickObj R I e G)) ≫ pGl U e = (s ≫ thick R I e) ≫ eSec D.toPre.P.A :=
    (Category.assoc _ _ _).trans ((congrArg (s ≫ ·) (UnitValue.eSec_pGl U e)).trans
      (Category.assoc _ _ _).symm)
  have hf : (s ≫ eSec (thickObj R I e G)) ≫ fGl I G e = (s ≫ thick R I e) ≫ eSec G :=
    (Category.assoc _ _ _).trans ((congrArg (s ≫ ·) (UnitValue.eSec_fGl (G := G) e)).trans
      (Category.assoc _ _ _).symm)
  rw [hp, hf, rigV]
  obtain ⟨j, hj⟩ : ∃ j, J ((s ≫ thick R I e) ≫ eSec D.toPre.P.A) = j := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, N ((s ≫ thick R I e) ≫ eSec G) = k := ⟨_, rfl⟩
  have mj : ((s ≫ thick R I e) ≫ eSec D.toPre.P.A) z ∈ D.toPre.P.L.U j := hj ▸ hJ _
  have mk : ((s ≫ thick R I e) ≫ eSec G) z ∈ U.LG.L.U k := hk ▸ hN _
  rw [val_of _ _ z J (fun _ => j) (fun _ => hj), val_of _ _ z N (fun _ => k) (fun _ => hk), hj, hk]
  have m₁ : s z ∈ eSec (thickObj R I e G) ⁻¹ᵁ
      ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => j) ⊓ (U.LG.L.pull (fstG I e G).left).U (fun _ => k)) :=
    ⟨mem_pull.2 ((congrArg (fun q => q z ∈ D.toPre.P.L.U j) hp).mpr mj),
      mem_pull.2 ((congrArg (fun q => q z ∈ U.LG.L.U k) hf).mpr mk)⟩
  have m₂ : s z ∈ thick R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => k) := mem_pull.2 mk
  have m₃ : s z ∈ thick R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => j) := mem_pull.2 mj
  have W := congrArg (gm s z _) (U.w_rig e (fun _ => j, fun _ => k) (_ ⊓ _ ⊓ _) (inf_le_left.trans inf_le_left)
    (inf_le_left.trans inf_le_right) inf_le_right)
  exact ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₃ _)).symm.trans (W.symm.trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₁ _))
      ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₂ _)))))

variable {U} (E : EndU U)

theorem act_fGl (e : ℕ) :
    ((Over.pullback (thick R I e)).map E.aG).left ≫ fGl I G e = fGl I G e ≫ E.aG.left :=
  pullback.lift_fst _ _ _

theorem act_pGl (e : ℕ) :
    ((Over.pullback (thick R I e)).map E.aG).left ≫ pGl U e = pGl U e ≫ E.aB.left := by
  have h1 := congrArg (fun f => f.left) (E.q_lin e)
  simp only [Over.comp_left] at h1
  simp only [GtCoord.pG, Over.comp_left, Over.map_map_left, DegPre.prBe, Over.homMk_left]
  rw [← Category.assoc, h1, Category.assoc, Category.assoc]
  congr 1
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

theorem exists_secG (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left]
    ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])) (hβ : β.IsGen) (σ : H0 U.LG.L k) :
    ∃ σ' : H0 U.LG.L k', ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good U.LG.L z J →
      sval σ' r z J = sval σ (r ≫ E.aG.left) z J * (val β r z J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G)
        (ε := fun _ => 1) U.LG.rig (r ≫ G.hom) z J ^ ((k' : ℤ) - k)).val := by
  obtain ⟨ρ, hρ, vρ⟩ := exists_zpow U.LG.isLB (LB.pullGen U.LG.L (fun _ : PUnit => eSec G) (fun _ => 1) U.LG.rig G.hom)
    (pullGen_isGen _ _ _ _ U.LG.rigGen _) k' k
  obtain ⟨s, hs⟩ := exists_sec U.LG.isLB (φ' := fun _ : Fin 1 => 𝟙 G.left) (ε' := fun _ => (k' : ℤ)) (fun V _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_three, Matrix.cons_val, Category.comp_id,
        Fintype.prod_unique, oneLeft]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
    (pullMulSec σ E.aG.left (LB.mulGen U.LG.L _ _ _ _ β ρ) (mulGen_isGen _ _ _ _ _ _ _ hβ hρ))
  refine ⟨s, fun Z r z J hJ => (hs Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ r z hJ).trans ?_)⟩
  rw [val_mul hJ, vρ Z r z J hJ, val_pull hJ]

theorem exists_secB (k' k : ℕ) (κ : LB.Gen (kapLB D.toPre E.aB k' k)) (hκ : κ.IsGen) (χ : D.toPre.X)
    (f : D.toPre.SecB k χ) :
    ∃ g : D.toPre.SecB k' (E.h χ), ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
      sval g r z J = sval f (r ≫ E.aB.left) z J * (val κ r z J *
        rigV D.toPre (r ≫ D.toPre.P.A.hom) z J ^ ((k' : ℤ) - k) * val (E.u χ) r z J).val := by
  obtain ⟨ρ, hρ, vρ⟩ := exists_zpow D.toPre.P.isLB (LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A)
    (fun _ => 1) D.toPre.rig D.toPre.P.A.hom) (pullGen_isGen _ _ _ _ D.toPre.rig_gen _) k' k
  obtain ⟨s, hs⟩ := exists_sec D.toPre.P.isLB (φ' := D.toPre.famφB (E.h χ)) (ε' := DegPre.famε k') (fun V _ h => by
      have p₁ := SectionScalarValuation.prod_famB D.toPre E.aB χ k h
      have p₂ := SectionScalarValuation.prod_famB D.toPre (𝟙 _) (E.h χ) k' h
      have e₃ : ∀ i, Over.Hom.left (𝟙 D.toPre.P.A) ≫ D.toPre.famφB (E.h χ) i = D.toPre.famφB (E.h χ) i :=
        fun i => by simp
      simp only [e₃] at p₂
      have p₃ : ∏ i, h (D.toPre.Oφ (𝟙 _) (E.h χ) i) ^ Oε i =
          h (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre _ (E.h χ)).left ^ (1 : ℤ) * h (SectionScalarValuation.cQ D.toPre _ (E.h χ)).left ^ (-1 : ℤ) *
            h (Over.Hom.left (𝟙 D.toPre.P.A)) ^ (-1 : ℤ) * h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left ^ (1 : ℤ) := by
        rw [Fin.prod_univ_four]; rfl
      have p₄ : ∏ i, h (D.toPre.Oφ E.aB χ i) ^ Oinvε i =
          h (E.aB * SectionScalarValuation.cQ D.toPre _ χ).left ^ (-1 : ℤ) * h (SectionScalarValuation.cQ D.toPre _ χ).left ^ (1 : ℤ) *
            h E.aB.left ^ (1 : ℤ) * h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left ^ (-1 : ℤ) := by
        rw [Fin.prod_univ_four]; rfl
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [p₁, p₂, p₃, p₄]
      simp only [Fin.prod_univ_three, Matrix.cons_val, Fintype.prod_unique, oneLeft, Over.id_left]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
    (pullMulSec f E.aB.left (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _ κ ρ) (E.u χ))
      (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hκ hρ) (E.u_norm χ).1))
  refine ⟨s, fun Z r z J hJ => (hs Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ r z hJ).trans ?_)⟩
  rw [val_mul hJ, val_mul hJ, vρ Z r z J hJ, val_pull hJ, rigV]

theorem alg {Γ : Type} [CommRing Γ] (k' k : ℕ) (wx wa wo β κ ρG ρB : Γˣ) (s : Γ)
    (h₁ : κ = β * wx ^ (k' : ℤ) * wa ^ (-(k : ℤ)) * wo ^ ((k : ℤ) - k')) (h₂ : ρB = wo * ρG) :
    (wx ^ k').val * (s * (β * ρG ^ ((k' : ℤ) - k)).val) = (κ * ρB ^ ((k' : ℤ) - k)).val * ((wa ^ k).val * s) := by
  have : wx ^ k' * (β * ρG ^ ((k' : ℤ) - k)) = κ * ρB ^ ((k' : ℤ) - k) * wa ^ k := by
    rw [h₁, h₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_pow]
    module
  rw [mul_comm s, ← _root_.mul_assoc, ← Units.val_mul, this, Units.val_mul, _root_.mul_assoc]

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (E : EndU U), Function.Injective E.h → ∀ (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left] ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])), β.IsGen → ∀ κ : LB.Gen (kapLB D.toPre E.aB k' k), κ.IsGen → (∀ (e : ℕ) (Z : Scheme.{0}) (x o : Z ⟶ (thickObj R I e G).left) (z : Z) (JG) (J), Good U.LG.L z JG → Good D.toPre.P.L z J → o = x ≫ (1 : thickObj R I e G ⟶ thickObj R I e G).left → ∀ W : (Z ⟶ (thickObj R I e G).left) → (Z.presheaf.stalk z)ˣ, (∀ y, W y = gw (U.w e) y z (J (y ≫ (U.gt e).pG.left)) (fun _ => JG (y ≫ (fstG I e G).left))) → val κ (x ≫ (U.gt e).pG.left) z J = val β (x ≫ (fstG I e G).left) z JG * W x ^ (k' : ℤ) * W (x ≫ ((Over.pullback (thick R I e)).map E.aG).left) ^ (-(k : ℤ)) * W o ^ ((k : ℤ) - k')) → ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ f) → ∃ (σ' : H0 U.LG.L k') (f' : ∀ α : D.toPre.X, D.toPre.SecB k' α), (∀ e, U.ExpandsAt e k' σ' f') ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good U.LG.L z J → sval σ' r z J = sval σ (r ≫ E.aG.left) z J * (val β r z J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (r ≫ G.hom) z J ^ ((k' : ℤ) - k)).val) ∧ (∀ (χ : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (f' (E.h χ)) r z J = sval (f χ) (r ≫ E.aB.left) z J * (val κ r z J * rigV D.toPre (r ≫ D.toPre.P.A.hom) z J ^ ((k' : ℤ) - k) * val (E.u χ) r z J).val) ∧ ∀ b, b ∉ Set.range E.h → ∀ j, (f' b).f j = 0 := by
  classical
  intro R _ _ I D A G _ _ U E hinj k' k β hβ κ hκ H σ f hf
  obtain ⟨σ', hσ'⟩ := exists_secG E k' k β hβ σ
  have key : ∀ b, ∃ s : D.toPre.SecB k' b, (∀ χ, b = E.h χ → ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J),
      Good D.toPre.P.L z J → sval s r z J = sval (f χ) (r ≫ E.aB.left) z J * (val κ r z J *
        rigV D.toPre (r ≫ D.toPre.P.A.hom) z J ^ ((k' : ℤ) - k) * val (E.u χ) r z J).val) ∧
      (b ∉ Set.range E.h → ∀ j, s.f j = 0) := by
    intro b
    by_cases hb : b ∈ Set.range E.h
    · obtain ⟨χ, rfl⟩ := hb
      obtain ⟨g, hg⟩ := exists_secB E k' k κ hκ χ (f χ)
      refine ⟨g, fun χ' e => ?_, fun h => (h ⟨χ, rfl⟩).elim⟩
      obtain rfl := hinj e
      exact hg
    · exact ⟨SecOps.secZero, fun χ e => (hb ⟨χ, e.symm⟩).elim, fun _ _ => rfl⟩
  choose f' hf₁ hf₂ using key
  refine ⟨σ', f', fun e => ?_, hσ', fun χ => hf₁ _ χ rfl, hf₂⟩
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f (hf e)
  refine expandsAt_of_val U e k' σ' f' (S.image E.h) fun y J hJ => ?_
  obtain ⟨b₁, b₂⟩ := hS _ ((Over.pullback (thick R I e)).map E.aG).left y J hJ
  simp only [act_pGl E e, act_fGl E e] at b₁
  refine ⟨fun α hα => ?_, fun jL hL => ?_⟩
  · by_cases hb : α ∈ Set.range E.h
    · obtain ⟨χ, rfl⟩ := hb
      rw [hf₁ _ χ rfl _ _ y J hJ, b₁ χ fun h => hα (Finset.mem_image_of_mem _ h), zero_mul]
    · exact (congrArg (gs _ y _) (hf₂ α hb _)).trans (gs_zero _ y _ (hJ.mem _ _))
  · obtain ⟨JG, hJG, eJ⟩ := exists_good U.LG.L U.LG.isLB y (fun _ : Unit => fGl I G e) (fun _ => jL)
      (fun _ _ _ => rfl) (fun _ => hL)
    obtain rfl : JG (fGl I G e) = jL := eJ ()
    have c₁ := b₂ _ (hJG (((Over.pullback (thick R I e)).map E.aG).left ≫ fGl I G e))
    have c₂ := H e _ (𝟙 _) _ y JG J hJG hJ rfl
      (fun x => wv U e x y (J (x ≫ pGl U e)) (JG (x ≫ fGl I G e))) (fun _ => rfl)
    have c₃ := rig_val U e (thickObj R I e G).hom hJG hJ _ oneLeft
    have c₄ := hσ' _ (fGl I G e) y JG hJG
    have sv_eq : ∀ (n : ℕ) (τ : H0 U.LG.L n) (q : (thickObj R I e G).left ⟶ G.left),
        sval τ q y JG = sv U n τ q y (JG q) := fun n τ q =>
      sval_of τ q y JG (fun _ => JG q) (fun _ => by rw [Category.comp_id])
    have w₁ : fGl I G e ≫ G.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (fstG I e G)
    have w₂ : pGl U e ≫ D.toPre.P.A.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (U.gt e).pG
    simp only [Category.id_comp] at c₂
    rw [sv_eq, sv_eq, w₁, ← act_fGl E e] at c₄
    rw [c₄, Finset.sum_image fun _ _ _ _ h => hinj h]
    refine (alg k' k _ _ _ _ _ _ _ _ c₂ c₃).trans ?_
    rw [c₁, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    have t := E.t_lin e χ _ (𝟙 _) y J hJ
    simp only [Category.id_comp] at t
    rw [hf₁ _ χ rfl _ _ y J hJ, w₂, act_pGl E e]
    refine (congrArg (fun u : ((thickObj R I e G).left.presheaf.stalk y)ˣ => _ * (_ * u.val)) t).trans ?_
    simp only [Units.val_mul]
    ring

end GlobalTheory.PullInt
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_section_endomorphism_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (E : EndU U), Function.Injective E.h → ∀ (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left] ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])), β.IsGen → ∀ κ : LB.Gen (kapLB D.toPre E.aB k' k), κ.IsGen → (∀ (e : ℕ) (Z : Scheme.{0}) (x o : Z ⟶ (thickObj R I e G).left) (z : Z) (JG) (J), Good U.LG.L z JG → Good D.toPre.P.L z J → o = x ≫ (1 : thickObj R I e G ⟶ thickObj R I e G).left → ∀ W : (Z ⟶ (thickObj R I e G).left) → (Z.presheaf.stalk z)ˣ, (∀ y, W y = gw (U.w e) y z (J (y ≫ (U.gt e).pG.left)) (fun _ => JG (y ≫ (fstG I e G).left))) → val κ (x ≫ (U.gt e).pG.left) z J = val β (x ≫ (fstG I e G).left) z JG * W x ^ (k' : ℤ) * W (x ≫ ((Over.pullback (thick R I e)).map E.aG).left) ^ (-(k : ℤ)) * W o ^ ((k : ℤ) - k')) → ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ f) → ∃ (σ' : H0 U.LG.L k') (f' : ∀ α : D.toPre.X, D.toPre.SecB k' α), (∀ e, U.ExpandsAt e k' σ' f') ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good U.LG.L z J → sval σ' r z J = sval σ (r ≫ E.aG.left) z J * (val β r z J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (r ≫ G.hom) z J ^ ((k' : ℤ) - k)).val) ∧ (∀ (χ : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (f' (E.h χ)) r z J = sval (f χ) (r ≫ E.aB.left) z J * (val κ r z J * rigV D.toPre (r ≫ D.toPre.P.A.hom) z J ^ ((k' : ℤ) - k) * val (E.u χ) r z J).val) ∧ ∀ b, b ∉ Set.range E.h → ∀ j, (f' b).f j = 0 := by
  atlas_forward_decl GlobalTheory.PullInt.main
end

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.TwistCompare

section Abstract

variable {X N Y V S₀ Z : Scheme.{0}} {L : LB X} {M : LB N} {c₀ : Y ⟶ X} {q : Y ⟶ N}

def wv (w : LB.Iso (L.pull c₀) (M.pull q)) (f : Z ⟶ Y) (z : Z) (JL : (Z ⟶ X) → L.ι) (JM : (Z ⟶ N) → M.ι) :
    (Z.presheaf.stalk z)ˣ := GlobalTheory.FieldBaseChange.isoVal w f z (JM (f ≫ q)) (JL (f ≫ c₀))

theorem val_through_iso (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso (L.pull c₀) (M.pull q)} (hw : w.IsGen)
    (n : X ⟶ Y) (hn : n ≫ c₀ = 𝟙 X) (s m : V ⟶ X) (a : N ⟶ N) (hc : m ≫ n ≫ q = (s ≫ n ≫ q) ≫ a) (k' k : ℤ)
    (b : LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 N, a] ![k', -k])) (hb : b.IsGen)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![s, m] ![k', -k])) (hα : α.IsGen)
    (p : V ⟶ S₀) (e : S₀ ⟶ V) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    (h₀ : ∀ y JL JM, Good L y JL → Good M y JM → val b (e ≫ s ≫ n ≫ q) y JM =
      wv w (e ≫ s ≫ n) y JL JM ^ k' * wv w (e ≫ m ≫ n) y JL JM ^ (-k) * val α e y JL)
    (r : Z ⟶ V) (z : Z) (JL) (JM) (hJL : Good L z JL) (hJM : Good M z JM) :
    val b (r ≫ s ≫ n ≫ q) z JM =
      wv w (r ≫ s ≫ n) z JL JM ^ k' * wv w (r ≫ m ≫ n) z JL JM ^ (-k) * val α r z JL := by
  obtain ⟨u, hu, hv⟩ := GlobalTheory.ThetaBaseChange.exists_unpull hw n hn rfl
  have hc' : ∀ κ, (![s, m] : Fin 2 → _) κ ≫ n ≫ q = (s ≫ n ≫ q) ≫ (![𝟙 N, a] : Fin 2 → _) κ := fun κ => by
    fin_cases κ
    exacts [(Category.comp_id _).symm, hc]
  obtain ⟨α', hα', hm⟩ := H1.exists_gen_move hM hL u hu ![𝟙 N, a] ![s, m] ![k', -k] (s ≫ n ≫ q) hc' b hb
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ V) (z : Z) (JL) (JM), Good L z JL → Good M z JM →
      val b (r ≫ s ≫ n ≫ q) z JM =
        wv w (r ≫ s ≫ n) z JL JM ^ k' * wv w (r ≫ m ≫ n) z JL JM ^ (-k) * val α' r z JL := by
    intro Z r z JL JM hJL hJM
    have g : ∀ f : V ⟶ X, gw u (r ≫ f) z (JM (r ≫ f ≫ n ≫ q)) (JL (r ≫ f)) = wv w (r ≫ f ≫ n) z JL JM := fun f => by
      rw [hv Z (r ≫ f) z _ _ (hJM (r ≫ f ≫ n ≫ q)) (hJL (r ≫ f)), wv]
      simp only [Category.assoc, hn, Category.comp_id]
    have := hm Z r z (fun κ => JM (r ≫ (![s, m] : Fin 2 → _) κ ≫ n ≫ q)) (fun κ => JL (r ≫ (![s, m] : Fin 2 → _) κ))
      (fun κ => hJM (r ≫ (![s, m] : Fin 2 → _) κ ≫ n ≫ q)) (fun κ => hJL (r ≫ (![s, m] : Fin 2 → _) κ))
    rw [Fin.prod_univ_two, g, g] at this
    rw [val_of b _ z JM (fun κ => JM (r ≫ (![s, m] : Fin 2 → _) κ ≫ n ≫ q))
      (fun κ => by rw [hc', Category.assoc])]
    exact this
  rw [key Z r z JL JM hJL hJM]
  refine congrArg _ (gen_unique hL p e he hp hα' hα (fun y J hJ => ?_) Z r z JL hJL)
  choose J' hJ' using fun ψ : S₀ ⟶ N => exists_chart hM (ψ y)
  exact mul_left_cancel ((key _ e y J J' hJ hJ').symm.trans (h₀ y J J' hJ hJ'))

end Abstract

section Rig

variable {S Z : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

abbrev rval (rig : LB.Gen (L.pull (eSec A))) (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    (Z.presheaf.stalk z)ˣ := val (L := L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig r z J

theorem val_rigT {T : Over S} (rig : LB.Gen (L.pull (eSec A))) (k : ℤ) (r : Z ⟶ T.left) {y : Z} {J} (hJ : Good L y J) :
    val (rigT A L rig T k) r y J = rval rig (r ≫ T.hom) y J ^ k := by
  have hy := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res _ y _ hy _).trans ?_))
  exact gm_pull r T.hom y (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (r ≫ T.hom ≫ eSec A)))
    (rigT_le A L _ hy) _

theorem exists_two (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))} (hr : rig.IsGen) (a : A.left ⟶ A.left) (k' k : ℤ)
    (β : LB.Gen (LB.LinComb L (K := Fin 3) ![𝟙 _, a, (1 : A ⟶ A).left] ![k', -k, k - k'])) (hβ : β.IsGen) :
    ∃ b : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 _, a] ![k', -k]), b.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good L z J →
        val b r z J = val β r z J * rval rig (r ≫ A.hom) z J ^ (k' - k) := by
  obtain ⟨b, hb, hv⟩ := exists_gen hL (φ' := ![𝟙 _, a]) (ε' := ![k', -k]) (fun U _ h => by
      have e : (1 : A ⟶ A).left = A.hom ≫ eSec A := rfl
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Fin.prod_univ_three, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val, e]
      rw [_root_.mul_assoc, ← zpow_add, sub_add_sub_cancel, sub_self, zpow_zero, _root_.mul_one])
    (LB.mulGen L _ _ _ _ β (rigT A L rig A (k' - k)))
    (mulGen_isGen _ _ _ _ _ _ _ hβ (GlobalTheory.NormTheta.rigT_isGen hr _))
  exact ⟨b, hb, fun Z r z J hJ => (hv Z r z J hJ).trans ((val_mul hJ _ _ _).trans
    (congrArg _ (val_rigT rig _ r hJ)))⟩

end Rig

theorem alg_origin {M : Type} [CommGroup M] {w r g : M} (k' k : ℤ) (h : w * r = g) :
    1 * g ^ (k' - k) = w ^ k' * w ^ (-k) * r ^ (k' - k) := by
  rw [← h, _root_.one_mul, mul_zpow, ← zpow_add, sub_eq_add_neg]

theorem dualNumber_unit_mul_decomposition {M : Type} [CommRing M] {w w' α b : Mˣ} {v v' t t' : M} {k' k : ℕ}
    (h₁ : v' = (w ^ k').val * t') (h₂ : v = (w' ^ k).val * t) (h₃ : t' = α.val * t)
    (h₄ : b = w ^ (k' : ℤ) * w' ^ (-(k : ℤ)) * α) : v' = v * b.val := by
  have e : w ^ k' * α = w' ^ k * b := by
    rw [h₄, zpow_neg, zpow_natCast, zpow_natCast, mul_comm (w ^ k') _⁻¹, _root_.mul_assoc, mul_inv_cancel_left]
  rw [h₁, h₂, h₃, ← _root_.mul_assoc, ← Units.val_mul, e, Units.val_mul, mul_right_comm]

theorem twist_through_iso : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (E : EndU U) (F : Type) [Field F] [Algebra (FractionRing R) F] (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left] ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])), β.IsGen → LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ β (eSec G)) (LB.oneGen U.LG.L) → ∀ (w₀ : W0 U) (ρ), NormW U w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') (v : U.SecGF F k) (v' : U.SecGF F k'), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) v → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k' (snd (TFK (R := R) F) A.A).left (U.genF F).left t' (UnifPre.gFK (G := G) F) (𝟙 _) v' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ (y : (UnifPre.GF (G := G) F).left) (J), Good U.LG.L y J → sval v' (𝟙 _) y J = sval v (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left y J * (val β (UnifPre.gFK (G := G) F) y J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (UnifPre.gFK (G := G) F ≫ G.hom) y J ^ ((k' : ℤ) - k)).val := by
  intro hG R _ _ I D A G _ _ U E F _ _ k' k β hβ nβ w₀ ρ hw ψ m hm hψ hm' α hα nα t t' v v' H H' HT y J hJ
  have := U.gen_hom
  have := E.homA
  have := E.homG
  obtain ⟨b, hb, vb⟩ := exists_two U.LG.isLB U.LG.rigGen E.aG.left (k' : ℤ) (k : ℤ) β hβ
  have hn : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id]; rfl
  have hn' : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id]; rfl
  have f₁ : ((Over.pullback (jK R)).map E.aG).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G.hom (jK R) ≫ E.aG.left := pullback.lift_fst _ _ _
  have f₂ : E.aA ≫ U.gen.inv = U.gen.inv ≫ (Over.pullback (jK R)).map E.aG := by
    rw [Iso.comp_inv_eq, Category.assoc, E.ext, Iso.inv_hom_id_assoc]
  have f₃ : m.left ≫ U.gen.inv.left =
      ((snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left) ≫ ((Over.pullback (jK R)).map E.aG).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, hm', Category.assoc, f₂, Category.assoc]
  have hc : m.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      ((snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ≫ E.aG.left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) f₃).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) f₁).trans (by simp only [Category.assoc]))))
  have o₀ : eSec A.A ≫ U.gen.inv.left = eSec ((Over.pullback (jK R)).obj G) := by
    rw [← EvalZero.eK_gen U, Category.assoc, hn', Category.comp_id]
  have o₁ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left =
      jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G) := by
    rw [← Category.assoc, ← Over.comp_left, ptSecT, lift_snd, ← o₀]; rfl
  have o₂ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ m.left ≫ U.gen.inv.left =
      jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G) := by
    rw [← Category.assoc, ← Over.comp_left, hm', ptSecT, lift_snd_assoc, MonObj.one_comp, ← o₀]; rfl
  have o₃ : (jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G)) ≫ U.gen.hom.left = jFK (R := R) F ≫ eSec A.A :=
    (Category.assoc _ _ _).trans (congrArg _ (EvalZero.eK_gen U))
  have o₄ : (jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G)) ≫ pullback.fst G.hom (jK R) =
      (jFK (R := R) F ≫ jK R) ≫ eSec G :=
    (Category.assoc _ _ _).trans ((congrArg _ EvalZero.eK_fst).trans (Category.assoc _ _ _).symm)
  have o₅ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫
      pullback.fst G.hom (jK R) = (jFK (R := R) F ≫ jK R) ≫ eSec G :=
    Eq.trans (Eq.trans (by simp only [Category.assoc]) (congrArg (· ≫ _) o₁)) o₄
  have o₆ : ((jFK (R := R) F ≫ jK R) ≫ eSec G) ≫ G.hom = jFK (R := R) F ≫ jK R :=
    (Category.assoc _ _ _).trans ((congrArg _ (Over.w η[G])).trans (Category.comp_id _))
  obtain ⟨JA, hA⟩ : ∃ JA, Good A.L y JA := by
    choose J' hJ' using fun χ : (UnifPre.GF (G := G) F).left ⟶ A.A.left => exists_chart A.isLB (χ y)
    exact ⟨J', hJ'⟩
  have key := val_through_iso A.isLB U.LG.isLB hw.1 U.gen.inv.left hn (snd (TFK (R := R) F) A.A).left m.left
    E.aG.left hc k' k b hb α hα (fst (TFK (R := R) F) A.A).left (ptSecT A.A 1).left
    (by rw [← Over.comp_left, ptSecT, lift_fst]; rfl) (surj_fst hG A.isAb _) (fun z JL JM hL hM => by
      have a₁ := (val_pull hM β (eSec G) (jFK (R := R) F ≫ jK R)).symm.trans
        ((val_corr hM nβ (jFK (R := R) F ≫ jK R)).trans (val_one _))
      have a₂ := (val_pull hL α _ (𝟙 _)).symm.trans ((val_corr hL nα (𝟙 _)).trans (val_rigT ρ _ _ hL))
      rw [Category.id_comp, Category.id_comp] at a₂
      have a₃ : wv w₀ (jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G)) z JL JM * rval ρ (jFK (R := R) F) z JL =
          rval U.LG.rig (jFK (R := R) F ≫ jK R) z JM := by
        refine Units.ext (Eq.trans ?_ (EvalZero.normW_ext U F hw z hL hM))
        rw [← o₃, ← o₄]
        rfl
      rw [o₅, o₁, o₂, vb _ _ z JM hM]
      refine (congrArg₂ (· * ·) a₁ (congrArg (fun x => rval U.LG.rig x z JM ^ ((k' : ℤ) - k)) o₆)).trans ?_
      exact (alg_origin _ _ a₃).trans (congrArg _ a₂.symm)) (U.genF F).left y JA J hA hJ
  have g₁ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left =
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
    rw [← Over.comp_left, ← Over.comp_left, lift_snd_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have g₂ : (U.genF F).left ≫ m.left ≫ U.gen.inv.left = (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left ≫
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, hm', Category.assoc, f₂, lift_snd_assoc, Category.assoc,
      Iso.hom_inv_id_assoc, whiskerLeft_snd]
  have g₃ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      UnifPre.gFK (G := G) F := Eq.trans (by simp only [Category.assoc]) (congrArg (· ≫ _) g₁)
  have g₄ : (U.genF F).left ≫ ψ.left = (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left ≫ (U.genF F).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, hψ, Category.assoc, lift_fst, whiskerLeft_fst]
    · rw [Category.assoc, hm, hm', Category.assoc, lift_snd, lift_snd_assoc, whiskerLeft_snd_assoc, E.ext,
        Category.assoc]
  rw [g₃, g₁, g₂, vb _ _ y J hJ] at key
  have b₁ := GlobalTheory.BoxExpansion.isoRel_val H' (𝟙 _) y hA hJ
  have b₂ := GlobalTheory.BoxExpansion.isoRel_val H (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left y hA hJ
  have b₃ := twist_val HT (U.genF F).left y hA
  rw [Category.comp_id, Category.id_comp, Category.id_comp] at b₁
  rw [Category.comp_id, ← g₄] at b₂
  exact dualNumber_unit_mul_decomposition b₁ b₂ b₃ key

end GlobalTheory.UT.TwistCompare
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endU_twist_of_iso : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (E : EndU U) (F : Type) [Field F] [Algebra (FractionRing R) F] (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left] ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])), β.IsGen → LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ β (eSec G)) (LB.oneGen U.LG.L) → ∀ (w₀ : W0 U) (ρ), NormW U w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') (v : U.SecGF F k) (v' : U.SecGF F k'), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) v → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k' (snd (TFK (R := R) F) A.A).left (U.genF F).left t' (UnifPre.gFK (G := G) F) (𝟙 _) v' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ (y : (UnifPre.GF (G := G) F).left) (J), Good U.LG.L y J → sval v' (𝟙 _) y J = sval v (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left y J * (val β (UnifPre.gFK (G := G) F) y J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (UnifPre.gFK (G := G) F ≫ G.hom) y J ^ ((k' : ℤ) - k)).val := by
  atlas_forward_decl GlobalTheory.UT.TwistCompare.twist_through_iso
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.PullExp
open GlobalTheory.FieldBaseChange

section Uniq

theorem comb_eq_zero {R K F : Type} [CommRing R] [IsDomain R] [Field K] [Field F] [Algebra K F] [Algebra R K]
    [IsFractionRing R K] {V₀ V V' : Type} [AddCommGroup V₀] [Module R V₀] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module F V'] {J : Type} {P₀ : J → Type} [∀ j, AddCommGroup (P₀ j)] [∀ j, Module R (P₀ j)]
    {P P' : Type} [AddCommGroup P] [Module K P] [AddCommGroup P'] [Module F P'] (X : Submodule R (V₀ × ∀ j, P₀ j))
    (j : J) (ρ : V₀ →ₛₗ[algebraMap R K] V) (ρ' : P₀ j →ₛₗ[algebraMap R K] P)
    (a : V →ₛₗ[algebraMap K F] V') (ha : IsExtension a) (b : P →ₛₗ[algebraMap K F] P') (hb : IsExtension b)
    (hX : ∀ x ∈ X, ρ x.1 = 0 → x.2 j = 0) {T : Type} [Fintype T] (c : T → F) (x : T → V₀ × ∀ j, P₀ j)
    (hx : ∀ i, x i ∈ X) (h : ∑ i, c i • a (ρ (x i).1) = 0) : ∑ i, c i • b (ρ' ((x i).2 j)) = 0 := by
  refine hb.eq_of_coord fun ℓ Λ' hΛ' => ?_
  obtain ⟨Λ, hΛ⟩ := ha.coord ℓ
  obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) (fun i => ℓ (c i))
  choose m hm using hr
  have hr : algebraMap R K r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (nonZeroDivisors.coe_ne_zero r)
  have e₁ : ρ (∑ i, m i • x i).1 = algebraMap R K r • Λ (∑ i, c i • a (ρ (x i).1)) := by
    rw [map_sum, Finset.smul_sum, Prod.fst_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΛ, Prod.smul_fst, map_smulₛₗ, hm, smul_smul, Algebra.smul_def]
  have e₂ : ρ' ((∑ i, m i • x i).2 j) = algebraMap R K r • Λ' (∑ i, c i • b (ρ' ((x i).2 j))) := by
    rw [map_sum, Finset.smul_sum, Prod.snd_sum, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΛ', Prod.smul_snd, Pi.smul_apply, map_smulₛₗ, hm, smul_smul, Algebra.smul_def]
  rw [h, map_zero, smul_zero] at e₁
  rw [hX _ (Submodule.sum_mem _ fun i _ => X.smul_mem _ (hx i)) e₁, map_zero] at e₂
  rw [map_zero]
  exact (smul_eq_zero.1 e₂.symm).resolve_left hr

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem term_eq_zero [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) (k : ℕ) (α : D.toPre.X)
    (x : IntSec U k × ∀ α, IntTerm D k α) (hx : x ∈ expansionPairs U k) (h : genericSec U k x.1 = 0) :
    x.2 α = 0 := by
  have := U.smooth
  have : Flat G.hom := inferInstance
  have hd := GlobalTheory.ExtUnique.spec_fractionRing R (FractionRing R)
  have : IsSchemeTheoreticallyDominant (jK R) := hd.2
  have : QuasiCompact (jK R) := hd.1
  have h₀ : ∀ j, x.1.f j = 0 := fun j => by
    refine (pullback.fst G.hom (jK R)).app_injective _ (fn_ext fun y hy => ?_)
    have hy' : y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j :=
      mem_wchart.2 fun i => mem_wchart.1 hy i
    refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ ((congrArg _ (map_zero _)).trans (gs_zero' _ y _ hy)).symm)
    exact (gs_pullFn pullback.condition _ _ (𝟙 _) y hy').symm.trans
      ((congrArg (fun s : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))) =>
        gs (𝟙 _) y (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j) (LB.Sec.f s j)) h).trans (gs_zero' _ y _ hy'))
  have := D.toPre.P.isAb.smooth
  have : GeometricallyConnected D.toPre.P.A.hom := D.toPre.P.isAb.geomConnected
  refine SecOver.ext _ _ ((sec_eq_zero_and_hom_eq_of_thickenings R I hI D.toPre.P.A).1 _
    (linComb_isLB _ D.toPre.P.isLB _ _) (x.2 α) fun e j => ?_)
  exact (GlobalTheory.ExtDiv.pG_app_eq_zero_iff (U.gt e) _ _).1 (WeightPf.weightIndep R I D A G U e k x.1 x.2
    (fun j => (congrArg _ (h₀ j)).trans (map_zero _)) (hx e) α j)

theorem secLin_of_expandsG [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (v : GroupSec U F k) (s : Fam D.toPre F k) (hs : U.ExpandsG F k v s)
    (n : ℕ) (c : Fin n → F) (σ : Fin n → IntSec U k) (f : Fin n → ∀ α : D.toPre.X, IntTerm D k α)
    (hf : ∀ i e, U.ExpandsAt e k (σ i) (f i))
    (hv : GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => (k : ℤ)) v (fun _ : Fin 1 => 𝟙 G.left)
      (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) F)
      (fun i => scal (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (c i))) (α : D.toPre.X) :
    GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (D.toPre.famφB α) (DegPre.famε k)
      (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (c i)) := by
  obtain ⟨n', c', x', hx', e₁, e₂⟩ := (expandsG_iff U F k v s).1 hs
  have d₁ := (secLin_iff U.LG.isLB v σ
    (UnifPre.gFK (G := G) F) c (fun i => extendSec U F k (genericSec U k (σ i))) (fun i y J hJ =>
      (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (σ i) q y J) (Category.assoc _ _ _))))).1 hv
  refine (secLin_iff D.toPre.P.isLB
    (famProj D.toPre F k α s) (fun i => f i α) (DegPre.prB D.toPre F).left c
    (fun i => termPull D.toPre (FractionRing R) F k α (genericTerm D k α (f i α))) (fun i y J hJ =>
      (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (f i α) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·)
          (congrArg (fun q => q.left) (famMap_snd D.toPre (FractionRing R) F)))))))).2 ?_
  have : TopologicalSpace.NoetherianSpace ((Over.pullback (jK R)).obj G).left := noetherianSpace_generic U
  have H := comb_eq_zero (expansionPairs U k) α (genericSec U k) (genericTerm D k α) (extendSec U F k)
    (isExtension_pullOver (isPullback_groupBase F) U.LG.isLB _ _) (termPull D.toPre (FractionRing R) F k α)
    (isExtension_termPull D.toPre _ F k α) (term_eq_zero U hI k α) (Sum.elim c' fun i => -c i)
    (Sum.elim x' fun i => (σ i, f i)) (by rintro (i | i); exacts [hx' i, hf i]) (by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib]
      rw [← e₁, ← d₁, add_neg_cancel])
  rw [Fintype.sum_sum_type] at H
  simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib] at H
  rw [← e₂ α] at H
  exact add_neg_eq_zero.1 H

end Uniq

section Norm
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left}

theorem eSec_comp_one : eSec G ≫ (1 : G ⟶ G).left = eSec G :=
  congrArg (fun q => q.left) ((MonObj.comp_one (M := G) η[G]).trans (by
    show toUnit _ ≫ η[G] = η[G]
    rw [toUnit_unit, Category.id_comp]))

theorem exists_normalised (hL : L.IsLB) (a : G ⟶ G) [IsMonHom a] (k' k : ℤ)
    (β : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 _, a.left] ![k', -k])) (hβ : β.IsGen) :
    ∃ ν : LB.Gen (LB.LinComb L (K := Fin 3) ![𝟙 _, a.left, (1 : G ⟶ G).left] ![k', -k, k - k']), ν.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ ν (eSec G)) (LB.oneGen L) := by
  have e : (1 : G ⟶ G).left ≫ a.left = (1 : G ⟶ G).left :=
    congrArg (fun q : G ⟶ G => q.left) (MonObj.one_comp a)
  obtain ⟨ν, hν, hv⟩ := exists_gen hL (K' := Fin 3) (φ' := ![𝟙 _, a.left, (1 : G ⟶ G).left]) (ε' := ![k', -k, k - k'])
    (fun V _ h => by
      rw [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_three]
      show h (𝟙 _) ^ k' * h a.left ^ (-k) * (h ((1 : G ⟶ G).left ≫ 𝟙 _) ^ (-k') * h ((1 : G ⟶ G).left ≫ a.left) ^ (- -k)) =
        h (𝟙 _) ^ k' * h a.left ^ (-k) * h (1 : G ⟶ G).left ^ (k - k')
      rw [e, Category.comp_id, ← zpow_add, neg_neg, neg_add_eq_sub])
    (LB.mulGen L _ _ _ _ β (LB.invGen L _ _ (LB.pullGen L _ _ β (1 : G ⟶ G).left)))
    (mulGen_isGen _ _ _ _ _ _ _ hβ (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hβ _)))
  refine ⟨ν, hν, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, val_one, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, Category.id_comp, eSec_comp_one,
    mul_inv_cancel]

end Norm

variable {R : Type} [CommRing R] [IsDomain R]

theorem normd_val_eq (hG : GlobalFnsSt) {D : DegPre R} {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)}
    {ε : K → ℤ} {u u' : LB.Gen (LB.LinComb D.P.L φ ε)} (hu : Normd u) (hu' : Normd u') {Z : Scheme.{0}}
    (r : Z ⟶ D.P.A.left) (z : Z) (J) (hJ : Good D.P.L z J) : val u r z J = val u' r z J := by
  refine gen_unique D.P.isLB D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2 hu.1 hu'.1
    (fun y J hJ => ?_) Z r z J hJ
  have a := val_corr hJ hu.2 (𝟙 _)
  have a' := val_corr hJ hu'.2 (𝟙 _)
  rw [val_pull hJ, Category.id_comp] at a a'
  exact a.trans a'.symm

theorem sval_comb {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k n : ℕ} {c : Fin n → F}
    {χ : D.X} {s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε k))} {f : Fin n → D.SecB k χ}
    (h : GeneratorPullback.SecLin D.P.L (DegPre.famφ D F χ) (DegPre.famε k) s (D.famφB χ) (DegPre.famε k) f (DegPre.prB D F).left
      (fun i => scal (fst (TF (R := R) F) D.P.A).left (c i))) (b : TF (R := R) F ⟶ D.P.A) (z) {J}
    (hJ : Good D.P.L z J) :
    sval s (lift (𝟙 (TF (R := R) F)) b).left z J = ∑ i, cst F z (c i) * sval (f i) b.left z J := by
  refine (GlobalTheory.BoxExpansion.secLin_val h _ z hJ).trans (Finset.sum_congr rfl fun i _ => ?_)
  have e₁ : (lift (𝟙 (TF (R := R) F)) b).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ :=
    by
    rw [← Over.comp_left, lift_fst]; rfl
  have e₂ : (lift (𝟙 (TF (R := R) F)) b).left ≫ (DegPre.prB D F).left = b.left :=
    by
    rw [← Over.comp_left, lift_snd]
  rw [e₂]
  exact congrArg (· * _) ((gs_scal _ _ z (c i)).trans (congrArg (fun q => constVal q z (c i)) e₁))

theorem main : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (E : EndU U.toUnifPre), Function.Injective E.h → ∀ (k' k : ℕ), 1 ≤ k → 1 ≤ k' → (∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, E.aG.left] ![(k' : ℤ), -(k : ℤ)]), β.IsGen) → (∃ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ) ∧ ∀ (w₀ : W0 U.toUnifPre) (ρ), NormW U.toUnifPre w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') s s', U.ExpandsF F k w₀ t s → U.ExpandsF F k' w₀ t' s' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ → ∀ (g g' : GtPtF D.toPre F), E.Act g g' → ∀ (w' : Frm D.toPre F k' g.b) (w : Frm D.toPre F k g'.b), w'.IsGen → w.IsGen → (∀ z J, Good D.toPre.P.L z J → val w' (𝟙 _) z J * val κ g.b.left z J = val w (𝟙 _) z J) → (∀ χ, coef s' g w' (E.h χ) = coef s g' w χ) ∧ ∀ β, β ∉ Set.range E.h → coef s' g w' β = 0 := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ E hh k' k hk hk' ⟨β₀, hβ₀⟩
  have hGF := hL.1.globalFns
  have := hI.1
  have := hI.2.2.2
  have := E.homG
  obtain ⟨β, hβ, hβ'⟩ := exists_normalised U.LG.isLB E.aG k' k β₀ hβ₀
  obtain ⟨κ₀, hκ₀, hrel⟩ := GlobalTheory.T.descent_powerIso_endomorphism_abelianPart_uniformization hL R I hI D A G hG U E k' k β hβ hβ'
  refine ⟨⟨κ₀, hκ₀⟩, ?_⟩
  intro w₀ ρ hw ψ m hm hψ hm' α hα hα' t t' s s' ⟨v, hv, n, c, σ, f, h₁, h₂, h₃⟩ ⟨v', hv', hs'⟩ htw κ hκ g g' hg w' w hw' hw₁ hww
  choose σ' f' p₁ p₂ p₃ p₄ using fun i => GlobalTheory.T.pullback_section_endomorphism_expansion R I D A G U.toUnifPre E hh k' k β hβ κ₀ hκ₀.1 hrel (σ i) (f i) (h₁ i)
  have tw := GlobalTheory.T.endU_twist_of_iso hGF R I D A G U.toUnifPre E F k' k β hβ hβ' w₀ ρ hw ψ m hm hψ hm' α hα hα' t t' v v' hv hv' htw
  have H := secLin_of_expandsG U.toUnifPre (IsAdicComplete.le_jacobson_bot I) F k' v' s' hs' n c σ' f' p₁
    ((secLin_iff_val U.LG.isLB _ _ _ _).2 fun y J hJ => by
      rw [tw y J hJ, GlobalTheory.BoxExpansion.secLin_val h₂ _ y hJ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e₁ : ((TFK (R := R) F) ◁ (Over.pullback (jK R)).map E.aG).left ≫
          (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
          (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
        rw [← Over.comp_left, whiskerLeft_fst]
      have e₂ : ((TFK (R := R) F) ◁ (Over.pullback (jK R)).map E.aG).left ≫ UnifPre.gFK (G := G) F =
          UnifPre.gFK (G := G) F ≫ E.aG.left := by
        rw [UnifPre.gFK, ← Category.assoc, ← Over.comp_left, whiskerLeft_snd, Over.comp_left, Category.assoc,
          Category.assoc]
        exact congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)
      rw [p₂ i _ _ y J hJ, gs_scal, gs_scal, e₁, e₂, Category.id_comp, Category.id_comp, _root_.mul_assoc])
  refine ⟨fun χ => CoefBasic.coef_eq fun z J hJ => ?_, fun b hb => CoefBasic.coef_eq fun z J hJ => ?_⟩
  · have a := CoefBasic.isCoef_coef g' hw₁ χ s z J hJ
    have e : g.b.left ≫ D.toPre.P.A.hom = (TF (R := R) F).hom := Over.w g.b
    have e' : g'.b.left = g.b.left ≫ E.aB.left := congrArg (fun q => q.left) hg.1
    rw [sval_comb (h₃ χ) _ z hJ, hg.2 χ z J hJ, ← hww z J hJ, e', normd_val_eq hGF hκ hκ₀ _ z J hJ] at a
    rw [sval_comb (H (E.h χ)) _ z hJ]
    simp only [p₃ _ χ _ _ z J hJ, e, ← _root_.mul_assoc, ← Finset.sum_mul]
    have e₃ : (rigV D.toPre (TF (R := R) F).hom z J).val ^ k' =
        (rigV D.toPre (TF (R := R) F).hom z J).val ^ k * (rigV D.toPre (TF (R := R) F).hom z J ^ ((k' : ℤ) - k)).val := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_natCast,
        ← zpow_add, add_sub_cancel]
    rw [e₃, ← _root_.mul_assoc, a]
    simp only [Units.val_mul]
    ring
  · rw [sval_comb (H b) _ z hJ, CoefBasic.cst_eq, map_zero, zero_mul, Finset.sum_eq_zero, zero_mul, zero_mul]
    intro i _
    exact (congrArg _ ((congrArg (gs _ z _) (p₄ i b hb _)).trans (gs_zero' _ z _ (hJ.mem _ _)))).trans (mul_zero _)

end GlobalTheory.UT.PullExp
end
end
