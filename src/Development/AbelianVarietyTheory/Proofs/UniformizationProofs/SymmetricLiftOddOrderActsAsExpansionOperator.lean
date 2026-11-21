import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NuGeIffOfIsActOfOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamEqOfCoefEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalOfIsTwistPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionPullbackSectionEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
import BuildAid.ForwardExisting

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.SymFrame

theorem exists_sval_ne_zero {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] {K : Type} [Fintype K] {φ : K → ((DegPre.BF D F).left ⟶ D.P.A.left)} {ε : K → ℤ}
    (σ : LB.Sec (LB.LinComb D.P.L φ ε)) (hσ : ¬ ∀ j, σ.f j = 0) (z : (TF (R := R) F).left) {J}
    (hJ : Good D.P.L z J) : ∃ x : TF (R := R) F ⟶ D.P.A, sval σ (lift (𝟙 (TF (R := R) F)) x).left z J ≠ 0 := by
  by_contra H
  push_neg at H
  have hsm := D.P.isAb.smooth
  let p : (DegPre.BF D F).left ⟶ Spec (CommRingCat.of F) := (fst (TF (R := R) F) D.P.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst (TF (R := R) F).hom D.P.A.hom))
  have : IsReduced (DegPre.BF D F).left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  refine hσ fun j => CoefDet.fn_ext_of_points p fun r hr z' hz => ?_
  obtain rfl : z' = z := CoefBasic.pt_eq (R := R) z' z
  let r' : TF (R := R) F ⟶ DegPre.BF D F := Over.homMk r (by
    rw [← Over.w (fst (TF (R := R) F) D.P.A), ← Category.assoc]
    exact (congrArg (· ≫ (TF (R := R) F).hom) hr).trans (Category.id_comp _))
  have er : lift (𝟙 (TF (R := R) F)) (r' ≫ snd _ _) = r' := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ (lift_snd _ _)
    rw [lift_fst]
    exact Over.OverMorphism.ext hr.symm
  have a := H (r' ≫ snd _ _)
  rw [er] at a
  refine (sec_trans σ r z' hz (hJ.mem _ r)).trans (((congrArg _ a).trans (mul_zero _)).trans ?_)
  rw [gs_eq r z' _ hz, map_zero, map_zero]

theorem exists_normW {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (w₀ : W0 U) (hw : w₀.IsGen) : ∃ ρ, NormW U w₀ ρ := by
  have := U.gen_hom
  let e : Spec (CommRingCat.of (FractionRing R)) ⟶ ((Over.pullback (jK R)).obj G).left :=
    eSec ((Over.pullback (jK R)).obj G)
  let eA : Spec (CommRingCat.of (FractionRing R)) ⟶ A.A.left := eSec A.A
  have e₁ : e ≫ pullback.fst G.hom (jK R) = jK R ≫ eSec G := by
    simp [e, eSec]
    erw [pullback.lift_fst]
    rw [← Category.assoc, ← pullback.condition, Category.comp_id]
  have e₂ : e ≫ U.gen.hom.left = eA :=
    congrArg (fun q => q.left) (IsMonHom.one_hom U.gen.hom)
  have pt : ∀ z z' : Spec (CommRingCat.of (FractionRing R)), z = z' := fun z z' =>
    Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z z'
  let z₀ : Spec (CommRingCat.of (FractionRing R)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  obtain ⟨i, hi⟩ := exists_chart U.LG.isLB ((jK R ≫ eSec G) z₀)
  have hi' : ∀ z, (jK R ≫ eSec G) z ∈ U.LG.L.U i := fun z => pt z₀ z ▸ hi
  have m₁ : ∀ z i, (jK R ≫ eSec G) z ∈ U.LG.L.U i → pullback.fst G.hom (jK R) (e z) ∈ U.LG.L.U i := fun z i h =>
    (congrArg (fun q => q z ∈ U.LG.L.U i) e₁).mpr h
  have m₂ : ∀ z (j : PUnit → A.L.ι), eA z ∈ A.L.U (j PUnit.unit) → e z ∈ (A.L.pull U.gen.hom.left).U j :=
    fun z j h => mem_pull.2 ((congrArg (fun q => q z ∈ A.L.U (j PUnit.unit)) e₂).mpr h)
  have l₁ : ∀ j : PUnit → A.L.ι, (A.L.pull eA).U j ≤
      e ⁻¹ᵁ ((U.LG.L.pull (pullback.fst G.hom (jK R))).U (fun _ => i) ⊓ (A.L.pull U.gen.hom.left).U j) :=
    fun j z hz => ⟨mem_pull.2 (m₁ z i (hi' z)), m₂ z j (mem_pull.1 hz)⟩
  have l₂ : ∀ j : PUnit → A.L.ι, (A.L.pull eA).U j ≤ jK R ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => i) :=
    fun j z _ => mem_pull.2 (hi' z)
  let ρ : LB.Gen (A.L.pull eA) := ⟨fun j => (res (l₁ j) (pullU e _ (w₀.s (fun _ => i, j))))⁻¹ *
    res (l₂ j) (pullU (jK R) _ (U.LG.rig.s fun _ => i))⟩
  have v : ∀ z j, z ∈ (A.L.pull eA).U j → gm (𝟙 _) z _ (ρ.s j) = (gw w₀ e z i j)⁻¹ *
      gm (jK R) z ((U.LG.L.pull (eSec G)).U (fun _ => i)) (U.LG.rig.s fun _ => i) := fun z j hz =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res _ z _ hz _).trans
      (gm_pull (𝟙 _) e z ((U.LG.L.pull (pullback.fst G.hom (jK R))).U (fun _ => i) ⊓ (A.L.pull U.gen.hom.left).U j)
        (l₁ j hz) _)))) ((gm_res _ z _ hz _).trans
      (gm_pull (𝟙 _) (jK R) z ((U.LG.L.pull (eSec G)).U (fun _ => i)) (l₂ j hz) _)))
  have P := (isGen_iff w₀).1 hw
  refine ⟨ρ, hw, fun j j' => unit_ext fun z hz => ?_, fun z JA JG hA hG => ?_⟩
  · refine ((gm_res _ z _ hz _).trans (v z j hz.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_pull_g A.L eA (𝟙 _) z j j' hz.1 hz.2) ((gm_res _ z _ hz _).trans (v z j' hz.2)))).symm)
    have a := P _ e z i i j j' (m₁ z i (hi' z)) (m₁ z i (hi' z)) (m₂ z j (mem_pull.1 hz.1)) (m₂ z j' (mem_pull.1 hz.2))
    rw [gm_self U.LG.isLB (e ≫ _) z (m₁ z i (hi' z)),
      gm_pull_g A.L _ e z j j' (m₂ z j (mem_pull.1 hz.1)) (m₂ z j' (mem_pull.1 hz.2)), e₂] at a
    rw [a, Category.id_comp, _root_.one_mul, mul_inv, inv_inv, _root_.mul_assoc]
  · have h₁ := m₂ z (fun _ => JA (eSec A.A)) (hA _)
    have a := P _ e z (JG (jK R ≫ eSec G)) i _ _ (m₁ z _ (hG _)) (m₁ z i (hi' z)) h₁ h₁
    rw [gm_pull_g A.L _ e z _ _ h₁ h₁,
      gm_self A.isLB (e ≫ U.gen.hom.left) z (i := JA (eSec A.A)) (mem_pull.1 h₁ :), e₁] at a
    have b := gen_trans (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rigGen (jK R) z
      (hG.mem _ _) (j' := fun _ => i) (mem_pull.2 (hi' z))
    rw [trF, Fintype.prod_unique, zpow_one] at b
    rw [val_of (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) ρ (𝟙 _) z JA (fun _ => JA (eSec A.A))
      (fun _ => by rw [Category.id_comp])]
    refine (congrArg₂ (· * ·) a (v z _ (mem_pull.2 (hA _)))).trans (Eq.trans ?_ b.symm)
    rw [inv_one, _root_.mul_one, _root_.mul_assoc, mul_inv_cancel_left]
    rfl

section Canon

variable {S : Scheme.{0}} {B : Over S} (L : LB B.left) (Y : Over S)

def HasGen (fm : ∀ (U : Type) [CommGroup U], ((Y.left ⟶ B.left) → U) → U)
    (f : ∀ (T : Over S) (_ : T ⟶ Y) (z : T.left) (_ : (T.left ⟶ B.left) → L.ι), (T.left.presheaf.stalk z)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y.left ⟶ B.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ B.left) → U), ∏ k, h (φ k) ^ ε k = fm U h) ∧
    ∀ T ρ z J, Good L z J → val t ρ.left z J = f T ρ z J

variable {L Y}

theorem HasGen.mul {fm fm' f f'} (a : HasGen L Y fm f) (b : HasGen L Y fm' f') :
    HasGen L Y (fun U _ h => fm U h * fm' U h) (fun T ρ z J => f T ρ z J * f' T ρ z J) := by
  obtain ⟨K, _, φ, ε, t, ht, p, v⟩ := a
  obtain ⟨K', _, φ', ε', t', ht', p', v'⟩ := b
  exact ⟨_, _, _, _, LB.mulGen L _ _ _ _ t t', mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ h => prod_sum₂ (K := K) (K' := K') (U := U) _ (p U h) (p' U h),
    fun T ρ z J hJ => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v T ρ z J hJ) (v' T ρ z J hJ))⟩

theorem HasGen.inv {fm f} (a : HasGen L Y fm f) :
    HasGen L Y (fun U _ h => (fm U h)⁻¹) (fun T ρ z J => (f T ρ z J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, p, v⟩ := a
  exact ⟨_, _, _, _, LB.invGen L _ _ t, invGen_isGen _ _ _ _ ht, fun U _ h => prod_neg _ _ (p U h),
    fun T ρ z J hJ => (val_inv _ _).trans (congrArg (·⁻¹) (v T ρ z J hJ))⟩

theorem hasGen_pull {K : Type} [Fintype K] {φ : K → (B.left ⟶ B.left)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    (ht : t.IsGen) (x : Y ⟶ B) :
    HasGen L Y (fun _ _ h => ∏ k, h (x.left ≫ φ k) ^ ε k) (fun _ ρ z J => val t (ρ ≫ x).left z J) :=
  ⟨_, _, _, _, LB.pullGen L _ _ t x.left, pullGen_isGen _ _ _ _ ht _, fun _ _ _ => rfl,
    fun _ _ _ _ hJ => val_pull hJ _ _ _⟩

theorem HasGen.unique (hL : L.IsLB) {fm fm' f f'} (a : HasGen L Y fm f) (b : HasGen L Y fm' f')
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ B.left) → U), fm U h = fm' U h)
    (hY : Function.Surjective Y.hom.appTop.hom) (e : 𝟙_ (Over S) ⟶ Y)
    (he : ∀ z J, Good L z J → f _ e z J = f' _ e z J) (T : Over S) (ρ : T ⟶ Y) (z : T.left) (J) (hJ : Good L z J) :
    f T ρ z J = f' T ρ z J := by
  obtain ⟨K, _, φ, ε, t, ht, p, v⟩ := a
  obtain ⟨K', _, φ', ε', t', ht', p', v'⟩ := b
  exact (v T ρ z J hJ).symm.trans ((gen_unique' hL (fun U _ h => (p' U h).trans ((hF U h).symm.trans (p U h).symm))
    Y.hom e.left (Over.w e) hY ht ht' (fun y I hI => (v _ e y I hI).trans ((he y I hI).trans (v' _ e y I hI).symm))
    _ ρ.left z J hJ).trans (v' T ρ z J hJ))

variable [GrpObj B] [IsCommMonObj B] {M : RigLB B} (c : CubicalStr B M)

theorem hasGen_cub (x x' y : Y ⟶ B) :
    HasGen M.L Y (fun _ _ h => h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ *
      h x.left * h x'.left * h y.left * (h (1 : Y ⟶ B).left)⁻¹)
      (fun _ ρ z J => cubV c z J (ρ ≫ x) (ρ ≫ x') (ρ ≫ y)) :=
  ⟨_, _, _, _, LB.pullGen M.L (thφ B (x3 B)) thε c.t (lift x (lift x' y)).left, pullGen_isGen _ _ _ _ c.isGen _,
    fun _ _ h => prod_cub x x' y h, fun _ ρ _ _ hJ => val_cub c ρ hJ _ _ _⟩

theorem hasGen_cubN (a m x : Y ⟶ B) (k : ℕ) :
    HasGen M.L Y (fun _ _ h => h (a * m ^ k * x).left * (h (a * m ^ k).left)⁻¹ * (h (a * x).left)⁻¹ * h a.left *
      (h (m * x).left ^ k)⁻¹ * h m.left ^ k * h x.left ^ k * (h (1 : Y ⟶ B).left ^ k)⁻¹)
      (fun _ ρ z J => cubN (cubV c z J) k (ρ ≫ a) (ρ ≫ m) (ρ ≫ x)) := by
  obtain ⟨t, ht, v⟩ := exists_cubN c a m x k
  refine ⟨_, _, _, _, t, ht, fun U _ h => ?_, v⟩
  simp [Fin.prod_univ_succ, _root_.mul_assoc]

end Canon

theorem canon_identity {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hG : GlobalFnsSt) (N : ℕ)
    (ν : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(𝟙 D.P.A ^ (N + 1)).left, (𝟙 D.P.A ^ N).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left]
      ![1, -1, -(2 * (N : ℤ) + 1), 2 * (N : ℤ) + 1])) (hν : Normd ν)
    {a : D.P.A ⟶ D.P.A} (ha : a = (𝟙 D.P.A)⁻¹) (κ : LB.Gen (kapLB D a N N)) (hκ : Normd κ) {T : Over (Spec (CommRingCat.of R))} (b x : T ⟶ D.P.A)
    (z : T.left) {J} (hJ : Good D.P.L z J) :
    val ν b.left z J * val κ (x * b).left z J * cubN (th D z J) N 1 b x * cubN (th D z J) N (b ^ N)⁻¹ b (x * b)⁻¹ *
        (th D z J (b ^ N)⁻¹ (x * b)⁻¹ b)⁻¹ * th D z J (b ^ N) (b ^ N)⁻¹ b =
      val κ x.left z J * th D z J (b ^ N)⁻¹ x x⁻¹ * (th D z J (b ^ N) (b ^ N)⁻¹ x)⁻¹ := by
  subst ha
  let β : D.P.A ⊗ D.P.A ⟶ D.P.A := fst _ _
  let ξ : D.P.A ⊗ D.P.A ⟶ D.P.A := snd _ _
  have nv : ∀ {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ}
      (u : LB.Gen (LB.LinComb D.P.L φ ε)), Normd u → ∀ y I, Good D.P.L y I →
      val u (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left y I = 1 := by
    intro K _ φ ε u hu y I hI
    have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) = η[D.P.A] := by simp [Hom.one_def]
    have := (val_pull hI u _ _).symm.trans ((val_corr hI hu.2 (𝟙 _)).trans (val_one _))
    rw [Category.id_comp] at this
    rw [o]; exact this
  have fκ : ∀ (q : D.P.A ⊗ D.P.A ⟶ D.P.A) (U : Type) [CommGroup U] (h : ((D.P.A ⊗ D.P.A).left ⟶ D.P.A.left) → U),
      ∏ k, h (q.left ≫ (![𝟙 _, ((𝟙 D.P.A)⁻¹ : D.P.A ⟶ D.P.A).left, (1 : D.P.A ⟶ D.P.A).left] : Fin 3 → _) k) ^
        (![(N : ℤ), -(N : ℤ), (N : ℤ) - N] : Fin 3 → ℤ) k = h q.left ^ N * (h q⁻¹.left ^ N)⁻¹ := by
    intro q U _ h
    have e : q ≫ (𝟙 D.P.A)⁻¹ = q⁻¹ := by rw [GrpObj.comp_inv, Category.comp_id]
    rw [← e]
    simp [Fin.prod_univ_succ]
  have fν : ∀ (U : Type) [CommGroup U] (h : ((D.P.A ⊗ D.P.A).left ⟶ D.P.A.left) → U),
      ∏ k, h (β.left ≫ (![(𝟙 D.P.A ^ (N + 1)).left, (𝟙 D.P.A ^ N).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] : Fin 4 → _) k) ^
        (![1, -1, -(2 * (N : ℤ) + 1), 2 * (N : ℤ) + 1] : Fin 4 → ℤ) k =
      h (β ^ N * β).left * (h (β ^ N).left)⁻¹ * h β.left ^ (-(2 * (N : ℤ) + 1)) *
        h (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left ^ (2 * (N : ℤ) + 1) := by
    intro U _ h
    have e : ∀ n : ℕ, β ≫ (𝟙 D.P.A ^ n) = β ^ n := fun n => by rw [MonObj.comp_pow, Category.comp_id]
    rw [← pow_succ, ← e, ← e, ← MonObj.comp_one (M := D.P.A) β, Fin.prod_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Over.comp_left, Category.comp_id, zpow_one,
      zpow_neg_one]
  have H := (((((((hasGen_pull (L := D.P.L) hν.1 β).mul (hasGen_pull hκ.1 (ξ * β))).mul (hasGen_cubN D.cub 1 β ξ N)).mul
    (hasGen_cubN D.cub (β ^ N)⁻¹ β (ξ * β)⁻¹ N)).mul (hasGen_cub D.cub (β ^ N)⁻¹ (ξ * β)⁻¹ β).inv).mul
    (hasGen_cub D.cub (β ^ N) (β ^ N)⁻¹ β)).unique D.P.isLB
    (((hasGen_pull (L := D.P.L) hκ.1 ξ).mul (hasGen_cub D.cub (β ^ N)⁻¹ ξ ξ⁻¹)).mul (hasGen_cub D.cub (β ^ N) (β ^ N)⁻¹ ξ).inv)
    (fun U _ h => by
      have a₁ : β * (ξ * β)⁻¹ = ξ⁻¹ := by rw [mul_inv, mul_comm ξ⁻¹, mul_inv_cancel_left]
      have a₂ : (ξ * β)⁻¹ * β = ξ⁻¹ := by rw [mul_comm, a₁]
      have a₃ : (β ^ N)⁻¹ * (ξ * β)⁻¹ * β = (β ^ N)⁻¹ * ξ⁻¹ := by rw [_root_.mul_assoc, a₂]
      rw [fκ, fκ, fν]
      simp only [_root_.one_mul, inv_mul_cancel, mul_inv_cancel, mul_inv_cancel_right, a₁, a₂, a₃, mul_comm β ξ]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (by
      rw [← Over.w (snd D.P.A D.P.A)]
      exact surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2) (lift 1 1) (fun y I hI => by
      have C : IsCub (cubV D.cub (T := 𝟙_ _) y I) := isCub_cubV D.cub hI
      simp only [β, ξ, MonObj.comp_mul, MonObj.comp_pow, GrpObj.comp_inv, MonObj.comp_one, lift_fst, lift_snd,
        _root_.mul_one, inv_one, one_pow, C.face, C.N_one, nv ν hν y I hI, nv κ hκ y I hI]) T (lift b x) z J hJ)
  simpa only [β, ξ, MonObj.comp_mul, MonObj.comp_pow, GrpObj.comp_inv, MonObj.comp_one, lift_fst, lift_snd] using H

theorem exists_twist {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα : α.IsGen)
    (s : LB.Sec (LPow A L b T)) : ∃ s' : LB.Sec (LPow A L a T), IsTwistPull A L ψ m hm a b α s s' := by
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T A).left) (ε' := fun _ => a)
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
        e, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, mul_inv_cancel_comm_assoc])
    (pullMulSec (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s ψ.left α hα)
  exact ⟨s', ThetaLin.isTwistPull_of_sval A hL hα fun y J hJ =>
    (hs' _ _ y J hJ).trans ((sval_pullMulSec _ _ α hα _ y hJ).trans (mul_comm _ _))⟩

section Sym

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ}

theorem val_symGen (θ : ThetaGrp A L k T) (nu : LB.Gen (negLB A L k T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) {z : Z}
    {J} (hJ : Good L z J) : val (symGen A L k θ nu) r z J =
      val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
          (r ≫ (translT A θ.pt⁻¹).left) z J *
        val (L := L) (φ := ![(snd T A).left, (snd T A ≫ ι[A]).left]) (ε := ![k, -k]) nu r z J *
      (val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (r ≫ (negT A T).left) z J *
        (val (L := L) (φ := ![(snd T A).left, (snd T A ≫ ι[A]).left]) (ε := ![k, -k]) nu
          (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _) rfl))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _))))))

theorem exists_norm_sym (hL : L.IsLB) (θ : ThetaGrp A L k T) (nu : LB.Gen (negLB A L k T)) (hnu : nu.IsGen)
    (h : LB.Gen.Corr L _ _ _ _ (symGen A L k θ nu) (LB.oneGen L)) :
    ∃ α : LB.Gen (negLB A L k T), α.IsGen ∧ LB.Gen.Corr L _ _ _ _ (symGen A L k θ α) (LB.oneGen L) ∧
      ∀ z J, Good L z J → val (L := L) (φ := ![(snd T A).left, (snd T A ≫ ι[A]).left]) (ε := ![k, -k]) α
        (ptSecT A (1 : T ⟶ A)).left z J = 1 := by
  let o : T ⊗ A ⟶ T ⊗ A := fst T A ≫ ptSecT A 1
  have o₁ : o.left ≫ (snd T A).left = (1 : T ⊗ A ⟶ A).left := by
    rw [← Over.comp_left, Category.assoc, ptSecT, lift_snd, MonObj.comp_one]
  have o₂ : o.left ≫ (snd T A ≫ ι[A]).left = (1 : T ⊗ A ⟶ A).left := by
    rw [← Over.comp_left, ← Category.assoc, Category.assoc (fst T A), ptSecT, lift_snd, MonObj.comp_one,
      ← Hom.inv_def, inv_one]
  obtain ⟨α, hα, v⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ≫ ι[A]).left]) (ε' := ![k, -k])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, o₁, o₂, neg_neg, zpow_neg, inv_inv, inv_mul_cancel, _root_.mul_one])
    (LB.mulGen L _ _ _ _ nu (LB.invGen L _ _ (LB.pullGen L _ _ nu o.left)))
    (mulGen_isGen _ _ _ _ _ _ _ hnu (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hnu _)))
  have v' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) z J, Good L z J → val α r z J =
      val (L := L) (φ := ![(snd T A).left, (snd T A ≫ ι[A]).left]) (ε := ![k, -k]) nu r z J *
        (val (L := L) (φ := ![(snd T A).left, (snd T A ≫ ι[A]).left]) (ε := ![k, -k]) nu (r ≫ o.left) z J)⁻¹ :=
    fun Z r z J hJ => (v Z r z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg _ ((val_inv _ _).trans
      (congrArg (·⁻¹) (val_pull hJ _ _ _)))))
  refine ⟨α, hα, corr_of_val hL fun y J hJ => ?_, fun z J hJ => ?_⟩
  · have e := val_corr hJ h (𝟙 _)
    have t : (translT A θ.pt⁻¹).left ≫ o.left = o.left := by
      rw [← Over.comp_left, ← Category.assoc, translT, lift_fst]
    refine ((val_symGen A θ α _ hJ).trans ?_).trans ((val_symGen A θ nu _ hJ).symm.trans e)
    rw [v' _ _ y J hJ, v' _ _ y J hJ, Category.assoc, t]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    try abel
  · have t : (ptSecT A (1 : T ⟶ A)).left ≫ o.left = (ptSecT A (1 : T ⟶ A)).left := by
      rw [← Over.comp_left, ← Category.assoc, ptSecT, lift_fst, Category.id_comp]
    rw [v' _ _ z J hJ, t, mul_inv_cancel]

theorem isTwistPull_of_sym [IsCommMonObj A] (hL : L.IsLB) (θ : ThetaGrp A L k T) (α : LB.Gen (negLB A L k T)) (hα : α.IsGen)
    (h : LB.Gen.Corr L _ _ _ _ (symGen A L k θ α) (LB.oneGen L)) {t t₁ t₂ t₃ : LB.Sec (LPow A L k T)}
    (h₁ : IsActOf A L k θ t t₁) (h₂ : IsTwistPull A L (negT A T) (snd T A ≫ ι[A]) (lift_snd _ _) k k α t₁ t₂)
    (h₃ : IsActOf A L k θ t₂ t₃) : IsTwistPull A L (negT A T) (snd T A ≫ ι[A]) (lift_snd _ _) k k α t t₃ := by
  refine ThetaLin.isTwistPull_of_sval A hL hα fun y J hJ => ?_
  have e := (val_symGen A θ α (translT A θ.pt).left hJ).symm.trans ((val_corr hJ h (translT A θ.pt).left).trans (val_one _))
  have t₁ : (translT A θ.pt).left ≫ (translT A θ.pt⁻¹).left = 𝟙 _ := by
    rw [← Over.comp_left, ThetaLin.translT_comp _ _ _ (inv_mul_cancel _), Over.id_left]
  have t₂ : ((translT A θ.pt).left ≫ (negT A T).left) ≫ (translT A θ.pt).left = (negT A T).left := by
    have e : translPt A θ.pt = (fst T A ≫ θ.pt) * snd T A := rfl
    have n : translT A θ.pt ≫ negT A T = lift (fst T A) ((fst T A ≫ θ.pt) * snd T A)⁻¹ := by
      rw [negT, comp_lift, ← Category.assoc, translT, lift_fst, lift_snd, e, Hom.inv_def]
    rw [← Over.comp_left, ← Over.comp_left, n, ThetaLin.lift_translT, mul_inv, mul_inv_cancel_left, Hom.inv_def, negT]
  rw [t₁] at e
  rw [ThetaLin.sval_of_isTwistPull A h₃ _ y hJ, ThetaLin.sval_of_isTwistPull A h₂ _ y hJ,
    ThetaLin.sval_of_isTwistPull A h₁ _ y hJ, Category.id_comp, Category.id_comp, t₂, ← _root_.mul_assoc,
    ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
  rw [← _root_.mul_assoc, mul_inv_eq_one] at e
  exact congrArg₂ (· * ·) (congrArg Units.val e) rfl

end Sym

section Main

variable {R : Type} [CommRing R] [IsDomain R]

theorem phi_at {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] (hG : GlobalFnsSt) {k : ℕ}
    (p : QkPt D F k) (w : Frm D F k p.g.b) (hw : w.IsGen) {s t : Fam D F k} (h : PhiRel D F k p w s t) (α β : D.X)
    (e : α + p.y = β) (x : TF (R := R) F ⟶ D.P.A) (z : (TF (R := R) F).left) {J} (hJ : Good D.P.L z J) :
    sval (t.s β) (lift (𝟙 _) x).left z J = sval (s.s α) (lift (𝟙 _) (x * p.g.b)).left z J *
      (cubN (th D z J) k (cP D _ α) p.g.b x * (th D z J (cP D _ α) x p.g.b)⁻¹ *
        (val (p.g.s α) (𝟙 _) z J * val w (𝟙 _) z J)).val := by
  have H := (phiRel_iff hG p w hw s t).1 h α β e _ (lift (𝟙 _) x) z J hJ
  have a : lift (𝟙 (TF (R := R) F)) x ≫ DegPre.trPt D F p.g.b = lift (𝟙 _) (x * p.g.b) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tr_fst, lift_fst, lift_fst]
    · rw [Category.assoc, lift_snd]
      refine (congrArg _ (tr_pr D F p.g.b)).trans ?_
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd, Category.id_comp]
  rw [a, uVal, lift_fst_assoc, lift_snd, lift_fst, Category.id_comp, val_mul hJ] at H
  exact H

theorem val_rigT_zero {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left)
    (ρ : LB.Gen (L.pull (eSec A))) (T : Over S) (k : ℤ) (hk : k = 0) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) (J) :
    val (rigT A L ρ T k) r z J = 1 := by
  subst hk
  exact (congrArg _ (zpow_zero _)).trans (map_one _)

theorem sq_frame_of_symmetric : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p : QkPt D.toPre F N) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (w₀ : W0 U.toUnifPre) (w : Frm D.toPre F N p.g.b), w₀.IsGen → w.IsGen → (∀ t t' s s', U.ExpandsF F N w₀ t s → U.ExpandsF F N w₀ t' s' → IsActOf A.A A.L N θ t t' → PhiRel D.toPre F N p w s s') → (∃ nu : LB.Gen (negLB A.A A.L N (TFK (R := R) F)), nu.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (symGen A.A A.L N θ nu) (LB.oneGen A.L)) → ∀ ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4) ![(𝟙 D.toPre.P.A ^ (N + 1)).left, (𝟙 D.toPre.P.A ^ N).left, 𝟙 _, (1 : D.toPre.P.A ⟶ D.toPre.P.A).left] ![1, -1, -(2 * (N : ℤ) + 1), 2 * (N : ℤ) + 1]), Normd ν → ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J ^ 2 = val (p.g.s p.y) (𝟙 _) z J * val ν p.g.b.left z J := by
  intro hL R _ _ _ I hA D A G _ _ hS U F _ _ _ N hN p θ w₀ w hw₀ hw hΦ ⟨nu, hnu, hsym⟩ ν hν z J hJ
  have hG := hL.1.globalFns
  have C : IsCub (th D.toPre (T := TF (R := R) F) z J) := isCub_cubV D.toPre.cub hJ
  obtain ⟨ρ, hρ⟩ := exists_normW U.toUnifPre w₀ hw₀
  obtain ⟨-, E, eG, eA, eB, eh, eAct⟩ := IntEnd.exists_nsmul_and_neg hL R I hA D A G hS U
  obtain ⟨α, hα, hαs, hα₁⟩ := exists_norm_sym A.A A.isLB θ nu hnu hsym
  obtain ⟨β, hβ, -⟩ := exists_gen U.LG.isLB (φ' := ![𝟙 _, E.aG.left]) (ε' := ![(N : ℤ), -(N : ℤ)]) (fun V _ h => by
      rw [eG, Hom.inv_def, Category.id_comp]
      simp [Fin.prod_univ_two, mul_comm])
    (GeneratorPullback.powGen U.LG.L _ _ (LB.invGen U.LG.L _ _ U.symG) N) (powGen_isGen _ _ _ _ (invGen_isGen _ _ _ _ U.symG_gen) N)
  obtain ⟨⟨κ, hκ⟩, hP⟩ := GlobalTheory.T.expansion_pullback_section_endomorphism hL R I hA D A G hS U F E
    (fun a b e => neg_injective ((eh a).symm.trans (e.trans (eh b)))) N N hN hN ⟨β, hβ⟩
  have hP' := hP w₀ ρ hρ (negT A.A _) (snd _ _ ≫ ι[A.A]) (lift_snd _ _) (lift_fst _ _)
    (by rw [eA, Hom.inv_def, Category.id_comp]) α hα (corr_of_val A.isLB fun y J' hJ' => by
      refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_rigT_zero _ _ _ _ _ (sub_self _) _ _ _).symm)
      rw [Category.id_comp]
      exact hα₁ y J' hJ')

  have neg : ∀ (t t' : SecA A F N) s s', U.ExpandsF F N w₀ t s → U.ExpandsF F N w₀ t' s' →
      IsTwistPull A.A A.L (negT A.A _) (snd _ _ ≫ ι[A.A]) (lift_snd _ _) N N α t t' → ∀ χ χ', χ + χ' = 0 →
      ∀ x : TF (R := R) F ⟶ D.toPre.P.A, sval (s'.s χ') (lift (𝟙 _) x).left z J =
        sval (s.s χ) (lift (𝟙 _) x⁻¹).left z J * (val κ x.left z J * th D.toPre z J (cP _ _ χ) x x⁻¹ *
          (th D.toPre z J (cP _ _ χ) (cP _ _ χ') x)⁻¹).val := by
    intro t t' s s' hs hs' ht χ χ' hχ x
    obtain ⟨g, rfl⟩ := (gt_onto_divisible_kernel hL R I hA D F).1 x
    obtain ⟨b', v'⟩ : (TorusExt.gtNeg g).b = g.b⁻¹ ∧ ∀ χ y J, Good D.toPre.P.L y J →
      TorusExt.charVal (TorusExt.gtNeg g) χ y J = (TorusExt.charVal g χ y J)⁻¹ *
        th D.toPre y J (cP D.toPre _ χ) g.b g.b⁻¹ := (TorusExt.exists_neg g).choose_spec
    have act : E.Act g (TorusExt.gtNeg g) := (eAct F _ _).2
      ⟨_, TorusExt.isZero_gtZero, TorusExt.gtAdd_neg g ▸ TorusExt.isAdd_gtAdd g _⟩
    obtain ⟨ω, hω⟩ := (CoefBasic.coef_basic R D.toPre F N g).1
    obtain ⟨ω', hω', vω⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F (TorusExt.gtNeg g).b)
      (ε' := DegPre.lineε N) (fun V _ h => by
        refine (prod_sum₂ (K := Fin 2) (K' := Fin 3) (U := V) _ (CoefBasic.prod_line N g.b h) rfl).trans ?_
        rw [CoefBasic.prod_line, act.1]
        simp [Fin.prod_univ_succ, _root_.mul_assoc])
      (LB.mulGen D.toPre.P.L _ _ _ _ ω (LB.pullGen D.toPre.P.L _ _ κ g.b.left))
      (mulGen_isGen _ _ _ _ _ _ _ hω (pullGen_isGen _ _ _ _ hκ.1 _))
    have vω' : ∀ z J, Good D.toPre.P.L z J → val ω (𝟙 _) z J * val κ g.b.left z J = val ω' (𝟙 _) z J := fun z J hJ => by
      rw [vω _ _ z J hJ, val_mul hJ, val_pull hJ, Category.id_comp]
    have c := (hP' t t' s s' hs hs' ht κ hκ g _ act ω ω' hω hω' vω').1 χ
    rw [eh, neg_eq_of_add_eq_zero_right hχ] at c
    have a := CoefBasic.isCoef_coef g hω χ' s' z J hJ
    have a' := CoefBasic.isCoef_coef _ hω' χ s z J hJ
    have m := TorusExt.charVal_add g hJ χ χ'
    have l : lift (𝟙 (TF (R := R) F)) (TorusExt.gtNeg g).b = lift (𝟙 _) g.b⁻¹ := by rw [b']
    rw [hχ, TorusExt.charVal_zero g hJ, _root_.one_mul] at m
    rw [c, a', l, ← vω' z J hJ, _root_.mul_assoc, _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul] at a
    rw [(Units.eq_mul_inv_iff_mul_eq _).2 a.symm, _root_.mul_assoc, ← Units.val_mul, m]
    congr 2
    have v := congrArg Additive.ofMul (v' χ z J hJ)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, TorusExt.charVal] at v ⊢
    linear_combination (norm := abel) v
  obtain ⟨bij, -⟩ := expBijF_and_expandsF_lin hL R I hA D A G hS U
  obtain ⟨ts, st⟩ := bij F N hN w₀ hw₀
  obtain ⟨σ, hσ⟩ := FamFree.exists_sec_ne_zero (D := D.toPre) (F := F) hL.2.1.secTwist hN (-p.y)
  obtain ⟨s, rfl, -⟩ := FamFree.exists_fam_single hG D.tau_bimult hN (-p.y) σ
  obtain ⟨x', hx⟩ := exists_sval_ne_zero _ hσ z hJ
  obtain ⟨x, rfl⟩ : ∃ x, x⁻¹ = x' := ⟨x'⁻¹, inv_inv _⟩
  obtain ⟨t, ht, -⟩ := st s
  obtain ⟨t₁, h₁⟩ := exists_twist A.A A.isLB (ψ := translT A.A θ.pt) (hm := lift_snd _ _) θ.isGen t
  obtain ⟨t₂, h₂⟩ := exists_twist A.A A.isLB (ψ := negT A.A _) (hm := lift_snd _ _) hα t₁
  obtain ⟨t₃, h₃⟩ := exists_twist A.A A.isLB (ψ := translT A.A θ.pt) (hm := lift_snd _ _) θ.isGen t₂
  obtain ⟨s₁, hs₁, -⟩ := ts t₁
  obtain ⟨s₂, hs₂, -⟩ := ts t₂
  obtain ⟨s₃, hs₃, -⟩ := ts t₃
  have e₁ := phi_at hG p w hw (hΦ _ _ _ _ ht hs₁ h₁) (-p.y) 0 (neg_add_cancel _) (x * p.g.b)⁻¹ z hJ
  have e₂ := neg _ _ _ _ hs₁ hs₂ h₂ 0 0 (add_zero _) (x * p.g.b)
  have e₃ := phi_at hG p w hw (hΦ _ _ _ _ hs₂ hs₃ h₃) 0 p.y (zero_add _) x z hJ
  have e₄ := neg _ _ _ _ ht hs₃ (isTwistPull_of_sym A.A A.isLB θ α hα hαs h₁ h₂ h₃) (-p.y) p.y (neg_add_cancel _) x
  have cn : cP D.toPre (TF (R := R) F) (-p.y) = (p.g.b ^ N)⁻¹ := by
    rw [← cPoint_y, eq_inv_iff_mul_eq_one, ← cPoint_add, neg_add_cancel, cPoint_zero]
  have m := TorusExt.charVal_add p.g hJ p.y (-p.y)
  rw [add_neg_cancel, TorusExt.charVal_zero p.g hJ, _root_.one_mul, cn, cPoint_y] at m
  have z₀ := TorusExt.charVal_zero p.g hJ
  have key := canon_identity hG N ν hν eB κ hκ p.g.b x z hJ
  have hu : IsUnit (sval (s.s (-p.y)) (lift (𝟙 (TF (R := R) F)) x⁻¹).left z J) := by
    obtain ⟨a, ha⟩ := CoefBasic.cstH_surj z (sval (s.s (-p.y)) (lift (𝟙 (TF (R := R) F)) x⁻¹).left z J)
    rw [← ha] at hx ⊢
    exact (IsUnit.mk0 a fun h => hx (by rw [h, map_zero])).map _
  rw [mul_inv x, inv_mul_cancel_right, ← mul_inv x, cn] at e₁
  rw [cPoint_zero, C.face, C.face] at e₂
  rw [cPoint_zero, C.face] at e₃
  rw [cn, cPoint_y, C.s01 _ (p.g.b ^ N), e₃, e₂, e₁, _root_.mul_assoc, _root_.mul_assoc, hu.mul_right_inj, ← Units.val_mul,
    ← Units.val_mul, Units.val_inj, ← key] at e₄
  have a₁ := congrArg Additive.ofMul e₄
  have a₂ := congrArg Additive.ofMul m
  have a₃ := congrArg Additive.ofMul z₀
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one, TorusExt.charVal] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₁ + a₂ - a₃

end Main

end GlobalTheory.SymFrame
end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_sq_eq_of_symmetric_thetaElement : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p : QkPt D.toPre F N) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (w₀ : W0 U.toUnifPre) (w : Frm D.toPre F N p.g.b), w₀.IsGen → w.IsGen → (∀ t t' s s', U.ExpandsF F N w₀ t s → U.ExpandsF F N w₀ t' s' → IsActOf A.A A.L N θ t t' → PhiRel D.toPre F N p w s s') → (∃ nu : LB.Gen (negLB A.A A.L N (TFK (R := R) F)), nu.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (symGen A.A A.L N θ nu) (LB.oneGen A.L)) → ∀ ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4) ![(𝟙 D.toPre.P.A ^ (N + 1)).left, (𝟙 D.toPre.P.A ^ N).left, 𝟙 _, (1 : D.toPre.P.A ⟶ D.toPre.P.A).left] ![1, -1, -(2 * (N : ℤ) + 1), 2 * (N : ℤ) + 1]), Normd ν → ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J ^ 2 = val (p.g.s p.y) (𝟙 _) z J * val ν p.g.b.left z J := by
  first | exact @GlobalTheory.SymFrame.sq_frame_of_symmetric | exact GlobalTheory.SymFrame.sq_frame_of_symmetric | (intros; apply GlobalTheory.SymFrame.sq_frame_of_symmetric <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.UT.PhiOrder

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

def pot (θ : A → A → A → U) (b : A) (n : ℕ) : U := ∏ j ∈ Finset.range n, cubN θ j 1 b b

theorem pot_zero (b : A) : Additive.ofMul (pot θ b 0) = 0 := by simp [pot]

theorem pot_one (b : A) : Additive.ofMul (pot θ b 1) = 0 := by simp [pot, cubN]

theorem pot_two (h : IsCub θ) (b : A) : Additive.ofMul (pot θ b 2) = 0 := by
  simp [pot, cubN, Finset.prod_range_succ, h.face]

theorem cub_eq_pot (h : IsCub θ) (b : A) (i j l : ℕ) :
    Additive.ofMul (θ (b ^ i) (b ^ j) (b ^ l)) = Additive.ofMul (pot θ b (i + j + l)) - Additive.ofMul (pot θ b (i + j)) -
      Additive.ofMul (pot θ b (i + l)) - Additive.ofMul (pot θ b (j + l)) + Additive.ofMul (pot θ b i) +
      Additive.ofMul (pot θ b j) + Additive.ofMul (pot θ b l) := by
  set P : ℕ → Additive U := fun n => Additive.ofMul (pot θ b n) with hP
  have P0 : P 0 = 0 := pot_zero b
  have P1 : P 1 = 0 := pot_one b
  have P2 : P 2 = 0 := pot_two h b
  show _ = P (i + j + l) - P (i + j) - P (i + l) - P (j + l) + P i + P j + P l
  have step : ∀ l : ℕ, (∀ i, Additive.ofMul (θ (b ^ i) (b ^ 1) (b ^ l)) =
      P (i + 1 + l) - P (i + 1) - P (i + l) - P (1 + l) + P i + P 1 + P l) → ∀ j i,
      Additive.ofMul (θ (b ^ i) (b ^ j) (b ^ l)) =
        P (i + j + l) - P (i + j) - P (i + l) - P (j + l) + P i + P j + P l := by
    intro l H j
    induction j with
    | zero => intro i; rw [pow_zero, h.face₂, ofMul_one, add_zero, zero_add, P0]; abel
    | succ j ih =>
      intro i
      have c := congrArg Additive.ofMul (h.coc (b ^ i) (b ^ j) (b ^ 1) (b ^ l))
      rw [← pow_add, ← pow_add, ofMul_mul, ofMul_mul, H, H, ih] at c
      rw [← add_assoc i j 1]
      linear_combination (norm := abel) -c
  have base : ∀ i, Additive.ofMul (θ (b ^ i) (b ^ 1) (b ^ 1)) =
      P (i + 1 + 1) - P (i + 1) - P (i + 1) - P (1 + 1) + P i + P 1 + P 1 := by
    intro i
    have e₁ : P (i + 1 + 1) = P (i + 1) + Additive.ofMul (cubN θ (i + 1) 1 b b) := by
      simp only [hP, pot, Finset.prod_range_succ _ (i + 1), ofMul_mul]
    have e₂ : P (i + 1) = P i + Additive.ofMul (cubN θ i 1 b b) := by
      simp only [hP, pot, Finset.prod_range_succ _ i, ofMul_mul]
    have e₃ : Additive.ofMul (cubN θ (i + 1) 1 b b) = Additive.ofMul (cubN θ i 1 b b) +
        Additive.ofMul (θ (b ^ i) (b ^ 1) (b ^ 1)) := by
      simp only [cubN, Finset.prod_range_succ _ i, ofMul_mul, _root_.one_mul, pow_one]
    rw [show 1 + 1 = 2 from rfl, P2, P1]
    linear_combination (norm := abel) - e₁ + e₂ - e₃
  refine step l (fun i => ?_) j i
  rw [h.s12, step 1 base l i, add_right_comm i l 1, add_comm l 1]
  abel

theorem cubN_eq_pot (h : IsCub θ) (b : A) (n a c x : ℕ) :
    Additive.ofMul (cubN θ n (b ^ a) (b ^ c) (b ^ x)) = Additive.ofMul (pot θ b (a + c * n + x)) -
      Additive.ofMul (pot θ b (a + x)) - Additive.ofMul (pot θ b (a + c * n)) + Additive.ofMul (pot θ b a) -
      n • (Additive.ofMul (pot θ b (c + x)) - Additive.ofMul (pot θ b c) - Additive.ofMul (pot θ b x)) := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    rw [cubN, Finset.prod_range_succ, ofMul_mul, ← cubN, ih, ← pow_mul, ← pow_add, cub_eq_pot h, mul_add c n 1,
      _root_.mul_one, ← add_assoc a, succ_nsmul]
    abel

theorem const_eq_one (h : IsCub θ) (b : A) (m k : ℕ) (hk : k = 2 * m + 1) (S : ℕ → U) (s w ψ ρ τ E : U)
    (hS : ∀ i, S i * cubN θ i 1 (b ^ k) b = s ^ i) (hτ : τ * cubN θ k 1 b (b ^ k) = s ^ k)
    (hE : τ = E * ψ ^ 2 * ρ ^ 2)
    (hw : w ^ k * ((E * pot θ b (2 * k)) ^ m * (pot θ b k ^ (k + 2 * m))⁻¹) = ψ * ρ) :
    (∏ i ∈ Finset.range k, H1.hv θ k ((b ^ k) ^ i) b (b ^ (k - 1 - i)) * (S i * w)) * (ψ ^ k * ρ ^ k)⁻¹ = 1 := by
  set P : ℕ → Additive U := fun n => Additive.ofMul (pot θ b n) with hP
  have P0 : P 0 = 0 := pot_zero b
  have P1 : P 1 = 0 := pot_one b
  have cN : ∀ n a c x, Additive.ofMul (cubN θ n (b ^ a) (b ^ c) (b ^ x)) = P (a + c * n + x) - P (a + x) - P (a + c * n) +
    P a - n • (P (c + x) - P c - P x) := cubN_eq_pot h b
  have cT : ∀ i j l, Additive.ofMul (θ (b ^ i) (b ^ j) (b ^ l)) =
    P (i + j + l) - P (i + j) - P (i + l) - P (j + l) + P i + P j + P l := cub_eq_pot h b
  let f : ℕ → Additive U := fun i => P (k * i + (k - i)) + k • P (k - i) - P (k - i) - P (k * i)
  let d : Additive U := Additive.ofMul s + P (k + 1) - P k
  have term : ∀ i ∈ Finset.range k, Additive.ofMul (H1.hv θ k ((b ^ k) ^ i) b (b ^ (k - 1 - i)) * (S i * w)) =
      (f (i + 1) - f i) + (i • d + Additive.ofMul w) := by
    intro i hi
    obtain ⟨x, hx⟩ : ∃ x, k = i + 1 + x := ⟨k - (i + 1), by have := Finset.mem_range.1 hi; omega⟩
    have x₁ : k - 1 - i = x := by omega
    have x₂ : k - (i + 1) = x := by omega
    have x₃ : k - i = 1 + x := by omega
    have a₁ := cN k (k * i) 1 x
    have a₂ := cT (k * i) x 1
    have a₃ := cN i 0 k 1
    have a₄ := congrArg Additive.ofMul (hS i)
    rw [pow_one] at a₁ a₂ a₃
    rw [pow_zero, zero_add, zero_add, P0, P1] at a₃
    rw [_root_.one_mul, P1, ← Nat.mul_succ] at a₁
    rw [P1, add_assoc (k * i), add_comm x 1] at a₂
    rw [ofMul_mul, a₃, ofMul_pow] at a₄
    simp only [f, d, H1.hv, ofMul_mul, ofMul_inv, x₁, x₂, x₃, ← pow_mul, a₁, a₂, Nat.succ_eq_add_one]
    linear_combination (norm := module) a₄
  have gauss : ∑ i ∈ Finset.range k, i = m * k := by
    have := Finset.sum_range_id_mul_two k
    rw [show k - 1 = 2 * m by omega] at this
    nlinarith
  apply Additive.ofMul.injective
  rw [ofMul_mul, ofMul_prod, Finset.sum_congr rfl term, Finset.sum_add_distrib, Finset.sum_range_sub,
    Finset.sum_add_distrib, Finset.sum_nsmul_assoc, gauss, Finset.sum_const, Finset.card_range]
  have a₁ := cN k 0 1 k
  rw [pow_zero, pow_one, zero_add, zero_add, _root_.one_mul, ← two_mul, add_comm 1 k, P0, P1] at a₁
  have a₂ := congrArg Additive.ofMul hτ
  have a₃ := congrArg Additive.ofMul hw
  rw [ofMul_mul, a₁, hE] at a₂
  simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one, f, d, Nat.sub_self, add_zero, mul_zero, zero_add, Nat.sub_zero,
    P0] at a₂ a₃ ⊢
  change k • _ + (m • (_ + P (2 * k)) + -((k + 2 * m) • P k)) = _ at a₃
  subst hk
  linear_combination (norm := module) a₃ - m • a₂

end Alg

section Formal

variable {A U : Type} [CommGroup A] [CommGroup U]

def wN (h : A → U) (x : A) (j : ℕ) : U :=
  h (x ^ (j + 1)) * (h (x ^ j))⁻¹ * (h (x ^ 2) ^ j)⁻¹ * h x ^ (2 * j) * (h x)⁻¹ * h 1 * (h 1 ^ j)⁻¹

theorem prod_wN (h : A → U) (x : A) (n : ℕ) (T : ℤ) (hT : 2 * T = n * (n - 1)) :
    Additive.ofMul (∏ j ∈ Finset.range n, wN h x j) = Additive.ofMul (h (x ^ n)) - T • Additive.ofMul (h (x ^ 2)) +
      (2 * T - n) • Additive.ofMul (h x) + (n - 1 - T) • Additive.ofMul (h 1) := by
  induction n generalizing T with
  | zero =>
    obtain rfl : T = 0 := by simpa using hT
    simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ofMul_mul, ih (T - n) (by push_cast at hT; linear_combination hT)]
    simp only [wN, ofMul_mul, ofMul_inv, ofMul_pow]
    push_cast
    module

theorem weight_eq (h : A → U) (x : A) (m k : ℕ) (hk : k = 2 * m + 1) :
    ((h (x ^ k * (x ^ k)⁻¹ * x ^ k) * (h (x ^ k * (x ^ k)⁻¹))⁻¹ * (h (x ^ k * x ^ k))⁻¹ * (h ((x ^ k)⁻¹ * x ^ k))⁻¹ *
        h (x ^ k) * h (x ^ k)⁻¹ * h (x ^ k) * (h 1)⁻¹ * (h (x ^ k)⁻¹ * (h (x ^ k))⁻¹)⁻¹) *
        ∏ j ∈ Finset.range (2 * k), wN h x j) ^ m * ((∏ j ∈ Finset.range k, wN h x j) ^ (k + 2 * m))⁻¹ =
      h x ^ ((k ^ 2 : ℕ) : ℤ) * h (x ^ k) ^ (-((1 : ℕ) : ℤ)) * h 1 ^ (((1 : ℕ) : ℤ) - (k ^ 2 : ℕ)) := by
  have a₁ := prod_wN h x (2 * k) (k * (2 * k - 1)) (by push_cast; ring)
  have a₂ := prod_wN h x k (m * k) (by rw [hk]; push_cast; ring)
  rw [mul_inv_cancel, inv_mul_cancel, _root_.one_mul, ← pow_add, ← two_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow, a₁, a₂]
  subst hk
  push_cast
  module

end Formal

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

def Rep (V : ∀ (T : Over (Spec (CommRingCat.of R))) (_ : T ⟶ D.P.A) (z : T.left),
      ((T.left ⟶ D.P.A.left) → D.P.L.ι) → (T.left.presheaf.stalk z)ˣ)
    (W : ∀ (U : Type) [CommGroup U], ((D.P.A ⟶ D.P.A) → U) → U) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (D.P.A.left ⟶ D.P.A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb D.P.L φ ε)),
    t.IsGen ∧ (∀ (U : Type) [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U),
      ∏ k, h (φ k) ^ ε k = W U (fun a => h a.left)) ∧
    ∀ T (x : T ⟶ D.P.A) z J, Good D.P.L z J → val t x.left z J = V T x z J

variable {D}

theorem Rep.mul {V V' W W'} (h : Rep D V W) (h' : Rep D V' W') :
    Rep D (fun T x z J => V T x z J * V' T x z J) (fun U _ g => W U g * W' U g) := by
  obtain ⟨K, _, φ, ε, t, ht, hw, hv⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', hw', hv'⟩ := h'
  exact ⟨K ⊕ K', inferInstance, _, _, LB.mulGen D.P.L _ _ _ _ t t', mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ g => prod_sum₂ _ (hw U g) (hw' U g),
    fun T x z J hJ => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv T x z J hJ) (hv' T x z J hJ))⟩

theorem Rep.inv {V W} (h : Rep D V W) : Rep D (fun T x z J => (V T x z J)⁻¹) (fun U _ g => (W U g)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, hw, hv⟩ := h
  exact ⟨K, inferInstance, _, _, LB.invGen D.P.L _ _ t, invGen_isGen _ _ _ _ ht,
    fun U _ g => prod_neg _ _ (hw U g),
    fun T x z J hJ => (val_inv _ _).trans (congrArg (·⁻¹) (hv T x z J hJ))⟩

theorem Rep.one : Rep D (fun _ _ _ _ => 1) (fun _ _ _ => 1) :=
  ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen D.P.L, fun _ _ =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    fun _ _ _ => Fintype.prod_empty _, fun _ _ _ _ _ => val_one _⟩

theorem Rep.prod {V : ℕ → _} {W : ℕ → _} (h : ∀ j, Rep D (V j) (W j)) (n : ℕ) :
    Rep D (fun T x z J => ∏ j ∈ Finset.range n, V j T x z J) (fun U _ g => ∏ j ∈ Finset.range n, W j U g) := by
  induction n with
  | zero => exact Rep.one
  | succ n ih => simpa only [Finset.prod_range_succ] using ih.mul (h n)

theorem Rep.pow {V W} (h : Rep D V W) (n : ℕ) : Rep D (fun T x z J => V T x z J ^ n) (fun U _ g => W U g ^ n) := by
  simpa only [Finset.prod_const, Finset.card_range] using Rep.prod (fun _ => h) n

theorem comp_idPow {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) (k : ℕ) : x ≫ (𝟙 D.P.A ^ k) = x ^ k :=
  (map_pow (preHom x) _ _).trans (congrArg (· ^ k) (Category.comp_id x))

theorem rep_cubN (j : ℕ) : Rep D (fun _ x z J => cubN (th D z J) j 1 x x) (fun _ _ g => wN g (𝟙 _) j) := by
  obtain ⟨t, ht, hv⟩ := exists_cubN D.cub (1 : D.P.A ⟶ D.P.A) (𝟙 _) (𝟙 _) j
  refine ⟨_, inferInstance, _, _, t, ht, fun U _ h => ?_, fun T x z J hJ => ?_⟩
  · rw [_root_.one_mul, _root_.one_mul, ← pow_succ, ← sq]
    apply Additive.ofMul.injective
    simp [wN, Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    module
  · rw [hv T x z J hJ, MonObj.comp_one, Category.comp_id]

theorem rep_cub (k : ℕ) : Rep D (fun _ x z J => th D z J (x ^ k) (x ^ k)⁻¹ (x ^ k))
    (fun _ _ h => h (𝟙 _ ^ k * (𝟙 _ ^ k)⁻¹ * 𝟙 _ ^ k) * (h (𝟙 _ ^ k * (𝟙 _ ^ k)⁻¹))⁻¹ * (h (𝟙 _ ^ k * 𝟙 _ ^ k))⁻¹ *
      (h ((𝟙 _ ^ k)⁻¹ * 𝟙 _ ^ k))⁻¹ * h (𝟙 _ ^ k) * h (𝟙 _ ^ k)⁻¹ * h (𝟙 _ ^ k) * (h 1)⁻¹) := by
  refine ⟨_, inferInstance, _, _, LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
    (lift (𝟙 D.P.A ^ k) (lift (𝟙 D.P.A ^ k)⁻¹ (𝟙 D.P.A ^ k))).left, pullGen_isGen _ _ _ _ D.cub.isGen _,
    fun U _ h => prod_cub _ _ _ h, fun T x z J hJ => ?_⟩
  rw [val_cub D.cub x hJ, show x ≫ (𝟙 D.P.A ^ k)⁻¹ = (x ≫ (𝟙 D.P.A ^ k))⁻¹ from map_inv (preHom x) _, comp_idPow]

theorem rep_sym (k : ℕ) : Rep D (fun _ x z J => val D.sym (x ^ k).left z J)
    (fun _ _ h => h (𝟙 _ ^ k)⁻¹ * (h (𝟙 _ ^ k))⁻¹) := by
  refine ⟨_, inferInstance, _, _, LB.pullGen D.P.L _ _ D.sym (𝟙 D.P.A ^ k).left, pullGen_isGen _ _ _ _ D.sym_gen _,
    fun U _ h => ?_, fun T x z J hJ => ?_⟩
  · rw [Fin.prod_univ_two]
    show h ((𝟙 D.P.A ^ k) ≫ ι[D.P.A]).left ^ (1 : ℤ) * h ((𝟙 D.P.A ^ k).left ≫ 𝟙 _) ^ (-1 : ℤ) = _
    rw [zpow_one, zpow_neg_one, Category.comp_id]; rfl
  · rw [val_pull hJ, ← Over.comp_left, comp_idPow]

theorem exists_kap (m k : ℕ) (hk : k = 2 * m + 1) :
    ∃ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ k) (k ^ 2) 1), Normd κ ∧
      ∀ T (x : T ⟶ D.P.A) z J, Good D.P.L z J → val κ x.left z J =
        (th D z J (x ^ k) (x ^ k)⁻¹ (x ^ k) * (val D.sym (x ^ k).left z J)⁻¹ * pot (th D z J) x (2 * k)) ^ m *
          (pot (th D z J) x k ^ (k + 2 * m))⁻¹ := by
  obtain ⟨K, _, φ, ε, t, ht, hw, hv⟩ := ((((rep_cub (D := D) k).mul (rep_sym k).inv).mul
    (Rep.prod rep_cubN (2 * k))).pow m).mul ((Rep.prod rep_cubN k).pow (k + 2 * m)).inv
  obtain ⟨κ, hκ, vκ⟩ := exists_gen D.P.isLB (K' := Fin 3)
    (φ' := ![𝟙 _, (𝟙 D.P.A ^ k).left, (1 : D.P.A ⟶ D.P.A).left])
    (ε' := ![((k ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - (k ^ 2 : ℕ)]) (fun U _ h => by
      rw [hw U h, Fin.prod_univ_three]
      exact weight_eq (fun a : D.P.A ⟶ D.P.A => h a.left) (𝟙 _) m k hk) t ht
  refine ⟨κ, ⟨hκ, corr_of_val D.P.isLB fun y J hJ => ?_⟩, fun T x z J hJ => (vκ _ _ z J hJ).trans (hv T x z J hJ)⟩
  have C : IsCub (th D (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J) := isCub_cubV D.cub hJ
  have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left = eSec D.P.A := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  have e := (vκ _ _ y J hJ).trans (hv (𝟙_ (Over (Spec (CommRingCat.of R)))) 1 y J hJ)
  have s₁ := val_corr hJ D.sym_rig (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_one] at s₁
  simp only [one_pow, C.face, C.N_one, Finset.prod_const_one, inv_one, _root_.mul_one, _root_.one_mul] at e
  rw [o, s₁, inv_one, one_pow] at e
  rw [val_pull hJ, Category.id_comp, val_one]
  exact e

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem tau_diag (hB : D.TauBimult) (hE : D.PsiEven) {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F)
    {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (y : D.X) :
    val (D.tau y y) (σ.left ≫ jFK (R := R) F) z J =
      th D z J (cP D T y) (cP D T y)⁻¹ (cP D T y) * (val D.sym (cP D T y).left z J)⁻¹ *
        val (D.psi y) (σ.left ≫ jFK (R := R) F) z J ^ 2 * val D.rigK (σ.left ≫ jFK (R := R) F) z J ^ 2 := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have e : ∀ a b : D.X, val (D.tau a b) (σ.left ≫ jFK (R := R) F) z J =
      val (D.psi (a + b)) (σ.left ≫ jFK (R := R) F) z J * (val (D.psi a) (σ.left ≫ jFK (R := R) F) z J)⁻¹ *
        (val (D.psi b) (σ.left ≫ jFK (R := R) F) z J)⁻¹ * (val D.rigK (σ.left ≫ jFK (R := R) F) z J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have c0 : cP D T 0 = 1 := by simpa using cPoint_nsmul D T 0 y
  have cn : cP D T (-y) = (cP D T y)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← cPoint_add, neg_add_cancel, c0]
  have t₀ := tau_mul σ hJ hB 0 0 y
  rw [c0, C.face, add_zero, e, zero_add] at t₀
  have t₁ := tau_mul σ hJ hB y (-y) y
  rw [add_neg_cancel, cn, e 0 y, e (-y) y, zero_add, neg_add_cancel] at t₁
  have t₂ := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
    (val_corr hJ (hE y) (σ.left ≫ jFK (R := R) F))
  have a₁ : (σ.left ≫ jFK (R := R) F) ≫ D.xK y = (cP D T y).left := by
    rw [← comp_cP D σ, Category.assoc]
    exact congrArg (σ.left ≫ ·) (Category.assoc _ _ _).symm
  rw [a₁] at t₂
  apply Additive.ofMul.injective
  have b₀ := congrArg Additive.ofMul t₀
  have b₁ := congrArg Additive.ofMul t₁
  have b₂ := congrArg Additive.ofMul t₂
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at b₀ b₁ b₂ ⊢
  linear_combination (norm := module) -b₁ - 2 • b₀ + b₂

theorem const_one (hB : D.TauBimult) (hE : D.PsiEven) {k : ℕ} (hk : Odd k) (p : QkPt D F k) (w : Frm D F k p.g.b)
    (hw : TXFrame k p w) (z : (TF (R := R) F).left) (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι)
    (hJ : Good D.P.L z J) :
    (∏ i ∈ Finset.range k, H1.hv (th D z J) k ((p.g.b ^ k) ^ i) p.g.b (p.g.b ^ (k - 1 - i)) *
        (val (p.g.s (i • p.y)) (Over.Hom.left (𝟙 (TF (R := R) F))) z J * val w (Over.Hom.left (𝟙 (TF (R := R) F))) z J)) *
      (val (GeneratorPullback.powGen D.P.L _ _ (D.psi p.y) k) ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J *
        val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J)⁻¹ = 1 := by
  obtain ⟨m, hm⟩ := hk
  have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ
  obtain ⟨κ, hκ, vκ⟩ := exists_kap (D := D) m k hm
  have h₁ := hw.2.2 κ hκ z J hJ
  rw [vκ _ p.g.b z J hJ] at h₁
  have c0 : cP D (TF (R := R) F) 0 = 1 := by simpa using cPoint_nsmul D (TF (R := R) F) 0 p.y
  have s0 : val (p.g.s 0) (Over.Hom.left (𝟙 (TF (R := R) F))) z J = 1 := by
    have := gt_mul (𝟙 (TF (R := R) F)) hJ p.g 0 0
    rw [c0, C.face, add_zero] at this
    exact (mul_left_cancel this).symm
  have hS : ∀ i : ℕ, val (p.g.s (i • p.y)) (Over.Hom.left (𝟙 (TF (R := R) F))) z J *
      cubN (th D z J) i 1 (p.g.b ^ k) p.g.b = val (p.g.s p.y) (Over.Hom.left (𝟙 (TF (R := R) F))) z J ^ i := fun i => by
    have := gt_nsmul (𝟙 (TF (R := R) F)) hJ p.g 0 p.y i
    rwa [zero_add, c0, s0, _root_.one_mul, cPoint_y, Category.id_comp] at this
  have hτ := chain_val (𝟙 (TF (R := R) F)) hJ p p.y
  rw [Category.id_comp, cPoint_y] at hτ
  have hd := tau_diag hB hE (𝟙 (TF (R := R) F)) hJ p.y
  rw [cPoint_y] at hd
  have r₁ : rigV D (TF (R := R) F).hom z J =
      val D.rigK ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J := by
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    refine congrArg (fun q => rigV D q z J) ?_
    rw [Over.id_left, Category.id_comp]; rfl
  have r₂ : val (D.psi p.y) (jFK (R := R) F) z J =
      val (D.psi p.y) ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J :=
    congrArg (fun q => val (D.psi p.y) q z J) (Category.id_comp _).symm
  have key := const_eq_one C p.g.b m k hm _ _ _ _ _ _ _ hS hτ hd (h₁.trans (congrArg₂ (· * ·) r₂ r₁))
  refine Eq.trans ?_ key
  exact congrArg₂ (· * ·) rfl (congrArg (·⁻¹) (congrArg₂ (· * ·) (map_pow _ _ _) (map_pow _ _ _)))

theorem phiPow_eq_one (hG : GlobalFnsSt) (hB : D.TauBimult) (hE : D.PsiEven) {k : ℕ} (hk : Odd k) (p : QkPt D F k)
    (w : Frm D F k p.g.b) (hX : TXFrame k p w) (ss : Fin (k + 1) → Fam D F k)
    (H : ∀ i : Fin k, PhiRel D F k p w (ss i.castSucc) (ss i.succ)) : ss (Fin.last k) = ss 0 := by
  have hw : w.IsGen := hX.1
  choose u hu hc using fun α => (gen_phi hG p w hw α).1
  choose v hv hcv using fun α => (gen_fe (D := D) (F := F) hG k p.y α).1
  have hb : DegPre.trF D F p.y = DegPre.trPt D F (p.g.b ^ k) := by rw [trF_eq, cPoint_y]
  have hV : ∀ α, ∃ a : Γ((TF (R := R) F).left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J),
      Good D.P.L z J → ((∏ i ∈ Finset.range k,
        val (u (α + i • p.y)) (r ≫ (DegPre.trPt D F (p.g.b ^ (k - 1 - i))).left) z J) * (val (v α) r z J)⁻¹).val =
        gs (r ≫ (fst (TF (R := R) F) D.P.A).left) z ⊤ a := by
    intro α
    obtain ⟨K', _, φ', ε', t', ht', hf, hvt⟩ := H1.exists_gen_prod D.P.L (fun _ => Fin 4 ⊕ Fin 4)
      (fun i j => (DegPre.trPt D F (p.g.b ^ (k - 1 - i))).left ≫ DegPre.phiφ D F p.y (α + i • p.y) p.g.b j)
      (fun _ => DegPre.deltaε k)
      (fun i => LB.pullGen D.P.L _ _ (u (α + i • p.y)) (DegPre.trPt D F (p.g.b ^ (k - 1 - i))).left)
      (fun i => pullGen_isGen _ _ _ _ (hu _) _) k
    obtain ⟨a, ha⟩ := H1.exists_const D.P.L D.P.isLB (fst (TF (R := R) F) D.P.A).left (surj_appTop D F hG)
      (LB.mulGen D.P.L _ _ _ _ t' (LB.invGen D.P.L _ _ (v α)))
      (mulGen_isGen _ _ _ _ _ _ _ ht' (invGen_isGen _ _ _ _ (hv α))) (fun U _ h => by
        rw [Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [hf U h]
        exact H1.tel_formal p.g.b p.y α hb h)
    refine ⟨a, fun Z r z J hJ => ?_⟩
    rw [← ha Z r z J hJ, val_mul hJ, val_inv, hvt Z r z J hJ]
    exact congrArg Units.val (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => (val_pull hJ _ _ _).symm) rfl)
  choose a ha using hV
  have hz : (DegPre.zF D F).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, show DegPre.zF D F ≫ fst _ _ = 𝟙 _ from lift_fst _ _]; rfl
  have hconst : ∀ α, a α = 1 := by
    intro α
    refine fn_ext fun z _ => ?_
    choose I hI using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
    have e₁ := ha α _ (DegPre.zF D F).left z I hI
    rw [hz] at e₁
    rw [← e₁, H1.const_at_zero hG p w hw u hu hc v hcv α z I hI, const_one hB hE hk p w hX z I hI,
      gs_eq _ z ⊤ trivial, map_one, map_one, Units.val_one]
  refine DVR.fam_ext fun β j => sec_ext_val D.P.isLB (fun y J hJ => ?_) j
  obtain ⟨α, rfl⟩ : ∃ α, α + k • p.y = β := ⟨β - k • p.y, sub_add_cancel _ _⟩
  have e₁ := H1.iter p w u hu hc ss H k (Nat.lt_succ_self k) α _ (𝟙 _) y J hJ
  have e₂ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ (v α)).1 ((ss 0).fe p.y α (v α) (hv α) (hcv α)) _ (𝟙 _) y J hJ
  have e₃ := ha α _ (𝟙 _) y J hJ
  rw [hconst α, gs_eq _ y ⊤ trivial, map_one, map_one] at e₃
  rw [e₂, hb]
  refine e₁.trans ?_
  rw [mul_inv_eq_one.1 (Units.ext e₃)]

theorem main : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) (w : Frm D.toPre F N p.g.b), TXFrame N p w → ∀ ss : Fin (N + 1) → Fam D.toPre F N, (∀ i : Fin N, PhiRel D.toPre F N p w (ss i.castSucc) (ss i.succ)) → ss (Fin.last N) = ss 0 :=
  fun hL _ _ _ _ _ _ D _ _ _ _ _ hN p w hX ss H =>
    phiPow_eq_one hL.1.globalFns D.tau_bimult D.psi_even hN p w hX ss H

end GlobalTheory.UT.PhiOrder

end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.symmetricFrame_phi_pow_order_eq_id : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) (w : Frm D.toPre F N p.g.b), TXFrame N p w → ∀ ss : Fin (N + 1) → Fam D.toPre F N, (∀ i : Fin N, PhiRel D.toPre F N p w (ss i.castSucc) (ss i.succ)) → ss (Fin.last N) = ss 0 := by
  atlas_forward_decl GlobalTheory.UT.PhiOrder.main
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.SymLiftPhi

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_ratio (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k) {w w' : Frm D F k p.g.b} (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ c : F, (∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val ^ k = gs (𝟙 _) z ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c ^ k)) * (val w (𝟙 _) z J).val ^ k) ∧
      ∀ s t : Fam D F k, PhiRel D F k p w s t → PhiRel D F k p w' s (c • t) := by
  obtain ⟨a, ha⟩ := H1.exists_const D.P.L D.P.isLB (𝟙 _) (fun a => ⟨a, rfl⟩)
    (LB.mulGen D.P.L _ _ _ _ w' (LB.invGen D.P.L _ _ w))
    (mulGen_isGen _ _ _ _ _ _ _ hw' (invGen_isGen _ _ _ _ hw)) (fun U _ h => by
      refine (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ rfl (prod_neg _ _ rfl)).trans ?_
      exact mul_inv_cancel _)
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
      (val w' r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * (val w r z J).val := by
    intro Z r z J hJ
    have e := ha Z r z J hJ
    rw [val_mul hJ, val_inv, Category.comp_id] at e
    refine Eq.trans ?_ (congrArg (· * (val w r z J).val) e)
    rw [← Units.val_mul, inv_mul_cancel_right]
  refine ⟨c, fun z J hJ => ?_, fun s t h => ?_⟩
  · rw [hv _ _ z J hJ, mul_pow, gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial, map_pow, map_pow, map_pow]
  · rw [phiRel_iff hG p w hw] at h
    rw [phiRel_iff hG p w' hw']
    intro α β hαβ T ρ z J hJ
    refine (sval_smul c t β ρ.left z hJ).trans ?_
    rw [h α β hαβ T ρ z J hJ, val_mul hJ, val_mul hJ]
    simp only [Units.val_mul]
    rw [hv _ _ z J hJ]
    simp only [Over.comp_left]
    ring

theorem phiRel_of_val_eq (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k) {w w' : Frm D F k p.g.b} (hw : w.IsGen)
    (hw' : w'.IsGen) (h : ∀ z J, Good D.P.L z J → val w (𝟙 _) z J = val w' (𝟙 _) z J) {s t : Fam D F k}
    (hs : PhiRel D F k p w' s t) : PhiRel D F k p w s t := by
  have hc := corr_of_val D.P.isLB h
  rw [phiRel_iff hG p w' hw'] at hs
  rw [phiRel_iff hG p w hw]
  intro α β hαβ T ρ z J hJ
  rw [hs α β hαβ T ρ z J hJ, val_mul hJ, val_mul hJ, val_corr hJ hc]

end GlobalTheory.UT.SymLiftPhi

namespace GlobalTheory.UT
open SymLiftPhi in

theorem symLift_acts_as_phi : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) x, QkToAkU U.toUnifPre F N p x → ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ w, TXFrame N p w → ∀ t t' s s', U.ExpandsF F N w₀ t s → U.ExpandsF F N w₀ t' s' → IsActOf A.A A.L N θ t t' → PhiRel D.toPre F N p w s s' := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ N hN p x hx θ hθ w₀ hw₀ w hw t t' s s' hs hs' hact
  have hN1 : 1 ≤ N := hN.pos
  have gf : GlobalFnsSt := hL.1.globalFns
  obtain ⟨hxN, hx'⟩ := hx w₀ hw₀
  obtain ⟨w', hw', H⟩ := hx' θ hθ.pt_eq
  obtain ⟨b₁, b₂⟩ := (expBijF_and_expandsF_lin hL R I hI D A G hG U).1 F N hN1 w₀ hw₀
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL.1 R I D F N hN1 p w hw.1
  obtain ⟨Φ', hΦ'⟩ := phiFun_of hL.1 R I D F N hN1 p w' hw'
  obtain ⟨c, hc, hcΦ⟩ := exists_ratio gf p hw.1 hw'
  have e : Φ' = c • Φ := LinearMap.ext fun u => ((hΦ' _ _).1 (hcΦ u _ ((hΦ _ _).2 rfl))).symm
  have h₁ : ∀ u, (Φ ^ N) u = u := fun u => by
    have := GlobalTheory.T.symmetricFrame_phi_pow_order_eq_id hL R I hI D F N hN p w hw (fun i => (Φ ^ (i : ℕ)) u) (fun i => (hΦ _ _).2 (by
      simp [pow_succ']))
    simpa using this
  have h₂ : ∀ u, (Φ' ^ N) u = u := fun u => by
    choose act hact using fun v => GlobalTheory.ThetaNu.exists_isActOf A.isLB θ v
    obtain ⟨v, hv, -⟩ := b₂ u
    have key : ∀ i : ℕ, U.ExpandsF F N w₀ (act^[i] v) ((Φ' ^ i) u) := fun i => by
      induction i with
      | zero => exact hv
      | succ i ih =>
        obtain ⟨u', hu', -⟩ := b₁ (act^[i + 1] v)
        have := (hΦ' _ _).1 (H _ _ _ _ ih hu' (by rw [Function.iterate_succ_apply']; exact hact _))
        rw [pow_succ', Module.End.mul_apply, ← this]
        exact hu'
    have hp := GlobalTheory.thetaGrp_act_iterate_eq_of_pow_eq_one _ A.A A.L A.isLB N _ θ N (hθ.pt_eq ▸ hxN) hθ.pow_eq
      (fun i => act^[i] v) (fun i => by
        rw [Fin.val_succ, Fin.val_castSucc, Function.iterate_succ_apply']; exact hact _)
    have hp' : act^[N] v = v := SecOps.sec_ext hp
    have kN := key N
    rw [hp'] at kN
    exact (b₁ v).unique kN hv
  by_cases hcN : c ^ N = 1
  · have hT : TXFrame N p w' := ⟨hw', GlobalTheory.T.frame_sq_eq_of_symmetric_thetaElement hL R I hI D A G hG U F N hN1 p θ w₀ w' hw₀ hw' H hθ.sym,
      fun κ hκ z J hJ => by
        have a := hc z J hJ
        rw [hcN, map_one, gs_eq _ z ⊤ trivial, map_one, map_one, _root_.one_mul,
          ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val] at a
        rw [Units.ext a]
        exact hw.2.2 κ hκ z J hJ⟩
    exact phiRel_of_val_eq gf p hw.1 hw' ((GlobalTheory.UT.SymFrame.main hL R I hI D F N hN p).2 w w' hw hT) (H t t' s s' hs hs' hact)
  · have z : ∀ u : Fam D.toPre F N, u = 0 := fun u => by
      have a := h₂ u
      rw [e, smul_pow, LinearMap.smul_apply, h₁] at a
      have b : (c ^ N - 1) • u = 0 := by rw [sub_smul, a, one_smul, sub_self]
      exact (smul_eq_zero.1 b).resolve_left (sub_ne_zero.2 hcN)
    exact (hΦ _ _).2 ((z _).trans (z _).symm)

end GlobalTheory.UT
end
end
