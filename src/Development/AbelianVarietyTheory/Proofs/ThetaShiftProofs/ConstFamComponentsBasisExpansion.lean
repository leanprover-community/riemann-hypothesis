import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSecIsMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSub
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFETranslateFeTranslate
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSmulMemSpanOfExpandsAt

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstFam

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
  {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)
  (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] (hG : GlobalFnsSt) {j : ℕ} (hj : 1 ≤ j)

theorem exists_basis_of_isExtension {K L : Type} [Field K] [Field L] [Algebra K L] {V W : Type} [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module L W] {g : V →ₛₗ[algebraMap K L] W} (hg : IsExtension g) {I : Type}
    (v : Module.Basis I K V) : ∃ B : Module.Basis I L W, ∀ i, B i = g (v i) := by
  refine ⟨Module.Basis.mk (linearIndependent_of_isExtension hg v.linearIndependent) ?_,
    fun i => Module.Basis.mk_apply _ _ i⟩
  rw [← hg.span, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ Submodule.span K (Set.range v) := v.mem_span x
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul d y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

theorem exists_basis_of_components {L : Type} [Field L] {M : Type} [AddCommGroup M] [Module L M] {C : Type}
    [Finite C] {W : C → Type} [∀ x, AddCommGroup (W x)] [∀ x, Module L (W x)] (p : ∀ x, M →ₗ[L] W x)
    (inj : ∀ m, (∀ x, p x m = 0) → m = 0) {Idx : C → Type} (bs : ∀ x, Module.Basis (Idx x) L (W x))
    (v : ∀ x, Idx x → M) (h₁ : ∀ x i, p x (v x i) = bs x i) (h₂ : ∀ x y i, y ≠ x → p y (v x i) = 0) :
    ∃ B : Module.Basis (Σ x, Idx x) L M, ∀ x i, B ⟨x, i⟩ = v x i := by
  classical
  have := Fintype.ofFinite C
  have key : ∀ x i, LinearMap.pi p (v x i) = Pi.basis bs ⟨x, i⟩ := fun x i => by
    rw [Pi.basis_apply]
    funext y
    by_cases h : y = x
    · subst h
      rw [LinearMap.pi_apply, h₁, Pi.single_eq_same]
    · rw [LinearMap.pi_apply, h₂ x y i h, Pi.single_eq_of_ne h]
  have hb : Function.Bijective (LinearMap.pi p) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun m hm => inj m fun x => congrFun hm x, ?_⟩
    rw [← LinearMap.range_eq_top, eq_top_iff, ← (Pi.basis bs).span_eq, Submodule.span_le]
    rintro _ ⟨⟨x, i⟩, rfl⟩
    exact ⟨v x i, key x i⟩
  refine ⟨(Pi.basis bs).map (LinearEquiv.ofBijective _ hb).symm, fun x i => ?_⟩
  rw [Module.Basis.map_apply, LinearEquiv.symm_apply_eq]
  exact (key x i).symm

theorem finite_of_reps {X : Type} [AddCommGroup X] [Module.Finite ℤ X] {j : ℕ} (hj : 1 ≤ j) {C : Type}
    (rep : C → X) (hrep : ∀ α, ∃! x, ∃ mu, rep x + j • mu = α) : Finite C := by
  have : AddGroup.FG X := Module.Finite.iff_addGroup_fg.1 inferInstance
  have := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg X (show j ≠ 0 by omega)
  refine Finite.of_injective
    (fun x => (QuotientAddGroup.mk (rep x) : X ⧸ (nsmulAddMonoidHom j : X →+ X).range)) fun x y h => ?_
  obtain ⟨mu, hmu⟩ := QuotientAddGroup.eq.1 h
  refine (hrep (rep y)).unique ⟨mu, ?_⟩ ⟨0, by rw [smul_zero, add_zero]⟩
  rw [show j • mu = -rep x + rep y from hmu, add_neg_cancel_left]

theorem exists_basis_constFam {C : Type} (rep : C → a.D₀.X) (hrep : ∀ α, ∃! x, ∃ mu, rep x + j • mu = α)
    {Idx : C → Type} (bas : ∀ x, Module.Basis (Idx x) k (SecBMod a.D₀ j (rep x))) :
    ∃ B : Module.Basis (Σ x, Idx x) F (Fam P.toPre F j),
      ∀ x i, B ⟨x, i⟩ = constFam hW F hG hj (rep x) (bas x i) := by
  let _ : Algebra k F := (constF k F).toAlgebra
  have := finite_of_reps hj rep hrep
  choose bs hbs using fun x => exists_basis_of_isExtension (isExtension_pullF hW F j (rep x)) (bas x)
  refine exists_basis_of_components (fun x => famComp P.toPre F j (e (rep x))) (fun m hm => ?_) bs _
    (fun x i => (constFam_self hW F hG hj _ _).trans (hbs x i).symm) (fun x y i h => ?_)
  · refine fam_ext fun χ i => ?_
    obtain ⟨x, ⟨mu, hmu⟩, -⟩ := hrep (e.symm χ)
    have hχ : ∃ nu, e (rep x) + j • nu = χ :=
      ⟨e mu, by rw [← map_nsmul, ← map_add, hmu, LinearEquiv.apply_symm_apply]⟩
    exact congrArg (fun q => LB.Sec.f q i) (FamFree.eq_of_eq_add_nsmul hG m 0 hχ (hm x))
  · refine constFam_off hW F hG hj _ _ _ fun mu hmu => h ?_
    refine (hrep (rep y)).unique ⟨0, by rw [smul_zero, add_zero]⟩ ⟨e.symm mu, e.injective ?_⟩
    rw [map_add, map_nsmul, LinearEquiv.apply_symm_apply, hmu]

end GlobalTheory.ConstFam
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstFam

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
  {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)
  (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] (hG : GlobalFnsSt) {j : ℕ} (hj : 1 ≤ j)

theorem finite_form_le {Y : Type} [AddCommGroup Y] [Module.Finite ℤ Y] (q : LinearMap.BilinForm ℤ Y)
    (hq : ∀ y, y ≠ 0 → 0 < q y y) (n : ℕ) : {y | q y y ≤ n}.Finite := by
  have h0 : ∀ y, 0 ≤ q y y := fun y => by
    by_cases h : y = 0
    · simp [h]
    · exact (hq y h).le
  have : AddGroup.FG Y := Module.Finite.iff_addGroup_fg.1 inferInstance
  have := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg Y (n := 4 * n + 1) (by omega)
  refine Set.Finite.of_finite_image (f := fun y => (QuotientAddGroup.mk y :
    Y ⧸ (nsmulAddMonoidHom (4 * n + 1) : Y →+ Y).range)) (Set.toFinite _) fun y hy y' hy' h => ?_
  obtain ⟨v, hv⟩ := QuotientAddGroup.eq.1 h
  obtain rfl : y' = y + (4 * n + 1) • v := by rw [show (4 * n + 1) • v = -y + y' from hv, add_neg_cancel_left]
  by_contra hne
  have hv0 : v ≠ 0 := fun e => hne (by rw [e, smul_zero, add_zero])
  have a₁ := hq v hv0
  have a₂ := h0 (y + (y + (4 * n + 1) • v))
  have a₃ : q y y ≤ n := hy
  have a₄ : q (y + (4 * n + 1) • v) (y + (4 * n + 1) • v) ≤ n := hy'
  simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at a₂ a₄
  push_cast at a₂ a₄
  have a₅ : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  nlinarith [mul_nonneg (mul_nonneg a₅ a₅) a₁.le, mul_nonneg a₅ a₁.le, mul_nonneg a₅ (sub_nonneg.2 (Int.add_one_le_of_lt a₁))]

include hj in

theorem finite_expo_lt (α : a.D₀.X) (n : ℤ) : {mu | expo a j α mu < n}.Finite := by
  refine Set.Finite.subset ((finite_form_le a.be a.be_pos (2 * n + a.be α α).toNat).preimage
    (add_left_injective α).injOn) fun mu h => ?_
  have h₁ : expo a j α mu < n := h
  have h₂ := two_mul_expo a j α mu
  have h₃ := a.be_symm α mu
  have h₄ : 0 ≤ a.be mu mu := by
    by_cases h : mu = 0
    · simp [h]
    · exact (a.be_pos mu h).le
  have h₅ : a.be mu mu ≤ j * a.be mu mu := le_mul_of_one_le_left h₄ (by exact_mod_cast hj)
  show a.be (mu + α) (mu + α) ≤ _
  simp only [map_add, LinearMap.add_apply]
  omega

include hj in
theorem exists_expo_bound (α : a.D₀.X) : ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ mu, 0 ≤ (m : ℤ) + expo a j α mu := by
  obtain ⟨n, hn⟩ := ((finite_expo_lt hj α 0).image fun mu => expo a j α mu).bddBelow
  refine ⟨(-n).toNat, fun m hm mu => ?_⟩
  by_cases h : expo a j α mu < 0
  · have : n ≤ expo a j α mu := hn ⟨mu, h, rfl⟩
    omega
  · omega

theorem map_add_nsmul (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) (α mu : a.D₀.X) : e (α + j • mu) = e α + j • e mu := by
  rw [map_add, map_nsmul]

theorem eq_or_off (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) (j : ℕ) (α : a.D₀.X) (χ : P.toPre.X) :
    (∃ mu, e (α + j • mu) = χ) ∨ ∀ mu, e α + j • mu ≠ χ := by
  by_cases h : ∃ mu, e α + j • mu = χ
  · obtain ⟨mu, rfl⟩ := h
    exact .inl ⟨e.symm mu, by rw [map_add_nsmul, e.apply_symm_apply]⟩
  · exact .inr fun mu h' => h ⟨mu, h'⟩

include hj in
theorem exists_isIntegralForm (α : a.D₀.X) (s₀ : SecBMod a.D₀ j α) {m : ℕ}
    (hm : ∀ mu, 0 ≤ (m : ℤ) + expo a j α mu) : ∃ f, IsIntegralForm hW j α s₀ m f := by
  have ex : ∀ χ, ∃ t : SecBMod P.toPre j χ, (∀ mu, e (α + j • mu) = χ → HEq t
      ((PowerSeries.X : PowerSeries k) ^ ((m : ℤ) + expo a j α mu).toNat •
        pullB hW j (α + j • mu) (feTranslate a.D₀ j mu α s₀))) ∧ ((∀ mu, e α + j • mu ≠ χ) → t = 0) := fun χ => by
    rcases eq_or_off e j α χ with ⟨mu, rfl⟩ | h
    · refine ⟨(PowerSeries.X : PowerSeries k) ^ ((m : ℤ) + expo a j α mu).toNat •
        pullB hW j (α + j • mu) (feTranslate a.D₀ j mu α s₀), fun mu' h => ?_, fun h => absurd (map_add_nsmul e α mu).symm (h _)⟩
      obtain rfl := FamFree.add_nsmul_inj hj α _ _ (e.injective h)
      rfl
    · exact ⟨0, fun mu h' => absurd ((map_add_nsmul e α mu).symm.trans h') (h _), fun _ => rfl⟩
  choose f h₁ h₂ using ex
  exact ⟨f, fun mu => ⟨hm mu, eq_of_heq (h₁ _ mu rfl)⟩, h₂⟩

variable {hW} in

theorem IsIntegralForm.resF_eq {α : a.D₀.X} {s₀ : SecBMod a.D₀ j α} {m : ℕ} {f : ∀ χ, SecBMod P.toPre j χ}
    (h : IsIntegralForm hW j α s₀ m f) (χ : P.toPre.X) : resF P.toPre F j χ (f χ) =
      toF (R := PowerSeries k) F (PowerSeries.X ^ m) • famComp P.toPre F j χ (constFam hW F hG hj α s₀) := by
  rcases eq_or_off e j α χ with ⟨mu, rfl⟩ | hχ
  · rw [(h.1 mu).2, map_smulₛₗ, resF_pullB, constFam_add_nsmul, smul_smul, map_pow, map_pow, ← zpow_natCast,
      Int.toNat_of_nonneg (h.1 mu).1, zpow_add₀ (toF_X_ne_zero F), zpow_natCast]
  · rw [h.2 χ hχ, map_zero, constFam_off hW F hG hj α s₀ χ hχ, smul_zero]

variable {A : PolAV (Spec (CommRingCat.of (FractionRing (PowerSeries k))))}
  {G : Over (Spec (CommRingCat.of (PowerSeries k)))} [GrpObj G] [IsCommMonObj G]
  (U : Unif (Ideal.span {PowerSeries.X}) P A G)

include hG hj in

theorem exists_expandsAt (α : a.D₀.X) (s₀ : SecBMod a.D₀ j α) : ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
    ∃ (f : ∀ χ, SecBMod P.toPre j χ) (σ : H0 U.LG.L j), IsIntegralForm hW j α s₀ m f ∧
      ∀ n, U.toUnifPre.ExpandsAt n j σ f := by
  obtain ⟨s, ⟨r, hr, σ, f', -, hf', hE⟩, -⟩ := (U.expand j hj).2 (constFam hW _ hG hj α s₀)
  obtain ⟨n₀, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr PowerSeries.X_irreducible
  obtain ⟨m₁, hm₁⟩ := exists_expo_bound hj α
  refine ⟨max n₀ m₁, fun m hm => ?_⟩
  obtain ⟨f, hf⟩ := exists_isIntegralForm hW hj α s₀ (hm₁ m ((le_max_right _ _).trans hm))
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ((le_max_left _ _).trans hm)
  refine ⟨f, SecOps.secScale (scal G.hom (u⁻¹.val * PowerSeries.X ^ d)) σ, hf, fun n =>
    expandsAt_secIsMul _ _ _ _ _ U.toUnifPre n j (u⁻¹.val * PowerSeries.X ^ d) σ _ f' f (fun _ => rfl)
      (fun χ => ?_) (hE n)⟩
  have e₁ : f χ = (u⁻¹.val * PowerSeries.X ^ d : PowerSeries k) • (show SecBMod P.toPre j χ from f' χ) := by
    refine resF_injective P.toPre (FractionRing (PowerSeries k)) j χ ?_
    rw [hf.resF_eq _ hG hj, map_smulₛₗ, (secScal_iff_resF P.toPre _ (famComp _ _ j χ _) _ _).1 (hf' χ), smul_smul,
      ← map_mul, _root_.mul_mul_mul_comm, Units.inv_mul, _root_.one_mul, ← pow_add, add_comm]
  rw [e₁]
  exact fun _ => rfl

include hG hj in

theorem exists_pow_smul_mem_span {C : Type} (rep : C → a.D₀.X) (hrep : ∀ α, ∃! x, ∃ mu, rep x + j • mu = α)
    {Idx : C → Type} (bas : ∀ x, Module.Basis (Idx x) k (SecBMod a.D₀ j (rep x))) (m : (Σ x, Idx x) → ℕ)
    (f : (Σ x, Idx x) → ∀ χ, SecBMod P.toPre j χ)
    (σ : (Σ x, Idx x) → SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ))))
    (hf : ∀ i : Σ x, Idx x, IsIntegralForm hW j (rep i.1) (bas i.1 i.2) (m i) (f i))
    (hE : ∀ i n, U.toUnifPre.ExpandsAt n j (σ i) (f i))
    (s : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ)))) :
    ∃ n : ℕ, (PowerSeries.X : PowerSeries k) ^ n • s ∈ Submodule.span (PowerSeries k) (Set.range σ) := by
  obtain ⟨B, hB⟩ := exists_basis_constFam hW (FractionRing (PowerSeries k)) hG hj rep hrep bas
  obtain ⟨t, ht, h⟩ := exists_smul_mem_span_of_expandsAt U hj B B.span_eq (fun i => PowerSeries.X ^ m i)
    (fun i => pow_ne_zero _ PowerSeries.X_ne_zero) σ f (fun i χ => by
      rw [show B i = _ from hB i.1 i.2]; exact (hf i).resF_eq _ hG hj χ) hE s
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht PowerSeries.X_irreducible
  refine ⟨n, ?_⟩
  have := Submodule.smul_mem _ u⁻¹.val h
  rwa [smul_smul, Units.inv_mul_cancel_left] at this

end GlobalTheory.ConstFam

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam

end GlobalTheory
end
end
