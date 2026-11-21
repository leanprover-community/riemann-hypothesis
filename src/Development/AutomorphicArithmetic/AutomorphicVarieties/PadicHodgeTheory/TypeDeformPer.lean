import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TypeDeformAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoRightExact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module UpperTheory.V.Loc

namespace UpperTheory.V.Loc.Thick

variable {l : ℕ} [Fact l.Prime]

section Mem

variable {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] A V]

theorem mem_Dcr (φ : G →* GQ l) (ρ : Representation A G V) (y : V ⊗[ℚ_[l]] Bcr l) :
    y ∈ Dcr φ ρ ↔ ∀ g, actC φ ρ g y = y := by
  simp [Dcr, Submodule.mem_iInf, sub_eq_zero]

theorem mem_Ddr (φ : G →* GQ l) (ρ : Representation A G V) (y : V ⊗[ℚ_[l]] Bdr l) :
    y ∈ Ddr φ ρ ↔ ∀ g, actD φ ρ g y = y := by
  simp [Ddr, Submodule.mem_iInf, sub_eq_zero]

theorem actC_mul (φ : G →* GQ l) (ρ : Representation A G V) (g h : G) (y : V ⊗[ℚ_[l]] Bcr l) :
    actC φ ρ (g * h) y = actC φ ρ g (actC φ ρ h y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b => simp [actC]

theorem actC_one (φ : G →* GQ l) (ρ : Representation A G V) (y : V ⊗[ℚ_[l]] Bcr l) : actC φ ρ 1 y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b => simp [actC]


theorem mem_FilD_iff (K : FinExt l) (ρ : Representation A ↥(GK K) V) (a : ℤ) (y : V ⊗[ℚ_[l]] Bdr l) :
    y ∈ FilD (GK K).subtype ρ a ↔
      y ∈ DdR ((PP l).PD K) (resCoef ℚ_[l] ρ) ⊓ FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) a := by
  refine and_congr ?_ ?_
  · simp only [SetLike.mem_coe, mem_Ddr, DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun g => ?_
    have : actD (GK K).subtype ρ g y = actVdR ((PP l).PD K) (resCoef ℚ_[l] ρ) g y := by
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul v b =>
        change ρ g v ⊗ₜ[ℚ_[l]] (PP l).actQdR (g : GQ l) b = ρ g v ⊗ₜ[ℚ_[l]] ((PP l).PD K).actdR g b
        rw [(PP l).PD_actdR]
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [this]
  · have : (((PP l).PD (botExt l)).Fil a).restrictScalars ℚ_[l] = (((PP l).PD K).Fil a).restrictScalars ℚ_[l] :=
      SetLike.coe_injective ((PP l).PD_Fil _ _ a)
    unfold FilT FilV
    rw [this]
    exact Iff.rfl






end Mem

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (L : Type) [Field L] [Algebra Qp L] [Algebra L LL] [Module L V] [IsScalarTower L LL V]
    [IsScalarTower Qp L V] (ρ : Representation LL G V) [FiniteDimensional L LL]

open GlobalTheory.BKRightExact

theorem isCrys_res_iff : IsCrys PD (res L ρ) ↔ IsCrys PD ρ := by
  unfold IsCrys
  rw [Dcris_res]
  change finrank L ↥(Dcris PD ρ) = _ ↔ _
  rw [← Module.finrank_mul_finrank L LL ↥(Dcris PD ρ), ← Module.finrank_mul_finrank L LL V, mul_left_comm]
  exact Nat.mul_right_inj Module.finrank_pos.ne'

theorem isDR_res_iff : IsDR PD (res L ρ) ↔ IsDR PD ρ := by
  unfold IsDR
  rw [DdR_res]
  change finrank L ↥(DdR PD ρ) = _ ↔ _
  rw [← Module.finrank_mul_finrank L LL ↥(DdR PD ρ), ← Module.finrank_mul_finrank L LL V, mul_left_comm]
  exact Nat.mul_right_inj Module.finrank_pos.ne'

end Generic

section Rat

variable {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL]
  {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional LL V]
  [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V'] [FiniteDimensional LL V']

open GlobalTheory.BKRightExact in
theorem res_facts (K K' : FinExt l) (h : K.1 ≤ K'.1) (ρ : Representation LL ↥(GK K) V) :
    (IsCrys ((PP l).PD K) ρ → IsDR ((PP l).PD K) ρ) ∧
      (IsCrys ((PP l).PD K) ρ → IsCrys ((PP l).PD K') (ρ.comp (incl h) : Representation LL ↥(GK K') V)) ∧
      (IsDR ((PP l).PD K') (ρ.comp (incl h) : Representation LL ↥(GK K') V) → IsDR ((PP l).PD K) ρ) := by
  obtain ⟨T⟩ := tiedP l
  let L : FinExt l := ⟨⊥, inferInstance⟩
  letI : Algebra ↥L.1 LL :=
    ((algebraMap ℚ_[l] LL).comp (IntermediateField.botEquiv ℚ_[l] (Om l)).toRingEquiv.toRingHom).toAlgebra
  haveI : IsScalarTower ℚ_[l] ↥L.1 LL := IsScalarTower.of_algebraMap_eq fun x =>
    (congrArg (algebraMap ℚ_[l] LL) ((IntermediateField.botEquiv ℚ_[l] (Om l)).commutes x)).symm
  haveI : FiniteDimensional ↥L.1 LL := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  letI : Module ↥L.1 V := Module.compHom V (algebraMap ↥L.1 LL)
  haveI : IsScalarTower ↥L.1 LL V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ℚ_[l] ↥L.1 V := IsScalarTower.to₁₂₄ ℚ_[l] ↥L.1 LL V
  haveI : FiniteDimensional ↥L.1 V := Module.Finite.trans LL V
  have := GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l _ _ T K K' L h V (res ↥L.1 ρ)
  refine ⟨fun h => (isDR_res_iff _ ↥L.1 ρ).1
    (GlobalTheory.Per.CrisDR.isDR_of_isCrys l _ _ T K L V _ ((isCrys_res_iff _ ↥L.1 ρ).2 h)).1, fun h1 => ?_, fun h1 => ?_⟩
  · exact (isCrys_res_iff ((PP l).PD K') ↥L.1 (ρ.comp (incl h) : Representation LL ↥(GK K') V)).1
      (this.1 ((isCrys_res_iff _ ↥L.1 ρ).2 h1))
  · have h2 := (isDR_res_iff ((PP l).PD K') ↥L.1 (ρ.comp (incl h) : Representation LL ↥(GK K') V)).2 h1
    exact (isDR_res_iff _ ↥L.1 ρ).1 (this.2.2 h2)

open GlobalTheory.BKRightExact in
theorem strict (K : FinExt l) (ρ : Representation LL ↥(GK K) V)
    (ρ' : Representation LL ↥(GK K) V') (f : V →ₗ[LL] V') (hf : ∀ g x, f (ρ g x) = ρ' g (f x))
    (hs : Function.Surjective f) (h : IsDR ((PP l).PD K) ρ) (a : ℤ) :
      ∀ y ∈ DdR ((PP l).PD K) ρ' ⊓ FilV ((PP l).PD K) (LL := LL) (V := V') a,
        ∃ x ∈ DdR ((PP l).PD K) ρ ⊓ FilV ((PP l).PD K) (LL := LL) (V := V) a,
          AlgebraTensorModule.map f (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) x = y := by
  obtain ⟨T⟩ := tiedP l
  let L : FinExt l := ⟨⊥, inferInstance⟩
  letI : Algebra ↥L.1 LL :=
    ((algebraMap ℚ_[l] LL).comp (IntermediateField.botEquiv ℚ_[l] (Om l)).toRingEquiv.toRingHom).toAlgebra
  haveI : IsScalarTower ℚ_[l] ↥L.1 LL := IsScalarTower.of_algebraMap_eq fun x =>
    (congrArg (algebraMap ℚ_[l] LL) ((IntermediateField.botEquiv ℚ_[l] (Om l)).commutes x)).symm
  haveI : FiniteDimensional ↥L.1 LL := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  letI : Module ↥L.1 V := Module.compHom V (algebraMap ↥L.1 LL)
  letI : Module ↥L.1 V' := Module.compHom V' (algebraMap ↥L.1 LL)
  haveI : IsScalarTower ↥L.1 LL V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ↥L.1 LL V' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ℚ_[l] ↥L.1 V := IsScalarTower.to₁₂₄ ℚ_[l] ↥L.1 LL V
  haveI : IsScalarTower ℚ_[l] ↥L.1 V' := IsScalarTower.to₁₂₄ ℚ_[l] ↥L.1 LL V'
  haveI : FiniteDimensional ↥L.1 V := Module.Finite.trans LL V
  haveI : FiniteDimensional ↥L.1 V' := Module.Finite.trans LL V'
  obtain ⟨-, h3⟩ := (GlobalTheory.DRSubQuot.deRham_sub_quot l _ _ T K L V (res ↥L.1 ρ) V' (res ↥L.1 ρ')
      (f.restrictScalars ↥L.1) hf).2 hs ((isDR_res_iff _ ↥L.1 ρ).2 h)
  rw [DdR_res, DdR_res] at h3
  intro y hy
  obtain ⟨x, hx, hxy⟩ := h3 a y ⟨hy.1, hy.2⟩
  exact ⟨x, ⟨hx.1, hx.2⟩, hxy⟩

end Rat

section Lift

variable {E B V V' : Type} [Field E] [CommRing B] [Algebra ℚ_[l] E] [Algebra ℚ_[l] B] [Algebra E B]
  [IsScalarTower ℚ_[l] E B] [Module.Finite E B] {π : B →ₐ[E] E} (hπ : ∀ a, π a = 0 → IsNilpotent a)
  [AddCommGroup V] [Module B V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] B V] [FiniteDimensional ℚ_[l] V]
  [AddCommGroup V'] [Module E V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] E V'] [FiniteDimensional ℚ_[l] V']
  {p : V →ₗ[ℚ_[l]] V'} {Λ : (B →ₗ[E] E) → V →ₗ[ℚ_[l]] V'} (hV : Red π p Λ)
  {K : FinExt l} (ρ : Representation B ↥(GK K) V) (ρ' : Representation E ↥(GK K) V')
  (hρ : ∀ g x, p (ρ g x) = ρ' g (p x))
include hπ hV hρ



end Lift

end UpperTheory.V.Loc.Thick
