import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasselmanWallachAdmissible
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.HarishChandraModulesIndefiniteUnitaryGroup
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirNonnegative
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.C3B
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.IsKUnitaryOfIsInfUnitary
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.KTypesFiniteOfHighestWeight
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.DerivativeContinuity
import Development.WeilBound.HeckeVectors.SmoothVectors.SobolevApproximation.PCDense
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CasselmanWallachOfHyp
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ExistsNormingFunctional
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SlopeLimitConstant
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.PageTheorem
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ZetaClassicalZeroFreeRegion
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.TendstoPiZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.PolarJmConjTranspose
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.BilinearFormCasimir
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenOrthogonalForm
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirNonnegativeSymmetric

section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace

namespace PositivityTheory.CW.KFiniteInclusion

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

def incl (hK : ∀ v : H, IsKFin ε σ v → v ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ) :
    kfin ε σ →ₗ[ℂ] ReciprocityTheory.ChartRestriction.DS.smD ε σ where
  toFun v := ⟨v, hK v v.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem incl_val (hK : ∀ v : H, IsKFin ε σ v → v ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ) (v : kfin ε σ) :
    ((incl hK v : ReciprocityTheory.ChartRestriction.DS.smD ε σ) : H) = v := rfl

theorem incl_inj (hK : ∀ v : H, IsKFin ε σ v → v ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ) {v w : kfin ε σ}
    (h : incl hK v = incl hK w) : v = w := by
  have h' := congrArg Subtype.val h
  exact Subtype.ext h'

def Eop (hK : ∀ v : H, IsKFin ε σ v → v ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ)
    (h2 : ∀ a b, ∀ v ∈ CompanionTheory.D.gk.HC.KF ε σ, ReciprocityTheory.ChartRestriction.DS.smE ε σ a b v ∈ CompanionTheory.D.gk.HC.KF ε σ)
    (a b : Fin n) : Module.End ℂ (kfin ε σ) where
  toFun v := ⟨(ReciprocityTheory.ChartRestriction.DS.smE ε σ a b (incl hK v) : H), h2 a b (incl hK v) v.2⟩
  map_add' x y := Subtype.ext (by simp only [map_add, Submodule.coe_add])
  map_smul' c x := Subtype.ext (by simp only [map_smul, Submodule.coe_smul, RingHom.id_apply])

variable (hK : ∀ v : H, IsKFin ε σ v → v ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ)
    (h2 : ∀ a b, ∀ v ∈ CompanionTheory.D.gk.HC.KF ε σ, ReciprocityTheory.ChartRestriction.DS.smE ε σ a b v ∈ CompanionTheory.D.gk.HC.KF ε σ)

theorem incl_E (a b : Fin n) (v : kfin ε σ) :
    incl hK (Eop hK h2 a b v) = ReciprocityTheory.ChartRestriction.DS.smE ε σ a b (incl hK v) := Subtype.ext rfl

theorem incl_actM (X : Mx n) (v : kfin ε σ) :
    incl hK (ReciprocityTheory.ChartRestriction.DS.actM (Eop hK h2) X v) = ReciprocityTheory.ChartRestriction.DS.actM (ReciprocityTheory.ChartRestriction.DS.smE ε σ) X (incl hK v) := by
  simp only [ReciprocityTheory.ChartRestriction.DS.actM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, incl_E]

end PositivityTheory.CW.KFiniteInclusion

namespace PositivityTheory.CW

open KFiniteInclusion

theorem c1 : C1 := by
  intro n ε H _ _ _ σ hσ hirr
  obtain ⟨hK, h2⟩ := CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr
  have hD := ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE hσ
  have hun := ReciprocityTheory.ChartRestriction.DS.isInfUnitary_of_isDerivedOn hσ hD
  refine ⟨Eop hK h2, ?_, ?_, ?_, ?_⟩
  · intro X hX v
    have h := ReciprocityTheory.ChartRestriction.DS.dS_eq_actM hD (X := X) hX (incl hK v)
    have e1 : ((ReciprocityTheory.ChartRestriction.DS.actM (Eop hK h2) X v : kfin ε σ) : H) =
        ((ReciprocityTheory.ChartRestriction.DS.actM (ReciprocityTheory.ChartRestriction.DS.smE ε σ) X (incl hK v) : ReciprocityTheory.ChartRestriction.DS.smD ε σ) : H) := by
      rw [← incl_actM hK h2 X v]
      rfl
    rw [e1, ← h]
    simp only [ReciprocityTheory.ChartRestriction.DS.dS, dRep, Complex.coe_smul, incl_val]
  · intro a b c d
    refine LinearMap.ext fun v => incl_inj hK ?_
    have h := LinearMap.congr_fun (hD.glRep a b c d) (incl hK v)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, incl_E] at h ⊢
    rw [h]
    split_ifs <;> simp [incl_E]
  · intro a b x y
    have h := hun a b (incl hK x) (incl hK y)
    rw [Submodule.coe_inner, Submodule.coe_inner] at h
    rw [Submodule.coe_inner, Submodule.coe_inner]
    exact h
  · intro N hN
    set M := N.map (incl hK) with hM
    have hMK : (M : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ)) ⊆ CompanionTheory.D.gk.HC.KF ε σ := by
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    have hMst : ∀ a b, ∀ v ∈ M, ReciprocityTheory.ChartRestriction.DS.smE ε σ a b v ∈ M := by
      rintro a b _ ⟨w, hw, rfl⟩
      exact ⟨Eop hK h2 a b w, hN a b w hw, incl_E hK h2 a b w⟩
    rcases CompanionTheory.D.gk.HC.uIrr n ε H σ hσ hirr M hMK hMst with h | h
    · left
      refine eq_bot_iff.2 fun x hx => ?_
      have : incl hK x ∈ M := ⟨x, hx, rfl⟩
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact incl_inj hK (this.trans (map_zero _).symm)
    · right
      refine eq_top_iff.2 fun x _ => ?_
      have : incl hK x ∈ (M : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ)) := by rw [h]; exact x.2
      obtain ⟨w, hw, e⟩ := this
      rwa [← incl_inj hK e]

end PositivityTheory.CW
end
end

section
open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary IsKStableSub adjSign)
open scoped InnerProductSpace

namespace PositivityTheory.CW.CasimirNonnegative

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem casK_symm (hU : IsInfUnitary ε E) (x y : V) :
    ⟪casimirK ε E x, y⟫_ℂ = ⟪x, casimirK ε E y⟫_ℂ := by
  unfold casimirK
  simp only [LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  have hs : adjSign ε a b = 1 := by simp [adjSign, hab]
  rw [hU a b, hs, one_mul, ← inner_conj_symm x, hU a b, hs, one_mul, inner_conj_symm]

end PositivityTheory.CW.CasimirNonnegative

namespace PositivityTheory.CW

open CasimirNonnegative in
theorem c2b : CardSubmodulesAndLinearEquivBounds := by
  intro n ε V _ _ E hGl hU hLF
  rw [eq_top_iff]
  intro v _
  obtain ⟨S, hfin, hvS, hstab⟩ := hLF v
  have hK : ∀ w ∈ S, casimirK ε E w ∈ S := by
    intro w hw
    unfold casimirK
    simp only [LinearMap.sum_apply, Module.End.mul_apply]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb => ?_
    have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
    exact hstab a b hab.symm _ (hstab b a hab _ hw)
  let T : S →ₗ[ℂ] S := (casimirK ε E).restrict hK
  have hT : T.IsSymmetric := by
    intro x y
    exact casK_symm hU x y
  have hn : Module.finrank ℂ S = Module.finrank ℂ S := rfl
  have hsum := (hT.eigenvectorBasis hn).sum_repr ⟨v, hvS⟩
  have hv : v = ∑ i, ((hT.eigenvectorBasis hn).repr ⟨v, hvS⟩ i) • ((hT.eigenvectorBasis hn i : S) : V) := by
    have h0 := congrArg Subtype.val hsum
    simpa using h0.symm
  rw [hv]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨hT.eigenvalues hn i, ?_⟩)
  show casimirK ε E (hT.eigenvectorBasis hn i : V) = ((hT.eigenvalues hn i : ℝ) : ℂ) • (hT.eigenvectorBasis hn i : V)
  exact congrArg Subtype.val (hT.apply_eigenvectorBasis hn i)

end PositivityTheory.CW
end

section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open ReciprocityTheory.ChartRestriction.DS (actM IsKHWVec smD smE dS smE_apply)

namespace PositivityTheory.CW

namespace MatrixActionAdditive

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem actM_single {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    actM E (Matrix.single a b 1) = E a b := by
  simp [actM, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

theorem actM_add' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (X Y : Matrix (Fin n) (Fin n) ℂ) : actM E (X + Y) = actM E X + actM E Y := by
  simp [actM, add_smul, Finset.sum_add_distrib]

theorem actM_smul' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) (c : ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) : actM E (c • X) = c • actM E X := by
  simp [actM, Finset.smul_sum, smul_smul]

theorem dS_eq_dRep (σ : Mx n → (H →L[ℂ] H)) (X : Mx n) (v : H) : dS σ X v = dRep σ X v := by
  have h : ∀ t : ℝ, ((t : ℂ) • X) = t • X := fun t => by
    ext i j
    simp
  simp only [dS, dRep, h]

theorem key {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (E : Fin n → Fin n → Module.End ℂ (kfin ε σ)) (hE : KDer ε σ E) (v : kfin ε σ) (hv : (v : H) ∈ smD ε σ)
    (a b : Fin n) : ((smE ε σ a b ⟨v, hv⟩ : smD ε σ) : H) = ((E a b v : kfin ε σ) : H) := by
  rw [smE_apply hσ ⟨v, hv⟩ a b]
  have hX := ReciprocityTheory.ChartRestriction.DS.S7.ccb_cpart_sum ε (single a b 1)
  have h1 : E a b = actM E (ReciprocityTheory.ChartRestriction.DS.S7.cpart1 ε (single a b 1))
      + Complex.I • actM E (ReciprocityTheory.ChartRestriction.DS.S7.cpart2 ε (single a b 1)) := by
    rw [← actM_single E a b, ← actM_smul', ← actM_add', hX]
  rw [h1]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul]
  rw [hE _ (ReciprocityTheory.ChartRestriction.DS.S7.ccb_inG_cpart1 ε _) v, hE _ (ReciprocityTheory.ChartRestriction.DS.S7.ccb_inG_cpart2 ε _) v,
    dS_eq_dRep, dS_eq_dRep]

end MatrixActionAdditive

open MatrixActionAdditive in
theorem c3a : HighestWeightSpaceFinite := by
  intro n ε H _ _ _ σ hσ hIrr E hE μ
  have hA := CompanionTheory.D.gk.HC.uAdm n ε H σ hσ hIrr μ
  have hsub : (kfin ε σ).subtype '' {v : kfin ε σ | IsKHWVec ε E μ v}
      ⊆ (smD ε σ).subtype '' {v : smD ε σ | v ∈ CompanionTheory.D.gk.HC.KF ε σ ∧ IsKHWVec ε (smE ε σ) μ v} := by
    rintro _ ⟨v, hvB, rfl⟩
    have hv : (v : H) ∈ smD ε σ := CompanionTheory.D.gk.HC.mem_smD_of_isKFin hσ hIrr v.2
    refine ⟨⟨v, hv⟩, ⟨v.2, ?_, ?_⟩, rfl⟩
    · intro a
      apply Subtype.ext
      rw [key hσ E hE v hv a a, hvB.1 a]
      rfl
    · intro a b hab he
      apply Subtype.ext
      rw [key hσ E hE v hv a b, hvB.2 a b hab he]
      rfl
  have hle : (Submodule.span ℂ {v : kfin ε σ | IsKHWVec ε E μ v}).map (kfin ε σ).subtype
      ≤ (Submodule.span ℂ {v : smD ε σ | v ∈ CompanionTheory.D.gk.HC.KF ε σ ∧ IsKHWVec ε (smE ε σ) μ v}).map
        (smD ε σ).subtype := by
    rw [Submodule.map_span, Submodule.map_span]
    exact Submodule.span_mono hsub
  haveI : FiniteDimensional ℂ ((Submodule.span ℂ {v : kfin ε σ | IsKHWVec ε E μ v}).map (kfin ε σ).subtype) :=
    Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional
    (Submodule.equivMapOfInjective _ (kfin ε σ).injective_subtype _).symm

end PositivityTheory.CW

end
end

section
namespace PositivityTheory.CW

theorem c3c : KStableHighestWeightVector := by
  intro n ε V _ _ E hgl hun S hfd hS hne
  obtain ⟨w, hw, hw0, μ, hμ⟩ := ReciprocityTheory.ChartRestriction.DS.exists_khw hgl (ReciprocityTheory.ChartRestriction.DS.isKUnitary_of_isInfUnitary hun) hfd hS hne
  exact ⟨w, μ, hw, hw0, hμ⟩

end PositivityTheory.CW
end

section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped ComplexOrder

namespace PositivityTheory.CW

theorem c5 : C5 := by
  intro n ε H _ _ _ σ hU hI
  have hHC := CompanionTheory.D.gk.HC.print_harishChandraModules
  refine ⟨fun v hv => GlobalTheory.CWGeneral.sm_of_isKFin hHC hU hI hv,
    fun v hv X hX => GlobalTheory.CWGeneral.isKFin_dRep_of_irred hHC hU hI hv hX, fun w hw S hS δ hδ => ?_⟩
  have hG : Formalism.IndefR.Tow.SobPf.IsGRep (Formalism.REAL.Jm ε) σ := ⟨hU.1.1, hU.1.2, hU.2.1, hU.2.2⟩
  have hC : Formalism.IndefR.Datum.IsCartanInv (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε) := by
    have hJ : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
      ext i j; simp only [Formalism.REAL.Jm, diagonal_conjTranspose, diagonal_apply]; split_ifs <;> simp_all
    refine ⟨Formalism.REAL.Jm_mul_self ε, ?_, ?_⟩
    · rw [hJ, Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
    · rw [Formalism.REAL.Jm_mul_self]; exact Matrix.PosDef.one
  set δ' : ℝ := δ / (S.length + 1) with hδ'
  have hδ'0 : 0 < δ' := div_pos hδ (by positivity)
  obtain ⟨v, hvS, hvK, hvw⟩ := CompanionTheory.D.gk.HC.sobApprox_holds (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε) σ hC hG w
    hw S hS δ' hδ'0
  refine ⟨v, ?_, ?_⟩
  · obtain ⟨W, hW, hvW, hst⟩ := hvK
    refine ⟨W, hW, hvW, fun g hg x hx => hst g ⟨?_, hg.2⟩ x hx⟩
    show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
    rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
      (Matrix.mem_unitaryGroup_iff').1 hg.1, Matrix.one_mul]
  · have hv' : Sm ε σ v := hvS
    have key : ∀ l ∈ S, ‖Dw σ l (w - v)‖ ≤ δ' := by
      intro l hl
      have e : Dw σ l (w - v) = Dw σ l w - Dw σ l v := by
        have := Dw_add hU (hS l hl) (sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hw) (sm_iff.1 hv'))) hv'
        rw [sub_add_cancel] at this
        rw [this, add_sub_cancel_right]
      rw [e, norm_sub_rev]
      exact (hvw l hl).le
    have hL : (S.length : ℝ) * δ' < δ := by
      rw [hδ', mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    unfold sobNorm
    calc (S.map fun l => ‖l.foldr (dRep σ) (w - v)‖).sum
        ≤ (S.map fun l => ‖l.foldr (dRep σ) (w - v)‖).length • δ' :=
          List.sum_le_card_nsmul _ _ (fun x hx => by
            obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
            exact key l hl)
      _ = S.length * δ' := by simp
      _ < δ := hL

end PositivityTheory.CW
end

section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace

namespace PositivityTheory.CW

namespace DerivativeContinuity

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem continuousOn_Dw (hU : IsURepOn (UJset ε) σ) (hI : IsIrredOn (UJset ε) σ) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) :
    ContinuousOn (fun g => Dw σ l (σ g w)) (UJset ε) :=
  continuousOn_iff_continuous_restrict.2
    (continuous_word_orbit (isUnit_Jm ε) hU (GlobalTheory.CWGeneral.dense_smoothAll_of_irred hU hI) continuous_subtype_val
      (fun t => t.2) l hl hw)

theorem hasDerivAt_Dw (hU : IsURepOn (UJset ε) σ) (hI : IsIrredOn (UJset ε) σ) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) {X : Mx n} (hX : X ∈ lieSet ε) :
    HasDerivAt (fun t : ℝ => Dw σ l (σ (NormedSpace.exp (t • X)) w)) (Dw σ l (dRep σ X w)) 0 := by
  have hden : Dense (smooth (Jm ε) σ : Set H) :=
    (GlobalTheory.CWGeneral.dense_smoothAll_of_irred hU hI).mono (smoothAll_le (isUnit_Jm ε))
  have hw' : Sm ε σ (dRep σ X w) := dRep_mem (isUnit_Jm ε) hU hw hX
  have hc : ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) →
      Continuous fun t : ℝ => Dw σ l (σ (NormedSpace.exp (t • X)) (dRep σ X w)) := fun l hl =>
    (continuousOn_Dw hU hI hl hw').comp_continuous (continuous_exp_smul X) (exp_mem_UJ hX)
  have e0 : ∀ z, σ (NormedSpace.exp ((0 : ℝ) • X)) z = z := fun z => by
    rw [zero_smul, NormedSpace.exp_zero, sigma_one hU]
  have key : ∀ t : ℝ, Dw σ l (σ (NormedSpace.exp (t • X)) w) =
      Dw σ l w + ∫ s in (0 : ℝ)..t, Dw σ l (σ (NormedSpace.exp (s • X)) (dRep σ X w)) := by
    intro t
    have h0 := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
      (fun s _ => hasDerivAt_orbit hU hw hX s) ((hc [] (by simp)).intervalIntegrable 0 t)
    rw [e0] at h0
    refine hden.eq_of_inner_right ℂ fun y hy => ?_
    have i1 := fun (z : H) (l : List (Mx n)) (hl : ∀ X ∈ l, X ∈ lieSet ε) =>
      (innerSL ℂ z).intervalIntegral_comp_comm ((hc l hl).intervalIntegrable (μ := volume) 0 t)
    simp only [innerSL_apply_apply] at i1
    have i2 := i1 (Dw σ l.reverse y) [] (by simp)
    simp only [Dw, List.foldr_nil] at i2
    rw [inner_add_right, ← i1 y l hl, inner_Dw hU hl hy (hw.translate hU (exp_mem_UJ hX t)), inner_Dw hU hl hy hw]
    simp only [fun s => inner_Dw hU hl hy (hw'.translate hU (exp_mem_UJ hX s))]
    rw [intervalIntegral.integral_const_mul, i2, h0, inner_sub_right]
    ring
  simp only [key]
  have := ((hc l hl).integral_hasStrictDerivAt 0 0).hasDerivAt.const_add (Dw σ l w)
  rwa [e0] at this

end DerivativeContinuity

theorem c6 : C6 := fun _ _ _ _ _ _ _ hU hI _ hl _ hw _ hX => DerivativeContinuity.hasDerivAt_Dw hU hI hl hw hX

end PositivityTheory.CW
end

section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace PositivityTheory.CW

theorem c7 : C7 := by
  classical
  intro hMax hC4 n ε H _ _ _ σ hU hI hD E hKD hM N
  obtain ⟨m, K, I0, hK0, hmax⟩ := hMax n ε (kfin ε σ) E hM N
  obtain ⟨S, C', hS, hC', hbd⟩ := hC4 n ε H σ hU hI hD E hKD m
  refine ⟨S, K * C', I0.image Subtype.val, hS, mul_nonneg hK0 hC', ?_, ?_⟩
  · intro e he
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 he
    exact x.2
  · intro F hcont hder hgrow B hB hI0 v hv
    let F' : kfin ε σ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ → ℂ := F ∘ₗ (kfin ε σ).subtype
    have key := hmax F' (fun w => hcont w w.2)
      (fun X hX w g hg => by
        have h1 := hder X hX.1 w w.2 g hg
        show HasDerivAt (fun t : ℝ => F (w : H) (g * NormedSpace.exp (t • X)))
          (F ((ReciprocityTheory.ChartRestriction.DS.actM E X w : kfin ε σ) : H) g) 0
        rw [hKD X hX.1 w]
        exact h1)
      (fun w => hgrow w w.2) B hB
      (fun e he g hg => hI0 e.1 (Finset.mem_image_of_mem _ he) g hg) ⟨v, hv⟩
    calc ‖F v 1‖ = ‖F' ⟨v, hv⟩ 1‖ := rfl
      _ ≤ K * B * ‖((1 + ReciprocityTheory.ChartRestriction.DS.casimirK ε E) ^ m) ⟨v, hv⟩‖ := key
      _ ≤ K * B * (C' * sobNorm σ S v) :=
        mul_le_mul_of_nonneg_left (hbd ⟨v, hv⟩) (mul_nonneg hK0 hB)
      _ = K * C' * B * sobNorm σ S v := by ring

end PositivityTheory.CW
end

section
namespace PositivityTheory.CW

theorem d5 : D5 := by
  intro n ε g hg
  have hu : ReciprocityTheory.ChartRestriction.DS.inUJ ε g := hg
  refine ⟨g * NormedSpace.exp (-ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L g),
    ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_k_mem hu,
    ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L g,
    (ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L_inP hu).1,
    ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.eq_mul_exp_neg_polar_L_mul_exp_polar_L⟩

end PositivityTheory.CW
end

section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace PositivityTheory.CW

namespace KInvarianceAlt

theorem kinv {n : ℕ} {ε : Fin n → Bool} {k : Mx n} (hk : k ∈ Kset ε) : ∃ k' ∈ Kset ε, k' * k = 1 := by
  obtain ⟨hu, hJ⟩ := hk
  have hu' : kᴴ * k = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hu; rwa [Matrix.star_eq_conjTranspose] at this
  have hJh : (Jm ε)ᴴ = Jm ε := by
    ext i j; simp only [Jm, diagonal_conjTranspose, diagonal_apply]; split_ifs <;> simp_all
  have hJ' : kᴴ * Jm ε = Jm ε * kᴴ := by
    have h := congrArg Matrix.conjTranspose hJ
    simp only [Matrix.conjTranspose_mul, hJh] at h
    exact h.symm
  have hs' : kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    have := Unitary.star_mem hu; rwa [Matrix.star_eq_conjTranspose] at this
  exact ⟨kᴴ, ⟨hs', hJ'⟩, hu'⟩

end KInvarianceAlt

theorem e1a : SmoothSeminormGrowth := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ i
  obtain ⟨q, N, hq, hg⟩ := hπ.growth i
  haveI : Nonempty (UJset ε) := ⟨⟨1, one_mem_UJ ε⟩⟩
  set W : Mx n → ℝ := fun g => (1 + hs g) ^ N with hWdef
  have hW : ∀ g, 0 < W g := fun g => pow_pos (by linarith [hs_nonneg g]) _
  have hWm : ∀ a b : Mx n, W (a * b) ≤ W a * W b := fun a b => by
    simp only [hWdef]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith [hs_nonneg (a * b)]) (one_add_hs_mul_le a b) N
  have hmul : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, ∀ x, π (a * b) x = π a (π b x) := fun a ha b hb x => by
    rw [hπ.map_mul a ha b hb]; rfl
  let f : UJset ε → Seminorm ℂ E := fun g => (Real.toNNReal (W g.1)⁻¹) • (p i).comp (π g.1 : E →ₗ[ℂ] E)
  have hf : ∀ g x, f g x = p i (π g.1 x) / W g.1 := fun g x => by
    show ((Real.toNNReal (W g.1)⁻¹ : NNReal) : ℝ) * p i (π g.1 x) = _
    rw [Real.coe_toNNReal _ (inv_nonneg.2 (hW _).le), div_eq_inv_mul]
  have hfq : ∀ g x, f g x ≤ q x := fun g x => by
    rw [hf, div_le_iff₀ (hW _), mul_comm]
    exact hg g.1 g.2 x
  have hbdd : BddAbove (Set.range f) := ⟨q, by
    rintro _ ⟨g, rfl⟩
    exact Pi.le_def.2 fun x => hfq g x⟩
  have hfb : ∀ x, BddAbove (Set.range fun g => f g x) := fun x => ⟨q x, by
    rintro _ ⟨g, rfl⟩
    exact hfq g x⟩
  set Q : Seminorm ℂ E := ⨆ g, f g with hQdef
  have hQ : ∀ x, Q x = ⨆ g, f g x := fun x => Seminorm.iSup_apply hbdd
  have hle : ∀ g x, f g x ≤ Q x := fun g x => by rw [hQ]; exact le_ciSup (hfb x) g
  have hQq : Q ≤ q := Pi.le_def.2 fun x => by rw [hQ]; exact ciSup_le fun g => hfq g x
  have h1 : ∀ g ∈ UJset ε, ∀ x, p i (π g x) ≤ W g * Q x := fun g hg x => by
    have := hle ⟨g, hg⟩ x
    rw [hf, div_le_iff₀ (hW _)] at this
    linarith
  have hKk : ∀ k ∈ Kset ε, ∀ x, Q (π k x) ≤ Q x := fun k hk x => by
    rw [hQ (π k x)]
    refine ciSup_le fun g => ?_
    have hgk : g.1 * k ∈ UJset ε := mul_mem_UJ g.2 (K_le_UJ hk)
    have := hle ⟨g.1 * k, hgk⟩ x
    rw [hf] at this ⊢
    have e : W (g.1 * k) = W g.1 := by
      simp only [hWdef, ((Formalism.REAL.hermitian_small_ball n ε).2 g.1 k hk).1]
    rw [← hmul g.1 g.2 k (K_le_UJ hk), ← e]
    exact this
  refine ⟨Q, N, Seminorm.continuous_of_le hq hQq, h1, fun h hh x => ?_, fun k hk x => ?_⟩
  · rw [hQ (π h x)]
    refine ciSup_le fun g => ?_
    rw [hf, hmul g.1 g.2 h hh x |>.symm, div_le_iff₀ (hW _)]
    calc p i (π (g.1 * h) x) ≤ W (g.1 * h) * Q x := h1 _ (mul_mem_UJ g.2 hh) x
      _ ≤ (W g.1 * W h) * Q x := mul_le_mul_of_nonneg_right (hWm _ _) (apply_nonneg _ _)
      _ = W h * Q x * W g.1 := by ring
  · refine le_antisymm (hKk k hk x) ?_
    obtain ⟨k', hk', e⟩ := KInvarianceAlt.kinv hk
    have := hKk k' hk' (π k x)
    rwa [← hmul k' (K_le_UJ hk') k (K_le_UJ hk), e, hπ.map_one] at this

end PositivityTheory.CW

end
end

section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined

namespace PositivityTheory.CW

namespace ExistsFunctional

theorem exists_functional {E : Type} [AddCommGroup E] [Module ℂ E] (q : Seminorm ℂ E) {x₀ : E} (hx : q x₀ ≠ 0) :
    ∃ φ : Module.Dual ℂ E, φ x₀ ≠ 0 ∧ ∀ x, ‖φ x‖ ≤ q x := by
  have h0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx (map_zero q)
  let e := LinearEquiv.toSpanNonzeroSingleton ℂ E x₀ h0
  let f : Module.Dual ℂ (Submodule.span ℂ {x₀}) := (q x₀ : ℂ) • (e.symm : _ →ₗ[ℂ] ℂ)
  have hfe : ∀ t : ℂ, f (e t) = t * q x₀ := by
    intro t
    simp [f, mul_comm]
  obtain ⟨g, hg, hgp⟩ := Module.Dual.exists_extension_of_le_seminorm (Submodule.span ℂ {x₀}) f
    (p := q) (by
      intro y
      obtain ⟨t, rfl⟩ := e.surjective y
      rw [hfe, norm_mul, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q x₀)]
      rw [LinearEquiv.toSpanNonzeroSingleton_apply]
      simp [map_smul_eq_mul])
  refine ⟨g, ?_, hgp⟩
  have h1 := hg (e 1)
  rw [hfe, one_mul] at h1
  have : ((e 1 : Submodule.span ℂ {x₀}) : E) = x₀ := by
    rw [LinearEquiv.toSpanNonzeroSingleton_one]
  rw [this] at h1
  rw [h1]
  exact_mod_cast hx

end ExistsFunctional

theorem e1b : faceMap_comp_succAbove_castSucc := by
  unfold faceMap_comp_succAbove_castSucc AllTgt
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hrep T hT i w₀ hw₀ hp u hu hu0
  by_contra hall
  push_neg at hall
  obtain ⟨φ, hφ0, hφ⟩ := ExistsFunctional.exists_functional (p i) hp
  let ℓ : H →ₗ[ℂ] ℂ := φ ∘ₗ T
  have hlie : ((GlobalTheory.LowTypeDetermined.lie (Jm ε) : Set (Mx n))) = lieSet ε := rfl
  have hsm : ∀ w, Sm ε σ w →
      w ∈ GlobalTheory.LowTypeDetermined.smooth (Jm ε) (fun g => σ (1 * g * (1 : Mx n)⁻¹)) := by
    intro w hw
    change SmoothVec ((GlobalTheory.LowTypeDetermined.lie (Jm ε) : Set (Mx n)))
      (fun g => σ (1 * g * (1 : Mx n)⁻¹)) w
    simp only [inv_one, mul_one, one_mul]
    rw [hlie]
    exact hw
  have key := GlobalTheory.LowTypeDetermined.eq_zero_of_translates (G := Jm ε) (P := 1) hU hI isUnit_one
    (by simp) (ℓ := ℓ) ?_ (hsm u hu) hu0 ?_ (hsm w₀ hw₀)
  · exact hφ0 key
  · obtain ⟨S, C, hS, hb⟩ := hT.2 i
    refine ⟨S, C, ?_, ?_⟩
    · rw [hlie]
      exact hS
    · simp only [inv_one, mul_one, one_mul]
      rw [hlie]
      intro w hw
      exact (hφ (T w)).trans (hb w hw)
  · intro g hg
    show φ (T (σ g u)) = 0
    rw [hT.1 g hg u hu]
    exact norm_le_zero_iff.mp ((hφ _).trans (hall g hg).le)

end PositivityTheory.CW
end

section
open scoped InnerProductSpace
open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary adjSign)

namespace PositivityTheory.CW.EigenOrthogonalForm

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem cas_symm (hu : IsInfUnitary ε E) (x y : V) :
    ⟪casimirK ε E x, y⟫_ℂ = ⟪x, casimirK ε E y⟫_ℂ := by
  unfold casimirK
  simp only [LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  rw [hu a b, hu b a]
  simp [adjSign, hab]

theorem inner_eq_zero_of_eig (hu : IsInfUnitary ε E) {μ μ' : ℝ} (hne : μ ≠ μ') {v y : V}
    (hv : casimirK ε E v = (μ : ℂ) • v) (hy : casimirK ε E y = (μ' : ℂ) • y) : ⟪v, y⟫_ℂ = 0 := by
  have h := cas_symm hu v y
  rw [hv, hy, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  have h' : ((μ : ℂ) - μ') * ⟪v, y⟫_ℂ = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.1 h' with h0 | h0
  · exact absurd (by exact_mod_cast sub_eq_zero.1 h0) hne
  · exact h0

theorem B_eq_zero (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ v y, B (casimirK ε E v) y = B v (casimirK ε E y))
    {μ μ' : ℝ} (hne : μ ≠ μ') {v y : V}
    (hv : casimirK ε E v = (μ : ℂ) • v) (hy : casimirK ε E y = (μ' : ℂ) • y) : B v y = 0 := by
  have h := hB v y
  rw [hv, hy] at h
  simp only [map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, Complex.conj_ofReal,
    RingHom.id_apply] at h
  have h2 : ((μ : ℂ) - μ') * B v y = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (by exact_mod_cast sub_eq_zero.1 h3) hne
  · exact h3

end PositivityTheory.CW.EigenOrthogonalForm

namespace PositivityTheory.CW

open EigenOrthogonalForm in
theorem e2c : CasimirPairingBound := by
  intro n ε V _ _ E _ _ hM Q hQ η
  let S : Submodule ℂ V :=
    { carrier := {a | ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖⟪a, y⟫_ℂ‖ ≤ C * Q y}
      add_mem' := by
        rintro a b ⟨C₁, h₁, ha⟩ ⟨C₂, h₂, hb⟩
        refine ⟨C₁ + C₂, add_nonneg h₁ h₂, fun y => ?_⟩
        rw [inner_add_left, add_mul]
        exact (norm_add_le _ _).trans (add_le_add (ha y) (hb y))
      zero_mem' := ⟨0, le_rfl, fun y => by simp⟩
      smul_mem' := by
        rintro c a ⟨C, h, ha⟩
        refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) h, fun y => ?_⟩
        rw [inner_smul_left, norm_mul, RCLike.norm_conj, mul_assoc]
        exact mul_le_mul_of_nonneg_left (ha y) (norm_nonneg _) }
  suffices hS : S = ⊤ by
    have hη : η ∈ S := hS ▸ Submodule.mem_top
    exact hη
  rw [eq_top_iff, ← hM.span, Submodule.span_le]
  rintro w ⟨μ, hw⟩
  let W : Submodule ℂ V := Module.End.eigenspace (casimirK ε E) (μ : ℂ)
  have hWmem : ∀ v, v ∈ W ↔ casimirK ε E v = (μ : ℂ) • v := fun v => Module.End.mem_eigenspace_iff
  haveI : FiniteDimensional ℂ W := by
    haveI := hM.fin μ
    have hle : W ≤ Submodule.span ℂ {v | ∃ μ' ≤ μ, Eig ε E μ' v} :=
      fun v hv => Submodule.subset_span ⟨μ, le_rfl, (hWmem v).1 hv⟩
    exact Submodule.finiteDimensional_of_le hle
  let P : (V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) → Prop := fun B =>
    (∀ v y, B (casimirK ε E v) y = B v (casimirK ε E y)) ∧ ∀ v y, ‖B v y‖ ≤ Q v * Q y
  let G : Set (Module.Dual ℂ W) := {g | ∃ B, P B ∧ ∃ v ∈ W, g = (B v).comp W.subtype}
  have hspan : Submodule.span ℂ G = ⊤ := by
    have hco : (Submodule.span ℂ G).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Submodule.mem_bot]
      by_contra hne
      have hy0 : (y : V) ≠ 0 := fun h => hne (Subtype.ext h)
      obtain ⟨B, hB1, hB2, hB3⟩ := hQ y hy0
      have hg : (B y).comp W.subtype ∈ Submodule.span ℂ G :=
        Submodule.subset_span ⟨B, ⟨hB1, hB2⟩, y, y.2, rfl⟩
      exact hB3 ((Submodule.mem_dualCoannihilator _).1 hy _ hg)
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ G), hco,
      Submodule.dualAnnihilator_bot]
  have hl : (innerₛₗ ℂ w).comp W.subtype ∈ Submodule.span ℂ G := hspan ▸ Submodule.mem_top
  obtain ⟨m, f, g, hfg⟩ := Submodule.mem_span_set'.1 hl
  choose B hB v hv hgv using fun i => (g i).2
  have hid : innerₛₗ ℂ w = ∑ i, f i • B i (v i) := by
    refine LinearMap.ext_on hM.span ?_
    rintro y ⟨lam, hy⟩
    by_cases hμ : lam = μ
    · subst hμ
      have hyW : y ∈ W := (hWmem y).2 hy
      have := LinearMap.congr_fun hfg ⟨y, hyW⟩
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, hgv, LinearMap.comp_apply,
        Submodule.subtype_apply] at this
      rw [← this, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply]
    · have h0 : ⟪w, y⟫_ℂ = 0 := inner_eq_zero_of_eig hM.uni (Ne.symm hμ) hw hy
      have h1 : ∀ i, B i (v i) y = 0 := fun i =>
        B_eq_zero (B i) (hB i).1 (Ne.symm hμ) ((hWmem _).1 (hv i)) hy
      rw [LinearMap.sum_apply, innerₛₗ_apply_apply, h0]
      simp [h1]
  show ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖⟪w, y⟫_ℂ‖ ≤ C * Q y
  refine ⟨∑ i, ‖f i‖ * Q (v i),
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (apply_nonneg Q _), fun y => ?_⟩
  have hwy : ⟪w, y⟫_ℂ = ∑ i, f i * B i (v i) y := by
    have h := LinearMap.congr_fun hid y
    rw [innerₛₗ_apply_apply, LinearMap.sum_apply] at h
    rw [h]
    simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [hwy, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((hB i).2 _ _) (norm_nonneg _)

end PositivityTheory.CW
end

section
open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary IsKStableSub adjSign)
open scoped InnerProductSpace

namespace PositivityTheory.CW.CasimirNonnegativeSymmetric

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem casK_symm (hU : IsInfUnitary ε E) (x y : V) :
    ⟪casimirK ε E x, y⟫_ℂ = ⟪x, casimirK ε E y⟫_ℂ := by
  simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  rw [hU a b (E b a x) y, hU b a x (E b a y)]
  simp [adjSign, hab]

theorem re_inner_casK_nonneg (hU : IsInfUnitary ε E) (x : V) : 0 ≤ (⟪x, casimirK ε E x⟫_ℂ).re := by
  simp only [ReciprocityTheory.ChartRestriction.DS.casimirK, LinearMap.sum_apply, Module.End.mul_apply,
    inner_sum, Complex.re_sum]
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b hb => ?_
  have hb' : ε b = ε a := (Finset.mem_filter.1 hb).2
  have h := hU b a x (E b a x)
  simp only [ReciprocityTheory.ChartRestriction.DS.adjSign, hb', if_true, one_mul] at h
  rw [← h]
  simpa using (inner_self_nonneg (𝕜 := ℂ) (x := E b a x))

theorem eig_nonneg (hU : IsInfUnitary ε E) {μ : ℝ} {v : V} (hv : v ≠ 0) (h : Eig ε E μ v) : 0 ≤ μ := by
  have h2 := re_inner_casK_nonneg hU v
  rw [show casimirK ε E v = (μ : ℂ) • v from h, inner_smul_right, inner_self_eq_norm_sq_to_K] at h2
  have h3 : 0 ≤ μ * ‖v‖ ^ 2 := by simpa [← Complex.ofReal_pow] using h2
  have hn : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv) 2
  by_contra hμ
  push_neg at hμ
  nlinarith [mul_neg_of_neg_of_pos hμ hn]

end PositivityTheory.CW.CasimirNonnegativeSymmetric

namespace PositivityTheory.CW

open CasimirNonnegativeSymmetric in
theorem e3a : CasimirPowerSurjectiveSymmetric := by
  intro k ε V _ _ E _ hU hM m
  set a := 1 + casimirK ε E with ha_def
  have ha : ∀ x y : V, ⟪a x, y⟫_ℂ = ⟪x, a y⟫_ℂ := by
    intro x y
    simp only [ha_def, LinearMap.add_apply, Module.End.one_apply, inner_add_left, inner_add_right,
      casK_symm hU]
  have hsymm : ∀ j : ℕ, ∀ x y : V, ⟪(a ^ j) x, y⟫_ℂ = ⟪x, (a ^ j) y⟫_ℂ := by
    intro j
    induction j with
    | zero => intro x y; simp
    | succ j ih =>
      intro x y
      calc ⟪(a ^ (j + 1)) x, y⟫_ℂ = ⟪(a ^ j) (a x), y⟫_ℂ := by rw [pow_succ, Module.End.mul_apply]
        _ = ⟪a x, (a ^ j) y⟫_ℂ := ih _ _
        _ = ⟪x, a ((a ^ j) y)⟫_ℂ := ha _ _
        _ = ⟪x, (a ^ (j + 1)) y⟫_ℂ := by rw [pow_succ', Module.End.mul_apply]
  refine ⟨?_, hsymm m⟩
  have hrange : LinearMap.range (a ^ m) = ⊤ := by
    rw [eq_top_iff, ← hM.span, Submodule.span_le]
    rintro v ⟨μ, hv⟩
    show v ∈ LinearMap.range (a ^ m)
    by_cases h0 : v = 0
    · rw [h0]; exact Submodule.zero_mem _
    have hμ : 0 ≤ μ := eig_nonneg hU h0 hv
    have h1 : a v = (1 + (μ : ℂ)) • v := by
      simp [ha_def, add_smul, show casimirK ε E v = (μ : ℂ) • v from hv]
    have hav : ∀ j : ℕ, (a ^ j) v = ((1 + (μ : ℂ)) ^ j) • v := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ, Module.End.mul_apply, h1, map_smul, ih, smul_smul, ← pow_succ']
    have hne1 : (1 + (μ : ℂ)) ≠ 0 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add]
      exact_mod_cast (by linarith : (0 : ℝ) < 1 + μ).ne'
    have hne : (1 + (μ : ℂ)) ^ m ≠ 0 := pow_ne_zero _ hne1
    refine LinearMap.mem_range.2 ⟨((1 + (μ : ℂ)) ^ m)⁻¹ • v, ?_⟩
    rw [map_smul, hav, smul_smul, inv_mul_cancel₀ hne, one_smul]
  exact LinearMap.range_eq_top.1 hrange

end PositivityTheory.CW
end

section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open ReciprocityTheory.ChartRestriction.DS (actM casimirK)

namespace PositivityTheory.CW.MatrixActionLinear

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem actM_add (A : Fin n → Fin n → Module.End ℂ M) (X Y : Mx n) : actM A (X + Y) = actM A X + actM A Y := by
  unfold actM
  simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem actM_smul (A : Fin n → Fin n → Module.End ℂ M) (c : ℂ) (X : Mx n) : actM A (c • X) = c • actM A X := by
  unfold actM
  simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem actM_single (A : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) : actM A (Matrix.single a b 1) = A a b := by
  classical
  unfold actM
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro d _ hd
      simp [Ne.symm hd]
    · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun d _ => ?_
    simp [Ne.symm hc]
  · simp

end PositivityTheory.CW.MatrixActionLinear

namespace PositivityTheory.CW

open MatrixActionLinear in
theorem e3b : faceMap_castSucc_comp_eq_succ := by
  classical
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ A hA T hT m
  haveI : IsTopologicalAddGroup E := hπ.withSeminorms.topologicalAddGroup
  haveI : ContinuousSMul ℂ E := hπ.withSeminorms.continuousSMul

  let P : Module.End ℂ (kfin ε σ) → Prop := fun u => ∃ D : E →L[ℂ] E, ∀ v : kfin ε σ, T ((u v : kfin ε σ) : H) = D (T v)
  have hone : P 1 := ⟨1, fun v => rfl⟩
  have hadd : ∀ u₁ u₂, P u₁ → P u₂ → P (u₁ + u₂) := by
    rintro u₁ u₂ ⟨D₁, h₁⟩ ⟨D₂, h₂⟩
    refine ⟨D₁ + D₂, fun v => ?_⟩
    simp only [LinearMap.add_apply, Submodule.coe_add, map_add, h₁, h₂, _root_.add_apply]
  have hmul : ∀ u₁ u₂, P u₁ → P u₂ → P (u₁ * u₂) := by
    rintro u₁ u₂ ⟨D₁, h₁⟩ ⟨D₂, h₂⟩
    refine ⟨D₁.comp D₂, fun v => ?_⟩
    rw [Module.End.mul_apply, h₁, h₂]
    rfl
  have hzero : P 0 := ⟨0, fun v => by simp⟩
  have hsum : ∀ (s : Finset (Fin n)) (f : Fin n → Module.End ℂ (kfin ε σ)), (∀ i ∈ s, P (f i)) → P (∑ i ∈ s, f i) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact hadd _ _ (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
  have hgen : ∀ a b, P (A a b) := by
    intro a b
    obtain ⟨h1, h2, h3, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
    set X₁ := cpart1 ε (Matrix.single a b 1)
    set X₂ := cpart2 ε (Matrix.single a b 1)
    have hX₁ : X₁ ∈ lieSet ε := h1
    have hX₂ : X₂ ∈ lieSet ε := h2
    have eA : A a b = actM A X₁ + Complex.I • actM A X₂ := by
      rw [← actM_single A a b, h3, actM_add, actM_smul]
    refine ⟨dπ X₁ + Complex.I • dπ X₂, fun v => ?_⟩
    have hv : IsKFin ε σ (v : H) := v.2
    rw [eA, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, hA X₁ hX₁ v,
      hA X₂ hX₂ v, map_add, map_smul, hT X₁ hX₁ v hv, hT X₂ hX₂ v hv]
    rfl
  have hcas : P (casimirK ε A) := by
    unfold casimirK
    exact hsum _ _ fun a _ => hsum _ _ fun b _ => hmul _ _ (hgen a b) (hgen b a)
  have hpow : ∀ k : ℕ, P ((1 + casimirK ε A) ^ k) := by
    intro k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih (hadd _ _ hone hcas)
  exact hpow m

end PositivityTheory.CW

end
end

section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open ReciprocityTheory.ChartRestriction.DS (actM casimirK)
open scoped InnerProductSpace

namespace PositivityTheory.CW

namespace HilbertSchmidtSqEq₂

theorem hs2_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : hs2 g = hs g := rfl

theorem smul_seminorm_cont {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] {q : Seminorm ℂ E}
    (hq : Continuous q) (c : NNReal) : Continuous (c • q) := by
  rw [Seminorm.coe_smul]
  exact hq.const_smul c

end HilbertSchmidtSqEq₂

open HilbertSchmidtSqEq₂ in
theorem e3c : SmoothMapSeminormBound := by
  classical
  intro hM e3a e3b n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD A hA hMod T hG hd Q N hQc hQg hη
  obtain ⟨m, K, I₀, hK, hmax⟩ := hM n ε (kfin ε σ) A hMod N
  have hC : ∀ e : kfin ε σ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y, Sm ε σ y → ‖⟪(e : H), y⟫_ℂ‖ ≤ C * Q (T y) :=
    fun e => hη e e.2
  choose Ce hCe0 hCe using hC
  set Cs : ℝ := ∑ e ∈ I₀, Ce e with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun e _ => hCe0 e
  have h3a := e3a n ε (kfin ε σ) A hMod.gl hMod.uni hMod m
  obtain ⟨D, hDm⟩ := e3b n ε H σ hU hI E p π dπ hπ A hA T hd m
  have key : ∀ y : kfin ε σ, ‖(y : H)‖ ≤ K * Cs * Q (D (T y)) := by
    intro y
    obtain ⟨v, hv⟩ := h3a.1 y
    set w : H := ((((1 + casimirK ε A) ^ m) y : kfin ε σ) : H) with hwdef
    have hw : Sm ε σ w := hD.1 _ (((1 + casimirK ε A) ^ m) y).2
    let F : kfin ε σ →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ) :=
      { toFun := fun η g => ⟪w, σ g (η : H)⟫_ℂ
        map_add' := fun a b => by funext g; simp [inner_add_right]
        map_smul' := fun c a => by funext g; simp [inner_smul_right] }
    have hF : ∀ (η : kfin ε σ) g, F η g = ⟪w, σ g (η : H)⟫_ℂ := fun _ _ => rfl
    have h1 : ∀ η : kfin ε σ, ContinuousOn (F η) (ReciprocityTheory.ChartRestriction.DS.UJset ε) := fun η => by
      have := (continuousOn_const (c := w) (s := UJset ε)).inner (𝕜 := ℂ) (hU.2.2 (η : H))
      exact this
    have h2 : ∀ X, ReciprocityTheory.ChartRestriction.DS.inP ε X → ∀ η : kfin ε σ, ∀ g ∈ ReciprocityTheory.ChartRestriction.DS.UJset ε,
        HasDerivAt (fun t : ℝ => F η (g * NormedSpace.exp (t • X))) (F (actM A X η) g) 0 := by
      intro X hX η g hg
      have hXl : X ∈ lieSet ε := hX.1
      have hg' : g ∈ UJset ε := hg
      have hη' : Sm ε σ (η : H) := hD.1 _ η.2
      have ho : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) (η : H)) (dRep σ X η) 0 := by
        have := hasDerivAt_orbit hU hη' hXl 0
        rwa [zero_smul, NormedSpace.exp_zero, sigma_one hU] at this
      have h4 : HasDerivAt (fun t : ℝ => σ g (σ (NormedSpace.exp (t • X)) (η : H))) (σ g (dRep σ X η)) 0 :=
        ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 ho
      have h5 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h4
      simp only [ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply] at h5
      rw [hF, hA X hXl η]
      refine h5.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [Function.comp_apply, hF, innerSL_apply_apply]
      rw [sigma_mul hU hg' (exp_mem_UJ hXl t)]
    have h3 : ∀ η : kfin ε σ, ∃ C : ℝ, ∀ g ∈ ReciprocityTheory.ChartRestriction.DS.UJset ε, ‖F η g‖ ≤ C * (1 + hs2 g) ^ N := by
      intro η
      refine ⟨‖w‖ * ‖(η : H)‖, fun g hg => ?_⟩
      have hg' : g ∈ UJset ε := hg
      rw [hF, hs2_eq]
      have e1 : ‖⟪w, σ g (η : H)⟫_ℂ‖ ≤ ‖w‖ * ‖(η : H)‖ := by
        have := norm_inner_le_norm (𝕜 := ℂ) w (σ g (η : H))
        rwa [hU.2.1 g hg' (η : H)] at this
      have e2 : (1 : ℝ) ≤ (1 + hs g) ^ N := one_le_pow₀ (by linarith [hs_nonneg g])
      calc _ ≤ ‖w‖ * ‖(η : H)‖ := e1
        _ = ‖w‖ * ‖(η : H)‖ * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left e2 (by positivity)
    have h5b : ∀ e ∈ I₀, ∀ g ∈ ReciprocityTheory.ChartRestriction.DS.UJset ε, ‖F e g‖ ≤ (Cs * Q (T w)) * (1 + hs2 g) ^ N := by
      intro e he g hg
      have hg' : g ∈ UJset ε := hg
      rw [hF, hs2_eq, inner_sigma hU hg' w (e : H), norm_inner_symm]
      have hgi : g⁻¹ ∈ UJset ε := inv_mem_UJ hg'
      have e1 := hCe e (σ g⁻¹ w) (Sm.translate hU hw hgi)
      rw [hG.1 g⁻¹ hgi w hw] at e1
      have e2 := hQg g⁻¹ hgi (T w)
      rw [hs_inv hg'] at e2
      have e3 : Ce e ≤ Cs := Finset.single_le_sum (f := Ce) (fun x _ => hCe0 x) he
      have hQ0 : 0 ≤ Q (T w) := apply_nonneg _ _
      have hW0 : 0 ≤ (1 + hs g) ^ N := pow_nonneg (by linarith [hs_nonneg g]) _
      calc _ ≤ Ce e * Q (π g⁻¹ (T w)) := e1
        _ ≤ Ce e * ((1 + hs g) ^ N * Q (T w)) := mul_le_mul_of_nonneg_left e2 (hCe0 e)
        _ ≤ Cs * ((1 + hs g) ^ N * Q (T w)) := mul_le_mul_of_nonneg_right e3 (mul_nonneg hW0 hQ0)
        _ = _ := by ring
    have hmv := hmax F h1 h2 h3 (Cs * Q (T w)) (mul_nonneg hCs0 (apply_nonneg _ _)) h5b v
    rw [hv, hF, sigma_one hU] at hmv
    have hin : ⟪w, (v : H)⟫_ℂ = ⟪(y : H), (y : H)⟫_ℂ := by
      rw [hwdef, ← Submodule.coe_inner, ← Submodule.coe_inner, h3a.2 y v, hv]
    have hn : ‖⟪(y : H), (y : H)⟫_ℂ‖ = ‖(y : H)‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K, norm_pow]; simp
    rw [hin, hn] at hmv
    have hTw : T w = D (T y) := hDm y
    rw [hTw] at hmv
    have hy0 : 0 ≤ ‖(y : H)‖ := norm_nonneg _
    have hR0 : 0 ≤ K * Cs * Q (D (T y)) := mul_nonneg (mul_nonneg hK hCs0) (apply_nonneg _ _)
    rcases hy0.eq_or_lt with h0 | h0
    · rw [← h0]; exact hR0
    · have : ‖(y : H)‖ * ‖(y : H)‖ ≤ K * Cs * Q (D (T y)) * ‖(y : H)‖ := by
        have e : K * (Cs * Q (D (T y))) * ‖(y : H)‖ = K * Cs * Q (D (T y)) * ‖(y : H)‖ := by ring
        rw [← e, ← sq]
        exact hmv
      exact le_of_mul_le_mul_right this h0
  refine ⟨(K * Cs).toNNReal • Q.comp (D : E →ₗ[ℂ] E), smul_seminorm_cont ?_ _, fun v hv => ?_⟩
  · rw [Seminorm.coe_comp]
    exact hQc.comp D.continuous
  · rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (mul_nonneg hK hCs0),
      Seminorm.comp_apply]
    exact key ⟨v, hv⟩

end PositivityTheory.CW

end
end

section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace

namespace PositivityTheory.CW

theorem e3d : SobolevNormDomination := by
  intro he2 n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD T hT hd q hq hq1 S hS
  let Dop : List (Mx n) → (E →L[ℂ] E) := fun l =>
    l.foldr (fun X f => (dπ X).comp f) (ContinuousLinearMap.id ℂ E)
  have key : ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∀ v, IsKFin ε σ v →
      IsKFin ε σ (Dw σ l v) ∧ T (Dw σ l v) = Dop l (T v) := by
    intro l
    induction l with
    | nil => intro _ v hv; exact ⟨hv, rfl⟩
    | cons X l ih =>
      intro hl v hv
      obtain ⟨h1, h2⟩ := ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) v hv
      refine ⟨hD.2.1 _ h1 X (hl X List.mem_cons_self), ?_⟩
      show T (dRep σ X (Dw σ l v)) = dπ X (Dop l (T v))
      rw [hd X (hl X List.mem_cons_self) _ h1, h2]
  have hcont : ∀ l, Continuous (q.comp (Dop l : E →ₗ[ℂ] E)) := fun l => by
    rw [Seminorm.coe_comp, ContinuousLinearMap.coe_coe]
    exact hq.comp (Dop l).continuous
  have hw : ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∀ w, Sm ε σ w →
      ‖Dw σ l w‖ ≤ (q.comp (Dop l : E →ₗ[ℂ] E)) (T w) := by
    intro l hl
    refine (he2 n ε H σ hU hI E p π dπ hπ hD T hT _ (hcont l) l 0 0 hl).2 fun y hy => ?_
    obtain ⟨h1, h2⟩ := key l hl y hy
    calc ‖Dw σ l y‖ ≤ q (T (Dw σ l y)) := hq1 _ h1
      _ = _ := by rw [h2]; rfl
  have main : ∀ S : List (List (Mx n)), Words (lieSet ε) S →
      ∃ q' : Seminorm ℂ E, Continuous q' ∧ ∀ w, Sm ε σ w → sobNorm σ S w ≤ q' (T w) := by
    intro S
    induction S with
    | nil =>
      intro _
      refine ⟨0, by rw [Seminorm.coe_zero]; exact continuous_zero, fun w _ => ?_⟩
      simp [sobNorm]
    | cons l S ih =>
      intro hS
      obtain ⟨q', hq', h'⟩ := ih (fun m hm => hS m (List.mem_cons_of_mem _ hm))
      have hl : ∀ X ∈ l, X ∈ lieSet ε := hS l List.mem_cons_self
      refine ⟨q.comp (Dop l : E →ₗ[ℂ] E) + q', ?_, fun w hw' => ?_⟩
      · rw [Seminorm.coe_add]
        exact (hcont l).add hq'
      · have e : sobNorm σ (l :: S) w = ‖Dw σ l w‖ + sobNorm σ S w := by
          first
            | rfl
            | simp [sobNorm]
        rw [e, Seminorm.add_apply]
        exact add_le_add (hw l hl w hw') (h' w hw')
  exact main S hS

end PositivityTheory.CW

end
end

section
namespace PositivityTheory.CW

theorem lift_of (hM : MaxPr) : GlobalTheory.Published.CasselmanWallachLift := by
  have hmodel := model_of c1 c2a c2b c3a c3b (k_types_finite_of_highest_weight c3c)
  exact lift_of_steps hM hmodel c4 c5 c6 c7 d0 d1b d2 d3 d4b d5

theorem cw_of (hM : MaxPr) : GlobalTheory.Published.CasselmanWallach := by
  have hmodel := model_of c1 c2a c2b c3a c3b (k_types_finite_of_highest_weight c3c)
  exact cw_of_steps hM hmodel c5 d0 (lift_of hM) e1a e1b e2a e2b e2c e2d e3a e3b e3c e3d

end PositivityTheory.CW
end
