import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactWhittakerEqGodementLocal
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableSplitWhittakerDensity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpanSetEqLatticePreimage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeAnnulusCosetDecomposition

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.WS.PF

theorem isSB_pF : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Φ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Φ → GlobalTheory.CompanionTheory.WS.IsSB (GlobalTheory.CompanionTheory.WS.pF χ Φ) := by
  intro F _ _ _ _ _ _ χ hχ Φ hΦ
  have hm := GodementSectionLocal.mem_schwartzBruhat2.1 (GlobalTheory.CompanionTheory.WcSplit.phiW_mem hχ hΦ.1 hΦ.2)
  have e : GlobalTheory.CompanionTheory.WS.pF χ Φ = GlobalTheory.CompanionTheory.WcSplit.phiW χ Φ ∘ (Homeomorph.finTwoArrow (X := F)).symm := by
    funext p
    simp [GlobalTheory.CompanionTheory.WS.pF, GlobalTheory.CompanionTheory.WcSplit.phiW, mul_comm]
  rw [e]
  exact ⟨hm.1.comp_continuous (Homeomorph.finTwoArrow (X := F)).symm.continuous,
    hm.2.comp_homeomorph (Homeomorph.finTwoArrow (X := F)).symm⟩

end GlobalTheory.CompanionTheory.WS.PF
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_fourier_schwartz_bruhat_plane : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Φ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Φ → GlobalTheory.CompanionTheory.WS.IsSB (GlobalTheory.CompanionTheory.WS.pF χ Φ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WS.PF.isSB_pF
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WS

theorem model_ne : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Φ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Φ → ∀ g : GL (Fin 2) F, g.val 1 0 ≠ 0 → ∀ u : Fˣ, GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => Φ (x * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) = mp u 1 * GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.pF χ Φ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) u := by
  intro F _ _ _ _ _ _ χ hχ Φ hΦ g hc u
  have hd0 : (g.val).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  have hdet : (g.val).det = g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 := Matrix.det_fin_two _
  rw [GlobalTheory.CompanionTheory.WcSplit.rW_lower hχ hΦ.1 hΦ.2 hc hdet hd0 u]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply, rowAct, pF, GlobalTheory.CompanionTheory.WcSplit.phiW, Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [mul_comm t]

end GlobalTheory.CompanionTheory.WS
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_whittaker_lower_left_nonzero : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Φ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Φ → ∀ g : GL (Fin 2) F, g.val 1 0 ≠ 0 → ∀ u : Fˣ, GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => Φ (x * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) = mp u 1 * GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.pF χ Φ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) u := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WS.model_ne
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WS

theorem modelzero_upper : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Φ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Φ → ∀ g : GL (Fin 2) F, g.val 1 0 = 0 → ∀ u : Fˣ, GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => Φ (x * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) = mp u 1 * GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.pF χ Φ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) u := by
  intro F _ _ _ _ _ _ χ hχ Φ hΦ g hg u
  have hdet : (g.val).det = g.val 0 0 * g.val 1 1 := by
    rw [Matrix.det_fin_two, hg]; ring
  have hdet0 : (g.val).det ≠ 0 := by
    have := g.isUnit.map (Matrix.detMonoidHom (n := Fin 2) (R := F))
    exact this.ne_zero
  have hA : g.val 0 0 ≠ 0 := fun h => hdet0 (by rw [hdet, h, zero_mul])
  have hD : g.val 1 1 ≠ 0 := fun h => hdet0 (by rw [hdet, h, mul_zero])
  have hu : (u : F) ≠ 0 := u.ne_zero
  set A := g.val 0 0 with hAdef
  set B := g.val 0 1 with hBdef
  set D := g.val 1 1 with hDdef
  have hc : (u : F) * D ≠ 0 := mul_ne_zero hu hD

  have hinn : GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.pF χ Φ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) u =
      ((modulus ((u : F) * D) : ℝ))⁻¹ * ((χ (B / D) : ℂ) * Φ ((u : F) * A, ((u : F) * D)⁻¹)) := by
    set G : F → ℂ := fun y' => GlobalTheory.CompanionTheory.WS.pF χ Φ ((u : F) * A, y') * (χ (-(y' / ((u : F) * D)) + B / D) : ℂ) with hG
    have h1 : GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.pF χ Φ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) u =
        ∫ y, (fun y => G (((u : F) * D) * y)) (y + B / D) ∂selfDualMeasure χ := by
      unfold GlobalTheory.CompanionTheory.WS.inn
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [Function.comp, GlobalTheory.CompanionTheory.WS.rowAct, hG, hg]
      have e1 : (u : F) * A + (u : F) * y * 0 = (u : F) * A := by ring
      have e2 : (u : F) * B + (u : F) * y * D = (u : F) * D * (y + B / D) := by
        field_simp
        ring
      have e3 : -((u : F) * D * (y + B / D) / ((u : F) * D)) + B / D = -y := by
        field_simp
        ring
      rw [e1, e2, e3]
    rw [h1, integral_add_right_eq_self (fun y => G (((u : F) * D) * y)) (B / D),
      GroundTheory.LocalField.integral_comp_mul_left _ hc G]
    have h2 : ∫ y, G y ∂selfDualMeasure χ = (χ (B / D) : ℂ) * Φ ((u : F) * A, ((u : F) * D)⁻¹) := by
      have h3 := GlobalTheory.CompanionTheory.WcSplit.integral_phiW hχ hΦ.1 hΦ.2 ((u : F) * A) (((u : F) * D)⁻¹)
      rw [← h3, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hG]
      have e4 : -(y / ((u : F) * D)) + B / D = B / D + -(y * ((u : F) * D)⁻¹) := by
        rw [div_eq_mul_inv y]; ring
      rw [e4, AddChar.map_add_eq_mul, Circle.coe_mul]
      have e7 : GlobalTheory.CompanionTheory.WS.pF χ Φ ((u : F) * A, y) = GlobalTheory.CompanionTheory.WcSplit.phiW χ Φ ![(u : F) * A, y] := by
        rw [GlobalTheory.CompanionTheory.WcSplit.phiW_pair]
        unfold GlobalTheory.CompanionTheory.WS.pF localFourier
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [mul_comm y t]
      rw [e7]
      ring
    rw [h2]
    simp [Complex.real_smul]
  rw [hinn]
  have hmod : ((modulus ((u : F) * D) : ℝ)) = (modulus (u : F) : ℝ) * (modulus D : ℝ) := by
    rw [modulus_mul]; push_cast; rfl
  have hmu : (modulus (u : F) : ℝ) ≠ 0 := by
    exact_mod_cast modulus_ne_zero hu
  have hmD : (modulus D : ℝ) ≠ 0 := by
    exact_mod_cast modulus_ne_zero hD
  have ha' : A / (g.val).det = D⁻¹ := by
    rw [hdet]; field_simp
  have hz : (0 : F) / (g.val).det = 0 := zero_div _
  unfold GL2LocalData.rW
  rw [hg, hz, if_pos rfl, ha', GlobalTheory.CompanionTheory.WcSplit.nsg_pair (inv_ne_zero hD), GlobalTheory.CompanionTheory.WcSplit.norm_pair]
  have e5 : D⁻¹ * B * ((u : F) * ((u⁻¹ : Fˣ) : F)) = B / D := by
    simp only [Units.val_inv_eq_inv_val]
    field_simp
  have e6 : (algebraMap F (F × F) D⁻¹ * ((u : F), ((u⁻¹ : Fˣ) : F))) * ((g.val).det, 1) =
      ((u : F) * A, ((u : F) * D)⁻¹) := by
    rw [hdet]
    ext
    · simp
      field_simp
    · simp
  simp only [e5, e6]
  have hmp : mp u 1 = ((modulus (u : F) : ℝ) : ℂ) := by
    simp [mp]
  rw [hmp, hmod, modulus_inv]
  have hmuC : ((modulus (u : F) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hmu
  have hmDC : ((modulus D : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hmD
  push_cast
  field_simp

end GlobalTheory.CompanionTheory.WS
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_whittaker_upper_triangular_case : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Φ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Φ → ∀ g : GL (Fin 2) F, g.val 1 0 = 0 → ∀ u : Fˣ, GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => Φ (x * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) = mp u 1 * GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.pF χ Φ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) u := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WS.modelzero_upper
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WS

theorem inner_integrable : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Ψ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Ψ → ∀ u : Fˣ, Integrable (fun y : F => Ψ ((u : F), (u : F) * y) * (χ (-y) : ℂ)) (selfDualMeasure χ) := by
  intro F _ _ _ _ _ _ χ hχ Ψ hΨ u
  have hcΨ : Continuous Ψ := hΨ.1.continuous
  have hcχ : Continuous (fun y : F => ((χ (-y) : Circle) : ℂ)) :=
    (continuous_induced_dom : Continuous ((↑) : Circle → ℂ)).comp (hχ.1.comp continuous_neg)
  have hcg : Continuous (fun y : F => Ψ ((u : F), (u : F) * y)) :=
    hcΨ.comp (continuous_const.prodMk (continuous_const.mul continuous_id))
  have hK : IsCompact ((fun p : F × F => ((u⁻¹ : Fˣ) : F) * p.2) '' tsupport Ψ) :=
    hΨ.2.isCompact.image (continuous_const.mul continuous_snd)
  have hs : HasCompactSupport (fun y : F => Ψ ((u : F), (u : F) * y)) := by
    refine HasCompactSupport.intro hK (fun y hy => ?_)
    by_contra hne
    exact hy ⟨((u : F), (u : F) * y), subset_tsupport _ hne, by simp⟩
  exact (hcg.mul hcχ).integrable_of_hasCompactSupport hs.mul_right

end GlobalTheory.CompanionTheory.WS
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_twisted_section_line : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Ψ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Ψ → ∀ u : Fˣ, Integrable (fun y : F => Ψ ((u : F), (u : F) * y) * (χ (-y) : ℂ)) (selfDualMeasure χ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WS.inner_integrable
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.WS.Comp

theorem rowAct_rowAct {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (h k : GL (Fin 2) F) (v : F × F) :
    GlobalTheory.CompanionTheory.WS.rowAct h (GlobalTheory.CompanionTheory.WS.rowAct k v) = GlobalTheory.CompanionTheory.WS.rowAct (k * h) v := by
  ext <;>
    simp only [GlobalTheory.CompanionTheory.WS.rowAct, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem rowAct_one {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (v : F × F) :
    GlobalTheory.CompanionTheory.WS.rowAct (1 : GL (Fin 2) F) v = v := by
  ext <;> simp [GlobalTheory.CompanionTheory.WS.rowAct]

theorem continuous_rowAct {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (g : GL (Fin 2) F) :
    Continuous (GlobalTheory.CompanionTheory.WS.rowAct g) := by
  unfold GlobalTheory.CompanionTheory.WS.rowAct
  fun_prop

def rowActHomeo {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (g : GL (Fin 2) F) :
    (F × F) ≃ₜ (F × F) where
  toFun := GlobalTheory.CompanionTheory.WS.rowAct g
  invFun := GlobalTheory.CompanionTheory.WS.rowAct g⁻¹
  left_inv v := by rw [rowAct_rowAct, mul_inv_cancel, rowAct_one]
  right_inv v := by rw [rowAct_rowAct, inv_mul_cancel, rowAct_one]
  continuous_toFun := continuous_rowAct g
  continuous_invFun := continuous_rowAct g⁻¹

theorem isSB_comp_rowAct : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (Ψ : F × F → ℂ),
    GlobalTheory.CompanionTheory.WS.IsSB Ψ → ∀ g : GL (Fin 2) F, GlobalTheory.CompanionTheory.WS.IsSB (Ψ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) := by
  intro F _ _ _ _ _ _ Ψ hΨ g
  exact ⟨hΨ.1.comp_continuous (continuous_rowAct g),
    hΨ.2.comp_homeomorph (rowActHomeo g)⟩

end GlobalTheory.CompanionTheory.WS.Comp
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

theorem _root_.GlobalTheory.T.schwartz_bruhat_plane_right_translate : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (Ψ : F × F → ℂ), GlobalTheory.CompanionTheory.WS.IsSB Ψ → ∀ g : GL (Fin 2) F, GlobalTheory.CompanionTheory.WS.IsSB (Ψ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) := by
  first | exact @GlobalTheory.CompanionTheory.WS.Comp.isSB_comp_rowAct | exact GlobalTheory.CompanionTheory.WS.Comp.isSB_comp_rowAct | (intros; apply GlobalTheory.CompanionTheory.WS.Comp.isSB_comp_rowAct <;> assumption) | exact @GlobalTheory.CompanionTheory.WS.Comp.isSB_comp_rowAct | exact GlobalTheory.CompanionTheory.WS.Comp.isSB_comp_rowAct | (intros; apply GlobalTheory.CompanionTheory.WS.Comp.isSB_comp_rowAct <;> assumption) | exact @GlobalTheory.CompanionTheory.WS.Comp.continuous_rowAct | exact GlobalTheory.CompanionTheory.WS.Comp.continuous_rowAct | (intros; apply GlobalTheory.CompanionTheory.WS.Comp.continuous_rowAct <;> assumption) | exact @GlobalTheory.CompanionTheory.WS.Comp.rowAct_one | exact GlobalTheory.CompanionTheory.WS.Comp.rowAct_one | (intros; apply GlobalTheory.CompanionTheory.WS.Comp.rowAct_one <;> assumption) | exact @GlobalTheory.CompanionTheory.WS.Comp.rowAct_rowAct | exact GlobalTheory.CompanionTheory.WS.Comp.rowAct_rowAct | (intros; apply GlobalTheory.CompanionTheory.WS.Comp.rowAct_rowAct <;> assumption)
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.WS.Coset

theorem isSB_cosetInd : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (n : ℤ) (x : F × F), GlobalTheory.CompanionTheory.WS.IsSB (GlobalTheory.CompanionTheory.WS.cosetInd n x) := by
  intro F _ _ _ _ _ _ n x
  have hB : IsClopen (valBall F n : Set F) :=
    ⟨AddSubgroup.isClosed_of_isOpen _ (isOpen_valBall n), isOpen_valBall n⟩
  have hP : IsClopen ((valBall F n : Set F) ×ˢ (valBall F n : Set F)) := hB.prod hB
  have hS : {v : F × F | v - x ∈ Ln F n} =
      (fun v : F × F => v - x) ⁻¹' ((valBall F n : Set F) ×ˢ (valBall F n : Set F)) := rfl
  have hC : IsClopen {v : F × F | v - x ∈ Ln F n} := by
    rw [hS]
    exact hP.preimage (continuous_id.sub continuous_const)
  have hK : IsCompact {v : F × F | v - x ∈ Ln F n} := by
    rw [hS]
    exact (Homeomorph.subRight x).isCompact_preimage.2
      ((isCompact_valBall n).prod (isCompact_valBall n))
  refine ⟨?_, ?_⟩
  · exact (LocallyConstant.indicator (1 : LocallyConstant (F × F) ℂ) hC).isLocallyConstant
  · exact HasCompactSupport.intro hK fun v hv => Set.indicator_of_notMem hv _

end GlobalTheory.CompanionTheory.WS.Coset
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_indicator_schwartz_bruhat : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (n : ℤ) (x : F × F), GlobalTheory.CompanionTheory.WS.IsSB (GlobalTheory.CompanionTheory.WS.cosetInd n x) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WS.Coset.isSB_cosetInd
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.WS.Decomp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem add_mem_Ln {n : ℤ} {u v : F × F} (hu : u ∈ Ln F n) (hv : v ∈ Ln F n) :
    u + v ∈ Ln F n :=
  ⟨add_mem hu.1 hv.1, add_mem hu.2 hv.2⟩

theorem neg_mem_Ln {n : ℤ} {u : F × F} (hu : u ∈ Ln F n) : -u ∈ Ln F n :=
  ⟨neg_mem hu.1, neg_mem hu.2⟩

theorem zero_mem_Ln (n : ℤ) : (0 : F × F) ∈ Ln F n :=
  ⟨zero_mem _, zero_mem _⟩

theorem Ln_anti {m n : ℤ} (h : m ≤ n) : Ln F n ⊆ Ln F m :=
  fun _ hv => ⟨valBall_antitone h hv.1, valBall_antitone h hv.2⟩

theorem isOpen_Ln (n : ℤ) : IsOpen (Ln F n) :=
  ((isOpen_valBall n).preimage continuous_fst).inter ((isOpen_valBall n).preimage continuous_snd)

theorem exists_Ln_subset {U : Set (F × F)} (hU : U ∈ 𝓝 (0 : F × F)) : ∃ n : ℤ, Ln F n ⊆ U := by
  rw [show (0 : F × F) = ((0 : F), (0 : F)) from rfl, mem_nhds_prod_iff] at hU
  obtain ⟨u, hu, v, hv, huv⟩ := hU
  obtain ⟨a, -, ha⟩ := hasBasis_nhds_zero_valBall.mem_iff.mp hu
  obtain ⟨b, -, hb⟩ := hasBasis_nhds_zero_valBall.mem_iff.mp hv
  refine ⟨max a b, fun w hw => huv ?_⟩
  exact ⟨ha (valBall_antitone (le_max_left a b) hw.1),
    hb (valBall_antitone (le_max_right a b) hw.2)⟩

theorem exists_periodic {Ψ : F × F → ℂ} (hl : IsLocallyConstant Ψ) (hc : HasCompactSupport Ψ) :
    ∃ n : ℤ, ∀ y, ∀ h ∈ Ln F n, Ψ (y + h) = Ψ y := by
  have hloc : ∀ x : F × F, ∃ n : ℤ, ∀ h ∈ Ln F n, Ψ (x + h) = Ψ x := by
    intro x
    have ho : IsOpen {h : F × F | Ψ (x + h) = Ψ x} :=
      (hl.isOpen_fiber (Ψ x)).preimage (continuous_const.add continuous_id)
    obtain ⟨n, hn⟩ := exists_Ln_subset (ho.mem_nhds (by simp))
    exact ⟨n, fun h hh => hn hh⟩
  choose n hn using hloc
  obtain ⟨t, -, ht⟩ := hc.isCompact.elim_nhds_subcover
    (fun x => {z : F × F | z - x ∈ Ln F (n x)})
    (fun x _ => ((isOpen_Ln _).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by simpa using zero_mem_Ln (n x)))
  obtain ⟨N, hN⟩ := (t.image n).exists_le
  have hval : ∀ y ∈ tsupport Ψ, ∀ h ∈ Ln F N, Ψ (y + h) = Ψ y := by
    intro y hy h hh
    have := ht hy
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hxt, hyx⟩ := this
    have hN' : h ∈ Ln F (n x) := Ln_anti (hN _ (Finset.mem_image_of_mem n hxt)) hh
    have e1 : Ψ y = Ψ x := by
      have := hn x (y - x) hyx
      rwa [add_sub_cancel] at this
    have e2 : Ψ (y + h) = Ψ x := by
      have := hn x (y + h - x)
        (by rw [show y + h - x = (y - x) + h by abel]; exact add_mem_Ln hyx hN')
      rwa [add_sub_cancel] at this
    rw [e1, e2]
  refine ⟨N, fun y h hh => ?_⟩
  by_cases hy : y ∈ tsupport Ψ
  · exact hval y hy h hh
  by_cases hyh : y + h ∈ tsupport Ψ
  · have := hval (y + h) hyh (-h) (neg_mem_Ln hh)
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyh]

theorem cosetInd_of_mem {n : ℤ} {x y : F × F} (h : y - x ∈ Ln F n) : cosetInd n x y = 1 := by
  unfold cosetInd
  rw [Set.indicator_of_mem (show y ∈ {v | v - x ∈ Ln F n} from h)]
  rfl

theorem cosetInd_of_notMem {n : ℤ} {x y : F × F} (h : y - x ∉ Ln F n) : cosetInd n x y = 0 := by
  unfold cosetInd
  exact Set.indicator_of_notMem (show y ∉ {v | v - x ∈ Ln F n} from h) _

theorem cosetInd_add {n : ℤ} (x y : F × F) {h : F × F} (hh : h ∈ Ln F n) :
    cosetInd n x (y + h) = cosetInd n x y := by
  by_cases hy : y - x ∈ Ln F n
  · rw [cosetInd_of_mem hy, cosetInd_of_mem]
    rw [show y + h - x = (y - x) + h by abel]
    exact add_mem_Ln hy hh
  · rw [cosetInd_of_notMem hy, cosetInd_of_notMem]
    intro hyh
    apply hy
    have := add_mem_Ln hyh (neg_mem_Ln hh)
    rwa [show y + h - x + -h = y - x by abel] at this

theorem mem_span_of_cover (n : ℤ) (t : Finset (F × F)) :
    ∀ Ψ : F × F → ℂ, (∀ y, ∀ h ∈ Ln F n, Ψ (y + h) = Ψ y) →
      (∀ y, Ψ y ≠ 0 → ∃ x ∈ t, y - x ∈ Ln F n) →
      Ψ ∈ Submodule.span ℂ (Set.range (cosetInd (F := F) n)) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro Ψ _ hs
    have : Ψ = 0 := by
      funext y
      by_contra hy
      obtain ⟨x, hx, -⟩ := hs y hy
      simp at hx
    rw [this]
    exact zero_mem _
  | insert x t _ ih =>
    intro Ψ hp hs
    have hmem : Ψ - Ψ x • cosetInd n x ∈ Submodule.span ℂ (Set.range (cosetInd (F := F) n)) := by
      refine ih _ (fun y h hh => ?_) (fun y hy => ?_)
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [hp y h hh, cosetInd_add x y hh]
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hy
        by_cases hyx : y - x ∈ Ln F n
        · exfalso
          apply hy
          have := hp x (y - x) hyx
          rw [add_sub_cancel] at this
          rw [cosetInd_of_mem hyx, this]
          ring
        · rw [cosetInd_of_notMem hyx, mul_zero, sub_zero] at hy
          obtain ⟨x', hx', hyx'⟩ := hs y hy
          rcases Finset.mem_insert.mp hx' with rfl | hx''
          · exact absurd hyx' hyx
          · exact ⟨x', hx'', hyx'⟩
    have hx : cosetInd n x ∈ Submodule.span ℂ (Set.range (cosetInd (F := F) n)) :=
      Submodule.subset_span ⟨x, rfl⟩
    have := add_mem hmem (Submodule.smul_mem _ (Ψ x) hx)
    rwa [sub_add_cancel] at this

theorem exists_sum_cosetInd : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (Ψ : F × F → ℂ),
    GlobalTheory.CompanionTheory.WS.IsSB Ψ → ∃ (n : ℤ) (s : Finset (F × F)) (a : F × F → ℂ),
      Ψ = ∑ x ∈ s, a x • GlobalTheory.CompanionTheory.WS.cosetInd n x := by
  intro F _ _ _ _ _ _ Ψ hΨ
  classical
  obtain ⟨n, hn⟩ := exists_periodic hΨ.1 hΨ.2
  obtain ⟨t, -, ht⟩ := hΨ.2.isCompact.elim_nhds_subcover
    (fun x => {z : F × F | z - x ∈ Ln F n})
    (fun x _ => ((isOpen_Ln _).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by simpa using zero_mem_Ln n))
  have hspan := mem_span_of_cover n t Ψ hn (fun y hy => by
    have := ht (subset_tsupport Ψ (Function.mem_support.mpr hy))
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hx, hyx⟩ := this
    exact ⟨x, hx, hyx⟩)
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hspan
  exact ⟨n, c.support, c, by rw [← hc]; rfl⟩

end GlobalTheory.CompanionTheory.WS.Decomp
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_plane_coset_span : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (Ψ : F × F → ℂ), GlobalTheory.CompanionTheory.WS.IsSB Ψ → ∃ (n : ℤ) (s : Finset (F × F)) (a : F × F → ℂ), Ψ = ∑ x ∈ s, a x • GlobalTheory.CompanionTheory.WS.cosetInd n x := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WS.Decomp.exists_sum_cosetInd
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.WS

theorem unit_mul_mem_valBall_iff {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℤ) (t : Fˣ) (ht : t ∈ unitFiltrationUnits F 0) (y : F) :
    (t : F) * y ∈ valBall F n ↔ y ∈ valBall F n := by
  have h0 : ord (t : F) = 0 := mem_unitFiltrationUnits_zero_iff_ord.1 ht
  by_cases hy : y = 0
  · simp [hy]
  rw [mem_valBall_iff_le_ord (mul_ne_zero t.ne_zero hy), mem_valBall_iff_le_ord hy,
    ord_mul t.ne_zero hy, h0, zero_add]

theorem cosetInd_unit_smul : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (n : ℤ) (x : F × F) (t : Fˣ),
    t ∈ unitFiltrationUnits F 0 →
      GlobalTheory.CompanionTheory.WS.cosetInd n ((t : F) • x) = fun v => GlobalTheory.CompanionTheory.WS.cosetInd n x (((t⁻¹ : Fˣ) : F) • v) := by
  intro F _ _ _ _ _ _ n x t ht
  have hti : t⁻¹ ∈ unitFiltrationUnits F 0 := inv_mem ht
  have hc : ∀ a b : F, a - (t : F) * b ∈ valBall F n ↔
      ((t⁻¹ : Fˣ) : F) * a - b ∈ valBall F n := by
    intro a b
    have e : ((t⁻¹ : Fˣ) : F) * (a - (t : F) * b) = ((t⁻¹ : Fˣ) : F) * a - b := by
      rw [mul_sub, ← mul_assoc, Units.inv_mul, one_mul]
    rw [← e, unit_mul_mem_valBall_iff n t⁻¹ hti]
  have hs : ∀ v : F × F, v - (t : F) • x ∈ Ln F n ↔ ((t⁻¹ : Fˣ) : F) • v - x ∈ Ln F n := by
    intro v
    simp only [Ln, Set.mem_ofPred_eq, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, hc]
  funext v
  have hm : v ∈ {w : F × F | w - (t : F) • x ∈ Ln F n} ↔
      ((t⁻¹ : Fˣ) : F) • v ∈ {w : F × F | w - x ∈ Ln F n} := hs v
  unfold cosetInd
  by_cases h : v ∈ {w : F × F | w - (t : F) • x ∈ Ln F n}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hm.1 h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hm.2 h'))]

end GlobalTheory.CompanionTheory.WS
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_indicator_unit_scaling : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (n : ℤ) (x : F × F) (t : Fˣ), t ∈ unitFiltrationUnits F 0 → GlobalTheory.CompanionTheory.WS.cosetInd n ((t : F) • x) = fun v => GlobalTheory.CompanionTheory.WS.cosetInd n x (((t⁻¹ : Fˣ) : F) • v) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WS.cosetInd_unit_smul
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.WS

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem mem_Ln_zero_iff (v : F × F) : v ∈ Ln F 0 ↔ v.1 ∈ 𝒪[F] ∧ v.2 ∈ 𝒪[F] := by
  simp only [Ln, Set.mem_setOf_eq, mem_valBall_zero_iff]

theorem rowAct_mem_Ln_zero {k : GL (Fin 2) F} (h : ∀ i j, k.val i j ∈ 𝒪[F]) {v : F × F}
    (hv : v ∈ Ln F 0) : rowAct k v ∈ Ln F 0 := by
  rw [mem_Ln_zero_iff] at hv ⊢
  exact ⟨add_mem (mul_mem hv.1 (h 0 0)) (mul_mem hv.2 (h 1 0)),
    add_mem (mul_mem hv.1 (h 0 1)) (mul_mem hv.2 (h 1 1))⟩

theorem rowAct_inv_rowAct (k : GL (Fin 2) F) (v : F × F) : rowAct k⁻¹ (rowAct k v) = v := by
  obtain ⟨m, hm⟩ : ∃ m : Matrix (Fin 2) (Fin 2) F, m = (k⁻¹).val := ⟨_, rfl⟩
  have h : k.val * m = 1 := by
    rw [hm, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel]; rfl
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  ext
  · simp only [rowAct, ← hm]
    linear_combination v.1 * e00 + v.2 * e10
  · simp only [rowAct, ← hm]
    linear_combination v.1 * e01 + v.2 * e11

theorem standard_lattice_indicator_invariant (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (k : GL (Fin 2) F)
    (hk : k ∈ GLnLocal.integralGL F 2) : lat0 F ∘ rowAct k = lat0 F := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
  have key : ∀ v, rowAct k v ∈ Ln F 0 ↔ v ∈ Ln F 0 := fun v =>
    ⟨fun h => by
      have := rowAct_mem_Ln_zero (k := k⁻¹) h2 h
      rwa [rowAct_inv_rowAct] at this, rowAct_mem_Ln_zero h1⟩
  funext v
  by_cases hv : v ∈ Ln F 0
  · simp [lat0, Set.indicator_of_mem hv, Set.indicator_of_mem ((key v).2 hv)]
  · simp [lat0, Set.indicator_of_notMem hv, Set.indicator_of_notMem (fun h => hv ((key v).1 h))]

end GlobalTheory.CompanionTheory.WS
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_lattice_integral_GL2_invariant : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (k : GL (Fin 2) F), k ∈ GLnLocal.integralGL F 2 → GlobalTheory.CompanionTheory.WS.lat0 F ∘ GlobalTheory.CompanionTheory.WS.rowAct k = GlobalTheory.CompanionTheory.WS.lat0 F := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WS.standard_lattice_indicator_invariant
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WS

theorem rowAct_mul_left {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (v g : GL (Fin 2) F) (w : F × F) :
    rowAct (v * g) w = rowAct g (rowAct v w) := by
  ext <;> simp only [rowAct, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem inn_unipotent_left {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (χ : AddChar F Circle) (Ψ : F × F → ℂ) (v g : GL (Fin 2) F)
    (hv : v ∈ Iwasawa.unipotent F 2) (u : Fˣ) :
    inn χ (Ψ ∘ rowAct (v * g)) u = (χ (v.val 0 1) : ℂ) * inn χ (Ψ ∘ rowAct g) u := by
  have h00 : v.val 0 0 = 1 := hv.2 0
  have h11 : v.val 1 1 = 1 := hv.2 1
  have h10 : v.val 1 0 = 0 := hv.1 (by decide : (0 : Fin 2) < 1)
  set x := v.val 0 1 with hx
  set h : F → ℂ := fun y => (Ψ ∘ rowAct g) ((u : F), (u : F) * y) * (χ (-y) : ℂ) with hh
  have key : ∀ y : F, (Ψ ∘ rowAct (v * g)) ((u : F), (u : F) * y) * (χ (-y) : ℂ) =
      (χ x : ℂ) * h (y + x) := by
    intro y
    have hrow : rowAct v ((u : F), (u : F) * y) = ((u : F), (u : F) * (y + x)) := by
      ext
      · simp only [rowAct, h00, h10]; ring
      · simp only [rowAct, h11, ← hx]; ring
    have hchi : (χ (-y) : ℂ) = (χ x : ℂ) * (χ (-(y + x)) : ℂ) := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    simp only [hh, Function.comp_apply, rowAct_mul_left, hrow, hchi]
    ring
  have htr : ∫ y, h (y + x) ∂selfDualMeasure χ = ∫ y, h y ∂selfDualMeasure χ :=
    integral_add_right_eq_self h x
  calc inn χ (Ψ ∘ rowAct (v * g)) u
      = ∫ y, (χ x : ℂ) * h (y + x) ∂selfDualMeasure χ := by
        unfold inn
        exact integral_congr_ae (Eventually.of_forall key)
    _ = (χ x : ℂ) * inn χ (Ψ ∘ rowAct g) u := by
        rw [integral_const_mul, htr]
        rfl

theorem WL_unipotent_left : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (Ψ : F × F → ℂ) (v g : GL (Fin 2) F), v ∈ Iwasawa.unipotent F 2 → GlobalTheory.CompanionTheory.WS.WL χ c₁ c₂ Ψ (v * g) = Whittaker.psiN (Circle.coeHom.compAddChar χ) v * GlobalTheory.CompanionTheory.WS.WL χ c₁ c₂ Ψ g := by
  intro F _ _ _ _ _ _ χ c₁ c₂ Ψ v g hv
  have h00 : v.val 0 0 = 1 := hv.2 0
  have h11 : v.val 1 1 = 1 := hv.2 1
  have h10 : v.val 1 0 = 0 := hv.1 (by decide : (0 : Fin 2) < 1)
  have hdetv : Matrix.GeneralLinearGroup.det v = 1 := by
    apply Units.ext
    simp [Matrix.det_fin_two, h00, h11, h10]
  have hdet : Matrix.GeneralLinearGroup.det (v * g) = Matrix.GeneralLinearGroup.det g := by
    rw [map_mul, hdetv, one_mul]
  have hpsi : Whittaker.psiN (Circle.coeHom.compAddChar χ) v = (χ (v.val 0 1) : ℂ) := by
    have hs : Whittaker.superdiagSum (v : Matrix (Fin 2) (Fin 2) F) = v.val 0 1 := by
      simp [Whittaker.superdiagSum, Fin.sum_univ_two]
    rw [Whittaker.psiN, hs]
    rfl
  have hlin : lin χ c₁ c₂ (Ψ ∘ rowAct (v * g)) =
      (χ (v.val 0 1) : ℂ) * lin χ c₁ c₂ (Ψ ∘ rowAct g) := by
    unfold lin
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [den, inn_unipotent_left χ Ψ v g hv u]
    ring
  rw [WL, WL, hdet, hlin, hpsi]
  ring

end GlobalTheory.CompanionTheory.WS
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_whittaker_left_unipotent : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (Ψ : F × F → ℂ) (v g : GL (Fin 2) F), v ∈ Iwasawa.unipotent F 2 → GlobalTheory.CompanionTheory.WS.WL χ c₁ c₂ Ψ (v * g) = Whittaker.psiN (Circle.coeHom.compAddChar χ) v * GlobalTheory.CompanionTheory.WS.WL χ c₁ c₂ Ψ g := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WS.WL_unipotent_left
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WS
namespace InnTorus

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem rowAct_torusPow (l : Fin 2 → ℤ) (v : F × F) :
    rowAct (Iwasawa.torusPow F 2 l) v =
      (v.1 * (GLnLocal.uniformizer F : F) ^ l 0, v.2 * (GLnLocal.uniformizer F : F) ^ l 1) := by
  have h : (Iwasawa.torusPow F 2 l).val = diagonal fun i => (GLnLocal.uniformizer F : F) ^ l i :=
    Iwasawa.coe_torusPow F 2 l
  unfold rowAct
  rw [h]
  simp [Matrix.diagonal]

theorem unif_ne_zero : (GLnLocal.uniformizer F : F) ≠ 0 :=
  (Iwasawa.uniformizerUnit F).ne_zero

theorem ord_mul_unif_zpow {x : F} (hx : x ≠ 0) (k : ℤ) :
    ord (x * (GLnLocal.uniformizer F : F) ^ k) = ord x + k := by
  have h := ord_units_zpow (Iwasawa.uniformizerUnit F) k
  have hz : (((Iwasawa.uniformizerUnit F ^ k : Fˣ)) : F) = (GLnLocal.uniformizer F : F) ^ k := by
    simp [Units.val_zpow_eq_zpow_val]
  rw [hz, Iwasawa.coe_uniformizerUnit, ord_uniformizer (GLnLocal.irreducible_uniformizer F),
    mul_one] at h
  rw [ord_mul hx (zpow_ne_zero _ unif_ne_zero), h]

theorem mul_unif_zpow_mem_iff {x : F} (hx : x ≠ 0) (k : ℤ) :
    x * (GLnLocal.uniformizer F : F) ^ k ∈ valBall F 0 ↔ -k ≤ ord x := by
  rw [mem_valBall_iff_le_ord (mul_ne_zero hx (zpow_ne_zero _ unif_ne_zero)), ord_mul_unif_zpow hx]
  omega

theorem mul_mul_unif_zpow_mem_iff {u : F} (hu : u ≠ 0) (y : F) (k : ℤ) :
    u * y * (GLnLocal.uniformizer F : F) ^ k ∈ valBall F 0 ↔ y ∈ valBall F (-ord u - k) := by
  by_cases hy : y = 0
  · simp [hy, zero_mem]
  rw [mul_unif_zpow_mem_iff (mul_ne_zero hu hy), mem_valBall_iff_le_ord hy, ord_mul hu hy]
  omega

variable [MeasurableSpace F] [BorelSpace F]

theorem selfDualMeasure_eq {χ : AddChar F Circle} (hχ : IsStd χ) :
    selfDualMeasure χ = haarIntegers F := by
  unfold GroundTheory.LocalField.selfDualMeasure
  rw [hχ.2.2]
  simp

theorem integral_indicator_valBall {χ : AddChar F Circle} (hχ : IsStd χ) (m : ℤ) :
    ∫ y, (valBall F m : Set F).indicator (fun y => ((χ (-y) : Circle) : ℂ)) y ∂haarIntegers F =
      if 0 ≤ m then (residueCard F : ℂ) ^ (-m) else 0 := by
  have ht : IsTrivialOn χ 0 := by
    have := isTrivialOn_addCharConductor hχ.1 hχ.2.1
    rwa [hχ.2.2] at this
  split_ifs with hm
  · have h1 : Set.EqOn (fun y => ((χ (-y) : Circle) : ℂ)) (fun _ => (1 : ℂ)) (valBall F m : Set F) := by
      intro y hy
      have hy0 : -y ∈ valBall F 0 := neg_mem (valBall_antitone hm hy)
      simp [ht _ hy0]
    rw [integral_indicator (measurableSet_valBall m),
      setIntegral_congr_fun (measurableSet_valBall m) h1, setIntegral_const, measureReal_def,
      haarIntegers_valBall, ENNReal.coe_toReal]
    simp
  · have hnot := not_isTrivialOn_addCharConductor_sub_one hχ.1 hχ.2.1
    rw [hχ.2.2] at hnot
    unfold IsTrivialOn at hnot
    push_neg at hnot
    obtain ⟨y₀, hy₀, hne⟩ := hnot
    have hy₀m : y₀ ∈ valBall F m := valBall_antitone (by omega) hy₀
    set f : F → ℂ := (valBall F m : Set F).indicator (fun y => ((χ (-y) : Circle) : ℂ)) with hf
    have shift : ∀ y, f (y + y₀) = ((χ (-y₀) : Circle) : ℂ) * f y := by
      intro y
      by_cases hy : y ∈ valBall F m
      · have hy' : y + y₀ ∈ valBall F m := add_mem hy hy₀m
        rw [hf, Set.indicator_of_mem (show y + y₀ ∈ (valBall F m : Set F) from hy'),
          Set.indicator_of_mem (show y ∈ (valBall F m : Set F) from hy), neg_add, add_comm,
          AddChar.map_add_eq_mul, Circle.coe_mul]
      · have hy' : y + y₀ ∉ valBall F m := fun h => hy (by simpa using sub_mem h hy₀m)
        rw [hf, Set.indicator_of_notMem (show y + y₀ ∉ (valBall F m : Set F) from hy'),
          Set.indicator_of_notMem (show y ∉ (valBall F m : Set F) from hy), mul_zero]
    have hI : ∫ y, f y ∂haarIntegers F = ((χ (-y₀) : Circle) : ℂ) * ∫ y, f y ∂haarIntegers F := by
      rw [← integral_const_mul, ← integral_add_right_eq_self f y₀]
      exact integral_congr_ae (Filter.Eventually.of_forall shift)
    have hc : ((χ (-y₀) : Circle) : ℂ) ≠ 1 := by
      intro h
      apply hne
      have h' : χ (-y₀) = 1 := Circle.ext (by simpa using h)
      rw [AddChar.map_neg_eq_inv, inv_eq_one] at h'
      exact h'
    have h0 : (1 - ((χ (-y₀) : Circle) : ℂ)) * ∫ y, f y ∂haarIntegers F = 0 := by
      rw [sub_mul, one_mul, ← hI, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc.symm)

theorem mp_one_inv (u : Fˣ) : (mp u 1)⁻¹ = (residueCard F : ℂ) ^ ord (u : F) := by
  unfold mp
  rw [Complex.cpow_one, modulus_of_ne_zero u.ne_zero]
  push_cast
  rw [_root_.zpow_neg, inv_inv]

theorem inner_integral_standard_lattice_torus : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ (l : Fin 2 → ℤ) (u : Fˣ), GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.lat0 F ∘ GlobalTheory.CompanionTheory.WS.rowAct (Iwasawa.torusPow F 2 l)) u = if -(l 0) ≤ ord (u : F) ∧ ord (u : F) ≤ -(l 1) then ((Spherical.qF F : ℕ) : ℂ) ^ (l 1) * (mp u 1)⁻¹ else 0 := by
  intro F _ _ _ _ _ _ χ hχ l u
  have hpt : ∀ y : F, (lat0 F ∘ rowAct (Iwasawa.torusPow F 2 l)) ((u : F), (u : F) * y) *
      ((χ (-y) : Circle) : ℂ) = if -(l 0) ≤ ord (u : F) then
        (valBall F (-ord (u : F) - l 1) : Set F).indicator (fun y => ((χ (-y) : Circle) : ℂ)) y
        else 0 := by
    intro y
    have h1 := mul_unif_zpow_mem_iff u.ne_zero (l 0)
    have h2 := mul_mul_unif_zpow_mem_iff u.ne_zero y (l 1)
    simp only [Function.comp, rowAct_torusPow, lat0]
    by_cases hA : -(l 0) ≤ ord (u : F)
    · rw [if_pos hA]
      by_cases hy : y ∈ valBall F (-ord (u : F) - l 1)
      · rw [Set.indicator_of_mem (show ((u : F) * (GLnLocal.uniformizer F : F) ^ l 0,
            (u : F) * y * (GLnLocal.uniformizer F : F) ^ l 1) ∈ Ln F 0 from ⟨h1.2 hA, h2.2 hy⟩),
          Set.indicator_of_mem (show y ∈ (valBall F (-ord (u : F) - l 1) : Set F) from hy)]
        simp
      · rw [Set.indicator_of_notMem (show ((u : F) * (GLnLocal.uniformizer F : F) ^ l 0,
            (u : F) * y * (GLnLocal.uniformizer F : F) ^ l 1) ∉ Ln F 0 from fun h => hy (h2.1 h.2)),
          Set.indicator_of_notMem (show y ∉ (valBall F (-ord (u : F) - l 1) : Set F) from hy)]
        simp
    · rw [if_neg hA, Set.indicator_of_notMem (show ((u : F) * (GLnLocal.uniformizer F : F) ^ l 0,
          (u : F) * y * (GLnLocal.uniformizer F : F) ^ l 1) ∉ Ln F 0 from fun h => hA (h1.1 h.1))]
      simp
  unfold inn
  rw [selfDualMeasure_eq hχ]
  simp_rw [hpt]
  have hq : Spherical.qF F = residueCard F := rfl
  have hq0 : (residueCard F : ℂ) ≠ 0 := by exact_mod_cast residueCard_ne_zero
  by_cases hA : -(l 0) ≤ ord (u : F)
  · simp only [if_pos hA, integral_indicator_valBall hχ]
    by_cases hD : ord (u : F) ≤ -(l 1)
    · rw [if_pos (by omega), if_pos ⟨hA, hD⟩, mp_one_inv, hq, ← zpow_add₀ hq0]
      congr 1
      omega
    · rw [if_neg (by omega), if_neg (fun h => hD h.2)]
  · rw [if_neg (fun h => hA h.1)]
    simp [if_neg hA]

end InnTorus
end GlobalTheory.CompanionTheory.WS
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_integral_lattice_torus_formula : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ (l : Fin 2 → ℤ) (u : Fˣ), GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.lat0 F ∘ GlobalTheory.CompanionTheory.WS.rowAct (Iwasawa.torusPow F 2 l)) u = if -(l 0) ≤ ord (u : F) ∧ ord (u : F) ≤ -(l 1) then ((Spherical.qF F : ℕ) : ℂ) ^ (l 1) * (mp u 1)⁻¹ else 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WS.InnTorus.inner_integral_standard_lattice_torus
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WS

theorem unramified_apply_eq_zpow_ord {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {μ : Fˣ →* ℂˣ} (hμ : IsUnramifiedChar μ) (u : Fˣ) :
    ((μ u : ℂˣ) : ℂ) = ((μ (unifUnit F) : ℂˣ) : ℂ) ^ ord (u : F) := by
  have h0 : (unifUnit F ^ (-ord (u : F)) * u) ∈ ordShell F 0 := by
    rw [mem_ordShell, ord_units_mul, ord_unifUnit_zpow]
    omega
  have h1 : μ (unifUnit F ^ (-ord (u : F)) * u) = 1 := isUnramifiedChar_iff.mp hμ _ h0
  have h2 : μ u = μ (unifUnit F) ^ ord (u : F) := by
    rw [map_mul, map_zpow, _root_.zpow_neg] at h1
    exact (inv_mul_eq_one.mp h1).symm
  rw [h2, Units.val_zpow_eq_zpow_val]

theorem integral_unramified_shells : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (μ : Fˣ →* ℂˣ), IsUnramifiedChar μ → ∀ A D : ℤ, ∫ u : Fˣ, (if -A ≤ ord (u : F) ∧ ord (u : F) ≤ -D then ((μ u : ℂˣ) : ℂ) else 0) ∂multHaar F = ∑ j ∈ Finset.Icc D A, ((μ (unifUnit F) : ℂˣ) : ℂ) ^ (-j) := by
  intro F _ _ _ _ _ _ μ hμ A D
  have hpt : (fun u : Fˣ => if -A ≤ ord (u : F) ∧ ord (u : F) ≤ -D then ((μ u : ℂˣ) : ℂ) else 0) =
      fun u => ∑ j ∈ Finset.Icc D A,
        (ordShell F (-j)).indicator (fun _ => ((μ (unifUnit F) : ℂˣ) : ℂ) ^ (-j)) u := by
    funext u
    by_cases h : -A ≤ ord (u : F) ∧ ord (u : F) ≤ -D
    · rw [if_pos h, Finset.sum_eq_single (-ord (u : F))]
      · rw [Set.indicator_of_mem (by rw [mem_ordShell]; omega), neg_neg,
          unramified_apply_eq_zpow_ord hμ]
      · intro j _ hj
        refine Set.indicator_of_notMem (fun hu => hj ?_) _
        rw [mem_ordShell] at hu
        omega
      · intro hn
        exact absurd (Finset.mem_Icc.mpr (by omega)) hn
    · rw [if_neg h]
      symm
      refine Finset.sum_eq_zero fun j hj => Set.indicator_of_notMem (fun hu => h ?_) _
      rw [mem_ordShell] at hu
      have := Finset.mem_Icc.mp hj
      omega
  have hint : ∀ j : ℤ, Integrable
      ((ordShell F (-j)).indicator (fun _ => ((μ (unifUnit F) : ℂˣ) : ℂ) ^ (-j))) (multHaar F) := by
    intro j
    rw [integrable_indicator_iff (measurableSet_ordShell _)]
    exact integrableOn_const (by rw [multHaar_ordShell]; exact ENNReal.one_ne_top)
  rw [hpt, integral_finset_sum _ fun j _ => hint j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_indicator (measurableSet_ordShell _), setIntegral_const, measureReal_def,
    multHaar_ordShell]
  simp

end GlobalTheory.CompanionTheory.WS
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_character_annulus_integral : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (μ : Fˣ →* ℂˣ), IsUnramifiedChar μ → ∀ A D : ℤ, ∫ u : Fˣ, (if -A ≤ ord (u : F) ∧ ord (u : F) ≤ -D then ((μ u : ℂˣ) : ℂ) else 0) ∂multHaar F = ∑ j ∈ Finset.Icc D A, ((μ (unifUnit F) : ℂˣ) : ℂ) ^ (-j) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WS.integral_unramified_shells
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.WS.SchurTwo

open GroundTheory.Automorphic.Spherical

theorem sum_Icc_sub_succ {G : Type*} [AddCommGroup G] (f : ℤ → G) (D A : ℤ) (h : D ≤ A) :
    ∑ j ∈ Finset.Icc D A, (f j - f (j + 1)) = f D - f (A + 1) := by
  induction A, h using Int.le_induction with
  | base => simp
  | succ A hA ih =>
    have hI : Finset.Icc D (A + 1) = insert (A + 1) (Finset.Icc D A) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hI, Finset.sum_insert (by simp), ih]
    abel

theorem alternant_two (a b : ℤ) :
    alternant ![a, b] = monomial ![a, b] - monomial ![b, a] := by
  rw [alternant_eq_det, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← monomial_add, ← monomial_add]
  congr 2
  · funext i
    fin_cases i <;> simp
  · funext i
    fin_cases i <;> simp

theorem monomial_mul_two (a b c d : ℤ) :
    (monomial ![a, b] : LaurentRing 2) * monomial ![c, d] = monomial ![a + c, b + d] := by
  rw [← monomial_add]
  congr 1
  funext i
  fin_cases i <;> simp

theorem schur_two_eq_sum (A D : ℤ) (h : D ≤ A) :
    schur ![A, D] = ∑ j ∈ Finset.Icc D A, (monomial ![A + D - j, j] : LaurentRing 2) := by
  refine mul_left_cancel₀ (alternant_staircase_ne_zero (n := 2)) ?_
  have hs : staircase 2 = ![1, 0] := by
    funext i
    fin_cases i <;> simp [staircase]
  have hl : ![A, D] + staircase 2 = ![A + 1, D] := by
    rw [hs]
    funext i
    fin_cases i <;> simp
  rw [alternant_mul_schur, hl, hs, alternant_two, alternant_two, Finset.mul_sum]
  have hterm : ∀ j ∈ Finset.Icc D A,
      ((monomial ![1, 0] : LaurentRing 2) - monomial ![0, 1]) * monomial ![A + D - j, j] =
        (fun j : ℤ => (monomial ![A + D + 1 - j, j] : LaurentRing 2)) j -
          (fun j : ℤ => (monomial ![A + D + 1 - j, j] : LaurentRing 2)) (j + 1) := by
    intro j _
    rw [sub_mul, monomial_mul_two, monomial_mul_two]
    have e1 : (1 : ℤ) + (A + D - j) = A + D + 1 - j := by ring
    have e2 : (0 : ℤ) + j = j := by ring
    have e3 : (0 : ℤ) + (A + D - j) = A + D + 1 - (j + 1) := by ring
    have e4 : (1 : ℤ) + j = j + 1 := by ring
    rw [e1, e2, e3, e4]
  rw [Finset.sum_congr rfl hterm, sum_Icc_sub_succ _ D A h]
  have e5 : A + D + 1 - D = A + 1 := by ring
  have e6 : A + D + 1 - (A + 1) = D := by ring
  simp only [e5, e6]

theorem evalAt_monomial_two (x y : ℂˣ) (a b : ℤ) :
    evalAt ![x, y] (monomial ![a, b]) = (x : ℂ) ^ a * (y : ℂ) ^ b := by
  rw [evalAt_single, one_mul, monomialChar_apply, Fin.prod_univ_two]
  simp [Units.val_zpow_eq_zpow_val]

theorem evalAt_schur_two :
    ∀ (x y : ℂˣ) (A D : ℤ), D ≤ A → Spherical.evalAt ![x, y] (Spherical.schur ![A, D]) = ∑ j ∈ Finset.Icc D A, (x : ℂ) ^ (A + D - j) * (y : ℂ) ^ j := by
  intro x y A D h
  rw [schur_two_eq_sum A D h, map_sum]
  exact Finset.sum_congr rfl fun j _ => evalAt_monomial_two x y _ _

end GlobalTheory.CompanionTheory.WS.SchurTwo
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_polynomial_GL2_sum : ∀ (x y : ℂˣ) (A D : ℤ), D ≤ A → Spherical.evalAt ![x, y] (Spherical.schur ![A, D]) = ∑ j ∈ Finset.Icc D A, (x : ℂ) ^ (A + D - j) * (y : ℂ) ^ j := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WS.SchurTwo.evalAt_schur_two
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.WS

theorem mp_uniformizer_zpow_half (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (m : ℤ) :
    mp (Iwasawa.uniformizerUnit F ^ m) (1 / 2) = Spherical.sqrtQ F ^ (-m) := by
  set r : NNReal := NNReal.sqrt (Spherical.qF F : NNReal) with hr
  have hr2 : r ^ 2 = (Spherical.qF F : NNReal) := NNReal.sq_sqrt _
  have hmod : Measures.modulus (((Iwasawa.uniformizerUnit F ^ m : Fˣ)) : F) = (r ^ (-m)) ^ 2 := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, Iwasawa.coe_uniformizerUnit,
      Spherical.modulus_uniformizer, ← hr2, ← zpow_natCast r 2, ← zpow_natCast (r ^ (-m)) 2,
      ← _root_.zpow_neg, ← _root_.zpow_mul, ← _root_.zpow_mul]
    congr 1
    push_cast
    ring
  have hS : Spherical.sqrtQ F = ((r : ℝ) : ℂ) := rfl
  have ht : (0 : ℝ) ≤ ((r ^ (-m) : NNReal) : ℝ) := NNReal.coe_nonneg _
  have hbr : GroundTheory.LocalField.modulus (((Iwasawa.uniformizerUnit F ^ m : Fˣ)) : F) = (r ^ (-m)) ^ 2 := by
    rw [← GroundTheory.LocalField.distribHaarChar_eq_modulus, ← Measures.modulus_units, hmod]
  unfold mp
  rw [hbr, hS, NNReal.coe_pow, Complex.ofReal_pow]
  have h1 : (((r ^ (-m) : NNReal) : ℝ) : ℂ) ^ 2 = (((((r ^ (-m) : NNReal) : ℝ) ^ 2 : ℝ)) : ℂ) := by
    push_cast; rfl
  rw [h1]
  have h2 : ((1 : ℂ) / 2) = (((1 / 2 : ℝ)) : ℂ) := by push_cast; rfl
  rw [h2, ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq ht,
    NNReal.coe_zpow, Complex.ofReal_zpow]

end GlobalTheory.CompanionTheory.WS
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_half_uniformizer_power : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (m : ℤ), mp (Iwasawa.uniformizerUnit F ^ m) (1 / 2) = Spherical.sqrtQ F ^ (-m) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WS.mp_uniformizer_zpow_half
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.WS

theorem L_pF : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Φ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Φ → GlobalTheory.CompanionTheory.WS.IsSB (GlobalTheory.CompanionTheory.WS.pF χ Φ) := GlobalTheory.T.partial_fourier_schwartz_bruhat_plane

theorem L_modelNe : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Φ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Φ → ∀ g : GL (Fin 2) F, g.val 1 0 ≠ 0 → ∀ u : Fˣ, GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => Φ (x * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) = mp u 1 * GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.pF χ Φ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) u := GlobalTheory.T.weil_whittaker_lower_left_nonzero

theorem L_modelZero : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Φ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Φ → ∀ g : GL (Fin 2) F, g.val 1 0 = 0 → ∀ u : Fˣ, GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => Φ (x * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) = mp u 1 * GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.pF χ Φ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) u := GlobalTheory.T.weil_whittaker_upper_triangular_case

theorem L_innInt : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Ψ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Ψ → ∀ u : Fˣ, Integrable (fun y : F => Ψ ((u : F), (u : F) * y) * (χ (-y) : ℂ)) (selfDualMeasure χ) := GlobalTheory.T.integrable_twisted_section_line

theorem L_denInt : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ c₁ c₂ : Fˣ →* ℂˣ, IsUnit1 c₁ → IsUnit1 c₂ → ∀ Ψ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Ψ → Integrable (GlobalTheory.CompanionTheory.WS.den χ c₁ c₂ Ψ) (multHaar F) := GlobalTheory.T.integrable_split_whittaker_density

theorem L_comp : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (Ψ : F × F → ℂ), GlobalTheory.CompanionTheory.WS.IsSB Ψ → ∀ g : GL (Fin 2) F, GlobalTheory.CompanionTheory.WS.IsSB (Ψ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) := GlobalTheory.T.schwartz_bruhat_plane_right_translate

theorem L_coset : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (n : ℤ) (x : F × F), GlobalTheory.CompanionTheory.WS.IsSB (GlobalTheory.CompanionTheory.WS.cosetInd n x) := GlobalTheory.T.coset_indicator_schwartz_bruhat

theorem L_decomp : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (Ψ : F × F → ℂ), GlobalTheory.CompanionTheory.WS.IsSB Ψ → ∃ (n : ℤ) (s : Finset (F × F)) (a : F × F → ℂ), Ψ = ∑ x ∈ s, a x • GlobalTheory.CompanionTheory.WS.cosetInd n x := GlobalTheory.T.schwartz_bruhat_plane_coset_span

theorem L_lat : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (n : ℤ) (x : F × F), ∃ h : GL (Fin 2) F, GlobalTheory.CompanionTheory.WS.spanSet n x = GlobalTheory.CompanionTheory.WS.rowAct h ⁻¹' GlobalTheory.CompanionTheory.WS.Ln F 0 := GlobalTheory.T.span_set_eq_lattice_preimage

theorem L_orbit : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (n : ℤ) (x : F × F), x ∉ GlobalTheory.CompanionTheory.WS.Ln F n → ∃ s : Finset Fˣ, s.Nonempty ∧ (∀ t ∈ s, t ∈ unitFiltrationUnits F 0) ∧ (GlobalTheory.CompanionTheory.WS.spanSet n x).indicator (1 : F × F → ℂ) - (GlobalTheory.CompanionTheory.WS.spanSet n (((unifUnit F : Fˣ) : F) • x)).indicator (1 : F × F → ℂ) = ∑ t ∈ s, GlobalTheory.CompanionTheory.WS.cosetInd n ((t : F) • x) := GlobalTheory.T.lattice_annulus_coset_decomposition

theorem L_cosetUnit : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (n : ℤ) (x : F × F) (t : Fˣ), t ∈ unitFiltrationUnits F 0 → GlobalTheory.CompanionTheory.WS.cosetInd n ((t : F) • x) = fun v => GlobalTheory.CompanionTheory.WS.cosetInd n x (((t⁻¹ : Fˣ) : F) • v) := GlobalTheory.T.coset_indicator_unit_scaling

theorem L_latK : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (k : GL (Fin 2) F), k ∈ GLnLocal.integralGL F 2 → GlobalTheory.CompanionTheory.WS.lat0 F ∘ GlobalTheory.CompanionTheory.WS.rowAct k = GlobalTheory.CompanionTheory.WS.lat0 F := GlobalTheory.T.standard_lattice_integral_GL2_invariant

theorem L_left : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (Ψ : F × F → ℂ) (v g : GL (Fin 2) F), v ∈ Iwasawa.unipotent F 2 → GlobalTheory.CompanionTheory.WS.WL χ c₁ c₂ Ψ (v * g) = Whittaker.psiN (Circle.coeHom.compAddChar χ) v * GlobalTheory.CompanionTheory.WS.WL χ c₁ c₂ Ψ g := GlobalTheory.T.split_whittaker_left_unipotent

theorem lattice_inner_integral_value : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ (l : Fin 2 → ℤ) (u : Fˣ), GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.lat0 F ∘ GlobalTheory.CompanionTheory.WS.rowAct (Iwasawa.torusPow F 2 l)) u = if -(l 0) ≤ ord (u : F) ∧ ord (u : F) ≤ -(l 1) then ((Spherical.qF F : ℕ) : ℂ) ^ (l 1) * (mp u 1)⁻¹ else 0 := GlobalTheory.T.inner_integral_lattice_torus_formula

theorem unramified_character_integral_sum : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (μ : Fˣ →* ℂˣ), IsUnramifiedChar μ → ∀ A D : ℤ, ∫ u : Fˣ, (if -A ≤ ord (u : F) ∧ ord (u : F) ≤ -D then ((μ u : ℂˣ) : ℂ) else 0) ∂multHaar F = ∑ j ∈ Finset.Icc D A, ((μ (unifUnit F) : ℂˣ) : ℂ) ^ (-j) := GlobalTheory.T.unramified_character_annulus_integral

theorem schur_polynomial_two_eval : ∀ (x y : ℂˣ) (A D : ℤ), D ≤ A → Spherical.evalAt ![x, y] (Spherical.schur ![A, D]) = ∑ j ∈ Finset.Icc D A, (x : ℂ) ^ (A + D - j) * (y : ℂ) ^ j := GlobalTheory.T.schur_polynomial_GL2_sum

theorem L_mpHalf : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (m : ℤ), mp (Iwasawa.uniformizerUnit F ^ m) (1 / 2) = Spherical.sqrtQ F ^ (-m) := GlobalTheory.T.modulus_half_uniformizer_power

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem rowAct_mul (g h : GL (Fin 2) F) (v : F × F) :
    rowAct (g * h) v = rowAct h (rowAct g v) := by
  simp only [rowAct, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ext <;> simp <;> ring

theorem mp_mul (x y : Fˣ) (s : ℂ) : mp (x * y) s = mp x s * mp y s := by
  simp only [mp, Units.val_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) s

theorem mp_ne_zero (x : Fˣ) (s : ℂ) : mp x s ≠ 0 := by
  have h0 : ((modulus (x : F) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast modulus_ne_zero x.ne_zero
  simp only [mp]
  rw [Complex.cpow_def_of_ne_zero h0]
  exact Complex.exp_ne_zero _

theorem WL_mul (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (Ψ : F × F → ℂ) (g h : GL (Fin 2) F) :
    WL χ c₁ c₂ Ψ (g * h) = ((c₁ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
      mp (Matrix.GeneralLinearGroup.det h) (1 / 2) * WL χ c₁ c₂ (Ψ ∘ rowAct h) g := by
  have hc : Ψ ∘ rowAct (g * h) = (Ψ ∘ rowAct h) ∘ rowAct g := by
    funext v; simp [rowAct_mul]
  simp only [WL, hc, map_mul, Units.val_mul, mp_mul]
  ring

theorem IsSB.add {Ψ₁ Ψ₂ : F × F → ℂ} (h₁ : IsSB Ψ₁) (h₂ : IsSB Ψ₂) : IsSB (Ψ₁ + Ψ₂) :=
  ⟨h₁.1.add h₂.1, h₁.2.add h₂.2⟩

theorem IsSB.smul {Ψ : F × F → ℂ} (a : ℂ) (h : IsSB Ψ) : IsSB (a • Ψ) :=
  ⟨h.1.comp (fun z : ℂ => a • z), h.2.comp_left (g := fun z : ℂ => a • z) (smul_zero a)⟩

theorem isSB_zero : IsSB (0 : F × F → ℂ) := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

theorem isSB_sum {ι : Type*} (s : Finset ι) (f : ι → F × F → ℂ) (h : ∀ i ∈ s, IsSB (f i)) :
    IsSB (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSB_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem lin_add {χ : AddChar F Circle} (hχ : IsStd χ) {c₁ c₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    {Ψ₁ Ψ₂ : F × F → ℂ} (hΨ₁ : IsSB Ψ₁) (hΨ₂ : IsSB Ψ₂) :
    lin χ c₁ c₂ (Ψ₁ + Ψ₂) = lin χ c₁ c₂ Ψ₁ + lin χ c₁ c₂ Ψ₂ := by
  have hinn : ∀ u, inn χ (Ψ₁ + Ψ₂) u = inn χ Ψ₁ u + inn χ Ψ₂ u := by
    intro u
    simp only [inn, Pi.add_apply, add_mul]
    exact integral_add (L_innInt F χ hχ Ψ₁ hΨ₁ u) (L_innInt F χ hχ Ψ₂ hΨ₂ u)
  have hden : den χ c₁ c₂ (Ψ₁ + Ψ₂) = fun u => den χ c₁ c₂ Ψ₁ u + den χ c₁ c₂ Ψ₂ u := by
    funext u
    simp only [den, hinn]
    ring
  simp only [lin, hden]
  exact integral_add (L_denInt F χ hχ c₁ c₂ h₁ h₂ Ψ₁ hΨ₁) (L_denInt F χ hχ c₁ c₂ h₁ h₂ Ψ₂ hΨ₂)

theorem lin_smul (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (a : ℂ) (Ψ : F × F → ℂ) :
    lin χ c₁ c₂ (a • Ψ) = a * lin χ c₁ c₂ Ψ := by
  have hinn : ∀ u, inn χ (a • Ψ) u = a * inn χ Ψ u := by
    intro u
    simp only [inn, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul a _
  have hden : den χ c₁ c₂ (a • Ψ) = fun u => a * den χ c₁ c₂ Ψ u := by
    funext u
    simp only [den, hinn]
    ring
  simp only [lin, hden]
  exact integral_const_mul a _

theorem mp_unit_one {t : Fˣ} (ht : t ∈ unitFiltrationUnits F 0) (s : ℂ) : mp t s = 1 := by
  have h := mem_unitFiltrationUnits_zero_iff_ord.1 ht
  simp only [mp, modulus_eq_one_iff.2 ⟨t.ne_zero, h⟩]
  simp

theorem lin_unit (χ : AddChar F Circle) {c₁ c₂ : Fˣ →* ℂˣ} (u₁ : IsUnramifiedChar c₁) (u₂ : IsUnramifiedChar c₂)
    (Ψ : F × F → ℂ) {t : Fˣ} (ht : t ∈ unitFiltrationUnits F 0) :
    lin χ c₁ c₂ (fun v => Ψ ((t : F) • v)) = lin χ c₁ c₂ Ψ := by
  have hinn : ∀ u, inn χ (fun v => Ψ ((t : F) • v)) u = inn χ Ψ (t * u) := by
    intro u
    simp only [inn, Prod.smul_mk, smul_eq_mul, Units.val_mul, mul_assoc]
  have e₁ : c₁ t = 1 := MonoidHom.mem_ker.1 (u₁ ht)
  have e₂ : c₂ t = 1 := MonoidHom.mem_ker.1 (u₂ ht)
  have hden : den χ c₁ c₂ (fun v => Ψ ((t : F) • v)) = fun u => den χ c₁ c₂ Ψ (t * u) := by
    funext u
    simp only [den, hinn, map_mul, Units.val_mul, mul_inv, mp_mul, e₁, e₂, mp_unit_one ht]
    simp
  simp only [lin, hden]
  exact integral_mul_left_eq_self (μ := multHaar F) (den χ c₁ c₂ Ψ) t

theorem WL_add {χ : AddChar F Circle} (hχ : IsStd χ) {c₁ c₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    {Ψ₁ Ψ₂ : F × F → ℂ} (hΨ₁ : IsSB Ψ₁) (hΨ₂ : IsSB Ψ₂) :
    WL χ c₁ c₂ (Ψ₁ + Ψ₂) = WL χ c₁ c₂ Ψ₁ + WL χ c₁ c₂ Ψ₂ := by
  funext g
  have hc : (Ψ₁ + Ψ₂) ∘ rowAct g = Ψ₁ ∘ rowAct g + Ψ₂ ∘ rowAct g := rfl
  simp only [WL, Pi.add_apply, hc,
    lin_add hχ h₁ h₂ (L_comp F Ψ₁ hΨ₁ g) (L_comp F Ψ₂ hΨ₂ g)]
  ring

theorem WL_smul (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (a : ℂ) (Ψ : F × F → ℂ) :
    WL χ c₁ c₂ (a • Ψ) = a • WL χ c₁ c₂ Ψ := by
  funext g
  have hc : (a • Ψ) ∘ rowAct g = a • (Ψ ∘ rowAct g) := rfl
  simp only [WL, Pi.smul_apply, smul_eq_mul, hc, lin_smul]
  ring

theorem WL_sub {χ : AddChar F Circle} (hχ : IsStd χ) {c₁ c₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    {Ψ₁ Ψ₂ : F × F → ℂ} (hΨ₁ : IsSB Ψ₁) (hΨ₂ : IsSB Ψ₂) :
    WL χ c₁ c₂ (Ψ₁ - Ψ₂) = WL χ c₁ c₂ Ψ₁ - WL χ c₁ c₂ Ψ₂ := by
  have h := WL_add hχ h₁ h₂ hΨ₁ (hΨ₂.smul (-1))
  rw [WL_smul] at h
  have e : Ψ₁ - Ψ₂ = Ψ₁ + (-1 : ℂ) • Ψ₂ := by simp [sub_eq_add_neg]
  rw [e, h]
  simp [sub_eq_add_neg]

theorem WL_sum {χ : AddChar F Circle} (hχ : IsStd χ) {c₁ c₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    {ι : Type*} (s : Finset ι) (f : ι → F × F → ℂ) (h : ∀ i ∈ s, IsSB (f i)) :
    WL χ c₁ c₂ (∑ i ∈ s, f i) = ∑ i ∈ s, WL χ c₁ c₂ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := WL_smul χ c₁ c₂ 0 (0 : F × F → ℂ)
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      WL_add hχ h₁ h₂ (h a (Finset.mem_insert_self a s))
        (isSB_sum s f fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem rowAct_smul (g : GL (Fin 2) F) (t : F) (v : F × F) : rowAct g (t • v) = t • rowAct g v := by
  simp only [rowAct, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.smul_mk]
  ext <;> simp <;> ring

theorem WL_unit (χ : AddChar F Circle) {c₁ c₂ : Fˣ →* ℂˣ} (u₁ : IsUnramifiedChar c₁) (u₂ : IsUnramifiedChar c₂)
    (Ψ : F × F → ℂ) {t : Fˣ} (ht : t ∈ unitFiltrationUnits F 0) :
    WL χ c₁ c₂ (fun v => Ψ ((t : F) • v)) = WL χ c₁ c₂ Ψ := by
  funext g
  have hc : (fun v => Ψ ((t : F) • v)) ∘ rowAct g = fun v => (Ψ ∘ rowAct g) ((t : F) • v) := by
    funext v
    simp [rowAct_smul]
  simp only [WL, hc, lin_unit χ u₁ u₂ _ ht]

abbrev Sp (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) : Submodule ℂ (GL (Fin 2) F → ℂ) :=
  Submodule.span ℂ {f : GL (Fin 2) F → ℂ | ∃ h : GL (Fin 2) F, f = fun g =>
    Spherical.sphericalWhittaker (Circle.coeHom.compAddChar χ) ![c₁ (unifUnit F), c₂ (unifUnit F)] (g * h)}

theorem L_detK (k : GL (Fin 2) F) (hk : k ∈ GLnLocal.integralGL F 2) :
    Matrix.GeneralLinearGroup.det k ∈ unitFiltrationUnits F 0 :=
  mem_unitFiltrationUnits_zero_iff_ord.2 (GroundTheory.Automorphic.GodementSectionLocal.ord_det_eq_zero hk)

theorem char_uniformizer {c : Fˣ →* ℂˣ} (u : IsUnramifiedChar c) :
    c (Iwasawa.uniformizerUnit F) = c (unifUnit F) := by
  have h : Iwasawa.uniformizerUnit F * (unifUnit F)⁻¹ ∈ unitFiltrationUnits F 0 := by
    rw [mem_unitFiltrationUnits_zero_iff_ord, ord_units_mul, ord_units_inv, ord_unifUnit,
      Iwasawa.coe_uniformizerUnit, ord_uniformizer (GLnLocal.irreducible_uniformizer F)]
    norm_num
  have := MonoidHom.mem_ker.1 (u h)
  rw [map_mul, map_inv] at this
  exact mul_inv_eq_one.1 this

theorem det_torusPow (l : Fin 2 → ℤ) :
    Matrix.GeneralLinearGroup.det (Iwasawa.torusPow F 2 l) = Iwasawa.uniformizerUnit F ^ (l 0 + l 1) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Iwasawa.coe_torusPow, Matrix.det_diagonal,
    Fin.prod_univ_two, Units.val_zpow_eq_zpow_val, Iwasawa.coe_uniformizerUnit,
    zpow_add₀ (by exact_mod_cast (GLnLocal.irreducible_uniformizer F).ne_zero)]

theorem L_val (χ : AddChar F Circle) (hχ : IsStd χ) (c₁ c₂ : Fˣ →* ℂˣ) (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    (u₁ : IsUnramifiedChar c₁) (u₂ : IsUnramifiedChar c₂) (l : Fin 2 → ℤ) :
    WL χ c₁ c₂ (lat0 F) (Iwasawa.torusPow F 2 l) = if Antitone l then Spherical.halfModulus F l *
      Spherical.evalAt ![c₁ (unifUnit F), c₂ (unifUnit F)] (Spherical.schur l) else 0 := by
  obtain ⟨A, D, rfl⟩ : ∃ A D : ℤ, l = ![A, D] := ⟨l 0, l 1, by
    funext i; fin_cases i <;> rfl⟩
  have hanti : Antitone (![A, D] : Fin 2 → ℤ) ↔ D ≤ A := by
    constructor
    · intro h
      simpa using h (show (0 : Fin 2) ≤ 1 by decide)
    · intro h i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  have hrho : Spherical.rhoPair (![A, D] : Fin 2 → ℤ) = A - D := by
    simp [Spherical.rhoPair, Fin.sum_univ_two]
    ring
  set x := c₁ (unifUnit F) with hx
  set y := c₂ (unifUnit F) with hy
  have hden : ∀ u, den χ c₁ c₂ (lat0 F ∘ rowAct (Iwasawa.torusPow F 2 ![A, D])) u =
      ((Spherical.qF F : ℕ) : ℂ) ^ D *
        (if -A ≤ ord (u : F) ∧ ord (u : F) ≤ -D then (((c₁ * c₂⁻¹) u : ℂˣ) : ℂ) else 0) := by
    intro u
    have hm := mp_ne_zero u 1
    simp only [den, lattice_inner_integral_value F χ hχ ![A, D] u, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    split_ifs
    · simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
      field_simp
    · simp
  have hlin : lin χ c₁ c₂ (lat0 F ∘ rowAct (Iwasawa.torusPow F 2 ![A, D])) =
      ((Spherical.qF F : ℕ) : ℂ) ^ D * ∑ j ∈ Finset.Icc D A, (((x * y⁻¹ : ℂˣ)) : ℂ) ^ (-j) := by
    have hμ : IsUnramifiedChar (c₁ * c₂⁻¹) := fun t ht => by
      have e₁ : c₁ t = 1 := MonoidHom.mem_ker.1 (u₁ ht)
      have e₂ : c₂ t = 1 := MonoidHom.mem_ker.1 (u₂ ht)
      simp [MonoidHom.mem_ker, e₁, e₂]
    have := unramified_character_integral_sum F (c₁ * c₂⁻¹) hμ A D
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply] at this
    simp only [lin, hden]
    rw [integral_const_mul]
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [this]
  simp only [WL, hlin, det_torusPow, L_mpHalf F, map_zpow, char_uniformizer u₁,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  by_cases hDA : D ≤ A
  · rw [if_pos (hanti.2 hDA), Spherical.halfModulus_eq, hrho, schur_polynomial_two_eval x y A D hDA, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hs : Spherical.sqrtQ F ≠ 0 := Spherical.sqrtQ_ne_zero
    have hq : ((Spherical.qF F : ℕ) : ℂ) = Spherical.sqrtQ F ^ (2 : ℤ) := by
      rw [zpow_ofNat, Spherical.sqrtQ_sq]
    have hx0 : (x : ℂ) ≠ 0 := x.ne_zero
    have hy0 : (y : ℂ) ≠ 0 := y.ne_zero
    rw [hq, ← _root_.zpow_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
      mul_zpow, _root_.inv_zpow', neg_neg]
    have e₁ : (x : ℂ) ^ (A + D - j) = (x : ℂ) ^ (A + D) * (x : ℂ) ^ (-j) := by
      rw [← zpow_add₀ hx0]
      congr 1
    have e₂ : Spherical.sqrtQ F ^ (-(A - D)) = Spherical.sqrtQ F ^ (-(A + D)) * Spherical.sqrtQ F ^ (2 * D) := by
      rw [← zpow_add₀ hs]
      congr 1
      ring
    rw [e₁, e₂]
    ring
  · rw [if_neg (fun h => hDA (hanti.1 h)), Finset.Icc_eq_empty hDA]
    simp

theorem psi_std {χ : AddChar F Circle} (hχ : IsStd χ) :
    ∀ x ∈ 𝒪[F], (Circle.coeHom.compAddChar χ) x = 1 := by
  intro x hx
  obtain ⟨hc, h1, h0⟩ := hχ
  have ht := isTrivialOn_addCharConductor hc h1
  rw [h0] at ht
  have := ht x (mem_valBall_zero_iff.2 hx)
  show ((χ x : Circle) : ℂ) = 1
  rw [this, Circle.coe_one]

theorem lattice_whittaker_eq_spherical {χ : AddChar F Circle} (hχ : IsStd χ) {c₁ c₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    (u₁ : IsUnramifiedChar c₁) (u₂ : IsUnramifiedChar c₂) (g : GL (Fin 2) F) :
    WL χ c₁ c₂ (lat0 F) g =
      Spherical.sphericalWhittaker (Circle.coeHom.compAddChar χ) ![c₁ (unifUnit F), c₂ (unifUnit F)] g := by
  have hu := Spherical.iwasawaUnip_mem g
  have hk := Spherical.iwasawaInt_mem g
  have hg := Spherical.eq_iwasawa g
  set u := Spherical.iwasawaUnip g
  set k := Spherical.iwasawaInt g
  set l := Iwasawa.iwasawaExponent F 2 g
  have hd := L_detK k hk
  rw [hg, WL_mul, L_latK F k hk, mul_assoc u, L_left F χ c₁ c₂ _ u _ hu, L_val χ hχ c₁ c₂ h₁ h₂ u₁ u₂ l,
    ← mul_assoc u, Spherical.sphericalWhittaker_apply (psi_std hχ) _ hu hk l,
    mp_unit_one hd, MonoidHom.mem_ker.1 (u₁ hd)]
  split_ifs <;> simp <;> ring

theorem WL_lat_mem {χ : AddChar F Circle} (hχ : IsStd χ) {c₁ c₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    (u₁ : IsUnramifiedChar c₁) (u₂ : IsUnramifiedChar c₂) (h : GL (Fin 2) F) :
    WL χ c₁ c₂ (lat0 F ∘ rowAct h) ∈ Sp χ c₁ c₂ := by
  set κ : ℂ := ((c₁ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * mp (Matrix.GeneralLinearGroup.det h) (1 / 2)
  have hκ : κ ≠ 0 := mul_ne_zero (Units.ne_zero _) (mp_ne_zero _ _)
  have e : WL χ c₁ c₂ (lat0 F ∘ rowAct h) = κ⁻¹ • fun g =>
      Spherical.sphericalWhittaker (Circle.coeHom.compAddChar χ) ![c₁ (unifUnit F), c₂ (unifUnit F)] (g * h) := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← lattice_whittaker_eq_spherical hχ h₁ h₂ u₁ u₂, WL_mul]
    show _ = κ⁻¹ * (κ * _)
    rw [inv_mul_cancel_left₀ hκ]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)

theorem ind_spanSet (n : ℤ) (x : F × F) : ∃ h : GL (Fin 2) F,
    (spanSet n x).indicator (1 : F × F → ℂ) = lat0 F ∘ rowAct h := by
  obtain ⟨h, e⟩ := L_lat F n x
  refine ⟨h, ?_⟩
  funext v
  have hv : v ∈ spanSet n x ↔ rowAct h v ∈ Ln F 0 := by rw [e]; rfl
  by_cases hw : rowAct h v ∈ Ln F 0
  · rw [Function.comp, lat0, Set.indicator_of_mem (hv.2 hw), Set.indicator_of_mem hw]
    rfl
  · rw [Function.comp, lat0, Set.indicator_of_notMem (mt hv.1 hw), Set.indicator_of_notMem hw]

theorem isSB_span (n : ℤ) (x : F × F) : IsSB ((spanSet n x).indicator (1 : F × F → ℂ)) := by
  obtain ⟨h, e⟩ := ind_spanSet n x
  rw [e]
  have := L_coset F 0 (0 : F × F)
  have e0 : cosetInd 0 (0 : F × F) = lat0 F := by
    simp [cosetInd, lat0]
  exact L_comp F _ (e0 ▸ this) h

theorem WL_span_mem {χ : AddChar F Circle} (hχ : IsStd χ) {c₁ c₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    (u₁ : IsUnramifiedChar c₁) (u₂ : IsUnramifiedChar c₂) (n : ℤ) (x : F × F) :
    WL χ c₁ c₂ ((spanSet n x).indicator (1 : F × F → ℂ)) ∈ Sp χ c₁ c₂ := by
  obtain ⟨h, e⟩ := ind_spanSet n x
  rw [e]
  exact WL_lat_mem hχ h₁ h₂ u₁ u₂ h

theorem Ln_sub {n : ℤ} {a b : F × F} (ha : a ∈ Ln F n) (hb : b ∈ Ln F n) : a - b ∈ Ln F n :=
  ⟨sub_mem ha.1 hb.1, sub_mem ha.2 hb.2⟩

theorem WL_coset_mem {χ : AddChar F Circle} (hχ : IsStd χ) {c₁ c₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    (u₁ : IsUnramifiedChar c₁) (u₂ : IsUnramifiedChar c₂) (n : ℤ) (x : F × F) :
    WL χ c₁ c₂ (cosetInd n x) ∈ Sp χ c₁ c₂ := by
  by_cases hx : x ∈ Ln F n
  · have e : cosetInd n x = (spanSet n 0).indicator (1 : F × F → ℂ) := by
      have : {v | v - x ∈ Ln F n} = spanSet n (0 : F × F) := by
        ext v
        constructor
        · intro hv
          refine ⟨0, zero_mem _, ?_⟩
          have := Ln_sub hv (Ln_sub (show (0 : F × F) ∈ Ln F n from ⟨zero_mem _, zero_mem _⟩) hx)
          simpa using this
        · rintro ⟨a, -, hv⟩
          simpa using Ln_sub (by simpa using hv) hx
      simp only [cosetInd, this]
    rw [e]
    exact WL_span_mem hχ h₁ h₂ u₁ u₂ n 0
  · obtain ⟨s, hs, ht, e⟩ := L_orbit F n x hx
    have hW : ∀ t ∈ s, WL χ c₁ c₂ (cosetInd n ((t : F) • x)) = WL χ c₁ c₂ (cosetInd n x) := by
      intro t hts
      rw [L_cosetUnit F n x t (ht t hts)]
      exact WL_unit χ u₁ u₂ _ (inv_mem (ht t hts))
    have hsum : ((s.card : ℂ)) • WL χ c₁ c₂ (cosetInd n x) =
        WL χ c₁ c₂ ((spanSet n x).indicator (1 : F × F → ℂ)) -
          WL χ c₁ c₂ ((spanSet n (((unifUnit F : Fˣ) : F) • x)).indicator (1 : F × F → ℂ)) := by
      rw [← WL_sub hχ h₁ h₂ (isSB_span _ _) (isSB_span _ _), e,
        WL_sum hχ h₁ h₂ s _ fun t _ => L_coset F n _, Finset.sum_congr rfl hW,
        Finset.sum_const, Nat.cast_smul_eq_nsmul]
    have hc : (s.card : ℂ) ≠ 0 := by
      exact_mod_cast hs.card_pos.ne'
    have : WL χ c₁ c₂ (cosetInd n x) = (s.card : ℂ)⁻¹ • ((s.card : ℂ) • WL χ c₁ c₂ (cosetInd n x)) := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [this, hsum]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (WL_span_mem hχ h₁ h₂ u₁ u₂ _ _)
      (WL_span_mem hχ h₁ h₂ u₁ u₂ _ _))

theorem WL_mem {χ : AddChar F Circle} (hχ : IsStd χ) {c₁ c₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    (u₁ : IsUnramifiedChar c₁) (u₂ : IsUnramifiedChar c₂) {Ψ : F × F → ℂ} (hΨ : IsSB Ψ) :
    WL χ c₁ c₂ Ψ ∈ Sp χ c₁ c₂ := by
  obtain ⟨n, s, a, rfl⟩ := L_decomp F Ψ hΨ
  rw [WL_sum hχ h₁ h₂ s _ fun x _ => (L_coset F n x).smul (a x)]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [WL_smul]
  exact Submodule.smul_mem _ _ (WL_coset_mem hχ h₁ h₂ u₁ u₂ n x)

theorem WcS_eq_WL {χ : AddChar F Circle} (hχ : IsStd χ) (c₁ c₂ : Fˣ →* ℂˣ) {Φ : F × F → ℂ} (hΦ : IsSB Φ) :
    GL2LocalData.WcS χ c₁ c₂ Φ = WL χ c₁ c₂ (pF χ Φ) := by
  funext g
  have hdet : ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = (g.val).det := rfl
  have key : ∀ u : Fˣ, GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1)
      (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => Φ (x * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) =
      mp u 1 * inn χ (pF χ Φ ∘ rowAct g) u := by
    intro u
    by_cases hc : g.val 1 0 = 0
    · exact L_modelZero F χ hχ Φ hΦ g hc u
    · exact L_modelNe F χ hχ Φ hΦ g hc u
  simp only [GL2LocalData.WcS, WL, lin, den, key]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  ring

theorem WcS_mem_span : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ c₁ c₂ : Fˣ →* ℂˣ, IsUnit1 c₁ → IsUnit1 c₂ → IsUnramifiedChar c₁ → IsUnramifiedChar c₂ → ∀ Φ : F × F → ℂ, IsLocallyConstant Φ → HasCompactSupport Φ → GL2LocalData.WcS χ c₁ c₂ Φ ∈ Submodule.span ℂ {f : GL (Fin 2) F → ℂ | ∃ h : GL (Fin 2) F, f = fun g => Spherical.sphericalWhittaker (Circle.coeHom.compAddChar χ) ![c₁ (unifUnit F), c₂ (unifUnit F)] (g * h)} := by
  intro F _ _ _ _ _ _ χ hχ c₁ c₂ h₁ h₂ u₁ u₂ Φ hl hc
  have hΦ : IsSB Φ := ⟨hl, hc⟩
  rw [WcS_eq_WL hχ c₁ c₂ hΦ]
  exact WL_mem hχ h₁ h₂ u₁ u₂ (L_pF F χ hχ Φ hΦ)

end GlobalTheory.CompanionTheory.WS
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_whittaker_mem_spherical_span : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ c₁ c₂ : Fˣ →* ℂˣ, IsUnit1 c₁ → IsUnit1 c₂ → IsUnramifiedChar c₁ → IsUnramifiedChar c₂ → ∀ Φ : F × F → ℂ, IsLocallyConstant Φ → HasCompactSupport Φ → GL2LocalData.WcS χ c₁ c₂ Φ ∈ Submodule.span ℂ {f : GL (Fin 2) F → ℂ | ∃ h : GL (Fin 2) F, f = fun g => Spherical.sphericalWhittaker (Circle.coeHom.compAddChar χ) ![c₁ (unifUnit F), c₂ (unifUnit F)] (g * h)} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WS.WcS_mem_span
end
