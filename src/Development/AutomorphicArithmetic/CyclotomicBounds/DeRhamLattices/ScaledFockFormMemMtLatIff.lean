import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteComplexFormsEqTwistComplexFormsFockModel
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsRationalStructureLowestFormSpace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ScaledFockFormCoefficientsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelTwistCharacterMemCoefficientIntegers
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LevEnvLevelSubgroupLeLevJAndCharacterEq

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.UpperTheory.KN.mem_lNab_iff_coefficients_in_nabla_lattice :
    ∀ (D : D7) (X : RealSide D) (j : Fin D.R.m) (t : X.T),
      ∀ gramR c0R c0L, Bridge.FamTie X.R.B X.R.pl (X.R.Sb : Set (Pl D.host.E)) X.R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L →
      ∀ x, x ∈ lNab D X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t ↔
        ∀ a, ∃ F : VV D.what₂.LL (lamV D j), F ∈ nabAtr (labLL D) (lamV D j) (Bridge.hLat (Vc D j) ((X.R.B.L j t).pres.y a)) ∧ (X.R.B.jL j t (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t x)) ((X.R.B.L j t).pres.y a) = c0L j F := by
  intro D X j t gramR c0R c0L hT x
  obtain ⟨e, -, he, -, hN, -⟩ := hT.coefL j t
  have h1 : x ∈ lNab D X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t ↔ ∀ a, (show (X.A3.A.MtCSD j t).Forms from GlobalTheory.Mem.R3.liftForm X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t x).1 a ∈ (X.A3.A.MtCSD j t).Nab a :=
    GlobalTheory.Mem.LiftForms.mem_lvlNab _ _ _ _ x
  refine h1.trans (forall_congr' fun a => ?_)
  generalize GlobalTheory.Mem.R3.liftForm X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j t x = f
  have h2 : (X.R.B.jL j t f) ((X.R.B.L j t).pres.y a) = (X.R.B.L j t).pres.coef ((show (X.A3.A.MtCSD j t).Forms from f).1 a) :=
    GlobalTheory.PresBasic.ext_y (X.R.B.L j t).pres f a
  have h3 := hN a
  constructor
  · intro h
    refine ⟨e _, ?_, h2.trans (he _)⟩
    exact h3.le ⟨_, h, rfl⟩
  · rintro ⟨F, hF, hv⟩
    obtain ⟨v, hv1, hv2⟩ := h3.ge hF
    have h4 : (X.R.B.L j t).pres.coef ((show (X.A3.A.MtCSD j t).Forms from f).1 a) = (X.R.B.L j t).pres.coef v := by
      refine h2.symm.trans (hv.trans ?_)
      refine Eq.trans ?_ (he v).symm
      exact congrArg (c0L j) hv2.symm
    have h5 : (show (X.A3.A.MtCSD j t).Forms from f).1 a - v = 0 :=
      Bridge.ClassPres.coef_inj (X.R.B.L j t).pres (by rw [map_sub, h4, sub_self])
    rw [sub_eq_zero.1 h5]
    exact hv1
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.UpperTheory.KN.mem_mtLat_of_coefficients_mem_coefLat :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ F ∈ (baseOf Z c w j).formsC (twVia Z.ρ ι), (∀ a, F ((X.R.B.L j (Y.tupT (D.what₂.muTw w))).pres.y a) ∈ (baseOf Z c w j).coefLat D.what₂.embLL (labLL D) (intLL D) ((X.R.B.L j (Y.tupT (D.what₂.muTw w))).pres.y a)) →
      F ∈ (baseOf Z c w j).mtLat D.what₂.embLL (labLL D) (intLL D) (twVia Z.ρ ι) := by
  intro D X X0 Y S YS Z c w j H ι hι F hF hy
  have hB := Z.good.base (c.twI w) j (c.sd w)
  have hc : IsCoefRing D.what₂.embLL (labLL D) (intLL D) :=
    ⟨fun τ => FWT.embV_spec (RingHom.id _) D.what₂.embLL (RingHom.comp_id _) τ, fun a => ⟨a, rfl⟩⟩
  refine (Base.mem_mtLat _ _ _ _).2 ⟨hF, fun h => ?_⟩
  obtain ⟨a, γ, k, e⟩ := ((X.R.B.L j (Y.tupT (D.what₂.muTw w))).pres.reps h).exists
  obtain ⟨hk, -⟩ := UpperTheory.KN.levEnv_level_subgroup_le_levJ_and_character_eq D X X0 Y S YS Z c w j H ι hι k
  have h1 := ((Base.mem_formsC _).1 hF).2 γ ((X.R.B.L j (Y.tupT (D.what₂.muTw w))).pres.y a) ⟨k, hk⟩
  have h2 := Base.act_mem_coefLat hB.frame hc γ _ k (Base.mem_St_of_mem_levJ hk) (hy a)
  have h3 := GlobalTheory.T.level_twist_character_mem_coefficientIntegers D X X0 Y S YS Z c w j H ι hι ⟨k, hk⟩
  have h4 := Submodule.smul_mem _ (⟨_, h3⟩ : intLL D) h2
  subst e
  exact h1 ▸ h4
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.UpperTheory.KN.scaled_fock_form_mem_mtLat_iff :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ), IsLow X j u →
      ∀ κ : ℂ, κ ≠ 0 → IsScale X.R X.geo.v₀ (baseOf Z c w j) κ →
      ∀ m : D.what₂.MtL (D.what₂.muTw w) (j.1 + 1), κ⁻¹ • fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) m) ∈ (baseOf Z c w j).mtLat D.what₂.embLL (labLL D) (intLL D) (twVia Z.ρ ι) ↔
        ∃ a : D.what₂.Mt (D.what₂.muTw w) (j.1 + 1) → 𝓞 D.what₂.LL, D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) m = ∑ v ∈ (D.what₂.MtLat (D.what₂.muTw w) (j.1 + 1)).gen, D.what₂.embLL (a v : D.what₂.LL) • v := by
  intro D X X0 Y S YS Z c w j H ι hι u hu κ hκ hs m
  obtain ⟨gramR, c0R, c0L, hft, u', hu', hF⟩ := hs
  obtain rfl : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  obtain ⟨e, he, hO, -⟩ := UpperTheory.KN.exists_rational_structure_lowest_form_space D X X0 Y (D.what₂.muTw w) (used_of_tw H.tw) j
  obtain ⟨x, rfl⟩ := e.surjective m
  have hN := UpperTheory.KN.mem_lNab_iff_coefficients_in_nabla_lattice D X j (Y.tupT (D.what₂.muTw w)) gramR c0R c0L hft x
  have hC := UpperTheory.KN.scaled_fock_form_coefficients_integral D X X0 Y S YS Z c w j H ι hι u' hu gramR c0R c0L hft κ hκ hF
  have hI := (UpperTheory.KN.ioP_tprod_injective_and_range_eq_valSpace D X X0 Y S YS Z c w j H ι hι u' hu).1
  have hv : ∀ h, (κ⁻¹ • fockOf Y (used_of_tw H.tw) j u' (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) (e x))) h =
      κ⁻¹ • X.R.ioP j (PiTensorProduct.tprod ℂ u') ((X.R.B.jL j (Y.tupT (D.what₂.muTw w))
        (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j (Y.tupT (D.what₂.muTw w)) x)) h) := fun h => by
    rw [Pi.smul_apply, fockOf_apply, he x]
  refine Iff.trans ?_ (hN.symm.trans (hO.2 x))
  constructor
  · intro hm a
    obtain ⟨F, hF1, hF2⟩ := (hC _ _).1 (((Base.mem_mtLat _ _ _ _).1 hm).2 ((X.R.B.L j (Y.tupT (D.what₂.muTw w))).pres.y a))
    rw [hv] at hF2
    exact ⟨F, hF1, hI (smul_right_injective _ (inv_ne_zero hκ) hF2)⟩
  · intro hm
    refine UpperTheory.KN.mem_mtLat_of_coefficients_mem_coefLat D X X0 Y S YS Z c w j H ι hι _ (Submodule.smul_mem _ _ ?_) fun a => ?_
    · rw [← (GlobalTheory.T.definiteComplexForms_eq_twistComplexForms_fockModel D X X0 Y S YS Z c w j H ι hι u' hu).2]
      exact LinearMap.mem_range_self _ _
    · obtain ⟨F, hF1, hF2⟩ := hm a
      exact (hC _ _).2 ⟨F, hF1, by rw [hv, hF2]⟩
end
