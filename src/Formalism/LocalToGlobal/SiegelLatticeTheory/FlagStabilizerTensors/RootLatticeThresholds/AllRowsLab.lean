import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsEtAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RhoSurjPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsTr
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoExt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.AutoReg
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTEquiv
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.IndefiniteReal.RankZerothComponentEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOnto
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsKpp
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsWt
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZGlueA
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppFwdPf

section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict Formalism.MainNotions.LeviCoordinates
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.SG.EvalTOntoPsi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.EvalTOntoExt

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {t : GA D (D.sp.Y 0)}
  {μ : Measure (GA D (D.sp.Y 0))} {c : ℝ}

section Pull

variable (hιs : Measurable ι.symm) (hι : Measurable ι) (hc : 0 < c)
  (hmap : Measure.map ι.symm (X.B.I.muA X.B.μf) = ENNReal.ofReal c • μ) (hH : μ.IsHaarMeasure)
include hιs hι hc hmap hH

end Pull

section P

open Classical

variable {S : D.what₂.Tau → SPar} {M : DSModel (D.sp.Y 0) S} (U : ∀ v, X.B.H v ≃ₗᵢ⋆[ℂ] M.H (X.pl v))

def P (v : M.Vec) : X.B.Hs := X.B.tens fun v' => (U v').symm (v (X.pl v'))

end P

section Psi

open Classical

def psi {S : D.what₂.Tau → SPar} {M : DSModel (D.sp.Y 0) S} (U : ∀ v, X.B.H v ≃ₗᵢ⋆[ℂ] M.H (X.pl v))
    (Φ : X.B.Hs →L[ℂ] L2X X) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (v : M.Vec)
    (h : GA D (D.sp.Y 0)) : ℂ :=
  star (ext0 X (Φ (P U v)) (ι (h * t⁻¹)))

variable {S : D.what₂.Tau → SPar} {M : DSModel (D.sp.Y 0) S} {U : ∀ v, X.B.H v ≃ₗᵢ⋆[ℂ] M.H (X.pl v)}
  {Φ : X.B.Hs →L[ℂ] L2X X}

variable (hιs : Measurable ι.symm) (hι : Measurable ι) (hc : 0 < c)
  (hmap : Measure.map ι.symm (X.B.I.muA X.B.μf) = ENNReal.ofReal c • μ) (hH : μ.IsHaarMeasure)
include hιs hι hc hmap hH

end Psi

end Formalism.L2.SG.EvalTOntoPsi

end
end

section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict Formalism.MainNotions.LeviCoordinates Formalism.MainNotions.S
open Formalism.MainNotions.StandardLattice Matrix
open scoped InnerProductSpace ComplexConjugate ENNReal TensorProduct

namespace Formalism.L2.SG.EvalTOntoEqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.EvalTOntoExt Formalism.L2.SG.EvalTOntoPsi Classical

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {t : GA D (D.sp.Y 0)}
  {μ : Measure (GA D (D.sp.Y 0))} {c : ℝ} {S : D.what₂.Tau → SPar} {M : DSModel (D.sp.Y 0) S}
  {U : ∀ v, X.B.H v ≃ₗᵢ⋆[ℂ] M.H (X.pl v)} {Φ : X.B.Hs →L[ℂ] L2X X}

def single (v' : NumberField.InfinitePlace X.B.I.F) (m : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)
    (hm : m ∈ UJset (X.B.I.ε v')) : X.B.I.Ginf :=
  Function.update 1 v' ⟨(Formalism.IndefR.SchurOrthogonalityAlt.isUnit_of_mem_UJ (X.B.I.ε v') hm).unit, hm⟩

end Formalism.L2.SG.EvalTOntoEqv

end
end

section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.L2.Theta Formalism.L2.SG.RowDict
open scoped InnerProductSpace

namespace Formalism.L2.SG.EvalTOntoPhi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem regAlg : (∀ a b, X.B.R (a * b) = (X.B.R a).comp (X.B.R b)) ∧ X.B.R 1 = 1 ∧ ∀ a F, ‖X.B.R a F‖ = ‖F‖ := by
  have := X.B.sf
  have := X.B.haar
  exact Formalism.L2.SG.Pf.reg_alg Formalism.L2.SG.Closed.UnimodGf_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec

theorem inner_reg (a : X.B.I.GA) (x z : L2X X) : ⟪x, X.B.R a z⟫_ℂ = ⟪X.B.R a⁻¹ x, z⟫_ℂ := by
  obtain ⟨hmul, hone, hiso⟩ := regAlg X
  have := Formalism.L2.SG.Pf.inner_orbit X.B.R hmul hiso a⁻¹ 1 x z
  rw [hone, ContinuousLinearMap.one_apply, inv_inv, mul_one] at this
  exact this.symm

variable {X}

end Formalism.L2.SG.EvalTOntoPhi

end
end

section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.AllRowsRMul

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

abbrev phi (x y : X.B.I.L2 X.B.μf X.B.fund) (c : X.B.I.Gf) : ℂ := ⟪x, X.B.R (1, c) y⟫_ℂ

theorem R_facts :
    (∀ a b : X.B.I.GA, X.B.R (a * b) = (X.B.R a).comp (X.B.R b)) ∧ (∀ a F, ‖X.B.R a F‖ = ‖F‖) ∧
      (∀ x y : X.B.I.L2 X.B.μf X.B.fund, StronglyMeasurable (phi X x y)) := by
  have : X.B.μf.IsHaarMeasure := X.B.haar
  have hU := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have hFR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  have := hFR.2.1
  have := hFR.2.2.2.1
  have : X.B.μf.IsMulRightInvariant := hU
  have : (X.B.I.muA X.B.μf).IsMulLeftInvariant := rr_muA_left X.B.I X.B.μf
  have : (X.B.I.muA X.B.μf).IsMulRightInvariant := rr_muA_right X.B.I X.B.μf
  have : SigmaFinite (X.B.I.muA X.B.μf) := rr_muA_sigmaFinite X.B.I X.B.μf
  have h1 := rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec
  have h2 := rr_IsReg_of X.B.I X.B.μf X.B.fund X.B.R X.B.R_spec
  refine ⟨fun a b => rr_mul h1 h2 a b, fun a F => rr_norm h1 h2 a F, fun x y => ?_⟩
  exact (rr_weak_meas h1 h2 x y).comp_measurable (measurable_const.prodMk measurable_id)

theorem phi_bound (x y : X.B.I.L2 X.B.μf X.B.fund) (c : X.B.I.Gf) : ‖phi X x y c‖ ≤ ‖x‖ * ‖y‖ := by
  have h := (R_facts X).2.1 (1, c) y
  calc ‖phi X x y c‖ ≤ ‖x‖ * ‖X.B.R (1, c) y‖ := norm_inner_le_norm _ _
    _ = ‖x‖ * ‖y‖ := by rw [h]

theorem isRConvF_conv {f g : X.B.I.Gf → ℂ} {T U : X.B.I.L2 X.B.μf X.B.fund →L[ℂ] X.B.I.L2 X.B.μf X.B.fund}
    (hf : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R f T) (hg : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R g U) :
    X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (X.B.I.convF X.B.μf f g) (T.comp U) := by
  obtain ⟨hmul, -, hmeas⟩ := R_facts X
  have : X.B.μf.IsHaarMeasure := X.B.haar
  have : SecondCountableTopology X.B.I.Gf := rr_secondCountable X.B.I X.B.μf
  have hK : Integrable (fun p : X.B.I.Gf × X.B.I.Gf => f p.1 * g (p.1⁻¹ * p.2)) (X.B.μf.prod X.B.μf) := by
    have h0 : Integrable (fun q : X.B.I.Gf × X.B.I.Gf => f q.1 * g q.2) (X.B.μf.prod X.B.μf) := hf.1.mul_prod hg.1
    exact ((measurePreserving_prod_inv_mul X.B.μf X.B.μf).integrable_comp h0.aestronglyMeasurable).2 h0
  have hF : ∀ x y : X.B.I.L2 X.B.μf X.B.fund, Integrable (fun p : X.B.I.Gf × X.B.I.Gf =>
      f p.1 * g (p.1⁻¹ * p.2) * phi X x y p.2) (X.B.μf.prod X.B.μf) := fun x y =>
    hK.mul_bdd ((hmeas x y).comp_measurable measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => phi_bound X x y p.2)
  refine ⟨hK.integral_prod_right, fun x y => ?_⟩
  have step : ∀ a, ⟪x, X.B.R (1, a) (U y)⟫_ℂ = ∫ c, g (a⁻¹ * c) * phi X x y c ∂X.B.μf := by
    intro a
    rw [← ContinuousLinearMap.adjoint_inner_left, hg.2]
    have e : ∀ b, g b * ⟪ContinuousLinearMap.adjoint (X.B.R (1, a)) x, X.B.R (1, b) y⟫_ℂ =
        g b * phi X x y (a * b) := by
      intro b
      rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, ← hmul, Prod.mk_mul_mk, one_mul]
    simp_rw [e]
    rw [← integral_mul_left_eq_self (fun c => g (a⁻¹ * c) * phi X x y c) a]
    congr 1
    funext b
    simp only [inv_mul_cancel_left]
  rw [ContinuousLinearMap.comp_apply, hf.2]
  simp_rw [step, ← integral_const_mul]
  have hF' : Integrable (Function.uncurry fun a c => f a * (g (a⁻¹ * c) * phi X x y c)) (X.B.μf.prod X.B.μf) := by
    have := hF x y
    simp only [mul_assoc] at this
    exact this
  rw [integral_integral_swap hF']
  congr 1
  funext c
  unfold AutInst.convF
  rw [← integral_mul_const]
  congr 1
  funext a
  ring

end Formalism.L2.SG.Pf.AllRowsRMul
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.RowDict Formalism.L2.SG.AllRowsOf
open scoped InnerProductSpace
open MeasureTheory

namespace Formalism.L2.SG.Pf.RowsGoodRed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def VT (t : Tup2 D) : Submodule ℂ (L2X X) :=
  Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X ⊓ LinearMap.ker ((ReT X {t} : L2X X →ₗ[ℂ] L2X X) - LinearMap.id)

def labOf (σ : Fin D.what₂.Drows) : Tup2 D := fun k => D.nd.lab k (D.what₂.ft σ)

def bRow (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) (σ : Fin D.what₂.Drows) : L2X X :=
  ((ι (D.sEE (D.what₂.onb σ)) : Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) : L2X X)

def LabTie (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) : Prop :=
  (∀ σ k v, IsLabel D k (D.nd.lab k (D.what₂.ft σ) v)) ∧ (∀ σ, D.ntypes.goodTuple (labOf σ)) ∧
    ∀ σ, bRow X ι σ ∈ VT X (labOf σ)

def ProjT (G : GoodOp X) : Prop :=
  (∀ t : Tup2 D, D.ntypes.goodTuple t → VT X t ≤ goodSub X G) ∧
    ∀ t t' : Tup2 D, t ≠ t' → ∀ φ ∈ VT X t, ∀ φ' ∈ VT X t', ⟪φ, φ'⟫_ℂ = 0

def DcountEq : Prop :=
  ∀ t ∈ labT (D := D), D.ntypes.goodTuple t → dimX X {t} = Module.finrank ℂ (VT X t)

theorem rowsGood_of (G : GoodOp X) (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) (hT : RowDictTie X G ι)
    (hL : LabTie X ι) (hP : ProjT X G) (hD : DcountEq X) : RowsGood X := by
  classical
  obtain ⟨hl1, hl2, hl3⟩ := hL
  refine ⟨hl1, hl2, fun t ht hg => ?_⟩
  have hT' := hT
  obtain ⟨j, hj⟩ := hT
  have hb : ∀ σ, bRow X ι σ = star ((j (D.what₂.onb σ) : EEC X G) : L2X X) := fun σ => by
    have h1 := hj (D.what₂.onb σ)
    simp only at h1
    unfold bRow; rw [h1]; rfl

  have hf : LinearIndependent ℂ (fun σ => ((j (D.what₂.onb σ) : EEC X G) : L2X X)) :=
    (D.what₂.onb.toBasis.linearIndependent.map' j.toLinearEquiv.toLinearMap j.toLinearEquiv.ker).map'
      (EEC X G).subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent ℂ (bRow X ι) := by
    rw [linearIndependent_iff']
    intro s g hs i hi
    have h0 : conjL (muX X) (∑ i ∈ s, (starRingEnd ℂ (g i)) • ((j (D.what₂.onb i) : EEC X G) : L2X X)) = 0 := by
      rw [map_sum]
      rw [← hs]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [LinearIsometryEquiv.map_smulₛₗ, conjL_apply, hb σ]
      simp
    have h1 : (∑ i ∈ s, (starRingEnd ℂ (g i)) • ((j (D.what₂.onb i) : EEC X G) : L2X X)) = 0 :=
      (conjL (muX X)).map_eq_zero_iff.1 h0
    have := (linearIndependent_iff'.1 hf) s (fun i => starRingEnd ℂ (g i)) h1 i hi
    simpa using this

  have hspan : ∀ φ ∈ goodSub X G, φ ∈ Submodule.span ℂ (Set.range (bRow X ι)) := by
    intro φ hφ
    obtain ⟨F, hF⟩ := (range_sEE X hT' ⟨φ, hφ.1⟩).1 hφ
    have e : φ = ((ι (D.sEE F) : Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) : L2X X) := by rw [hF]
    rw [e, ← D.what₂.onb.sum_repr F, map_sum, map_sum, Submodule.coe_sum]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [map_smulₛₗ, map_smul, Submodule.coe_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)

  let Sf : Finset (Fin D.what₂.Drows) := Finset.univ.filter fun σ => labOf σ = t
  have hEq : VT X t = Submodule.span ℂ (Set.range (fun σ : Sf => bRow X ι σ)) := by
    apply le_antisymm
    · intro φ hφ
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan φ (hP.1 t hg hφ))
      set φ1 := ∑ σ ∈ Sf, c σ • bRow X ι σ with hφ1
      set φ2 := ∑ σ ∈ Finset.univ.filter (fun σ => ¬ labOf σ = t), c σ • bRow X ι σ with hφ2
      have hsplit : φ = φ1 + φ2 := by
        rw [← hc, hφ1, hφ2, Finset.sum_filter_add_sum_filter_not]
      have h1V : φ1 ∈ VT X t := Submodule.sum_mem _ fun σ hσ => Submodule.smul_mem _ _ (by
        have := hl3 σ; rwa [(Finset.mem_filter.1 hσ).2] at this)
      have h2V : φ2 ∈ VT X t := by
        have := Submodule.sub_mem _ hφ h1V
        rwa [hsplit, add_sub_cancel_left] at this
      have horth : ⟪φ2, φ2⟫_ℂ = 0 := by
        conv_lhs => rw [hφ2]
        rw [sum_inner]
        refine Finset.sum_eq_zero fun σ hσ => ?_
        rw [inner_smul_left, hP.2 (labOf σ) t (Finset.mem_filter.1 hσ).2 _ (hl3 σ) _ h2V, mul_zero]
      have h20 : φ2 = 0 := inner_self_eq_zero.1 horth
      rw [hsplit, h20, add_zero, hφ1]
      exact Submodule.sum_mem _ fun σ hσ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨σ, hσ⟩, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨σ, rfl⟩
      have := hl3 σ
      rwa [(Finset.mem_filter.1 σ.2).2] at this
  have hli' : LinearIndependent ℂ (fun σ : Sf => bRow X ι σ) := hli.comp (Subtype.val : Sf → _) Subtype.val_injective
  rw [hD t ht hg, hEq, finrank_span_eq_card hli', Fintype.card_coe]
  rfl

def EtConv : Prop := ∀ (S S' : Set (Tup2 D)) (φ : L2X X), ReT X S (ReT X S' φ) = ReT X (S ∩ S') φ

def EtEmpty : Prop := ∀ φ : L2X X, ReT X ∅ φ = 0

def EtAdj : Prop := ∀ (S : Set (Tup2 D)) (φ ψ : L2X X), ⟪ReT X S φ, ψ⟫_ℂ = ⟪φ, ReT X S ψ⟫_ℂ

def EtGood (G : GoodOp X) : Prop :=
  ∀ t : Tup2 D, D.ntypes.goodTuple t → ∀ φ : L2X X, G.Rg (ReT X {t} φ) = ReT X {t} φ

theorem mem_VT {t : Tup2 D} {φ : L2X X} (h : φ ∈ VT X t) : ReT X {t} φ = φ := by
  have h2 := (Submodule.mem_inf.mp h).2
  rw [LinearMap.mem_ker] at h2
  simpa [sub_eq_zero] using h2

theorem projT_of (G : GoodOp X) (hC : EtConv X) (hE : EtEmpty X) (hA : EtAdj X) (hG : EtGood X G) : ProjT X G := by
  refine ⟨fun t ht φ hφ => ?_, fun t t' htt φ hφ φ' hφ' => ?_⟩
  · refine Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hφ).1, ?_⟩
    have h1 := hG t ht φ
    rw [mem_VT X hφ] at h1
    rw [LinearMap.mem_ker]
    simpa [sub_eq_zero] using h1
  · rw [← mem_VT X hφ, ← mem_VT X hφ', hA, hC]
    have hE0 : ({t} : Set (Tup2 D)) ∩ {t'} = ∅ := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
      rintro rfl
      exact htt
    rw [hE0, hE, inner_zero_right]

theorem etEmpty : EtEmpty X := by
  intro φ
  have hES : ∀ g, (ES (D := D) ∅).coeff g = 0 := by
    intro g
    simp [ES]
  have hg : egA X (ES (D := D) ∅) = 0 := by
    funext y
    simp [egA, hES]
  have he : eT X ∅ = 0 := by
    funext x
    simp [eT, Formalism.MainNotions.S.AutInst.convF, hg]
  unfold ReT
  split_ifs with h
  · have hT := (Classical.choose_spec h).2
    have h0 : ∀ x, ⟪x, (Classical.choose h) φ⟫_ℂ = 0 := fun x => by
      rw [hT x φ, he]
      simp
    exact inner_self_eq_zero.mp (h0 _)
  · rfl

theorem invInvariant_muf : X.B.μf.IsInvInvariant := by
  have : X.B.μf.IsMulRightInvariant := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hL := Formalism.L2.SG.Closed.level_subgroup_properties X
  have he1 : X.B.e 1 ≠ 0 := by
    rw [X.e_eq]
    have h1 : (1 : X.B.I.Gf) ∈ X.K2 := hK.1
    rw [if_pos (show (1 : X.B.I.Gf) ∈ Formalism.L2.SG.HidaSetting.K2set X.B.I X.B.g X.e0 X.z0 X.bw from h1)]
    have hc : X.chi2 1 ≠ 0 := by
      intro h0; have := hK.2.2.2.2 1 h1; rw [h0, norm_zero] at this; exact zero_ne_one this
    have hv : ((X.B.μf X.K2).toReal : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact (ENNReal.toReal_pos hL.2.2.1.ne' hL.2.2.2.ne).ne'
    exact div_ne_zero (star_ne_zero.2 hc) hv
  exact Formalism.MainNotions.BridgeLemma.inv_invariant_of_bi_invariant X.B.μf (fun g => ‖X.B.e g‖) X.B.e_adm.1.continuous.norm
    X.B.Re_spec.1.norm (norm_pos_iff.2 he1)

def EtSA : Prop := ∀ (S : Set (Tup2 D)) (x : X.B.I.Gf), star (eT X S x⁻¹) = eT X S x

theorem etAdj_of (hSA : EtSA X) : EtAdj X := by
  haveI := invInvariant_muf X
  intro S φ ψ
  have hT := reT_spec X (etInt_holds X) S
  have hreg : ∀ g : X.B.I.Gf, ⟪X.B.R ((1, g) : X.B.I.GA) φ, ψ⟫_ℂ = ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ := by
    intro g
    have := Formalism.L2.SG.EvalTOntoPhi.inner_reg X ((1, g⁻¹) : X.B.I.GA) φ ψ
    rw [this, Prod.inv_mk, inv_one, inv_inv]
  calc ⟪ReT X S φ, ψ⟫_ℂ = star ⟪ψ, ReT X S φ⟫_ℂ := (inner_conj_symm _ _).symm
    _ = star (∫ g, eT X S g * ⟪ψ, X.B.R ((1, g) : X.B.I.GA) φ⟫_ℂ ∂X.B.μf) := by rw [hT.2]
    _ = ∫ g, star (eT X S g) * ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ ∂X.B.μf := by
        rw [← starRingEnd_apply, ← integral_conj]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show (starRingEnd ℂ) (eT X S g * ⟪ψ, X.B.R ((1, g) : X.B.I.GA) φ⟫_ℂ) = _
        rw [map_mul]
        show _ = star (eT X S g) * ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ
        rw [← hreg g, inner_conj_symm]
        rfl
    _ = ∫ g, star (eT X S g⁻¹) * ⟪φ, X.B.R ((1, g) : X.B.I.GA) ψ⟫_ℂ ∂X.B.μf := by
        rw [← MeasureTheory.integral_inv_eq_self (fun g => star (eT X S g) * ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ) X.B.μf]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show star (eT X S g⁻¹) * ⟪φ, X.B.R ((1, g⁻¹⁻¹) : X.B.I.GA) ψ⟫_ℂ = _
        rw [inv_inv]
    _ = ∫ g, eT X S g * ⟪φ, X.B.R ((1, g) : X.B.I.GA) ψ⟫_ℂ ∂X.B.μf := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show star (eT X S g⁻¹) * _ = _
        rw [hSA S g]
    _ = ⟪φ, ReT X S ψ⟫_ℂ := (hT.2 φ ψ).symm

theorem etGood_of (G : GoodOp X)
    (hEC : ∀ S S' : Set (Tup2 D), X.B.I.convF X.B.μf (egA X (ES S')) (eT X S) = eT X (S' ∩ S)) : EtGood X G := by
  intro t ht φ
  have h1 := Formalism.L2.SG.Pf.AllRowsRMul.isRConvF_conv X G.Rg_spec (reT_spec X (etInt_holds X) {t})
  have e : X.B.I.convF X.B.μf (eg X) (eT X {t}) = eT X {t} := by
    rw [← goodIdempotent_eq, ← ES_good, hEC]
    congr 1
    exact Set.inter_eq_right.2 (Set.singleton_subset_iff.2 ht)
  rw [e] at h1
  have h2 := isRConvF_unique X h1 (reT_spec X (etInt_holds X) {t})
  exact congrArg (fun T : L2X X →L[ℂ] L2X X => T φ) h2

end Formalism.L2.SG.Pf.RowsGoodRed
end
end

section
noncomputable section

open MonoidAlgebra MeasureTheory
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.AllRowsAdd

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsGA
  Formalism.L2.SG.Pf.AllRowsFin Formalism.L2.SG.Pf.AllRowsRhoX Formalism.L2.SG.Pf.AllRowsES Formalism.L2.SG.Pf.AllRowsTr
  Formalism.L2.SG.Pf.AllRowsEtAlg

variable {D : D7}

instance instFactG' (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

open Classical in

theorem ES_inter (S S' : Set (Tup2 D)) : ES S * ES S' = ES (S ∩ S') := by
  rw [ES_eq, ES_eq, ES_eq, Finset.sum_mul_sum]
  simp only [Ea_mul]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_ite_eq _ _ _, ← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff]

theorem Ea_zero (a : CV D) (h : tupOf a ∉ labT (D := D)) : Ea a = 0 := by
  classical
  have : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  have : ∃ kv : (Σ k : Fin 2, D.nd.PlG k), ¬ IsLabel D kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) := by
    by_contra hc
    push Not at hc
    apply h
    unfold labT
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩, fun k v => hc ⟨k, v⟩⟩
  obtain ⟨kv, hkv⟩ := this
  have h0 : D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) = 0 := D.ntypes.eSer_zero _ _ hkv
  apply MonoidAlgebra.ext; ext γ
  rw [Ea_coeff, Finset.prod_eq_zero (Finset.mem_univ kv) (by rw [h0]; rfl)]
  rfl

open Classical in

theorem ES_split (S : Set (Tup2 D)) : ES S = ∑ t ∈ (labT (D := D)).filter (· ∈ S), ES {t} := by
  simp only [ES_eq]
  have e1 : ∑ a ∈ Finset.univ.filter (fun a : CV D => tupOf a ∈ S), Ea a =
      ∑ a ∈ Finset.univ.filter (fun a : CV D => tupOf a ∈ S ∧ tupOf a ∈ labT (D := D)), Ea a := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h1 : tupOf a ∈ S
    · by_cases h2 : tupOf a ∈ labT (D := D)
      · rw [if_pos h1, if_pos ⟨h1, h2⟩]
      · rw [if_pos h1, if_neg (fun h => h2 h.2), Ea_zero a h2]
    · rw [if_neg h1, if_neg (fun h => h1 h.1)]
  rw [e1, ← Finset.sum_fiberwise_of_maps_to (g := tupOf) (t := (labT (D := D)).filter (· ∈ S)) (fun a ha => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ⟨ha.2, ha.1⟩)]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.filter_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h; rw [Finset.mem_filter] at ht; exact ⟨⟨h ▸ ht.2, h ▸ ht.1⟩, h⟩

section Fin

variable {X : HidaSetting D} (hS : Function.Surjective (rhoX X))
include hS

theorem eT_inter (S S' : Set (Tup2 D)) : X.B.I.convF X.B.μf (eT X S) (eT X S') = eT X (S ∩ S') := by
  refine hat_inj hS (biInv_conv hS (biInv_eT X S) (biInv_eT X S')) (biInv_eT X _) fun γ => ?_
  rw [conv_hat hS (biInv_eT X S) (biInv_eT X S'), hat_eT' hS]
  simp only [hat_eT' hS]
  rw [← coeff_mul_fin]
  have key : (Ehat hS * ES S) * (Ehat hS * ES S') = Ehat hS * ES (S ∩ S') := by
    calc (Ehat hS * ES S) * (Ehat hS * ES S') = Ehat hS * (ES S * Ehat hS) * ES S' := by noncomm_ring
      _ = Ehat hS * (Ehat hS * ES S) * ES S' := by rw [ES_central]
      _ = (Ehat hS * Ehat hS) * (ES S * ES S') := by noncomm_ring
      _ = Ehat hS * ES (S ∩ S') := by rw [Ehat_idem, ES_inter]
  rw [key]

omit hS in
theorem biInv_sum {ι : Type} (F : Finset ι) (f : ι → X.B.I.Gf → ℂ) (h : ∀ i, BiInv X (f i)) :
    BiInv X (fun x => ∑ i ∈ F, f i x) := by
  refine ⟨fun x hx => ?_, fun x n hn => ?_, fun x n hn => ?_⟩
  · obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    exact (h i).1 x hi
  · exact Finset.sum_congr rfl fun i _ => (h i).2.1 x n hn
  · exact Finset.sum_congr rfl fun i _ => (h i).2.2 x n hn

theorem hat_sum {ι : Type} (F : Finset ι) (f : ι → X.B.I.Gf → ℂ) (γ : G0g D.nd) :
    hat hS (fun x => ∑ i ∈ F, f i x) γ = ∑ i ∈ F, hat hS (f i) γ := by
  unfold hat; rw [Finset.mul_sum]

open Classical in

theorem eT_split (S : Set (Tup2 D)) :
    eT X S = fun x => ∑ t ∈ (labT (D := D)).filter (· ∈ S), eT X {t} x := by
  refine hat_inj hS (biInv_eT X S) (biInv_sum _ _ fun t => biInv_eT X {t}) fun γ => ?_
  rw [hat_sum, hat_eT' hS, ES_split, Finset.mul_sum, MonoidAlgebra.coeff_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hat_eT' hS]

end Fin

section Ops

variable (X : HidaSetting D)

theorem hS_X : Function.Surjective (rhoX X) := Formalism.L2.SG.Pf.RhoSurjW.reduction_map_surjective D X

theorem egA_conv_eT (S S' : Set (Tup2 D)) :
    X.B.I.convF X.B.μf (egA X (ES S')) (eT X S) = eT X (S' ∩ S) := by
  have hS := hS_X X
  refine hat_inj hS (biInv_conv hS (biInv_egA X _ (ES_conj S')) (biInv_eT X S)) (biInv_eT X _) fun γ => ?_
  rw [conv_hat hS (biInv_egA X _ (ES_conj S')) (biInv_eT X S), hat_eT' hS]
  simp only [hat_egA hS _ (ES_conj S'), hat_eT' hS]
  rw [← coeff_mul_fin]
  have key : ES S' * (Ehat hS * ES S) = Ehat hS * ES (S' ∩ S) := by
    rw [← mul_assoc, ES_central, mul_assoc, ES_inter]
  rw [key]

theorem reT_inter (S S' : Set (Tup2 D)) : (ReT X S).comp (ReT X S') = ReT X (S ∩ S') := by
  have h := Formalism.L2.SG.Pf.AllRowsRMul.isRConvF_conv X (reT_spec X (etInt_holds X) S) (reT_spec X (etInt_holds X) S')
  rw [eT_inter (hS_X X) S S'] at h
  exact isRConvF_unique X h (reT_spec X (etInt_holds X) (S ∩ S'))

theorem etConv_holds : Formalism.L2.SG.Pf.RowsGoodRed.EtConv X := fun S S' φ => by
  rw [← ContinuousLinearMap.comp_apply, reT_inter]

theorem etSA_holds : Formalism.L2.SG.Pf.RowsGoodRed.EtSA X := fun S x => by
  rw [eT_inv (hS_X X) S x, star_star]

theorem projT_holds (G : Formalism.L2.SG.RowDict.GoodOp X) : Formalism.L2.SG.Pf.RowsGoodRed.ProjT X G :=
  Formalism.L2.SG.Pf.RowsGoodRed.projT_of X G (etConv_holds X) (Formalism.L2.SG.Pf.RowsGoodRed.etEmpty X)
    (Formalism.L2.SG.Pf.RowsGoodRed.etAdj_of X (etSA_holds X)) (Formalism.L2.SG.Pf.RowsGoodRed.etGood_of X G (egA_conv_eT X))

end Ops

section Split

variable (X : HidaSetting D)

theorem isRConvF_sum {ι : Type} (F : Finset ι) (f : ι → X.B.I.Gf → ℂ)
    (T : ι → (X.B.I.L2 X.B.μf X.B.fund →L[ℂ] X.B.I.L2 X.B.μf X.B.fund))
    (h : ∀ i, X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (f i) (T i)) :
    X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (fun x => ∑ i ∈ F, f i x) (∑ i ∈ F, T i) := by
  obtain ⟨-, -, hmeas⟩ := Formalism.L2.SG.Pf.AllRowsRMul.R_facts X
  refine ⟨integrable_finsetSum _ fun i _ => (h i).1, fun x y => ?_⟩
  rw [ContinuousLinearMap.sum_apply, inner_sum]
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ => (h i).1.mul_bdd ((hmeas x y).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun c => Formalism.L2.SG.Pf.AllRowsRMul.phi_bound X x y c)]
  exact Finset.sum_congr rfl fun i _ => (h i).2 x y

open Classical in

theorem reT_split (S : Set (Tup2 D)) : ReT X S = ∑ t ∈ (labT (D := D)).filter (· ∈ S), ReT X {t} := by
  have h := isRConvF_sum X ((labT (D := D)).filter (· ∈ S)) (fun t => eT X {t}) (fun t => ReT X {t})
    (fun t => reT_spec X (etInt_holds X) {t})
  rw [← eT_split (hS_X X) S] at h
  exact isRConvF_unique X (reT_spec X (etInt_holds X) S) h

theorem reT_orth (t t' : Tup2 D) :
    (ReT X {t}).comp (ReT X {t'}) = if t = t' then ReT X {t} else 0 := by
  rw [reT_inter]
  split_ifs with h
  · rw [h, Set.inter_self]
  · have e : ({t} : Set (Tup2 D)) ∩ {t'} = ∅ := by
      ext u; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨rfl, rfl⟩; exact h rfl
    rw [e]
    exact ContinuousLinearMap.ext fun φ => Formalism.L2.SG.Pf.RowsGoodRed.etEmpty X φ

end Split

section LA

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V)

theorem finrank_map_sum {ι : Type} [DecidableEq ι] (Q : ι → V →ₗ[ℂ] V) :
    ∀ (F : Finset ι), (∀ i ∈ F, ∀ j ∈ F, Q i ∘ₗ Q j = if i = j then Q i else 0) →
      (∀ i ∈ F, ∀ x ∈ W, Q i x ∈ W) →
      (∀ G ⊆ F, FiniteDimensional ℂ (W.map (∑ i ∈ G, Q i))) →
      Module.finrank ℂ (W.map (∑ i ∈ F, Q i)) = ∑ i ∈ F, Module.finrank ℂ (W.map (Q i)) := by
  intro F
  induction F using Finset.induction_on with
  | empty => intro _ _ _; rw [Finset.sum_empty, Finset.sum_empty, Submodule.map_zero, finrank_bot]
  | insert t F ht ih =>
    intro hQ hW hfin
    have hQ' : ∀ i ∈ F, ∀ j ∈ F, Q i ∘ₗ Q j = if i = j then Q i else 0 := fun i hi j hj =>
      hQ i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    have hW' : ∀ i ∈ F, ∀ x ∈ W, Q i x ∈ W := fun i hi => hW i (Finset.mem_insert_of_mem hi)
    have hfin' : ∀ G ⊆ F, FiniteDimensional ℂ (W.map (∑ i ∈ G, Q i)) := fun G hG =>
      hfin G (hG.trans (Finset.subset_insert _ _))
    rw [Finset.sum_insert ht, Finset.sum_insert ht, ← ih hQ' hW' hfin']
    set QF := ∑ i ∈ F, Q i with hQF
    have htt : ∀ x, Q t (Q t x) = Q t x := fun x => by
      have := congrArg (fun L : V →ₗ[ℂ] V => L x) (hQ t (Finset.mem_insert_self t F) t (Finset.mem_insert_self t F))
      simpa using this
    have htF : ∀ x, Q t (QF x) = 0 := fun x => by
      rw [hQF, LinearMap.sum_apply, map_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      have := congrArg (fun L : V →ₗ[ℂ] V => L x)
        (hQ t (Finset.mem_insert_self t F) i (Finset.mem_insert_of_mem hi))
      simp only [LinearMap.comp_apply] at this
      rw [this, if_neg (fun (h : t = i) => ht (h ▸ hi))]
      rfl
    have hFt : ∀ x, QF (Q t x) = 0 := fun x => by
      rw [hQF, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i hi => ?_
      have := congrArg (fun L : V →ₗ[ℂ] V => L x)
        (hQ i (Finset.mem_insert_of_mem hi) t (Finset.mem_insert_self t F))
      simp only [LinearMap.comp_apply] at this
      rw [this, if_neg (fun (h : i = t) => ht (h ▸ hi))]
      rfl
    have hFF : ∀ x, QF (QF x) = QF x := fun x => by
      rw [hQF]
      simp only [LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.sum_eq_single i]
      · have := congrArg (fun L : V →ₗ[ℂ] V => L x) (hQ' i hi i hi)
        simpa using this
      · intro j hj hji
        have := congrArg (fun L : V →ₗ[ℂ] V => L x) (hQ' j hj i hi)
        simp only [LinearMap.comp_apply] at this
        rw [this, if_neg hji]; rfl
      · intro h; exact absurd hi h
    have hWF : ∀ x ∈ W, QF x ∈ W := fun x hx => by
      rw [hQF, LinearMap.sum_apply]; exact Submodule.sum_mem _ fun i hi => hW' i hi x hx
    have hC : W.map (Q t + QF) = W.map (Q t) ⊔ W.map QF := by
      apply le_antisymm
      · rintro _ ⟨w, hw, rfl⟩
        exact Submodule.add_mem_sup ⟨w, hw, rfl⟩ ⟨w, hw, rfl⟩
      · refine sup_le ?_ ?_
        · rintro _ ⟨w, hw, rfl⟩
          refine ⟨Q t w, hW t (Finset.mem_insert_self t F) w hw, ?_⟩
          simp only [LinearMap.add_apply, htt, hFt, add_zero]
        · rintro _ ⟨w, hw, rfl⟩
          refine ⟨QF w, hWF w hw, ?_⟩
          simp only [LinearMap.add_apply, htF, hFF, zero_add]
    have hdis : W.map (Q t) ⊓ W.map QF = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨⟨w, _, rfl⟩, ⟨w', _, hw'⟩⟩
      have h1 : Q t (Q t w) = Q t w := htt w
      have h2 : Q t (Q t w) = 0 := by rw [← hw', htF]
      rw [Submodule.mem_bot, ← h1, h2]
    have hfA : FiniteDimensional ℂ (W.map (Q t)) := by
      have := hfin {t} (Finset.singleton_subset_iff.2 (Finset.mem_insert_self t F))
      rwa [Finset.sum_singleton] at this
    have hfB : FiniteDimensional ℂ (W.map QF) := hfin' F (Finset.Subset.refl _)
    have := Submodule.finrank_sup_add_finrank_inf_eq (W.map (Q t)) (W.map QF)
    rw [hdis, finrank_bot, add_zero] at this
    rw [hC, this]

end LA

section Add

variable (X : HidaSetting D)

theorem reT_comm (S : Set (Tup2 D)) (g : X.B.I.Ginf) :
    (ReT X S).comp (X.B.R (g, 1)) = (X.B.R (g, 1)).comp (ReT X S) := by
  obtain ⟨hmul, -, -⟩ := Formalism.L2.SG.Pf.AllRowsRMul.R_facts X
  have hT := reT_spec X (etInt_holds X) S
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hT.2,
    ← ContinuousLinearMap.adjoint_inner_left, hT.2]
  congr 1
  funext a
  rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
    ← hmul, ← hmul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, mul_one, one_mul, mul_one]

theorem reT_univ' : ReT X Set.univ = X.B.Re :=
  reT_univ X (etUniv_of X (redKer_of X (redKerOne_of X (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 0)
    (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 1)))) (etInt_holds X)

open Classical in

theorem rowsAdd_of (hFD : FiniteDimensional ℂ (X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re)) : RowsAdd X := by
  intro S
  set W := X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R
  let Q : Tup2 D → ((X.B.Hs →L[ℂ] X.B.I.L2 X.B.μf X.B.fund) →ₗ[ℂ] (X.B.Hs →L[ℂ] X.B.I.L2 X.B.μf X.B.fund)) :=
    fun t => (ContinuousLinearMap.compL ℂ X.B.Hs _ _ (ReT X {t}) : _ →ₗ[ℂ] _)
  have hQapp : ∀ t A, Q t A = (ReT X {t}).comp A := fun t A => rfl
  have hsumQ : ∀ G : Finset (Tup2 D), (∑ t ∈ G, Q t) =
      (ContinuousLinearMap.compL ℂ X.B.Hs _ _ (∑ t ∈ G, ReT X {t}) : _ →ₗ[ℂ] _) := by
    intro G
    apply LinearMap.ext
    intro A
    rw [LinearMap.sum_apply]
    simp only [hQapp]
    show ∑ t ∈ G, (ReT X {t}).comp A = (∑ t ∈ G, ReT X {t}).comp A
    ext y
    simp
  have hQQ : ∀ i ∈ labT (D := D), ∀ j ∈ labT (D := D), Q i ∘ₗ Q j = if i = j then Q i else 0 := by
    intro i _ j _
    apply LinearMap.ext
    intro A
    rw [LinearMap.comp_apply, hQapp, hQapp, ← ContinuousLinearMap.comp_assoc, reT_orth]
    split_ifs
    · rfl
    · simp
  have hWQ : ∀ i ∈ labT (D := D), ∀ A ∈ W, Q i A ∈ W := by
    intro i _ A hA g
    rw [hQapp]
    show ((ReT X {i}).comp A).comp (X.B.σs g) = (X.B.R (g, 1)).comp ((ReT X {i}).comp A)
    rw [ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, reT_comm,
      ContinuousLinearMap.comp_assoc]
  have hfin : ∀ G ⊆ labT (D := D), FiniteDimensional ℂ (W.map (∑ t ∈ G, Q t)) := by
    intro G _
    have := hFD
    let Qe : (X.B.Hs →L[ℂ] X.B.I.L2 X.B.μf X.B.fund) →ₗ[ℂ] (X.B.Hs →L[ℂ] X.B.I.L2 X.B.μf X.B.fund) :=
      (ContinuousLinearMap.compL ℂ X.B.Hs (X.B.I.L2 X.B.μf X.B.fund) (X.B.I.L2 X.B.μf X.B.fund) X.B.Re :
        (X.B.Hs →L[ℂ] X.B.I.L2 X.B.μf X.B.fund) →ₗ[ℂ] (X.B.Hs →L[ℂ] X.B.I.L2 X.B.μf X.B.fund))
    have hcomp : (∑ t ∈ G, Q t) ∘ₗ Qe = ∑ t ∈ G, Q t := by
      apply LinearMap.ext
      intro A
      rw [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hQapp, hQapp]
      show (ReT X {t}).comp (X.B.Re.comp A) = (ReT X {t}).comp A
      rw [← ContinuousLinearMap.comp_assoc, ← reT_univ' X, reT_inter, Set.inter_univ]
    have e2 : W.map (∑ t ∈ G, Q t) = (X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re).map (∑ t ∈ G, Q t) := by
      unfold AutInst.eHom
      rw [← Submodule.map_comp]
      exact congrArg (fun L => W.map L) hcomp.symm
    rw [e2]
    infer_instance
  have hF := finrank_map_sum W Q ((labT (D := D)).filter (· ∈ S))
    (fun i hi j hj => hQQ i (Finset.mem_of_mem_filter i hi) j (Finset.mem_of_mem_filter j hj))
    (fun i hi => hWQ i (Finset.mem_of_mem_filter i hi))
    (fun G hG => hfin G (hG.trans (Finset.filter_subset _ _)))
  unfold dimX AutInst.Dcount AutInst.eHom
  rw [reT_split X S, ← hsumQ, hF, Finset.sum_filter]

end Add

end Formalism.L2.SG.Pf.AllRowsAdd
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsAddFin

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

theorem eHom_fin (hHC : Formalism.L2.SG.RowsDef.RowsFinDim) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) :
    FiniteDimensional ℂ (X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re) := by
  have hint := Formalism.L2.SG.Pf.RowDictPf.hint_of_gap X hG
  have hB := Formalism.L2.SG.Closed.RowsBij_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec X.B.e X.B.Re
    X.B.Re_spec X.B.H X.B.σ X.dv X.B.w (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1)
    (Formalism.L2.SG.EvalTRph.isFdeg_dv X) (fun v => (X.low v).1) hint X.Rph X.Rph_spec X.B.Hs X.B.σs X.B.tens
    X.B.tens_spec
  have : FiniteDimensional ℂ (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) :=
    Formalism.L2.SG.Pf.RowDictPf.finiteDimensional_HHX_of_gap X hHC hG
  exact Formalism.L2.SG.RowsDef.finiteDimensional_eHom hB.1 hB.2

theorem rowsAdd_holds (hHC : Formalism.L2.SG.RowsDef.RowsFinDim) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) : RowsAdd X :=
  Formalism.L2.SG.Pf.AllRowsAdd.rowsAdd_of X (eHom_fin X hHC hG)

end Formalism.L2.SG.Pf.AllRowsAddFin
end
end

section
noncomputable section

open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.AllRowsDcount

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsAdd

variable {D : D7} (X : HidaSetting D)

theorem reT_rph (S : Set (Tup2 D)) : (ReT X S).comp X.Rph = X.Rph.comp (ReT X S) := by
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left,
    X.Rph_spec, X.Rph_spec]
  congr 1
  funext g
  rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
    reT_comm]

theorem HH_eq_VT (t : Tup2 D) :
    Formalism.L2.SG.RowsDef.HH X.B.I X.B.μf X.B.fund (ReT X {t}) X.Rph = Formalism.L2.SG.Pf.RowsGoodRed.VT X t := by
  have hPE : (ReT X {t}).comp X.B.Re = ReT X {t} := by
    rw [← reT_univ' X, reT_inter, Set.inter_univ]
  have hEP : X.B.Re.comp (ReT X {t}) = ReT X {t} := by
    rw [← reT_univ' X, reT_inter, Set.univ_inter]
  have hPP : (ReT X {t}).comp (ReT X {t}) = ReT X {t} := by
    rw [reT_inter, Set.inter_self]
  have hR := reT_rph X {t}
  apply le_antisymm
  · rintro v ⟨y, rfl⟩
    refine ⟨⟨ReT X {t} y, ?_⟩, ?_⟩
    · show X.B.Re (X.Rph (ReT X {t} y)) = ReT X {t} (X.Rph y)
      have := congrArg (fun L => L y) hR
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [← this]
      have := congrArg (fun L => L (X.Rph y)) hEP
      simpa only [ContinuousLinearMap.comp_apply] using this
    · show ReT X {t} (ReT X {t} (X.Rph y)) - ReT X {t} (X.Rph y) = 0
      have := congrArg (fun L => L (X.Rph y)) hPP
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [this, sub_self]
  · rintro v ⟨⟨y, hy⟩, hv⟩
    have hv' : ReT X {t} v = v := by
      have : ReT X {t} v - v = 0 := hv
      exact sub_eq_zero.1 this
    refine ⟨y, ?_⟩
    show ReT X {t} (X.Rph y) = v
    have hy' : X.B.Re (X.Rph y) = v := hy
    rw [← hv', ← hy']
    have := congrArg (fun L => L (X.Rph y)) hPE
    simp only [ContinuousLinearMap.comp_apply] at this
    exact this.symm

theorem dcountEq_holds (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) : Formalism.L2.SG.Pf.RowsGoodRed.DcountEq X := by
  intro t _ _
  have hint := Formalism.L2.SG.Pf.RowDictPf.hint_of_gap X hG
  have hB := Formalism.L2.SG.Closed.RowsBij_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec (eT X {t})
    (ReT X {t}) (reT_spec X (etInt_holds X) {t}) X.B.H X.B.σ X.dv X.B.w (fun v => (X.ds v).2.2.1)
    (fun v => (X.ds v).2.2.2.1) (Formalism.L2.SG.EvalTRph.isFdeg_dv X) (fun v => (X.low v).1) hint X.Rph X.Rph_spec
    X.B.Hs X.B.σs X.B.tens X.B.tens_spec
  unfold dimX
  rw [← Formalism.L2.SG.RowsDef.finrank_HH_eq_Dcount hB.1 hB.2, HH_eq_VT]

end Formalism.L2.SG.Pf.AllRowsDcount
end
end

section
noncomputable section

open MonoidAlgebra MeasureTheory

namespace Formalism.L2.SG.Pf.AllRowsEtOne

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsGA
  Formalism.L2.SG.Pf.AllRowsFin Formalism.L2.SG.Pf.AllRowsRhoX Formalism.L2.SG.Pf.AllRowsES Formalism.L2.SG.Pf.AllRowsTr
  Formalism.L2.SG.Pf.AllRowsEtAlg Formalism.L2.SG.Pf.AllRowsKpp Formalism.L2.SG.Pf.AllRowsWt

variable {D : D7} {X : HidaSetting D}

instance instFactG (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

abbrev eJv (kv : Σ k : Fin 2, D.nd.PlG k) (ψ : AddChar (ZMod (D.host.g kv.1)) ℂ) :
    MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :=
  eJ (D.host.g kv.1) D.R.r D.R.k (D.R.m / 2 - 1) ψ

theorem star_psi {g : ℕ} [NeZero g] (ψ : AddChar (ZMod g) ℂ) (x : ZMod g) : star (ψ x) = (ψ x)⁻¹ := by
  rw [Complex.inv_eq_conj (AddChar.norm_apply ψ x)]
  rfl

open Classical in
theorem card_PJ (D : D7) (k : Fin 2) :
    ((Finset.univ.filter fun u : GL (Fin D.R.r) (ZMod (D.host.g k)) =>
      PJ D.R.k (D.R.m / 2 - 1) (u : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k)))).card : ℂ) =
      (cJ D (D.host.g k) : ℂ) := by
  unfold cJ
  rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  congr 1
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun u => ?_)
  exact jPred_iff _ _ (r_eq D) _

theorem levelVolume_eq_index (hS : Function.Surjective (rhoX X)) :
    X.volK2 = ((cJ D (D.host.g 0) ^ D.R.f * cJ D (D.host.g 1) ^ D.R.f : ℕ) : ℝ) * V X := by
  have : X.B.μf.IsHaarMeasure := X.B.haar
  have hopen : IsOpen ((Formalism.L2.SG.Pf.AllRowsKpp.KgSub X : Set X.B.I.Gf)) := X.B.I.topf_open X.B.g (g_pos X)
  have hc := levelSubgroup_relIndex_eq hS
  have hpos2 : (Formalism.L2.SG.Pf.AllRowsKpp.KgSub X).relIndex (Formalism.L2.SG.Pf.AllRowsKpp.concreteLevelAdelicSubset X) ≠ 0 := by
    rw [hc]; exact Nat.pos_iff_ne_zero.1 (Nat.mul_pos (pow_pos (cJ_pos D 0) _) (pow_pos (cJ_pos D 1) _))
  have hμ2 := PI.MassDataKppVolLemmas.Glob_measure_eq_relIndex_mul X.B.μf (Formalism.L2.SG.Pf.AllRowsKpp.concreteLevelAdelicSubset X) (Formalism.L2.SG.Pf.AllRowsKpp.KgSub X) (Formalism.L2.SG.Pf.AllRowsKpp.le2 X) hopen hpos2
  unfold HidaSetting.volK2
  have e : X.B.μf X.K2 = X.B.μf (Formalism.L2.SG.Pf.AllRowsKpp.concreteLevelAdelicSubset X : Set X.B.I.Gf) := rfl
  rw [e, hμ2, ENNReal.toReal_mul, ENNReal.toReal_natCast, hc]
  rfl

variable (hS : Function.Surjective (rhoX X))

theorem hat_e_eq (P : G0g D.nd) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ)
    (hmem : ∀ x : KSub X.B.I, (x : X.B.I.Gf) ∈ X.K2 ↔ ∀ kv, JPred D.R.k (D.R.m / 2 - 1) (cjM P (rhoX X x) kv))
    (hchi : ∀ x : KSub X.B.I, (x : X.B.I.Gf) ∈ X.K2 →
      X.chi2 x = ∏ kv, ψ kv (phiJ D.R.k (D.R.m / 2 - 1) (cjM P (rhoX X x) kv)))
    (γ : G0g D.nd) :
    hat hS X.B.e γ = ∏ kv, (eJv kv (ψ kv)).coeff ((P kv)⁻¹ * γ kv * P kv) := by
  classical
  have hx : rhoX X (sec hS γ) = γ := rho_sec hS γ
  unfold hat
  rw [X.e_eq]
  simp only [eJ_coeff]
  by_cases hJ : ∀ kv, JPred D.R.k (D.R.m / 2 - 1) (cjM P γ kv)
  · have hxK : ((sec hS γ : KSub X.B.I) : X.B.I.Gf) ∈ X.K2 := (hmem _).2 (by rw [hx]; exact hJ)
    have hxK' : ((sec hS γ : KSub X.B.I) : X.B.I.Gf) ∈ K2set X.B.I X.B.g X.e0 X.z0 X.bw := hxK
    have hJ' : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), PJ D.R.k (D.R.m / 2 - 1)
        (((P kv)⁻¹ * γ kv * P kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := hJ
    rw [if_pos hxK', Finset.prod_congr rfl (fun kv _ => if_pos (hJ' kv))]
    have hc := hchi _ hxK
    rw [hx] at hc
    have hv : (X.B.μf (K2set X.B.I X.B.g X.e0 X.z0 X.bw)).toReal =
        ((cJ D (D.host.g 0) ^ D.R.f * cJ D (D.host.g 1) ^ D.R.f : ℕ) : ℝ) * V X := levelVolume_eq_index hS
    show (V X : ℂ) * (star (X.chi2 (sec hS γ)) / ((X.B.μf (K2set X.B.I X.B.g X.e0 X.z0 X.bw)).toReal : ℂ)) = _
    rw [hc, hv, star_prod]
    simp only [star_psi, card_PJ]
    rw [Finset.prod_div_distrib]
    have hprod : ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (cJ D (D.host.g kv.1) : ℂ) =
        ((cJ D (D.host.g 0) ^ D.R.f * cJ D (D.host.g 1) ^ D.R.f : ℕ) : ℂ) := by
      rw [← prod_sigma_const (fun k => cJ D (D.host.g k))]; push_cast; rfl
    rw [hprod]
    have hV := V_ne X
    have hJ0 : ((cJ D (D.host.g 0) ^ D.R.f * cJ D (D.host.g 1) ^ D.R.f : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos (pow_pos (cJ_pos D 0) _) (pow_pos (cJ_pos D 1) _)).ne'
    push_cast
    field_simp
  · have hxK : ((sec hS γ : KSub X.B.I) : X.B.I.Gf) ∉ X.K2 := fun h => hJ (by rw [← hx]; exact (hmem _).1 h)
    push Not at hJ
    obtain ⟨kv, hkv⟩ := hJ
    have hxK' : ((sec hS γ : KSub X.B.I) : X.B.I.Gf) ∉ K2set X.B.I X.B.g X.e0 X.z0 X.bw := hxK
    rw [if_neg hxK', mul_zero]
    symm
    have hkv' : ¬ PJ D.R.k (D.R.m / 2 - 1)
        (((P kv)⁻¹ * γ kv * P kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := hkv
    exact Finset.prod_eq_zero (Finset.mem_univ kv) (if_neg hkv')

theorem conjP_coeff {G : Type} [Group G] (P γ : G) (a : MonoidAlgebra ℂ G) :
    (MonoidAlgebra.single P 1 * a * MonoidAlgebra.single P⁻¹ 1).coeff γ = a.coeff (P⁻¹ * γ * P) := by
  simp [MonoidAlgebra.single_mul_apply, MonoidAlgebra.mul_single_apply, mul_assoc]

theorem Ehat_eq (P : G0g D.nd) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ)
    (hmem : ∀ x : KSub X.B.I, (x : X.B.I.Gf) ∈ X.K2 ↔ ∀ kv, JPred D.R.k (D.R.m / 2 - 1) (cjM P (rhoX X x) kv))
    (hchi : ∀ x : KSub X.B.I, (x : X.B.I.Gf) ∈ X.K2 →
      X.chi2 x = ∏ kv, ψ kv (phiJ D.R.k (D.R.m / 2 - 1) (cjM P (rhoX X x) kv))) :
    Ehat hS = pA (fun kv => MonoidAlgebra.single (P kv) 1 * eJv kv (ψ kv) * MonoidAlgebra.single (P kv)⁻¹ 1) := by
  classical
  apply MonoidAlgebra.ext; ext γ
  rw [Ehat_coeff, pA_coeff, hat_e_eq hS P ψ hmem hchi γ]
  refine Finset.prod_congr rfl fun kv _ => ?_
  rw [conjP_coeff]

theorem Ea_pA (a : CV D) : Ea a = pA (fun kv => D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))) := by
  classical
  apply MonoidAlgebra.ext; ext γ
  rw [Ea_coeff, pA_coeff]

theorem tau_conjP {G : Type} [Group G] [Fintype G] (P : G) (a e : MonoidAlgebra ℂ G) (hc : ∀ y, e * y = y * e) :
    (MonoidAlgebra.single P 1 * a * MonoidAlgebra.single P⁻¹ 1 * e).coeff 1 = (a * e).coeff 1 := by
  rw [mul_assoc (MonoidAlgebra.single P 1 * a), ← hc, ← mul_assoc, mul_assoc (MonoidAlgebra.single P 1) a e,
    conjP_coeff]
  simp

section Val

variable (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ)

def Nc (k : Fin 2) (f : Polynomial (ZMod (D.host.g k))) : ℂ := (eJk D k (ψ₀ k) * D.ntypes.eSer k f).coeff 1

def Zc (k : Fin 2) : ℂ := (eJk D k (ψ₀ k)).coeff 1

open Classical in
include hS in
theorem val_eT_sum (P : G0g D.nd) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ)
    (hψ : ∀ kv, ψ kv ≠ 1) (hψ₀ : ∀ k, ψ₀ k ≠ 1)
    (hmem : ∀ x : KSub X.B.I, (x : X.B.I.Gf) ∈ X.K2 ↔ ∀ kv, JPred D.R.k (D.R.m / 2 - 1) (cjM P (rhoX X x) kv))
    (hchi : ∀ x : KSub X.B.I, (x : X.B.I.Gf) ∈ X.K2 →
      X.chi2 x = ∏ kv, ψ kv (phiJ D.R.k (D.R.m / 2 - 1) (cjM P (rhoX X x) kv)))
    (S : Set (Tup2 D)) :
    (Ehat hS * ES S).coeff 1 =
      ∑ a ∈ Finset.univ.filter (fun a : CV D => tupOf a ∈ S),
        ∏ kv : (Σ k : Fin 2, D.nd.PlG k), Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) := by
  classical
  rw [ES_eq, Finset.mul_sum, MonoidAlgebra.coeff_sum, Finset.sum_apply']
  refine Finset.sum_congr (by congr 1) fun a _ => ?_
  rw [Ehat_eq hS P ψ hmem hchi, Ea_pA, pA_mul, pA_one_coeff]
  refine Finset.prod_congr rfl fun kv _ => ?_
  rw [tau_conjP _ _ _ (D.ntypes.eSer_central kv.1 _)]
  exact (wt_indep (ψ₀ kv.1) (ψ kv) (hψ₀ kv.1) (hψ kv) _ (D.ntypes.eSer_central kv.1 _)).1

include hS in
theorem val_e (P : G0g D.nd) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ)
    (hψ : ∀ kv, ψ kv ≠ 1) (hψ₀ : ∀ k, ψ₀ k ≠ 1)
    (hmem : ∀ x : KSub X.B.I, (x : X.B.I.Gf) ∈ X.K2 ↔ ∀ kv, JPred D.R.k (D.R.m / 2 - 1) (cjM P (rhoX X x) kv))
    (hchi : ∀ x : KSub X.B.I, (x : X.B.I.Gf) ∈ X.K2 →
      X.chi2 x = ∏ kv, ψ kv (phiJ D.R.k (D.R.m / 2 - 1) (cjM P (rhoX X x) kv))) :
    (Ehat hS).coeff 1 = ∏ kv : (Σ k : Fin 2, D.nd.PlG k), Zc ψ₀ kv.1 := by
  classical
  rw [Ehat_eq hS P ψ hmem hchi, pA_one_coeff]
  refine Finset.prod_congr rfl fun kv _ => ?_
  rw [conjP_coeff, mul_one, inv_mul_cancel]
  exact (wt_indep (ψ₀ kv.1) (ψ kv) (hψ₀ kv.1) (hψ kv) 1 (fun y => by rw [one_mul, mul_one])).2

end Val

section Fact

variable (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ)

theorem sum_N_single (k : Fin 2) (f : Polynomial (ZMod (D.host.g k))) :
    ∑ c : Fin D.R.r → ZMod (D.host.g k), (if Formalism.CyclotomicNorms.monicOf c = f then Nc ψ₀ k (Formalism.CyclotomicNorms.monicOf c) else 0) =
      Nc ψ₀ k f := by
  classical
  by_cases hf : f.Monic ∧ f.natDegree = D.R.r
  · have hc0 := Formalism.L2.SG.Pf.RowDictPf.monicOf_coeff hf.1 hf.2
    rw [Finset.sum_eq_single (fun i : Fin D.R.r => f.coeff i)]
    · rw [if_pos hc0, hc0]
    · intro c _ hc
      rw [if_neg]
      intro h
      apply hc
      exact monicOf_inj (h.trans hc0.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_zero fun c _ => if_neg fun (h : Formalism.CyclotomicNorms.monicOf c = f) => hf (h ▸ Formalism.L2.SG.Pf.RowDictPf.monicOf_monic c)]
    unfold Nc
    rw [D.ntypes.eSer_zero k f (fun h => hf ⟨h.1, h.2.1⟩), mul_zero]
    rfl

theorem sum_N_all (k : Fin 2) : ∑ c : Fin D.R.r → ZMod (D.host.g k), Nc ψ₀ k (Formalism.CyclotomicNorms.monicOf c) = Zc ψ₀ k := by
  unfold Nc Zc
  have := congrArg (fun y => (eJk D k (ψ₀ k) * y).coeff 1) (sum_eSer' (D := D) k)
  simp only [Finset.mul_sum, MonoidAlgebra.coeff_sum, Finset.sum_apply', mul_one] at this
  exact this

end Fact

section Cyl

variable (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ)

open Classical in

theorem sum_cyl (k : Fin 2) (S : Finset (Tup D k)) :
    ∑ a ∈ Finset.univ.filter (fun a : CV D => tupOf a ∈ cyl D k (S : Set (Tup D k))),
        ∏ kv : (Σ k : Fin 2, D.nd.PlG k), Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) =
      ∑ t ∈ S, ∏ kv : (Σ k : Fin 2, D.nd.PlG k),
        (if kv.1 = k then Nc ψ₀ kv.1 (Function.update (0 : Tup2 D) k t kv.1 kv.2) else Zc ψ₀ kv.1) := by
  rw [Finset.sum_filter]
  have h1 : ∀ a : CV D, (if tupOf a ∈ cyl D k (S : Set (Tup D k)) then
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) else 0) =
      ∑ t ∈ S, (if tupOf a k = t then ∏ kv : (Σ k : Fin 2, D.nd.PlG k), Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) else 0) := by
    intro a
    rw [Finset.sum_ite_eq]
    exact if_congr (Iff.rfl) rfl rfl
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  set G : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1)) → ℂ := fun kv c =>
    if kv.1 = k then (if Formalism.CyclotomicNorms.monicOf c = Function.update (0 : Tup2 D) k t kv.1 kv.2 then
      Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf c) else 0) else Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf c) with hG
  have h2 : ∀ a : CV D, (if tupOf a k = t then ∏ kv : (Σ k : Fin 2, D.nd.PlG k), Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))
      else 0) = ∏ kv, G kv (a kv) := by
    intro a
    have hG' : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), G kv (a kv) =
        if (kv.1 = k → Formalism.CyclotomicNorms.monicOf (a kv) = Function.update (0 : Tup2 D) k t kv.1 kv.2) then
          Nc ψ₀ kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) else 0 := by
      intro kv
      by_cases hk : kv.1 = k
      · simp only [hG, hk, if_true, true_implies]
      · simp only [hG, hk, if_false, false_implies, if_true]
    rw [Finset.prod_congr rfl fun kv _ => hG' kv, Finset.prod_ite_zero]
    congr 1
    apply propext
    constructor
    · intro h kv _ hk
      obtain ⟨k', v⟩ := kv
      simp only at hk
      subst hk
      rw [Function.update_self, ← h]
      rfl
    · intro h
      funext v
      have := h ⟨k, v⟩ (Finset.mem_univ _) rfl
      rw [Function.update_self] at this
      exact this
  simp_rw [h2]
  rw [← Fintype.prod_sum]
  refine Finset.prod_congr rfl fun kv _ => ?_
  by_cases hk : kv.1 = k
  · rw [if_pos hk]
    simp only [hG, hk, if_true]
    exact sum_N_single ψ₀ kv.1 _
  · rw [if_neg hk]
    simp only [hG, hk, if_false]
    exact sum_N_all ψ₀ kv.1

end Cyl

section Final

variable (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ)

theorem Nc_real (k : Fin 2) (f : Polynomial (ZMod (D.host.g k))) : Nc ψ₀ k f = ((Nc ψ₀ k f).re : ℂ) := by
  have hc := D.ntypes.eSer_central k f
  have hs := selfadj_of_central_idem _ (D.ntypes.eSer_idem k f) hc
  have h := tau_eJ (kk := D.R.k) (s := D.R.m / 2 - 1) (ψ₀ k) _ (D.ntypes.eSer_idem k f) hc hs
  have hre : Nc ψ₀ k f = ((∑ h, Complex.normSq ((eJ (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) (ψ₀ k) *
      D.ntypes.eSer k f).coeff h) : ℝ) : ℂ) := h
  rw [hre, Complex.ofReal_re]

theorem phiJ_one' {g N kk s : ℕ} : phiJ kk s (1 : Matrix (Fin N) (Fin N) (ZMod g)) = 0 := by
  simp [phiJ, entN, Matrix.one_apply]
  intros
  omega

theorem Zc_eq (k : Fin 2) : Zc ψ₀ k = (((cJ D (D.host.g k) : ℝ)⁻¹ : ℝ) : ℂ) := by
  classical
  unfold Zc
  show (eJ (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) (ψ₀ k)).coeff 1 = _
  rw [eJ_coeff, if_pos (by rw [Units.val_one]; exact jPred_one _ _), card_PJ, Units.val_one, phiJ_one',
    AddChar.map_zero_eq_one, inv_one]
  push_cast
  ring

end Final

section Main

theorem split_prod (F : (Σ k : Fin 2, D.nd.PlG k) → ℂ) :
    ∏ kv : (Σ k : Fin 2, D.nd.PlG k), F kv = (∏ v : D.nd.PlG 0, F ⟨0, v⟩) * ∏ v : D.nd.PlG 1, F ⟨1, v⟩ := by
  rw [Fintype.prod_sigma, Fin.prod_univ_two]

include hS in

theorem etOne_of (hK : KppShape X) (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) (hψ₀ : ∀ k, ψ₀ k ≠ 1) :
    EtOne X ψ₀ := by
  classical
  obtain ⟨P, ψ, hψ, hK⟩ := hK
  have hmem := fun x => (hK x).1
  have hchi := fun x => (hK x).2
  intro k S
  have h1 : eT X (cyl D k (S : Set (Tup D k))) 1 =
      (Ehat hS * ES (cyl D k (S : Set (Tup D k)))).coeff 1 / (V X : ℂ) := by
    have := val_hat hS (biInv_eT X (cyl D k (S : Set (Tup D k)))) (1 : KSub X.B.I)
    rw [map_one, hat_eT'] at this
    exact this
  have h2 : X.B.e 1 = (Ehat hS).coeff 1 / (V X : ℂ) := by
    have := val_hat hS (biInv_e X) (1 : KSub X.B.I)
    rw [map_one, ← Ehat_coeff] at this
    exact this
  rw [h1, h2, val_eT_sum hS ψ₀ P ψ hψ hψ₀ hmem hchi, sum_cyl ψ₀ k S, val_e hS ψ₀ P ψ hψ hψ₀ hmem hchi]
  have hZ : ∀ j : Fin 2, Zc ψ₀ j = (((cJ D (D.host.g j) : ℝ)⁻¹ : ℝ) : ℂ) := Zc_eq ψ₀
  have hzpos : ∀ j : Fin 2, (0 : ℝ) < (cJ D (D.host.g j) : ℝ)⁻¹ := fun j => by
    have := cJ_pos D j; positivity
  have hw : ∀ f, wtOf D k (eJk D k (ψ₀ k)) f = (Nc ψ₀ k f).re / (cJ D (D.host.g k) : ℝ)⁻¹ := by
    intro f
    show (Nc ψ₀ k f).re / (Zc ψ₀ k).re = _
    rw [hZ, Complex.ofReal_re]
  simp only [hw]
  have hV := V_pos X
  have hVc : (V X : ℂ) ≠ 0 := V_ne X
  obtain rfl | rfl : k = 0 ∨ k = 1 := by fin_cases k <;> simp
  · simp only [split_prod, if_true, if_neg (show (1 : Fin 2) ≠ 0 by decide), Function.update_self,
      Finset.prod_const, Finset.card_univ, D.nd.card_PlG, hZ]
    have e1 : ∑ x ∈ S, (∏ v, Nc ψ₀ 0 (x v)) * ((((cJ D (D.host.g 1) : ℝ)⁻¹ : ℝ) : ℂ)) ^ D.R.f =
        ((∑ x ∈ S, (∏ v, (Nc ψ₀ 0 (x v)).re) * ((cJ D (D.host.g 1) : ℝ)⁻¹) ^ D.R.f : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 1
      exact Finset.prod_congr rfl fun v _ => Nc_real ψ₀ 0 _
    rw [e1]
    rw [show ((((cJ D (D.host.g 0) : ℝ)⁻¹ : ℝ) : ℂ)) ^ D.R.f * ((((cJ D (D.host.g 1) : ℝ)⁻¹ : ℝ) : ℂ)) ^ D.R.f / (V X : ℂ) =
      ((((cJ D (D.host.g 0) : ℝ)⁻¹) ^ D.R.f * ((cJ D (D.host.g 1) : ℝ)⁻¹) ^ D.R.f / V X : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_div, Complex.ofReal_re, Complex.ofReal_re]
    simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, D.nd.card_PlG]
    rw [← Finset.sum_div, ← Finset.sum_mul]
    have h0 := hzpos 0
    have h1' := hzpos 1
    field_simp
    rw [mul_div_assoc, div_self (pow_ne_zero _ (one_div_ne_zero (by exact_mod_cast (cJ_pos D 0).ne'))), mul_one]
  · simp only [split_prod, if_true, if_neg (show (0 : Fin 2) ≠ 1 by decide), Function.update_self,
      Finset.prod_const, Finset.card_univ, D.nd.card_PlG, hZ]
    have e1 : ∑ x ∈ S, ((((cJ D (D.host.g 0) : ℝ)⁻¹ : ℝ) : ℂ)) ^ D.R.f * (∏ v, Nc ψ₀ 1 (x v)) =
        ((∑ x ∈ S, ((cJ D (D.host.g 0) : ℝ)⁻¹) ^ D.R.f * (∏ v, (Nc ψ₀ 1 (x v)).re) : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 1
      exact Finset.prod_congr rfl fun v _ => Nc_real ψ₀ 1 _
    rw [e1]
    rw [show ((((cJ D (D.host.g 0) : ℝ)⁻¹ : ℝ) : ℂ)) ^ D.R.f * ((((cJ D (D.host.g 1) : ℝ)⁻¹ : ℝ) : ℂ)) ^ D.R.f / (V X : ℂ) =
      ((((cJ D (D.host.g 0) : ℝ)⁻¹) ^ D.R.f * ((cJ D (D.host.g 1) : ℝ)⁻¹) ^ D.R.f / V X : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_div, Complex.ofReal_re, Complex.ofReal_re]
    simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, D.nd.card_PlG]
    rw [← Finset.sum_div, ← Finset.mul_sum]
    have h0 := hzpos 0
    have h1' := hzpos 1
    field_simp
    rw [mul_div_assoc, div_self (pow_ne_zero _ (one_div_ne_zero (by exact_mod_cast (cJ_pos D 1).ne'))), mul_one]

end Main

end Formalism.L2.SG.Pf.AllRowsEtOne
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsKCRT

open NumberField Matrix IsDedekindDomain Formalism.MainNotions.S Formalism.L2.SG.Pf.unitaryCongruence
open scoped TensorProduct

section Alg

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def pm (u : R) (X : Matrix n n R) : Matrix n n R := 1 + u • (X - 1)

theorem pm_one (u : R) : pm u (1 : Matrix n n R) = 1 := by simp [pm]


theorem one_add_mul_one_add (a b : Matrix n n R) : (1 + a) * (1 + b) = 1 + a + b + a * b := by noncomm_ring

theorem pm_mul {u : R} (hu : u * u = u) (X Y : Matrix n n R) : pm u X * pm u Y = pm u (X * Y) := by
  have e : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1) := by noncomm_ring
  unfold pm
  rw [one_add_mul_one_add, smul_mul_smul_comm, hu, e, smul_add, smul_add]
  abel


theorem cT_pm (σ : R →+* R) {u : R} (hu : σ u = u) (X : Matrix n n R) :
    Formalism.UG.cT σ (pm u X) = pm u (Formalism.UG.cT σ X) := by
  ext a b
  simp only [Formalism.UG.cT, pm, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, smul_eq_mul, map_add, map_mul, map_sub, hu, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp
  · have h' : ¬ b = a := fun e => h e.symm
    simp [h, h']

theorem pm_form {u : R} (hu : u * u = u) (A J X : Matrix n n R) (h : A * J * X = J) :
    pm u A * J * pm u X = J := by
  have e : (A - 1) * J + J * (X - 1) + (A - 1) * J * (X - 1) = A * J * X - J := by noncomm_ring
  have e0 : (A - 1) * J + J * (X - 1) + (A - 1) * J * (X - 1) = 0 := by rw [e, h, sub_self]
  have key : (A - 1) * J * (X - 1) = -((A - 1) * J + J * (X - 1)) := eq_neg_of_add_eq_zero_right e0
  have e3 : ∀ a b : Matrix n n R, (1 + a) * J * (1 + b) = J + a * J + J * b + a * J * b := by
    intro a b; noncomm_ring
  unfold pm
  rw [e3, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_smul, hu, key, smul_neg, smul_add]
  abel

end Alg

section Ad

variable {F : Type} [Field F] [NumberField F]

open LatDictZ.Z5

def Tm (m : ℕ) : Set (HeightOneSpectrum (𝓞 F)) := {v | ((m : ℕ) : 𝓞 F) ∈ v.asIdeal}

theorem natc (m : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (m : Af F) v = algebraMap (𝓞 F) (v.adicCompletion F) (m : 𝓞 F) := by
  rw [map_natCast]
  exact map_natCast (ev v) m

theorem comp_sub (a b : Af F) (v : HeightOneSpectrum (𝓞 F)) : (a - b) v = a v - b v := map_sub (ev v) a b

theorem eT_idem (T : Set (HeightOneSpectrum (𝓞 F))) : eT T * eT T = eT T := by
  refine FiniteAdeleRing.ext (K := F) fun v => ?_
  rw [comp_mul]
  by_cases hv : v ∈ T
  · rw [eT_of_mem hv, one_mul]
  · rw [eT_of_not hv, zero_mul]

theorem not_mem_of_coprime {m₁ m₂ : ℕ} (h : Nat.Coprime m₁ m₂) {v : HeightOneSpectrum (𝓞 F)}
    (h1 : v ∈ Tm (F := F) m₁) : ((m₂ : ℕ) : 𝓞 F) ∉ v.asIdeal := by
  intro h2
  have hz := Nat.gcd_eq_gcd_ab m₁ m₂
  rw [h, Nat.cast_one] at hz
  have hO := congrArg (Int.cast : ℤ → 𝓞 F) hz
  push_cast at hO
  have h1' : ((m₁ : ℕ) : 𝓞 F) ∈ v.asIdeal := h1
  have : (1 : 𝓞 F) ∈ v.asIdeal := by
    rw [hO]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h1') (Ideal.mul_mem_right _ _ h2)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)

open Classical in
theorem compl_eq (m : ℕ) : ∃ c ∈ Formalism.UG.intAd F, 1 - eT (Tm (F := F) m) = (m : Af F) * c := by
  refine ⟨mkI (fun v => if v ∈ Tm (F := F) m then 0 else (algebraMap (𝓞 F) (v.adicCompletion F) (m : 𝓞 F))⁻¹)
    (fun v => by split_ifs with h; exacts [zero_mem _, inv_mem' h]), mkI_mem _ _, ?_⟩
  refine FiniteAdeleRing.ext (K := F) fun v => ?_
  rw [comp_sub, LatDictZ.Z5.comp_one, comp_mul, natc, mkI_apply]
  by_cases hv : v ∈ Tm (F := F) m
  · rw [eT_of_mem hv, if_pos hv, sub_self, mul_zero]
  · rw [eT_of_not hv, if_neg hv, sub_zero, mul_inv_cancel₀ (ne0 hv)]

open Classical in
theorem idem_eq {m₁ m₂ : ℕ} (h : Nat.Coprime m₁ m₂) :
    ∃ c ∈ Formalism.UG.intAd F, eT (Tm (F := F) m₁) = (m₂ : Af F) * c := by
  refine ⟨mkI (fun v => if v ∈ Tm (F := F) m₁ then (algebraMap (𝓞 F) (v.adicCompletion F) (m₂ : 𝓞 F))⁻¹ else 0)
    (fun v => by split_ifs with hv; exacts [inv_mem' (not_mem_of_coprime h hv), zero_mem _]), mkI_mem _ _, ?_⟩
  refine FiniteAdeleRing.ext (K := F) fun v => ?_
  rw [comp_mul, natc, mkI_apply]
  by_cases hv : v ∈ Tm (F := F) m₁
  · rw [eT_of_mem hv, if_pos hv, mul_inv_cancel₀ (ne0 (not_mem_of_coprime h hv))]
  · rw [eT_of_not hv, if_neg hv, mul_zero]

end Ad

section Inst

variable (I : AutInst)

open LatDictZ.Z5

theorem sig_iA (a : Af I.F) : Formalism.UG.sigR I.cm.sig (Af I.F) (iA I a) = iA I a := by
  simp [Formalism.UG.sigR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

theorem fmat_mul_inv' (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  rw [← fmat_mul, mul_inv_cancel, fmat_one]

def mkG (u : I.E ⊗[I.F] Af I.F) (hu : u * u = u) (hσ : Formalism.UG.sigR I.cm.sig (Af I.F) u = u) (x : I.Gf) : I.Gf :=
  ⟨⟨pm u (I.fmat x), pm u (I.fmat x⁻¹),
    by rw [pm_mul hu, fmat_mul_inv', pm_one], by rw [pm_mul hu, fmat_inv_mul, pm_one]⟩, by
    have hx : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.fmat x) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        I.fmat x = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := x.2
    show Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (pm u (I.fmat x)) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        pm u (I.fmat x) = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))
    rw [cT_pm _ hσ]
    exact pm_form hu _ _ _ hx⟩


theorem smul_Lf {u : I.E ⊗[I.F] Af I.F} (hI : u ∈ IntAf I.F I.E) {y : Fin I.n → I.E ⊗[I.F] Af I.F}
    (hy : y ∈ I.Lf) : u • y ∈ I.Lf :=
  I.Lf.smul_mem ⟨u, hI⟩ hy





end Inst

end Formalism.L2.SG.Pf.AllRowsKCRT
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsClosed

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

theorem rhoSurj_X : Function.Surjective (AllRowsRhoX.rhoX X) := Formalism.L2.SG.Pf.RhoSurjW.reduction_map_surjective D X

theorem redKerOne_holds : RedKerOne X := redKerOne_of (X := X) (AllRowsRedKer.redKerP_holds X 0) (AllRowsRedKer.redKerP_holds X 1)

theorem etUniv_holds : EtUniv X := etUniv_of (X := X) (redKer_of (X := X) (redKerOne_holds X))

theorem etUnip_holds (k : Fin 2) (S : Set (Tup D k)) : EtUnip X k S := etUnip_of (X := X) k (AllRowsRedKer.redKerP_holds X (1 - k)) S

theorem kppShape_holds : AllRowsKpp.KppShape X := Formalism.L2.SG.Pf.AllRowsKpp.kppShape_of_fwd (X := X) (rhoSurj_X X) (Formalism.L2.SG.Pf.KppFwdPf.kppFwd_holds (X := X))

theorem etAlg_holds (S : Set (Tup2 D)) : EtAlg X S := Formalism.L2.SG.Pf.AllRowsEtAlg.etAlg_of (X := X) (rhoSurj_X X) S

theorem etOne_holds (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) (hψ₀ : ∀ k, ψ₀ k ≠ 1) : EtOne X ψ₀ := Formalism.L2.SG.Pf.AllRowsEtOne.etOne_of (X := X) (rhoSurj_X X) (kppShape_holds X) ψ₀ hψ₀



def allRowsOfL (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) (hψ₀ : ∀ k, ψ₀ k ≠ 1) (hL : RowsLab X) : AllRows D :=
  allRowsOfP X ψ₀ (AllRowsRedKer.redKerP_holds X 0) (AllRowsRedKer.redKerP_holds X 1) (etOne_holds X ψ₀ hψ₀) hL


end Formalism.L2.SG.Pf.AllRowsClosed
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsLab

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

theorem rowsGood_holds (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (G : Formalism.L2.SG.RowDict.GoodOp X)
    (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) (hT : Formalism.L2.SG.RowDict.RowDictTie X G ι)
    (hL : Formalism.L2.SG.Pf.RowsGoodRed.LabTie X ι) : RowsGood X :=
  Formalism.L2.SG.Pf.RowsGoodRed.rowsGood_of X G ι hT hL (Formalism.L2.SG.Pf.AllRowsAdd.projT_holds X G)
    (Formalism.L2.SG.Pf.AllRowsDcount.dcountEq_holds X hG)

theorem rowsLab_holds (hHC : Formalism.L2.SG.RowsDef.RowsFinDim) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (G : Formalism.L2.SG.RowDict.GoodOp X) (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X)
    (hT : Formalism.L2.SG.RowDict.RowDictTie X G ι) (hL : Formalism.L2.SG.Pf.RowsGoodRed.LabTie X ι)
    (hAT : AutTie D X.B X.pl) : RowsLab X :=
  rowsLab_of X (Formalism.L2.SG.Pf.AllRowsAddFin.rowsAdd_holds X hHC hG) (rowsGood_holds X hG G ι hT hL)
    (Formalism.L2.SG.Pf.AllRowsClosed.etUniv_holds X) hAT

end Formalism.L2.SG.Pf.AllRowsLab
end
end
