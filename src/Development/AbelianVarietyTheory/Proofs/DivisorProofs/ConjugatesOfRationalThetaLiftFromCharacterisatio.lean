import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IpMSelfEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueBarCompatibility
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaValuesCoefficientExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsEvaluateFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsEvaluateSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfConjOnFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefAtOfPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResEtaHasInfExpOfIsEtaConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HvMemOfInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CircleEqOneIffOfConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsWeightCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatiblePhaseExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaPForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JEvExistsAndJEvBar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsIndependentAndSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JEvExistsAndJEvBar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvInjOfIsModelsOfTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasisOfFive
import Development.AbelianVarietyTheory.Definitions.Divisors.OfCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientConjugateThetaForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjFormsRescale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolShapeOfOverK

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
open Formalism.IndefR.Arith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GalLift.Assembly

section Abstract

variable {L : Type} [Field L] {G : Type} [Group G] [Fintype G] {C Y H : Type} [AddCommGroup Y] [Module L Y]
  [AddCommGroup H] [Module ℂ H]

theorem read_sum (σ : L →+* ℂ) (J : Y →ₛₗ[σ] H) (ι : C → Y) (act : G → C → C) (chi : G →* Lˣ) (ρ : Representation ℂ G H)
    (h : ∀ g f, J (ι (act g f)) = σ (chi g : L) • ρ g (J (ι f))) (e : G → L) {n : ℕ} (b : Fin n → L) (f : Fin n → C) :
    J (∑ g, (e g * (((chi g)⁻¹ : Lˣ) : L)) • ∑ k, b k • ι (act g (f k))) =
      ∑ g, σ (e g) • ρ g (∑ k, σ (b k) • J (ι (f k))) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smulₛₗ, map_sum, map_sum, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ, h, map_smul, smul_smul, smul_smul, smul_smul, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  have := (chi g).inv_mul
  linear_combination (e g * b k) * this

theorem shift_sum (ρ : Representation ℂ G H) (e : G → ℂ) {z₀ z : G} (h₀ : z₀ ∈ Subgroup.center G) (hz : z ∈ Subgroup.center G)
    (α β κ : ℂ) (hβ : β ≠ 0) (S T : H) (hT : κ • T = ∑ g, e g • ρ g (β • ρ z S)) :
    ∑ g, e g • ρ g (α • ρ z₀ S) = (α * β⁻¹ * κ) • ρ (z₀ * z⁻¹) T := by
  rw [mul_smul, ← map_smul (ρ (z₀ * z⁻¹)) κ, hT, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have h1 : ρ (z₀ * z⁻¹) (ρ g (ρ z S)) = ρ g (ρ z₀ S) := by
    have e1 : z₀ * z⁻¹ * (g * z) = g * z₀ := by
      rw [Subgroup.mem_center_iff.1 hz g, Subgroup.mem_center_iff.1 h₀ g]; group
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_assoc, e1, map_mul, Module.End.mul_apply]
  simp only [map_smul, h1, smul_smul]
  congr 1
  field_simp

theorem norm_of_pow {a : ℂ} {m : ℕ} (hm : 0 < m) (h : a ^ m = 1) : ‖a‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg a) hm.ne').1 (by rw [← norm_pow, h, norm_one])

theorem norm_chi (σ : L →+* ℂ) (chi : G →* Lˣ) (g : G) : ‖σ (chi g : L)‖ = 1 :=
  norm_of_pow (m := Fintype.card G) Fintype.card_pos (by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one, map_one])

variable {P : Type} [AddCommGroup P] [Module ℂ P]

theorem conj_abstract (σ : L →+* ℂ) (J : Y →ₛₗ[σ] H) (ι : C → Y) (act : G → C → C) (chi : G →* Lˣ) (ρ : Representation ℂ G H)
    (h : ∀ g f, J (ι (act g f)) = σ (chi g : L) • ρ g (J (ι f))) (e : G → L) (ev : H →ₗ[ℂ] P) (hev : Function.Injective ev)
    (W : P →ₗ[ℂ] P) (hW : ∀ y, W (ev y) = ev (∑ g, σ (e g) • ρ g y)) {z₀ z : G} (h₀ : z₀ ∈ Subgroup.center G)
    (hz : z ∈ Subgroup.center G) (ze : L) (κ : ℂ) {n : ℕ} (a : Fin n → L) (f : Fin n → C) (θ : P)
    (hθ : κ • θ = ∑ k, σ (a k) • ev (J (ι (act z (f k))))) (T : H) (hT : ev T = W θ) :
    J (∑ g, (e g * (((chi g)⁻¹ : Lˣ) : L)) • ∑ k, (ze * a k) • ι (act g (act z₀ (f k)))) =
      (σ ze * σ (chi z₀ : L) * (σ (chi z : L))⁻¹ * κ) • ρ (z₀ * z⁻¹) T := by
  have e1 : ∑ k, σ (a k) • ev (J (ι (act z (f k)))) = ev (σ (chi z : L) • ρ z (∑ k, σ (a k) • J (ι (f k)))) := by
    rw [map_sum, Finset.smul_sum, map_sum]
    exact Finset.sum_congr rfl fun k _ => by simp only [h, map_smul]; rw [smul_comm]
  have h3 : ∑ k, σ (ze * a k) • J (ι (act z₀ (f k))) = (σ ze * σ (chi z₀ : L)) • ρ z₀ (∑ k, σ (a k) • J (ι (f k))) := by
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [h, map_smul, smul_smul, smul_smul, map_mul]
    congr 1
    ring
  rw [read_sum σ J ι act chi ρ h e (fun k => ze * a k) (fun k => act z₀ (f k)), h3]
  refine shift_sum ρ _ h₀ hz _ _ κ (norm_ne_zero_iff.1 (by rw [norm_chi]; exact one_ne_zero)) _ _ (hev ?_)
  rw [map_smul, hT, ← map_smul, hθ, e1, hW]

theorem exists_ev (ev : H →ₗ[ℂ] P) {κ : ℂ} (hκ : ‖κ‖ = 1) {n : ℕ} (a : Fin n → ℂ) (t : Fin n → H) (θ : P)
    (hθ : κ • θ = ∑ k, a k • ev (t k)) : ∃ s, ev s = θ := by
  have hκ0 : κ ≠ 0 := norm_ne_zero_iff.1 (by rw [hκ]; exact one_ne_zero)
  refine ⟨κ⁻¹ • ∑ k, a k • t k, ?_⟩
  rw [map_smul, map_sum, ← inv_smul_smul₀ hκ0 θ, hθ]
  simp only [map_smul]

def evL {I : Type} {M : I → Type} [∀ τ, AddCommGroup (M τ)] [∀ τ, Module ℂ (M τ)] (e : H →ₗ[ℂ] MultilinearMap ℂ M P)
    (v : ∀ τ, M τ) : H →ₗ[ℂ] P where
  toFun y := e y v
  map_add' x y := by rw [map_add]; rfl
  map_smul' a x := by rw [map_smul]; rfl

end Abstract

section Main

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

def crdF (fw : FWTie T R κw v₀) (i : Fin D.R.m) (f : Cu T κw i) : Fin (R.nW i) → D.what₂.LL := (fw.e i f : (R.FW i).WK)

def ratOf (fw : FWTie T R κw v₀) (i : Fin D.R.m) (act : G → Cu T κw i → Cu T κw i) (z : G) (ze : D.what₂.LL) {n : ℕ}
    (a : Fin n → D.what₂.LL) (f : Fin n → Cu T κw i) : Fin (R.nW i) → D.what₂.LL :=
  ∑ g, ((idemOf A.X).coeff g * ((((R.FW i).chi g)⁻¹ : D.what₂.LLˣ) : D.what₂.LL)) •
    ∑ k, (ze * a k) • crdF fw i (act g (act z (f k)))

theorem sign_at_base_place_eq_embedding (R : RealDat D A T.Q.c.F) : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0

theorem exists_reps {i : Fin D.R.m} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} (hP : OMPins T R κw v₀ O i) :
    ∃ h, RepsAt (O i) (v₀ i (sg0 D A)) h := (hP.2.tuple ()).reps

end Main

section Final

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem smul_inv_of {H : Type} [AddCommGroup H] [Module ℂ H] (L : H →ₗ[ℂ] H) {κ κ' : ℂ} (h : ‖κ'‖ = 1) {a b : H}
    (e : b = κ' • a) : κ • L a = (κ * κ'⁻¹) • L b := by
  have h0 : κ' ≠ 0 := norm_ne_zero_iff.1 (by rw [h]; exact one_ne_zero)
  rw [e, map_smul, smul_smul, mul_assoc, inv_mul_cancel₀ h0, mul_one]

end Final

end GlobalTheory.GalLift.Assembly

end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MovedWeights

open Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift in

theorem exists_io_conj_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → HypConj R i σ μ' η' → ∀ (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁ → ∀ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω → VecData R i σ f₀ f B → ∃ io, IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ B f) (deltaConj i σ) io := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i σ _ μ' η' _ hH c c₁ hc ω f₀ f B hω hv
  have hM := hR.models
  have hθ : IsInfFam R.θ := hM.inf
  have hψ : IsStdChar D R.ψ (-1) := hv.vec.1.1
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) f :=
    hv.vec.2.elim fun _ h => isThetaFunO_of_isThetaAt hψ hθ h.2 hv.vec.1.2.theta
  have hBS : ∀ τ, (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = 1 := fun τ => onb_eq_one (hM.BV i τ)
  have hBu : ∀ τ, IsUnit (R.BV i τ) := fun τ => (IsUnit.of_mul_eq_one_right _ (hBS τ))
  have hw := fun ρ => weights_label D i (lab σ ρ) (pW D i ρ) (qW D i ρ)
    (congrArg Prod.fst ((hH.sig ρ).trans (hH.sig _).symm)) (congrArg Prod.snd ((hH.sig ρ).trans (hH.sig _).symm))
    ((R.MW i σ).lam ρ) ((R.MW i σ).ε ρ) (by have := (R.MW i σ).enum ρ; rw [hH.par ρ] at this; exact this)
  choose x₁ x₂ x₃ hx₁ hx₂ hx₃ hK hU hpq hε hap ham using hw
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hj := exists_poly_model (Vc D i) R.θ c (lamV D i) σ (Equiv.ofBijective _ hH.lab_bij) hH.lab_at c₁ hθ
    hc.coef hc.act hc.indep hc.span (R.BV i) hBu
  obtain ⟨j, hj1, hj2⟩ := hj
  exact exists_isIoW D (Vc D i) (Wc D i) R.ψ R.θ _ (R.MW i σ) c (lamV D i) (Equiv.ofBijective _ hH.lab_bij) (R.BV i) B
    j hj1 hj2 _ _ _ _ x₁ x₂ x₃ (hrk.le.trans (r_le_V i)) hpq hε hap ham hK hU _ _ ω hω hψ hθ
    (D.sp.V_sig _) (D.sp.W_sig _) hBS hv.onb _ _ hH.mu_inf
    (fun τ => GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hH.mu_inf τ) (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hH.eta_inf τ)))
    hx₁ hx₂ hx₃ f hth (GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv.vec hth)

end GlobalTheory.MovedWeights

end
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.GalLift.overK_iff_good_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ ↔ GoodEmb T.Q.c (res T σ) :=
  GlobalTheory.GalLift.overK_iff_good_ofFive

theorem GlobalTheory.EtaValues.etaVals_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), EtaVals R := by
  classical
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR _ P e he x hx
  have htie := hR.fam.tie
  obtain ⟨_, _, _, hT⟩ := htie
  have hok := hT.ok A.μ0
  have h := GlobalTheory.EtaValues.hv_mem_host D R.C.eta R.C.isEta (R.Sb ∪ R.Q A.μ0) (fun v hs => by
    rw [Finset.coe_union] at hs
    obtain ⟨Q, rfl⟩ := hR.fam.pl_onto v (GlobalTheory.EtaValues.splitOff_mono hs Set.subset_union_left)
    exact ⟨_, (hR.fam.etaVal Q ((hok Q).2 hs)).trans (GlobalTheory.EtaValues.valTw_eq _ _)⟩) P
  obtain ⟨y, hy⟩ := h
  refine ⟨y, hy.trans ?_⟩
  rw [hR.lev.eta.2 P e he _ x hx]
  rfl

theorem GlobalTheory.EtaConjExist.exists_isEtaConj_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), EtaVals R → ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∃ η', IsEtaConj σ R.eta η' := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR _ hV σ hσ
  refine GlobalTheory.EtaConjExist.exists_conj R.eta R.C.eta hR.lev.eta R.C.isEta (fun P => ?_) σ hσ
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  obtain ⟨y, hy⟩ := hV P e he (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl
  refine ⟨y, hy.trans ?_⟩
  rw [hR.lev.eta.2 P e he _ (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl]
  rfl

theorem GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ η', IsEtaConj σ R.eta η' → ResEta D η' 1 ∧ ∀ ρ, HasInfExp D η' ρ (1 / 2) :=
  GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj_ofFive

theorem GlobalTheory.GalLift.hypConj_of_chars_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), Function.Bijective (lab (D := D) σ) → (∀ ρ, labE σ (lab σ ρ) = tauE D ρ) → logHookSum i (lab σ) = logHookSum i id ∧ ∀ (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → ResEta D η' 1 → (∀ ρ, HasInfExp D η' ρ (1 / 2)) → HypConj R i σ μ' η' :=
  GlobalTheory.GalLift.hypConj_of_chars_ofFive

theorem GlobalTheory.ConjCharUnique.conjChar_unique_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), (∀ μ' μ'', ChiAt R i σ μ' → ChiAt R i σ μ'' → μ' = μ'') ∧ ∀ η' η'', IsEtaConj σ R.eta η' → IsEtaConj σ R.eta η'' → η' = η'' :=
  GlobalTheory.ConjCharUnique.conjChar_unique_ofFive

theorem GlobalTheory.GalLift.ConjWeil.exists_conj_weil_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → HypConj R i σ μ' η' → ∃ ω, IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i σ μ' η' hμ hη hH
  have hV : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  exact GlobalTheory.GalLift.ConjWeil.exists_of_datum (hR.thP.ωP i A.μ0) hμ.1 (GlobalTheory.GalLift.ConjWeil.hecke_mul_inv hμ.1 hη.1)
    (resEta_parity hH.mu_res ((GlobalTheory.GalLift.ConjWeil.even_im_hermitian_sub D.R).1.trans (congrArg (· % 2) hV.symm)))
    (resEta_parity (resEta_mul hH.mu_res (resEta_inv hH.eta_res))
      ((GlobalTheory.GalLift.ConjWeil.even_im_hermitian_sub D.R).2.trans (congrArg (· % 2) hW.symm)))

theorem GlobalTheory.GalLift.reading_base_injective_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → JUnif T R κw v₀ → Function.Injective ((R.FW i).j (sg0 D A)) := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ _ fw i hev hinj hu
  have hg : GoodEmb T.Q.c (res T (sg0 D A)) := base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := fw.laws.spaceW _ (inR i) _ hg
  have h1 := fw.jK_eq hev hinj hg hV
  have h2 : ∀ f, fw.jK i (sg0 D A) f = (1 : ℂ) • jTop T R κw v₀ i (sg0 D A) f := fun f =>
    (LinearMap.congr_fun h1 f).trans (one_smul ℂ _).symm
  have h3 := GlobalTheory.TiedUnif.indep_span (C := Cu T κw i) (R.FW i) (fw.ks i) (fw.e i) (sg0 D A) one_ne_zero h2
    (hu i _).1 (hu i _).2
  exact GlobalTheory.TiedUnif.injective_of_indep (W := fun σ => (R.HW i σ).H) _ h3.1

theorem GlobalTheory.GalLift.conjChars_five : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ ↔ GoodEmb T.Q.c (res T σ)) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), EtaVals R) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), EtaVals R → ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∃ η', IsEtaConj σ R.eta η') ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ η', IsEtaConj σ R.eta η' → ResEta D η' 1 ∧ ∀ ρ, HasInfExp D η' ρ (1 / 2)) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), Function.Bijective (lab (D := D) σ) → (∀ ρ, labE σ (lab σ ρ) = tauE D ρ) → logHookSum i (lab σ) = logHookSum i id ∧ ∀ (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → ResEta D η' 1 → (∀ ρ, HasInfExp D η' ρ (1 / 2)) → HypConj R i σ μ' η') ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), (∀ μ' μ'', ChiAt R i σ μ' → ChiAt R i σ μ'' → μ' = μ'') ∧ ∀ η' η'', IsEtaConj σ R.eta η' → IsEtaConj σ R.eta η'' → η' = η'') ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → HypConj R i σ μ' η' → ∃ ω, IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → JUnif T R κw v₀ → Function.Injective ((R.FW i).j (sg0 D A))) :=
  ⟨GlobalTheory.GalLift.overK_iff_good_five, GlobalTheory.EtaValues.etaVals_five, GlobalTheory.EtaConjExist.exists_isEtaConj_five,
    GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj_five, GlobalTheory.GalLift.hypConj_of_chars_five,
    GlobalTheory.ConjCharUnique.conjChar_unique_five, GlobalTheory.GalLift.ConjWeil.exists_conj_weil_five,
    GlobalTheory.GalLift.reading_base_injective_five⟩

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateCharacters_embeddings_of_characterisation : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ ↔ GoodEmb T.Q.c (res T σ)) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), EtaVals R) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), EtaVals R → ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∃ η', IsEtaConj σ R.eta η') ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ η', IsEtaConj σ R.eta η' → ResEta D η' 1 ∧ ∀ ρ, HasInfExp D η' ρ (1 / 2)) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), Function.Bijective (lab (D := D) σ) → (∀ ρ, labE σ (lab σ ρ) = tauE D ρ) → logHookSum i (lab σ) = logHookSum i id ∧ ∀ (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → ResEta D η' 1 → (∀ ρ, HasInfExp D η' ρ (1 / 2)) → HypConj R i σ μ' η') ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), (∀ μ' μ'', ChiAt R i σ μ' → ChiAt R i σ μ'' → μ' = μ'') ∧ ∀ η' η'', IsEtaConj σ R.eta η' → IsEtaConj σ R.eta η'' → η' = η'') ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → HypConj R i σ μ' η' → ∃ ω, IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → JUnif T R κw v₀ → Function.Injective ((R.FW i).j (sg0 D A))) := by
  atlas_forward_decl GlobalTheory.GalLift.conjChars_five
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefModel

theorem exists_coefAt_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∃ (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁ :=
  fun _ _ hR i _ _ _ _ σ hσ => exists_coefAt_of_posDef i (hR.models.vpos i) σ hσ

end GlobalTheory.CoefModel

namespace GlobalTheory.ConjForms

set_option maxHeartbeats 2000000 in

theorem exists_conjForms_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁ → ∃ (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L i) c c₁ H j := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i gramR c0R c0L hT σ c c₁ hc
  have h1 := hT.coefL i A.μ0
  obtain ⟨e, -, he, -⟩ := h1
  have hact : ∀ γ : GQ (Vc D i), ∃ T : VsV D i D.what₂.LL → VsV D i D.what₂.LL,
      (∀ v, c0L i (T v) = (R.cV i).coef.ρ γ (c0L i v)) ∧ ∀ v, c₁ (T v) = c.coef.ρ γ (c₁ v) := fun γ =>
    (exists_ratMat (Vc D i) γ).elim fun γE hγ =>
      ⟨rhoVr (labLL D) (lamV D i) γE, (hT.mapL i).1 γ γE hγ, hc.act γ γE hγ⟩
  have h2 := exists_baseChange (W' := c.W) σ c.coef.ρ (R.B.L i A.μ0).pres (c0L i) c₁ e he hact
    (levChar_mem R hC.lev hC.grp.chiW i)
  obtain ⟨H, j, hm, hb⟩ := h2
  refine ⟨H, j, hc.coef, hc.act, hc.indep, hc.span, hc.pair, hm, fun x h => ?_⟩
  exact (hb x h).imp fun v hv => ⟨(congrFun (hC.models.jV i A.μ0 x) h).trans hv.1, hv.2⟩

end GlobalTheory.ConjForms

namespace GlobalTheory.GalLift

theorem conjForms_rescale_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ gramR' c0R' c0L', Comparison₂ R gramR' c0R' c0L' → ∀ (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L' i) c c₁ H j → ∃ c₁' : VsV D i D.what₂.LL →ₛₗ[σ] c.W, IsConjForms R i σ (c0L i) c c₁' H j := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F _ i gramR c0R c0L ht gramR' c0R' c0L' ht' σ c c₁ H j hf
  have h1 := ht.coefL i A.μ0
  have h2 := ht'.coefL i A.μ0
  have m1 := ht.mapL i
  have m2 := ht'.mapL i
  obtain ⟨e, he1, he2, he3, -⟩ := h1
  obtain ⟨e', he1', he2', he3', -⟩ := h2
  have key := rescale_abstract _ (bVV D.what₂.LL (lamV D i)) D.what₂.embLL σ _ (c0L i) (c0L' i) _ _ e e' he1 he1' he2 he2'
    he3 he3' m2.2.1 c₁ hf.indep hf.span hf.pair
  obtain ⟨c₁', k1, k2, k3, k4, k5⟩ := key
  refine ⟨c₁', ⟨hf.coef, fun γ γE hγ => ?_, k1, k2, k3, hf.model, fun x h => ?_⟩⟩
  · exact k5 _ _ _ (m1.1 γ γE hγ) (m2.1 γ γE hγ) (hf.act γ γE hγ)
  · have hb := hf.base x h
    obtain ⟨v', a1, a2⟩ := hb
    have hv := k4 v'
    obtain ⟨v, b1, b2⟩ := hv
    exact ⟨v, a1.trans b1, a2.trans b2⟩

end GlobalTheory.GalLift

namespace GlobalTheory.GalLift.Vec

theorem exists_vecData_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∃ f₀ f B, VecData R i σ f₀ f B := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ _
  have hθ : IsInfFam R.θ := hC.models.inf
  have hψ : IsStdChar D R.ψ (-1) := (hC.thP.ωP i A.μ0).std
  have hQ : R.Q A.μ0 = ∅ := Finset.eq_empty_iff_forall_notMem.2 fun PP hPP =>
    (hC.lev.Q_ram A.μ0 PP).2 (Or.inl hPP) (by rw [hC.lev.xi_base]; exact fun _ _ => rfl)
  have h0 := (hC.thP.vP i A.μ0).2
  obtain ⟨e, he, -⟩ := h0
  rw [hQ] at he
  have sdV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have sdW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  have hc := GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MW i σ)
  have h1 := GlobalTheory.Member.vacuum_oriented_exists D R.ψ R.θ hψ hθ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ))
    (D.sp.V_sig _) (D.sp.W_sig _) (fun τ => isCartanInv_one (hC.models.BV i τ)) hc _ _ sdV sdW
  obtain ⟨f₀, hf₀⟩ := h1
  have h2 := GlobalTheory.PlaceVec.thPVecExists D R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) _ _ (R.βV i) (R.βW i)
    R.Pg ∅ (fun _ => 1) sdV sdW (hC.lev.βV i).choose_spec.1 (hC.lev.βW i).choose_spec.1 (Finset.disjoint_empty_right _)
    ⟨e, he⟩ f₀ hf₀
  obtain ⟨f, hf⟩ := h2
  have h3 := fun ρ => exists_isONBasis (hc ρ) (D.sp.W_sig _ (tauE D ρ))
  choose B hB using h3
  have h4 := hf.2
  obtain ⟨e', -, h5⟩ := h4
  exact ⟨f₀, f, B, hf, hB, theta_pureTensorO hψ hθ _ _ _ _ (theta_of_thetaAt hψ hθ h5 hf₀.2.theta)⟩

end GlobalTheory.GalLift.Vec

namespace GlobalTheory.ConjThetaIntegral
open scoped Topology ComplexOrder

theorem exists_isThetaP_conj_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE D)ˣ →* Circle) (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ c₀ c c₁ H j → ∀ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω → VecData R i σ f₀ f B → ∃ thP, Lift.IsThetaP (R.νV i A.μ0) (R.fdV i A.μ0) (fun g h φ => thetaKO ω h g φ) (ptAt R i σ B f) io (LinearMap.range (c.ext ∘ₗ H.e)) thP := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i σ μ' η' c₀ c c₁ H j hj ω f₀ f B io hω hv
  have hm := hj.model
  obtain ⟨χ', hχ, hH⟩ := hm
  exact IsThetaP₂ hω (D.sp.V_sig _) (hR.models.vpos i) c hj.coef (R.βV i) (R.datVt i A.μ0) χ'
    (fun k hk => Units.ext (conjVal_one (hχ k) (congrArg Units.val hk))) H.e
    (fun x => hH.2.1.le (LinearMap.mem_range_self _ x))
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) B f) hv.theta io (hR.models.νV i A.μ0)

end GlobalTheory.ConjThetaIntegral

namespace GlobalTheory.GalLift.ProjLift

set_option maxHeartbeats 1600000 in

theorem exists_isProjOf_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L i) c c₁ H j → ∀ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))), LiftData R i σ μ' η' c H ω f₀ f B io thP → ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, IsExtVec (R.MW i σ) (fun ρ => v ρ) → (∀ x, ∃ t : (R.HW i σ).H, (R.HW i σ).e t (fun ρ => v ρ) = thP ((c.ext ∘ₗ H.e).rangeRestrict (j x)) (PiTensorProduct.tprod ℂ v)) → ∃ th, IsProjOf R i σ thP th := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i gramR c0R c0L hT σ hσ μ' η' c c₁ H j hj ω f₀ f B io thP hL v hv h
  have hspan := GlobalTheory.ConjSpan.span_conjForms R hC.models.jV gramR c0R c0L hT i σ c c₁ H j hj
  have hlow := GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ _ (holShape_of_overK R i hσ)
  have he : ∀ τ, v τ ≠ 0 := fun τ h0 => by
    have := (hv τ).1
    simp [h0] at this
  have hex := exists_lift hlow.1 hlow.2 (R.HW i σ).e
    (fun t => (hC.models.HW i σ).2.1.le (LinearMap.mem_range_self _ t)) (thP ∘ₗ (c.ext ∘ₗ H.e).rangeRestrict)
    (fun y => kEquiv_thetaP hL.2.2.1 hL.2.2.2 _) j hspan v he h
  obtain ⟨φ, hφ⟩ := hex
  exact ⟨(∑ g, RealDat.eC (A := A) σ g • R.gW i σ g) ∘ₗ φ, fun x u =>
    (proj_apply R hC.models.gW i σ (φ x) _).trans (congrArg (R.eWf i σ) (hφ x u))⟩

end GlobalTheory.GalLift.ProjLift

namespace GlobalTheory.GalLift

theorem conjLift_five : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A
    : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks
    D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ
    : D.what₂.LL →+* ℂ), OverK σ → ∃ (c : CoefA (Vc D i)) (c₁
    : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype
    G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField
    Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ : D.what₂.LL →+* ℂ) (c
    : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁ → ∃ (H : HMod (Bridge.Gf
    (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L
    i) c c₁ H j) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A
    : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks
    D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ gramR' c0R' c0L', Comparison₂ R gramR' c0R' c0L' → ∀ (σ
    : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H
    : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L'
    i) c c₁ H j → ∃ c₁' : VsV D i D.what₂.LL →ₛₗ[σ] c.W, IsConjForms R i σ (c0L
    i) c c₁' H j) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A
    : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks
    D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∃ f₀ f B, VecData R i σ f₀ f B) ∧ (∀ {D
    : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks
    : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F
    : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE
    D)ˣ →* Circle) (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) (c : CoefA (Vc D i)) (c₁
    : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j
    : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ c₀ c c₁ H j → ∀ (ω : GA D (Vc D
    i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D
    i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i
    σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), IsWeilDatumO R.ψ (Vc D i) (Wc D
    i) μ' (μ' * η'⁻¹) ω → VecData R i σ f₀ f B → ∃ thP, Lift.IsThetaP (R.νV i A.μ0) (R.fdV i
    A.μ0) (fun g h φ => thetaKO ω h g φ) (ptAt R i σ B f) io (LinearMap.range (c.ext ∘ₗ
    H.e)) thP) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A
    : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks
    D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ
    : D.what₂.LL →+* ℂ), OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (c₁
    : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j
    : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L i) c c₁ H j → ∀ (ω : GA D (Vc D
    i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D
    i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i
    σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP : LinearMap.range (c.ext ∘ₗ
    H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) →
    ℂ))), LiftData R i σ μ' η' c H ω f₀ f B io thP → ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, IsExtVec (R.MW i
    σ) (fun ρ => v ρ) → (∀ x, ∃ t : (R.HW i σ).H, (R.HW i σ).e t (fun ρ => v ρ) = thP ((c.ext ∘ₗ
    H.e).rangeRestrict (j x)) (PiTensorProduct.tprod ℂ v)) → ∃ th, IsProjOf R i σ thP th) :=
  ⟨GlobalTheory.CoefModel.exists_coefAt_five,
   GlobalTheory.ConjForms.exists_conjForms_five,
   GlobalTheory.GalLift.conjForms_rescale_five,
   GlobalTheory.GalLift.Vec.exists_vecData_five,
   GlobalTheory.ConjThetaIntegral.exists_isThetaP_conj_five,
   GlobalTheory.GalLift.ProjLift.exists_isProjOf_five⟩

end GlobalTheory.GalLift

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateLift_of_characterisationClauses : (∀ {D : D7} {G
    : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks
    : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F
    : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ
    : D.what₂.LL →+* ℂ), OverK σ → ∃ (c : CoefA (Vc D i)) (c₁
    : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype
    G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField
    Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ : D.what₂.LL →+* ℂ) (c
    : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁ → ∃ (H : HMod (Bridge.Gf
    (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L
    i) c c₁ H j) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A
    : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks
    D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ gramR' c0R' c0L', Comparison₂ R gramR' c0R' c0L' → ∀ (σ
    : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H
    : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L'
    i) c c₁ H j → ∃ c₁' : VsV D i D.what₂.LL →ₛₗ[σ] c.W, IsConjForms R i σ (c0L
    i) c c₁' H j) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A
    : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks
    D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∃ f₀ f B, VecData R i σ f₀ f B) ∧ (∀ {D
    : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks
    : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F
    : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE
    D)ˣ →* Circle) (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) (c : CoefA (Vc D i)) (c₁
    : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j
    : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ c₀ c c₁ H j → ∀ (ω : GA D (Vc D
    i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D
    i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i
    σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), IsWeilDatumO R.ψ (Vc D i) (Wc D
    i) μ' (μ' * η'⁻¹) ω → VecData R i σ f₀ f B → ∃ thP, Lift.IsThetaP (R.νV i A.μ0) (R.fdV i
    A.μ0) (fun g h φ => thetaKO ω h g φ) (ptAt R i σ B f) io (LinearMap.range (c.ext ∘ₗ
    H.e)) thP) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A
    : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks
    D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ
    : D.what₂.LL →+* ℂ), OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (c₁
    : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j
    : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L i) c c₁ H j → ∀ (ω : GA D (Vc D
    i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D
    i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i
    σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP : LinearMap.range (c.ext ∘ₗ
    H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) →
    ℂ))), LiftData R i σ μ' η' c H ω f₀ f B io thP → ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, IsExtVec (R.MW i
    σ) (fun ρ => v ρ) → (∀ x, ∃ t : (R.HW i σ).H, (R.HW i σ).e t (fun ρ => v ρ) = thP ((c.ext ∘ₗ
    H.e).rangeRestrict (j x)) (PiTensorProduct.tprod ℂ v)) → ∃ th, IsProjOf R i σ thP th) := by
  atlas_forward_decl GlobalTheory.GalLift.conjLift_five
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift

theorem act_eq_translation_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), (∀ g, ∃ k, IsLiftW R i g k) ∧ ∀ (σ : D.what₂.LL →+* ℂ), (∀ g k, IsLiftW R i g k → ∀ y v h, (R.HW i σ).e (R.gW i σ g y) v h = (R.HW i σ).e y v (h * k)) ∧ ∀ y v, R.eWf i σ ((R.HW i σ).e y v) = (R.HW i σ).e (∑ g, RealDat.eC (A := A) σ g • R.gW i σ g y) v := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i
  exact ⟨fun g => Transl.lifts R i hC.lev (R.eG g), fun σ =>
    ⟨Transl.transl R i hC.models.HW hC.models.gW σ, Transl.proj R i hC.models.gW σ⟩⟩

end GlobalTheory.GalLift

namespace GlobalTheory.GalLift.BaseDatum

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

set_option maxHeartbeats 2000000 in
theorem isConjForms_base_five {F : Face D A} (hC : GlobalTheory.Core5 R F) {gramR c0R c0L} (hT : Comparison₂ R gramR c0R c0L) :
    IsConjForms R i (sg0 D A) (c0L i) (R.cV i) (along (realisation_embedding_eq_baseEmbedding R) (c0L i)) (R.HV i A.μ0)
      (along (realisation_embedding_eq_baseEmbedding R) (R.jV i A.μ0)) := by
  have h1 := hT.coefL i A.μ0
  obtain ⟨e, -, he, hp, -⟩ := h1
  have hχ := GlobalTheory.ConjForms.levChar_mem R hC.lev hC.grp.chiW i
  have hact : ∀ γ : GQ (Vc D i), ∃ T : VsV D i D.what₂.LL → VsV D i D.what₂.LL,
      ∀ v, c0L i (T v) = (R.cV i).coef.ρ γ (c0L i v) := fun γ =>
    (GlobalTheory.ConjForms.exists_ratMat (Vc D i) γ).elim fun γE hγ =>
      ⟨rhoVr (labLL D) (lamV D i) γE, (hT.mapL i).1 γ γE hγ⟩
  refine ⟨hC.models.cV i, (hT.mapL i).1, (hT.mapL i).2.1, (hT.mapL i).2.2, fun a b => ?_,
    ⟨_, fun k => (hχ k).imp fun y hy => ⟨hy, (RingHom.congr_fun (realisation_embedding_eq_baseEmbedding R) y).symm.trans hy⟩, hC.models.HV i A.μ0⟩,
    fun x h => ?_⟩
  · exact (pair_val (R.B.L i A.μ0).pres (c0L i) e he (fun v w => pairVr (labLL D) (lamV D i) (gramV D i) v w) hp _ _).trans
      (RingHom.congr_fun (realisation_embedding_eq_baseEmbedding R) _)
  · exact (ext_val (R.B.L i A.μ0).pres (c0L i) e he hact hχ _ h).imp fun v hv =>
      ⟨(congrFun (hC.models.jV i A.μ0 x) h).trans hv, (congrFun (hC.models.jV i A.μ0 x) h).trans hv⟩
set_option maxHeartbeats 2000000 in
theorem isConjLift_base_five {F : Face D A} (hC : GlobalTheory.Core5 R F) :
    IsConjLift R i (sg0 D A) (R.mu0 ((i : ℕ) + 1)) R.eta (R.cV i) (R.HV i A.μ0) (R.thG i A.μ0) := by
  have h1 := hC.thP.thF i A.μ0
  obtain ⟨thP, h2, h3⟩ := h1
  have hω : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (R.toLevCh.mu A.μ0 ((i : ℕ) + 1))
      (R.toLevCh.mu A.μ0 ((i : ℕ) + 1) * R.eta⁻¹) (R.ωP i A.μ0) := hC.thP.ωP i A.μ0
  rw [mu_base R hC.lev] at hω
  have hio := hC.thP.ioP i A.μ0
  rw [← deltaConj_base R i] at hio
  refine ⟨R.ωP i A.μ0, R.vacP i, R.vP i A.μ0, onb (R.MW i (sg0 D A)), R.ioP i, thP, hω,
    isThPVecOf_empty (places_base R hC.lev) _ (hC.thP.vP i A.μ0),
    fun τ => GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.isONBasis_onb _ τ _ (hC.models.order i τ), hC.thP.pt_theta i A.μ0, hio, h2, fun x v => ?_⟩
  exact (congrArg (fun w : MMap (R.MW i (sg0 D A)) => w fun ρ => v ρ) (hC.thP.thG i A.μ0 x)).trans
    (congrArg (R.eWf i (sg0 D A)) (h3 x v))

theorem isConjDatum_base_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → EtaVals R → ∃ (c₁ : VsV D i D.what₂.LL →ₛₗ[sg0 D A] (R.cV i).W) (j : A.fam.amb.FL i A.μ0 →ₛₗ[sg0 D A] (R.HV i A.μ0).H), IsConjDatum R i (sg0 D A) (c0L i) (R.mu0 ((i : ℕ) + 1)) R.eta (R.cV i) c₁ (R.HV i A.μ0) j (R.thG i A.μ0) ∧ ∀ x, j x = R.jV i A.μ0 x := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ hC fw i gramR c0R c0L hT hV
  have hg := (GlobalTheory.GalLift.overK_iff_good_ofFive T R F κw v₀ hC fw i (sg0 D A)).1 fun x _ => (RingHom.congr_fun (realisation_embedding_eq_baseEmbedding R) _).symm
  have h1 := fw.chiR i (sg0 D A) hg
  have h2 := h1.2.2.2.2 (congrArg (·.comp (algebraMap T.Q.c.F D.what₂.LL)) (realisation_embedding_eq_baseEmbedding R).symm)
  exact ⟨along (realisation_embedding_eq_baseEmbedding R) (c0L i), along (realisation_embedding_eq_baseEmbedding R) (R.jV i A.μ0),
    ⟨Eq.subst (motive := ChiAt R i (sg0 D A)) h2 h1, isEtaConj_base R hC.lev hV, isConjForms_base_five R i hC hT,
      isConjLift_base_five R i hC⟩, fun _ => rfl⟩

end GlobalTheory.GalLift.BaseDatum

namespace GlobalTheory.GalLift.BaseEquiv

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

theorem reading_actG_five (F : Face D A) (hc : GlobalTheory.Core5 R F) (fw : FWTie T R κw v₀) (i : Fin D.R.m) (hev : fw.Evaluates)
    (hinj : EvInj T R v₀) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (hE : (O i).EquivAt (κw i) (T.cE ((i : ℕ) + 1) (O i).s0)) (g : G) (f : Cu T κw i) :
    ∃ f₁ : Cu T κw i, (f₁ : T.R ((i : ℕ) + 1)) = actG (O i) g (f : T.R ((i : ℕ) + 1)) ∧
      fw.jK i (sg0 D A) f₁ =
        D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) • R.gW i (sg0 D A) g (fw.jK i (sg0 D A) f) := by
  have ht := GlobalTheory.GalLift.act_eq_translation_five R F hc i
  have hk := ht.1 g
  obtain ⟨k, hk⟩ := hk
  have hq := hE g k hk (f : T.R ((i : ℕ) + 1)) f.2
  refine ⟨⟨_, hq.1⟩, rfl, hinj i (sg0 D A) (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) (funext fun h => ?_)⟩
  have h1 := ev_base T R κw v₀ fw i hev O ⟨_, hq.1⟩ h
  have h2 := ev_base T R κw v₀ fw i hev O f (h * k)
  have h3 := (ht.2 (sg0 D A)).1 g k hk (fw.jK i (sg0 D A) f) (v₀ i (sg0 D A)) h
  have h4 := (hq.2 h).trans (congrArg (· * _) (hc.grp.chiW i g).symm)
  have h5 := alg_step h1 h4 (h3.trans h2)
  refine h5.trans ?_
  exact (congrFun (congrArg (fun y => y (v₀ i (sg0 D A))) (map_smul (R.HW i (sg0 D A)).e _ _)) h).symm

theorem base_equiv_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), (O i).EquivAt (κw i) (T.cE ((i : ℕ) + 1) (O i).s0) → ∀ (g : G) (f : Cu T κw i), ∃ f₁ : Cu T κw i, (f₁ : T.R ((i : ℕ) + 1)) = actG (O i) g (f : T.R ((i : ℕ) + 1)) ∧ fw.jK i (sg0 D A) f₁ = D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) • R.gW i (sg0 D A) g (fw.jK i (sg0 D A) f) :=
  fun T _ R F κw v₀ hc fw i hev hinj O hE g f => reading_actG_five T R κw v₀ F hc fw i hev hinj O hE g f

end GlobalTheory.GalLift.BaseEquiv

namespace GlobalTheory.GalLift.BaseId

theorem base_identity_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ), OMPins T R κw v₀ O i → (O i).OneMapOf (κw i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph → ∀ h, RepsAt (O i) (v₀ i (sg0 D A)) h → ∃ z ∈ Subgroup.center G, ∃ ze : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x₀, ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → Cu T κw i), IsClassSum (O i) κw h x₀ a f ∧ ∀ f₁ : Fin n → Cu T κw i, (∀ k, (f₁ k : T.R ((i : ℕ) + 1)) = actG (O i) z (f k : T.R ((i : ℕ) + 1))) → ph • R.thG i A.μ0 (R.jV i A.μ0 x₀) = ∑ g, RealDat.eC (A := A) (sg0 D A) g • R.gW i (sg0 D A) g (∑ k, D.what₂.embLL (ze * a k) • fw.jK i (sg0 D A) (f₁ k)) := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ hch fw i hev hinj O ph hpins hone h hreps
  have hrk : (Vc D i).rank = (κw i).n :=
    (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).trans (fw.kap i (D.eTau.symm 1)).2.2.symm
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hpf : T.Q.PinField := fw.laws.toLawsM.pins.2.2.1
  have hres : res T (sg0 D A) = (O i).s0 :=
    (congrArg (res T) hs).trans ((res_embLL T fw.alg_eq hpf).trans (sOv_eq T.toCore (O i).c' (O i).hle).symm)
  have hgood : GoodEmb T.Q.c (res T (sg0 D A)) := base_embedding_good T R fw.alg_eq hpf
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := (congrArg (T.V ((i : ℕ) + 1)) hres).trans (O i).hV
  have hfield : ∀ b, inC (O i).c' ((O i).jL b) = D.what₂.embLL b := fun b => RingHom.congr_fun hpins.2.lift.field b
  refine (tie_baseChange (O i).hle (T.U ((i : ℕ) + 1)) (inC (O i).c') (Wc D i) (O i).dict (O i).mu
    (xiR D) (wtA (κw i)) hone.2.1 ()).imp fun z hz => ⟨hz.1, hz.2.elim fun ze hze => hze.1.elim fun ze' hze' => ?_⟩
  have hze'' : D.what₂.embLL ze' = ze := hze'
  refine ⟨ze', hze.2.1.imp fun m hm => ⟨hm.1, D.what₂.embLL.injective
    ((map_pow _ _ _).trans ((congrArg (· ^ m) hze'').trans (hm.2.trans (map_one _).symm)))⟩, fun x₀ => ?_⟩
  refine hreps.elim fun J' hJ => (hJ.2.1 x₀).elim fun x hx => ?_
  refine (hze.2.2 x ((hJ.2.2.2 x).2 ⟨x₀, hx⟩)).elim fun f' h1 => h1.elim fun m h1 => h1.elim fun as h1 => h1.elim fun fs h1 => ?_
  have has : ∀ k, ∃ b : D.what₂.LL, D.what₂.embLL b = inC (O i).c' (as k) := fun k => hpins.1.le (as k).2
  have has' : (fun k => (O i).jL (has k).choose) = as := funext fun k =>
    (inC (O i).c').injective ((hfield _).trans (has k).choose_spec)
  have hfs : ∀ k, fs k ∈ T.cuspA ((i : ℕ) + 1) (wtA (κw i)) (κw i).n := fun k => hrk ▸ h1.2.2.1 k
  refine ⟨m, fun k => (has k).choose, fun k => ⟨fs k, hfs k⟩, ⟨x, f', hx, h1.1, h1.2.1, ?_⟩, fun f₁ hf₁ => ?_⟩
  · exact (congrArg (fun b => IsBC (O i).hle f' b fs) has').mpr h1.2.2.2.1
  have hHW := hch.models.HW i (sg0 D A)
  have hy : R.thF i A.μ0 (jVx R i A.μ0 x₀) ∈ LinearMap.range (R.HW i (sg0 D A)).e :=
    hHW.2.1.ge (hch.thP.thF_mem i A.μ0 _)
  refine hy.elim fun y hy => ?_
  refine proj_model (R.MW i (sg0 D A)) (R.HW i (sg0 D A)).e hHW.1
    (fun g => Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) _ (fun g => R.gW i (sg0 D A) g)
    (hch.models.gW i (sg0 D A)) ph y _ _
    ((hch.thP.thG i A.μ0 (jVx R i A.μ0 x₀)).trans (congrArg (postOn _ (R.eWf i (sg0 D A))) hy.symm)) ?_
  refine eq_of_reps (R.HW i (sg0 D A)).e hHW.2.1 (v₀ i (sg0 D A)) (hinj i _ hgood) ph y _ _ fun q => ?_
  have h2 : (R.HW i (sg0 D A)).e y (v₀ i (sg0 D A)) q.out = (O i).thAd () x q :=
    (congrArg (fun S : MMap (R.MW i (sg0 D A)) => S (v₀ i (sg0 D A)) q.out) hy).trans
      (congrFun (hJ.2.2.1 _ x hx) q).symm
  refine (congrArg (ph * ·) h2).trans ((h1.2.2.2.2 q).trans (Finset.sum_congr rfl fun k _ => congrArg₂ (· * ·) ?_ ?_))
  · exact (congrArg₂ (· * ·) hze'' (has k).choose_spec).symm.trans (map_mul D.what₂.embLL _ _).symm
  · refine (phi_cE T R O i (wtA (κw i)) (actG (O i) z (fs k)) q.out).trans ?_
    refine Eq.symm ((congrFun (hev i _ hgood hV (f₁ k)) q.out).trans ?_)
    exact congrFun ((phiC_congr T hres hV (O i).hV _ _).trans
      (congrArg (phiC T (O i).hV (wtA (κw i))) (hf₁ k))) q.out

end GlobalTheory.GalLift.BaseId

namespace GlobalTheory.ConjLiftUnique

set_option maxHeartbeats 1600000 in

theorem lift_unique_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H) (c' : CoefA (Vc D i)) (c₁' : VsV D i D.what₂.LL →ₛₗ[σ] c'.W) (H' : HMod (Bridge.Gf (Vc D i) → c'.W)) (j' : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H'.H), IsConjForms R i σ (c0L i) c c₁ H j → IsConjForms R i σ (c0L i) c' c₁' H' j' → ∀ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))) (ω' : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀' f' : WO (Vc D i) (Wc D i) → ℂ) (B' : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io' : LowT (R.MW i σ) →ₗ[ℂ] c'.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP' : LinearMap.range (c'.ext ∘ₗ H'.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))), LiftData R i σ μ' η' c H ω f₀ f B io thP → LiftData R i σ μ' η' c' H' ω' f₀' f' B' io' thP' → ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ x v, thP' ((c'.ext ∘ₗ H'.e).rangeRestrict (j' x)) v = κ • thP ((c.ext ∘ₗ H.e).rangeRestrict (j x)) v := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i gramR c0R c0L hT σ hσ μ' η' c c₁ H j c' c₁' H' j' hj hj' ω f₀ f B io thP ω' f₀' f'
    B' io' thP' hL hL'
  have hθ : IsInfFam R.θ := hC.models.inf
  have hlow := GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ _ (GlobalTheory.GalLift.ProjLift.holShape_of_overK R i hσ)
  have sdV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have sdW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  have hc := GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MW i σ)
  have hV := fun τ => GlobalTheory.GalLift.Vec.isCartanInv_one (hC.models.BV i τ)
  have h1 := vec_unique (D.sp.V_sig _) (D.sp.W_sig _) hV hc sdV sdW hL.2.1.vec hL'.2.1.vec
  obtain ⟨a, ha, rfl⟩ := h1
  have h2 := exists_isometry (bVV D.what₂.LL (lamV D i)) hj.coef hj'.coef c₁ c₁' hj.indep hj.span hj'.indep hj'.span
    (fun a b => (hj'.pair a b).trans (hj.pair a b).symm) (fun γ hγ => by
      have hγ' := hγ
      unfold GQ HFinIn at hγ'
      obtain ⟨g, -, hg⟩ := hγ'
      exact ⟨_, hj.act ⟨γ, hγ⟩ g hg.symm, hj'.act ⟨γ, hγ⟩ g hg.symm⟩)
  obtain ⟨Φ, p1, p2, p3⟩ := h2
  have hv := hL.2.1.vec
  have hv2 := hv.2
  obtain ⟨e, -, h5⟩ := hv2
  have hf := GlobalTheory.GalLift.Vec.theta_of_thetaAt hL.1.std hθ h5 hv.1.2.theta
  have h3 := io_unique hL.1 hL'.1 hθ (D.sp.V_sig _) (D.sp.W_sig _) hV hlow.1 hlow.2 hj.coef Φ p2 p3 hf
    (GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv hf) ha hL.2.1.onb hL'.2.1.onb hL.2.2.1 hL'.2.2.1
  obtain ⟨κ, hκ, hk⟩ := h3
  have hinj := rescale_inj (bVV D.what₂.LL (lamV D i)) D.what₂.embLL (c0L i) (hT.mapL i).2.1
  have hb : ∀ x h, H'.e (j' x) h = Φ (H.e (j x) h) := fun x h => by
    have b1 := hj.base x h
    have b2 := hj'.base x h
    obtain ⟨v, q1, q2⟩ := b1
    obtain ⟨v', q1', q2'⟩ := b2
    have q3 : v = v' := hinj (q1.symm.trans q1')
    exact q2'.trans ((congrArg c₁' q3.symm).trans ((p1 v).symm.trans (congrArg Φ q2.symm)))
  exact ⟨κ, hκ, fun x v => thetaP_eq (fun p y => (GlobalTheory.WeilUniq.weilDatum_unique D R.ψ hL.1.std _ _ _ _ ω ω' hL.1 hL'.1 p _
    (hL'.2.1.theta y)).symm) Φ hk hL.2.2.2 hL'.2.2.2 _ _
    (fun h => (congrArg (c'.ρ h⁻¹) (hb x _)).trans (p3 _ _).symm) v⟩

end GlobalTheory.ConjLiftUnique

namespace GlobalTheory.GalLift

theorem lift_and_base_five : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A
    : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks
    D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ
    : D.what₂.LL →+* ℂ), OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (c₁
    : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j
    : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H) (c' : CoefA (Vc D i)) (c₁'
    : VsV D i D.what₂.LL →ₛₗ[σ] c'.W) (H' : HMod (Bridge.Gf (Vc D i) → c'.W)) (j'
    : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H'.H), IsConjForms R i σ (c0L i) c c₁ H j → IsConjForms R i σ (c0L
    i) c' c₁' H' j' → ∀ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) →
    ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D
    i).rank) ℂ) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP
    : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))) (ω'
    : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀' f' : WO (Vc D
    i) (Wc D i) → ℂ) (B' : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io'
    : LowT (R.MW i σ) →ₗ[ℂ] c'.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP'
    : LinearMap.range (c'.ext ∘ₗ H'.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) →
    ℂ))), LiftData R i σ μ' η' c H ω f₀ f B io thP → LiftData R i σ μ' η' c' H' ω' f₀' f' B' io' thP' → ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ x v, thP' ((c'.ext
    ∘ₗ H'.e).rangeRestrict (j' x)) v = κ • thP ((c.ext ∘ₗ H.e).rangeRestrict (j x)) v) ∧ (∀ {D
    : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T
    : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw
    : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ
    : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → EtaVals R → ∃ (c₁
    : VsV D i D.what₂.LL →ₛₗ[sg0 D A] (R.cV i).W) (j : A.fam.amb.FL i A.μ0 →ₛₗ[sg0 D A] (R.HV i
    A.μ0).H), IsConjDatum R i (sg0 D A) (c0L i) (R.mu0 ((i : ℕ) + 1)) R.eta (R.cV i) c₁ (R.HV i
    A.μ0) j (R.thG i A.μ0) ∧ ∀ x, j x = R.jV i A.μ0 x) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype
    G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField
    Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), (∀ g, ∃ k, IsLiftW R i g k) ∧ ∀ (σ
    : D.what₂.LL →+* ℂ), (∀ g k, IsLiftW R i g k → ∀ y v h, (R.HW i σ).e (R.gW i σ g y) v h = (R.HW
    i σ).e y v (h * k)) ∧ ∀ y v, R.eWf i σ ((R.HW i σ).e y v) = (R.HW i σ).e (∑ g, RealDat.eC (A :=
    A) σ g • R.gW i σ g y) v) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A
    : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R
    : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) +
    1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i
    σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i
    : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → ∀ (O
    : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), (O i).EquivAt (κw i) (T.cE ((i : ℕ) + 1) (O
    i).s0) → ∀ (g : G) (f : Cu T κw i), ∃ f₁ : Cu T κw i, (f₁ : T.R ((i : ℕ) + 1)) = actG (O i) g (f
    : T.R ((i : ℕ) + 1)) ∧ fw.jK i (sg0 D A) f₁ = D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ)
    : D.what₂.LL) • R.gW i (sg0 D A) g (fw.jK i (sg0 D A) f)) ∧ (∀ {D : D7} {G : Type} [Group
    G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra
    T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw
    : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ
    : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i
    : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → ∀ (O
    : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ), OMPins T R κw v₀ O i → (O
    i).OneMapOf (κw i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph → ∀ h, RepsAt (O i) (v₀ i
    (sg0 D
    A)) h → ∃ z ∈ Subgroup.center G, ∃ ze : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x₀, ∃ (n
    : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → Cu T κw i), IsClassSum (O
    i) κw h x₀ a f ∧ ∀ f₁ : Fin n → Cu T κw i, (∀ k, (f₁ k : T.R ((i : ℕ) + 1)) = actG (O i) z (f k
    : T.R ((i : ℕ) + 1))) → ph • R.thG i A.μ0 (R.jV i A.μ0 x₀) = ∑ g, RealDat.eC (A := A) (sg0 D
    A) g • R.gW i (sg0 D A) g (∑ k, D.what₂.embLL (ze * a k) • fw.jK i (sg0 D A) (f₁ k))) :=
  ⟨GlobalTheory.ConjLiftUnique.lift_unique_five, GlobalTheory.GalLift.BaseDatum.isConjDatum_base_five, GlobalTheory.GalLift.act_eq_translation_five,
    GlobalTheory.GalLift.BaseEquiv.base_equiv_five, GlobalTheory.GalLift.BaseId.base_identity_five⟩

end GlobalTheory.GalLift

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateLift_unique_and_baseDatum : (∀ {D : D7} {G : Type} [Group
    G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field
    Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F
    : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ
    : D.what₂.LL →+* ℂ), OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (c₁
    : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j
    : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H) (c' : CoefA (Vc D i)) (c₁'
    : VsV D i D.what₂.LL →ₛₗ[σ] c'.W) (H' : HMod (Bridge.Gf (Vc D i) → c'.W)) (j'
    : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H'.H), IsConjForms R i σ (c0L i) c c₁ H j → IsConjForms R i σ (c0L
    i) c' c₁' H' j' → ∀ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) →
    ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D
    i).rank) ℂ) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP
    : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))) (ω'
    : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀' f' : WO (Vc D
    i) (Wc D i) → ℂ) (B' : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io'
    : LowT (R.MW i σ) →ₗ[ℂ] c'.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP'
    : LinearMap.range (c'.ext ∘ₗ H'.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) →
    ℂ))), LiftData R i σ μ' η' c H ω f₀ f B io thP → LiftData R i σ μ' η' c' H' ω' f₀' f' B' io' thP' → ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ x v, thP' ((c'.ext
    ∘ₗ H'.e).rangeRestrict (j' x)) v = κ • thP ((c.ext ∘ₗ H.e).rangeRestrict (j x)) v) ∧ (∀ {D
    : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T
    : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw
    : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ
    : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → EtaVals R → ∃ (c₁
    : VsV D i D.what₂.LL →ₛₗ[sg0 D A] (R.cV i).W) (j : A.fam.amb.FL i A.μ0 →ₛₗ[sg0 D A] (R.HV i
    A.μ0).H), IsConjDatum R i (sg0 D A) (c0L i) (R.mu0 ((i : ℕ) + 1)) R.eta (R.cV i) c₁ (R.HV i
    A.μ0) j (R.thG i A.μ0) ∧ ∀ x, j x = R.jV i A.μ0 x) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype
    G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField
    Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), (∀ g, ∃ k, IsLiftW R i g k) ∧ ∀ (σ
    : D.what₂.LL →+* ℂ), (∀ g k, IsLiftW R i g k → ∀ y v h, (R.HW i σ).e (R.gW i σ g y) v h = (R.HW
    i σ).e y v (h * k)) ∧ ∀ y v, R.eWf i σ ((R.HW i σ).e y v) = (R.HW i σ).e (∑ g, RealDat.eC (A :=
    A) σ g • R.gW i σ g y) v) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A
    : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R
    : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) +
    1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i
    σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i
    : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → ∀ (O
    : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), (O i).EquivAt (κw i) (T.cE ((i : ℕ) + 1) (O
    i).s0) → ∀ (g : G) (f : Cu T κw i), ∃ f₁ : Cu T κw i, (f₁ : T.R ((i : ℕ) + 1)) = actG (O i) g (f
    : T.R ((i : ℕ) + 1)) ∧ fw.jK i (sg0 D A) f₁ = D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ)
    : D.what₂.LL) • R.gW i (sg0 D A) g (fw.jK i (sg0 D A) f)) ∧ (∀ {D : D7} {G : Type} [Group
    G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra
    T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw
    : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ
    : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i
    : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → ∀ (O
    : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ), OMPins T R κw v₀ O i → (O
    i).OneMapOf (κw i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph → ∀ h, RepsAt (O i) (v₀ i
    (sg0 D
    A)) h → ∃ z ∈ Subgroup.center G, ∃ ze : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x₀, ∃ (n
    : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → Cu T κw i), IsClassSum (O
    i) κw h x₀ a f ∧ ∀ f₁ : Fin n → Cu T κw i, (∀ k, (f₁ k : T.R ((i : ℕ) + 1)) = actG (O i) z (f k
    : T.R ((i : ℕ) + 1))) → ph • R.thG i A.μ0 (R.jV i A.μ0 x₀) = ∑ g, RealDat.eC (A := A) (sg0 D
    A) g • R.gW i (sg0 D A) g (∑ k, D.what₂.embLL (ze * a k) • fw.jK i (sg0 D A) (f₁ k))) := by
  atlas_forward_decl GlobalTheory.GalLift.lift_and_base_five
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CentralShift

theorem exists_isCentralShift_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), ∀ z ∈ Subgroup.center G, ∃ ζ, IsCentralShift R i σ z ζ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ z hz
  obtain ⟨e, he⟩ := exists_idemSum R.Pg (GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hC.lev.Pg)
  have h := exists_central_lift (Wc D i) (R.βW i) (R.datWp i R.triv) he (g := R.eG z) (map_center R.eG hz)
  obtain ⟨ζ, hc, hs, hl⟩ := h
  have ht : ∀ y v h, (R.HW i σ).e (R.gW i σ z y) v h = (R.HW i σ).e y v (h * ζ) := fun y v h =>
    (congrArg (fun T : MMap (R.MW i σ) => T v h) (hC.models.gW i σ z y)).trans
      (GlobalTheory.GeoActCompare.actW_apply R hC.models.HW σ hl y v h)
  refine ⟨ζ, hz, hc, hl.1, ⟨e, he, hs⟩, hl, ht,
    inner_eq_of_norm (R.gW i σ z) (GlobalTheory.gW_norm_eq R hC.models.HW hC.models.gW hC.models.νW i σ z),
    comm_of_center (R.gW i σ) hz, fun _ _ S _ y y' h => ?_⟩
  refine MultilinearMap.ext fun v => funext fun g => (ht y' v g).trans ?_
  refine (congrArg (fun T : MMap (R.MW i σ) => T v (g * ζ)) h).trans ?_
  show ∑ γ ∈ S, (R.HW i σ).e y v (g * ζ * γ) = ∑ γ ∈ S, (R.HW i σ).e (R.gW i σ z y) v (g * γ)
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [ht, mul_assoc, mul_assoc, Subgroup.mem_center_iff.1 hc γ]

end GlobalTheory.CentralShift

theorem GlobalTheory.CompPhase.exists_isCompPhase_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (u : GA D (Wc D i) → ℂ), PhaseFun R i u → ∃ U, IsCompPhase R i σ u U := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i σ u hu
  have hc := GlobalTheory.CompPhase.compFun_of_level _ _ hu.2.1 hu.2.2.1 hu.2.2.2
  have h := GlobalTheory.CompPhase.exists_unitary _ (hR.models.HW i σ) (postOn _ (LinearMap.mulLeft ℂ u))
    (fun T hT => Submodule.subset_span (hc.multMap hu.2.2.2 ((GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ T).1 hT)))
    (fun T T' => congrArg (_ * ·) (GlobalTheory.CompPhase.ipM_phase hu.1 _ _ T T'))
  obtain ⟨U, hU⟩ := h
  exact ⟨U, hu.1, hu.2.1, hu.2.2.1, hu.2.2.2, fun y v h => congrFun (DFunLike.congr_fun (hU y) v) h⟩

namespace GlobalTheory.ConjInner

set_option maxHeartbeats 1000000 in

theorem inner_reading_conj_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), JEvExists T R κw v₀ → JEvBar T R κw → BarTie fw → ∀ (σ : D.what₂.LL →+* ℂ), ¬ GoodEmb T.Q.c (res T σ) → ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ hC fw i hE hB hT σ hσ
  have hg : GoodEmb T.Q.c (resC T σ) := good_resC T hσ
  have hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i := fw.laws.spaceW _ (inR i) _ hg
  have h1 := (hT i σ hσ hV).1 (hB i σ hσ hV)
  obtain ⟨v, hv, h1⟩ := h1
  have h2 := fw.evaluates hE i ((starRingEnd ℂ).comp σ) hg hV
  have h3 : ∀ f g, evAt R i σ v (fw.jK i σ f) g =
      starRingEnd ℂ (evAt R i _ (v₀ i ((starRingEnd ℂ).comp σ)) (fw.jK i ((starRingEnd ℂ).comp σ) f) g) := fun f g =>
    (congrFun (h1 f) g).trans (congrArg (starRingEnd ℂ) (congrFun (h2 f) g).symm)
  have h4 : ∀ f f', ⟪fw.jK i σ f, fw.jK i σ f'⟫_ℂ =
      starRingEnd ℂ ⟪fw.jK i ((starRingEnd ℂ).comp σ) f, fw.jK i ((starRingEnd ℂ).comp σ) f'⟫_ℂ := fun f f' =>
    inner_conj_of_values R hC.models.HW i σ hv (fun τ => ((fw.hv₀ i _).1 τ).1) (h3 f) (h3 f')
  have h5 := fw.ks i
  obtain ⟨n, b, hb, -, -, -, h5⟩ := h5
  refine inner_conj_of_span σ _ _ _ h5 ?_
  rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
  have e : ∀ k, ∃ f, ((fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = b k := fun k =>
    ⟨(fw.e i).symm ⟨b k, hb k⟩, congrArg Subtype.val ((fw.e i).apply_symm_apply _)⟩
  have e1 := e k
  have e2 := e l
  obtain ⟨f, e1⟩ := e1
  obtain ⟨f', e2⟩ := e2
  rw [← e1, ← e2]
  exact h4 f f'

end GlobalTheory.ConjInner

namespace GlobalTheory.CoreFive

theorem shift_phase_conj : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), ∀ z ∈ Subgroup.center G, ∃ ζ, IsCentralShift R i σ z ζ) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (u : GA D (Wc D i) → ℂ), PhaseFun R i u → ∃ U, IsCompPhase R i σ u U) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), JEvExists T R κw v₀ → JEvBar T R κw → BarTie fw → ∀ (σ : D.what₂.LL →+* ℂ), ¬ GoodEmb T.Q.c (res T σ) → ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ) :=
  ⟨GlobalTheory.CentralShift.exists_isCentralShift_five, GlobalTheory.CompPhase.exists_isCompPhase_five,
    GlobalTheory.ConjInner.inner_reading_conj_five⟩

end GlobalTheory.CoreFive

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralShift_phase_conjReadings_fiveClauses : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), ∀ z ∈ Subgroup.center G, ∃ ζ, IsCentralShift R i σ z ζ) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (u : GA D (Wc D i) → ℂ), PhaseFun R i u → ∃ U, IsCompPhase R i σ u U) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), JEvExists T R κw v₀ → JEvBar T R κw → BarTie fw → ∀ (σ : D.what₂.LL →+* ℂ), ¬ GoodEmb T.Q.c (res T σ) → ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ) := by
  atlas_forward_decl GlobalTheory.CoreFive.shift_phase_conj
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne GlobalTheory.GalLift.Assembly

namespace GlobalTheory.ConjRatLiftFive

set_option maxHeartbeats 1000000 in

theorem oneMapConj5 : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), OMPins T R κw v₀ O i → ∀ h, RepsAt (O i) (v₀ i (sg0 D A)) h → ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → CoefficientBaseChange R i (O i).jL (inC (O i).c') (c0L i) (O i).c0' → ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → ∀ (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L i) c c₁ H j → ∀ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))), LiftData R i σ μ' η' c H ω f₀ f B io thP → ∃ (u : GA D (Wc D i) → ℂ) (z : G) (κ : ℂ), PhaseFun R i u ∧ z ∈ Subgroup.center G ∧ ‖κ‖ = 1 ∧ EquivBy (O i) κw σ hV u ∧ ∀ x₀ (n : ℕ) (a : Fin n → D.what₂.LL) (fs : Fin n → Cu T κw i), IsClassSum (O i) κw h x₀ a fs → ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (fun ρ => (v ρ : (R.MW i σ).sm ρ)) = v₀ i σ → ∀ g, κ * thP ((c.ext ∘ₗ H.e).rangeRestrict (j x₀)) (PiTensorProduct.tprod ℂ v) g = ∑ k, σ (a k) * (u g * phiC T hV (wtA (κw i)) (actG (O i) z (fs k : T.R ((i : ℕ) + 1))) g) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR tie i O hO h hh gramR c0R c0L _ hc σ hσ hV μ' η' hμ hη c c₁ H j hj ω f₀ f B io thP hL
  refine hh.elim fun J' hJ => (exists_ext (O i) hO.1 hO.2 σ).elim fun σ' hσ' => ?_
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) f := by
    have h1 := hL.2.1.theta 1
    have e : (1 : PolF D (Wc D i).rank (Vc D i).rank) = MvPolynomial.basisMonomials _ ℂ 0 := by
      rw [MvPolynomial.coe_basisMonomials]; rfl
    rw [e, ptAt, pureTensorO, pureTensorL, Module.Basis.constr_basis] at h1
    simpa [opPow] using h1
  exact oneMap_of_ext_ofFive hR tie (O i) hO.2 hJ.1 hc hσ' (GlobalTheory.GalOne.Facts.factsAt_ofFive T R F κ v₀ hR tie i (O i) hO.2 σ σ' hσ' hσ).1 hV hj
    ⟨hσ, hμ, hη, hL.1, hL.2.1.vec, hth⟩ hL

section Main

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem base_lift5 (hR : GlobalTheory.Core5 R F) (fw : FWTie T R κw v₀) (i : Fin D.R.m) (hE : fw.Evaluates) (hI : EvInj T R v₀)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ) (hP : OMPins T R κw v₀ O i)
    (hO : (O i).OneMapOf (κw i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph)
    (h : (O i).Cl' () → GA D (Vc D i)) (hh : RepsAt (O i) (v₀ i (sg0 D A)) h) :
    ∃ (act : G → Cu T κw i → Cu T κw i) (z : G) (ze : D.what₂.LL),
      (∀ g f, (act g f : T.R ((i : ℕ) + 1)) = actG (O i) g (f : T.R ((i : ℕ) + 1))) ∧ z ∈ Subgroup.center G ∧
      (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x₀, ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → Cu T κw i),
        IsClassSum (O i) κw h x₀ a f ∧ IsRatLift R i ph x₀ (ratOf fw i act z ze a f) := by
  choose act hact hj using (GlobalTheory.T.conjugateLift_unique_and_baseDatum).2.2.2.1 T R F κw v₀ hR fw i hE hI O hO.1
  have hq1 := (GlobalTheory.T.conjugateLift_unique_and_baseDatum).2.2.2.2 T R F κw v₀ hR fw i hE hI O ph hP hO h hh
  obtain ⟨z, hz, ze, hze, hx⟩ := hq1
  refine ⟨act, z, ze, hact, hz, hze, fun x₀ => ?_⟩
  have hq2 := hx x₀
  obtain ⟨n, a, f, hc, he⟩ := hq2
  refine ⟨n, a, f, hc, ?_⟩
  have hs : ∀ b, D.what₂.embLL b = sg0 D A b := fun b => by rw [sign_at_base_place_eq_embedding R]
  have h1 := he (fun k => act z (f k)) (fun k => hact z (f k))
  have h2 := read_sum (sg0 D A) ((R.FW i).j (sg0 D A)) (crdF fw i) act (R.FW i).chi (R.gW i (sg0 D A))
    (fun g f => by rw [← hs]; exact hj g f) (fun g => (idemOf A.X).coeff g) (fun k => ze * a k) (fun k => act z (f k))
  refine h2.trans (Eq.trans ?_ h1.symm)
  simp only [hs]
  rfl

set_option maxHeartbeats 800000 in

theorem conj_lift5 (hR : GlobalTheory.Core5 R F) (fw : FWTie T R κw v₀) (i : Fin D.R.m) (hE : fw.Evaluates)
    (hI : EvInj T R v₀) (hinj : Function.Injective ((R.FW i).j (sg0 D A)))
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ) (hP : OMPins T R κw v₀ O i)
    (hO : (O i).OneMapOf (κw i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph)
    {gramR c0R c0L} (hT : Comparison₂ R gramR c0R c0L) (hC : CoefficientBaseChange R i (O i).jL (inC (O i).c') (c0L i) (O i).c0')
    (σ : D.what₂.LL →+* ℂ) (hσ : OverK σ) {μ' η' : (AE D)ˣ →* Circle} (hμ : ChiAt R i σ μ') (hη : IsEtaConj σ R.eta η')
    {c : CoefA (Vc D i)} {c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W} {H : HMod (Bridge.Gf (Vc D i) → c.W)}
    {j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H} (hF : IsConjForms R i σ (c0L i) c c₁ H j) {ω f₀ f B io thP}
    (hL : LiftData R i σ μ' η' c H ω f₀ f B io thP) :
    ∃ (th : H.H →ₗ[ℂ] (R.HW i σ).H) (u : GA D (Wc D i) → ℂ) (U : (R.HW i σ).H ≃ₗᵢ[ℂ] (R.HW i σ).H) (z : G) (κ : ℂ),
      IsProjOf R i σ thP th ∧ IsCompPhase R i σ u U ∧ z ∈ Subgroup.center G ∧ ‖κ‖ = 1 ∧
      ∀ x y, IsRatLift R i ph x y → U ((R.FW i).j σ y) = κ • R.gW i σ z (th (j x)) := by
  refine (exists_reps hP).elim fun h hh => ?_
  have hg : GoodEmb T.Q.c (res T σ) := (GlobalTheory.GalLift.overK_iff_good_ofFive T R F κw v₀ hR fw i σ).1 hσ
  have hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i := fw.laws.toLawsM.spaceW _ (inR i) _ hg
  have hq3 := base_lift5 hR fw i hE hI O ph hP hO h hh
  obtain ⟨act, z₀, ze, hact, hz₀, ⟨m, hm, hze⟩, hx⟩ := hq3
  have hq4 := oneMapConj5 T R F κw v₀ hR fw i O hP h hh gramR c0R c0L hT hC σ hσ hV
    μ' η' hμ hη c c₁ H j hF ω f₀ f B io thP hL
  obtain ⟨u, z, κ, hu, hz, hκ, hEq, hid⟩ := hq4
  have hq5 := (GlobalTheory.T.centralShift_phase_conjReadings_fiveClauses).2.1 R F hR i σ u hu
  obtain ⟨U, hU⟩ := hq5
  have hq6 := (GlobalTheory.T.conjugateLift_unique_and_baseDatum).2.2.1 R F hR i
  obtain ⟨hlift, htr⟩ := hq6
  have hq7 := htr σ
  obtain ⟨htr, hW⟩ := hq7
  let J : (Fin (R.nW i) → D.what₂.LL) →ₛₗ[σ] (R.HW i σ).H := U.toLinearEquiv.toLinearMap.comp ((R.FW i).j σ)
  let ev : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) := evL (R.HW i σ).e (v₀ i σ)
  have hev : Function.Injective ev := hI i σ hg
  have hJ : ∀ (f : Cu T κw i) g, ev (J (crdF fw i f)) g =
      u g * phiC T hV (wtA (κw i)) (f : T.R ((i : ℕ) + 1)) g := fun f g =>
    (hU.2.2.2.2 _ _ _).trans (congrArg (u g * ·) (congrFun (hE i σ hg hV f) g))
  have hJa : ∀ z (f : Cu T κw i) g, ev (J (crdF fw i (act z f))) g =
      u g * phiC T hV (wtA (κw i)) (actG (O i) z (f : T.R ((i : ℕ) + 1))) g := fun z f g =>
    (hJ (act z f) g).trans (congrArg (fun w => u g * phiC T hV (wtA (κw i)) w g) (hact z f))
  have hJe : ∀ g f, J (crdF fw i (act g f)) = σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) • R.gW i σ g (J (crdF fw i f)) := by
    intro g f
    have hk := hlift g
    obtain ⟨k, hk⟩ := hk
    refine hev (Eq.trans (funext fun x => ?_) (ev.map_smul _ _).symm)
    exact (hJa g f x).trans ((hEq g k hk f x).trans (congrArg (σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) * ·)
      ((hJ f (x * k)).symm.trans (htr g k hk _ _ x).symm)))
  let v : ∀ ρ, lowT (R.MW i σ) ρ := fun ρ => ⟨v₀ i σ ρ, ((fw.hv₀ i σ).1 ρ).2.1⟩
  have hS : ∀ x₀ (n : ℕ) (a : Fin n → D.what₂.LL) (fs : Fin n → Cu T κw i), IsClassSum (O i) κw h x₀ a fs →
      κ • thP ((c.ext ∘ₗ H.e).rangeRestrict (j x₀)) (PiTensorProduct.tprod ℂ v) =
        ∑ k, σ (a k) • ev (J (crdF fw i (act z (fs k)))) := by
    intro x₀ n a fs hc
    funext g
    refine (hid x₀ n a fs hc v rfl g).trans (Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (Finset.sum_apply g Finset.univ fun k => σ (a k) • ev (J (crdF fw i (act z (fs k))))).symm)
    exact congrArg (σ (a k) * ·) (hJa z (fs k) g).symm
  have hex : ∀ x, ∃ t : (R.HW i σ).H, (R.HW i σ).e t (fun ρ => v ρ) =
      thP ((c.ext ∘ₗ H.e).rangeRestrict (j x)) (PiTensorProduct.tprod ℂ v) := fun x => by
    have h1 := hx x
    obtain ⟨n, a, fs, hc, -⟩ := h1
    exact exists_ev ev hκ _ _ _ (hS x n a fs hc)
  have h2 := (GlobalTheory.T.conjugateLift_of_characterisationClauses).2.2.2.2.2 R F hR i gramR c0R c0L hT σ hσ μ' η' c c₁ H j hF ω f₀ f B io thP hL v (fw.hv₀ i σ).1 hex
  obtain ⟨th, hth⟩ := h2
  refine ⟨th, u, U, z₀ * z⁻¹, σ ze * σ (((R.FW i).chi z₀ : D.what₂.LLˣ) : D.what₂.LL) *
    (σ (((R.FW i).chi z : D.what₂.LLˣ) : D.what₂.LL))⁻¹ * κ, hth, hU, mul_mem hz₀ (inv_mem hz), ?_, fun x y hy => ?_⟩
  · rw [norm_mul, norm_mul, norm_mul, norm_inv, norm_chi, norm_chi, hκ,
      norm_of_pow hm (a := σ ze) (by rw [← map_pow, hze, map_one])]
    norm_num
  · have h1 := hx x
    obtain ⟨n, a, fs, hc, hy'⟩ := h1
    have hyy : y = ratOf fw i act z₀ ze a fs := hinj (Eq.trans hy (Eq.symm hy'))
    refine (congrArg J hyy).trans ?_
    exact conj_abstract σ J (crdF fw i) act (R.FW i).chi (R.gW i σ) hJe (fun g => (idemOf A.X).coeff g) ev hev (R.eWf i σ)
      (fun y => hW y (v₀ i σ)) hz₀ hz ze κ a fs _ (hS x n a fs hc) (th (j x)) (hth (j x) v)

theorem hypConj5 (hR : GlobalTheory.Core5 R F) (i : Fin D.R.m) {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) {μ' η' : (AE D)ˣ →* Circle}
    (hμ : ChiAt R i σ μ') (hη : IsEtaConj σ R.eta η') : HypConj R i σ μ' η' :=
  (GlobalTheory.GalLift.hypConj_of_chars_ofFive R F hR i σ ((GlobalTheory.GalLift.labels_overK σ).1 hσ).1 ((GlobalTheory.GalLift.labels_overK σ).1 hσ).2).2 μ' η' hμ hη
    (GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj_ofFive R F hR i σ hσ η' hη).1 (GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj_ofFive R F hR i σ hσ η' hη).2

theorem lift_unique5 (hR : GlobalTheory.Core5 R F) (fw : FWTie T R κw v₀) (hI : EvInj T R v₀) (i : Fin D.R.m) {gramR c0R c0L}
    (hT : Comparison₂ R gramR c0R c0L) {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) {μ' η' c c₁ H j th μ'' η'' c' c₁' H' j' th'}
    (h : IsConjDatum R i σ (c0L i) μ' η' c c₁ H j th) (h' : IsConjDatum R i σ (c0L i) μ'' η'' c' c₁' H' j' th') :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ x, th' (j' x) = κ • th (j x) := by
  have e1 : μ'' = μ' := (GlobalTheory.ConjCharUnique.conjChar_unique_ofFive R F hR i σ).1 _ _ h'.1 h.1
  have e2 : η'' = η' := (GlobalTheory.ConjCharUnique.conjChar_unique_ofFive R F hR i σ).2 _ _ h'.2.1 h.2.1
  subst e1 e2
  have h1 := (isConjLift_iff R i σ _ _ _ _ _).1 h.2.2.2
  obtain ⟨ω, f₀, f, B, io, thP, hL, hp⟩ := h1
  have h2 := (isConjLift_iff R i σ _ _ _ _ _).1 h'.2.2.2
  obtain ⟨ω', f₀', f', B', io', thP', hL', hp'⟩ := h2
  have h3 := (GlobalTheory.T.conjugateLift_unique_and_baseDatum).1 R F hR i gramR c0R c0L hT σ hσ _ _ c c₁ H j c' c₁' H' j' h.2.2.1 h'.2.2.1 ω f₀ f B io thP
    ω' f₀' f' B' io' thP' hL hL'
  obtain ⟨κ, hκ, he⟩ := h3
  have hg : GoodEmb T.Q.c (res T σ) := (GlobalTheory.GalLift.overK_iff_good_ofFive T R F κw v₀ hR fw i σ).1 hσ
  let v : ∀ ρ, lowT (R.MW i σ) ρ := fun ρ => ⟨v₀ i σ ρ, ((fw.hv₀ i σ).1 ρ).2.1⟩
  let ev : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) := evL (R.HW i σ).e (v₀ i σ)
  have hev : Function.Injective ev := hI i σ hg
  refine ⟨κ, hκ, fun x => hev (Eq.trans ?_ (ev.map_smul _ _).symm)⟩
  exact (hp' (j' x) v).trans ((congrArg (R.eWf i σ) (he x _)).trans
    (((R.eWf i σ).map_smul _ _).trans (congrArg (κ • ·) (hp (j x) v).symm)))

theorem conjugateRationalLift_at_embedding_of_datum (hR : GlobalTheory.Core5 R F) (fw : FWTie T R κw v₀) (hI : EvInj T R v₀) (i : Fin D.R.m) {gramR c0R c0L}
    (hT : Comparison₂ R gramR c0R c0L) {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) (ph : ℂ) {μ' η' c c₁ H j th}
    (h : IsConjDatum R i σ (c0L i) μ' η' c c₁ H j th) {u U} (hU : IsCompPhase R i σ u U) (hu : σ = sg0 D A → ∀ h, u h = 1)
    {z : G} (hz : z ∈ Subgroup.center G) {κ : ℂ} (hκ : ‖κ‖ = 1)
    (he : ∀ x y, IsRatLift R i ph x y → U ((R.FW i).j σ y) = κ • R.gW i σ z (th (j x))) : ConjAt R i σ ph (c0L i) := by
  have h1 := (GlobalTheory.T.centralShift_phase_conjReadings_fiveClauses).1 R F hR i σ z hz
  obtain ⟨ζ, hζ⟩ := h1
  refine ⟨(GlobalTheory.GalLift.hypConj_of_chars_ofFive R F hR i σ ((GlobalTheory.GalLift.labels_overK σ).1 hσ).1 ((GlobalTheory.GalLift.labels_overK σ).1 hσ).2).1, ⟨_, _, _, _, _, _, _, h⟩,
    u, U, z, ζ, hU, hu, hζ, fun μ'' η'' c' c₁' H' j' th' h' => ⟨hypConj5 hR i hσ h'.1 h'.2.1, ?_⟩⟩
  have h2 := lift_unique5 hR fw hI i hT hσ h h'
  obtain ⟨κ', hκ', e⟩ := h2
  refine ⟨κ * κ'⁻¹, by rw [norm_mul, norm_inv, hκ, hκ']; norm_num, fun x y hy => ?_⟩
  exact (he x y hy).trans (smul_inv_of (R.gW i σ z) hκ' (e x))

theorem conjAt_base5 (hR : GlobalTheory.Core5 R F) (fw : FWTie T R κw v₀) (hI : EvInj T R v₀) (i : Fin D.R.m) {gramR c0R c0L}
    (hT : Comparison₂ R gramR c0R c0L) {ph : ℂ} (hph : ‖ph‖ = 1) : ConjAt R i (sg0 D A) ph (c0L i) := by
  have hσ : OverK (sg0 D A) := fun x _ => congrArg (fun s : D.what₂.LL →+* ℂ => s (D.embE x)) (sign_at_base_place_eq_embedding R)
  have h1 := (GlobalTheory.T.conjugateLift_unique_and_baseDatum).2.1 T R F κw v₀ hR fw i gramR c0R c0L hT ((GlobalTheory.T.conjugateCharacters_embeddings_of_characterisation).2.1 R F hR i)
  obtain ⟨c₁, j, hd, hj⟩ := h1
  refine conjugateRationalLift_at_embedding_of_datum hR fw hI i hT hσ ph hd (u := fun _ => 1) (U := LinearIsometryEquiv.refl ℂ _)
    ⟨fun _ => norm_one, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun y v h => (one_mul _).symm⟩
    (fun _ _ => rfl) (one_mem _) hph fun x y hy => ?_
  refine Eq.trans hy (congrArg (ph • ·) ?_)
  exact (congrArg (R.thG i A.μ0) (hj x).symm).trans (LinearMap.congr_fun (map_one (R.gW i (sg0 D A))) _).symm

theorem conjugateRationalLift_at_nonBaseEmbedding (hR : GlobalTheory.Core5 R F) (fw : FWTie T R κw v₀) (i : Fin D.R.m) (hE : fw.Evaluates)
    (hI : EvInj T R v₀) (hinj : Function.Injective ((R.FW i).j (sg0 D A)))
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ) (hP : OMPins T R κw v₀ O i)
    (hO : (O i).OneMapOf (κw i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph)
    {gramR c0R c0L} (hT : Comparison₂ R gramR c0R c0L) {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) (hne : σ ≠ sg0 D A) :
    ConjAt R i σ ph (c0L i) := by
  have h0 := hP.2.lift.c0
  obtain ⟨gramR', c0R', c0L', hT', hC⟩ := h0
  have hg : GoodEmb T.Q.c (res T σ) := (GlobalTheory.GalLift.overK_iff_good_ofFive T R F κw v₀ hR fw i σ).1 hσ
  have hμ := fw.chiR i σ hg
  have h1 := (GlobalTheory.T.conjugateCharacters_embeddings_of_characterisation).2.2.1 R F hR i ((GlobalTheory.T.conjugateCharacters_embeddings_of_characterisation).2.1 R F hR i) σ hσ
  obtain ⟨η', hη⟩ := h1
  have hH := hypConj5 hR i hσ hμ hη
  have h2 := (GlobalTheory.T.conjugateLift_of_characterisationClauses).1 R F hR i gramR' c0R' c0L' hT' σ hσ
  obtain ⟨c, c₁, hc⟩ := h2
  have h3 := (GlobalTheory.T.conjugateLift_of_characterisationClauses).2.1 R F hR i gramR' c0R' c0L' hT' σ c c₁ hc
  obtain ⟨H, j, hF⟩ := h3
  have h4 := (GlobalTheory.T.conjugateCharacters_embeddings_of_characterisation).2.2.2.2.2.2.1 R F hR i σ _ η' hμ hη hH
  obtain ⟨ω, hω⟩ := h4
  have h5 := (GlobalTheory.T.conjugateLift_of_characterisationClauses).2.2.2.1 R F hR i σ hσ
  obtain ⟨f₀, f, B, hv⟩ := h5
  have h6 := GlobalTheory.MovedWeights.exists_io_conj_ofFive R F hR i σ hσ _ η' hμ hH c c₁ hc ω f₀ f B hω hv
  obtain ⟨io, hio⟩ := h6
  have h7 := (GlobalTheory.T.conjugateLift_of_characterisationClauses).2.2.2.2.1 R F hR i σ _ η' _ c c₁ H j hF ω f₀ f B io hω hv
  obtain ⟨thP, hth⟩ := h7
  have hL : LiftData R i σ _ η' c H ω f₀ f B io thP := ⟨hω, hv, hio, hth⟩
  have h8 := conj_lift5 hR fw i hE hI hinj O ph hP hO hT' hC σ hσ hμ hη hF hL
  obtain ⟨th, u, U, z, κ, hp, hU, hz, hκ, he⟩ := h8
  have h9 := (GlobalTheory.T.conjugateLift_of_characterisationClauses).2.2.1 R F hR i gramR c0R c0L hT gramR' c0R' c0L' hT' σ c c₁ H j hF
  obtain ⟨c₁', hF'⟩ := h9
  exact conjugateRationalLift_at_embedding_of_datum hR fw hI i hT hσ ph ⟨hμ, hη, hF', (isConjLift_iff R i σ _ _ _ _ _).2 ⟨ω, f₀, f, B, io, thP, hL, hp⟩⟩ hU
    (fun h => absurd h hne) hz hκ he

end Main

theorem conjRatLift5 : GlobalTheory.LowRow.ConjRatLift5 := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ O ph hR _ fw hb _ hLU hP i hO
  have hJ' := GlobalTheory.ConjReading.jEvExists_and_jEvBar T R κw v₀ O hR.lev hR.models fw hP
  have hI : EvInj T R v₀ := GlobalTheory.EvalAtUnitVectorFinal.evInj_of_isModels_of_tie T R κw v₀ hR.models fw
  have hE : fw.Evaluates := fw.evaluates hJ'.1
  have hinj : Function.Injective ((R.FW i).j (sg0 D A)) := GlobalTheory.GalOne.inj_of_indep _ (hLU i (sg0 D A)).1
  refine ⟨fun x => ?_, fun gramR c0R c0L hT σ hσ => ?_, fun σ hσ => ⟨(GlobalTheory.GalLift.labels_overK σ).2 hσ, ?_⟩⟩
  · obtain ⟨h, hh⟩ := exists_reps (hP i)
    obtain ⟨act, z, ze, -, -, -, hx⟩ := base_lift5 hR fw i hE hI O ph (hP i) hO h hh
    obtain ⟨n, a, f, -, hy⟩ := hx x
    exact ⟨_, hy, fun y hy' => hinj (Eq.trans hy' (Eq.symm hy))⟩
  · by_cases hs : σ = sg0 D A
    · subst hs
      exact conjAt_base5 hR fw hI i hT hO.2.1.2.2.2.2.1
    · exact conjugateRationalLift_at_nonBaseEmbedding hR fw i hE hI hinj O ph (hP i) hO hT hσ hs
  · exact (GlobalTheory.T.centralShift_phase_conjReadings_fiveClauses).2.2 T R F κw v₀ hR fw i hJ'.1 hJ'.2 hb σ fun hg =>
      hσ ((GlobalTheory.GalLift.overK_iff_good_ofFive T R F κw v₀ hR fw i σ).2 hg)

end GlobalTheory.ConjRatLiftFive

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatesOfRationalThetaLift_from_characterisation : ConjRatLift5 := by
  atlas_forward_decl GlobalTheory.ConjRatLiftFive.conjRatLift5
end
