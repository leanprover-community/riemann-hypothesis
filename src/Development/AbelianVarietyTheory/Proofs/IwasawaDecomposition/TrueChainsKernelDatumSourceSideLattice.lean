import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralFormsStatement
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainMiddleStageChartsJoinedMember
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZero
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KernelRationalReferenceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardOperatorPreservesRationality
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncreasingRowChoicePerColumn
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormsSharpAtOfValTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeIffIntegralWeylCoordinates

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_memberStep_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (i : ℕ) (hi : i ≤ B.R.m), ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u I.mu0 i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // chOf c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))), I.ReadsK l Z u I.mu0 i hi chOf K ∧ (∀ c, ((K (chOf c)).y ⟨c, rfl⟩).1 = I.yStd u i c) ∧ ((i = 0 ∨ i = B.R.m) → Nonempty (Unique Ch)) := by
  first | exact @GlobalTheory.Mem.Col2.MemChart.exists_charts | exact GlobalTheory.Mem.Col2.MemChart.exists_charts | (intros; apply GlobalTheory.Mem.Col2.MemChart.exists_charts <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_charts_reading_step_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι), ∃ (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a 0).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad 0 (Nat.zero_le _) (fun c : {c // chOf c = β} => (I.chain l u a).stab 0 c.1) (fun c => latCrd (I.rec7 l Z) 0 (Nat.zero_le _) (I.latAt u a 0 c.1))), I.ReadsK l Z u a 0 (Nat.zero_le _) chOf K := by
  first | exact @GlobalTheory.Mem.Col2.TC.Chart0.charts_zero | exact GlobalTheory.Mem.Col2.TC.Chart0.charts_zero | (intros; apply GlobalTheory.Mem.Col2.TC.Chart0.charts_zero <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.DualOffLevel

theorem mem_divs_of {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A}
    (h : P ∈ divs a) : a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · exact (hf.mem_toFinset.1 h)
  · simp at h

theorem isLocBasis_dual_iff_N : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (u : B.Word) (a : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u a w → ∀ (i : ℕ) (hi : i ≤ B.R.m) (c : (I.stp u a i).Cl) (Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (dualSet (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c))) Bm ↔ Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (((I.stp u a i).rep c).1.1.deco.1.N : Set (Sp B.fields.E (B.R.N i))) Bm := by
  intro B X I hOk hPins l Z Y u a w hw i hi c Bm
  classical
  have hpP : ((I.rec7 l Z).what₂.places.resChar w).Prime := (I.rec7 l Z).what₂.places.resChar_prime w
  have hTP : (B.T u).Prime := l.pr.T_prime u
  have hpT : ¬ (I.rec7 l Z).what₂.places.resChar w ∣ B.T u := fun h => hw.1 ((Nat.prime_dvd_prime_iff_eq hpP hTP).1 h)
  obtain ⟨hG, -, hc⟩ := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 i hi
  have hL := (hc u a).1 c
  have hS : dualSet (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)
      (latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) =
      (((I.stp u a i).rep c).1.1.deco.1.Lsh : Set (Sp B.fields.E (B.R.N i))) := by
    rw [hG, hL]
    exact GlobalTheory.Mem.Col2.ValTie.dualSet_std (E := B.fields.E) _ (fun _ => rfl) _
  rw [hS]
  set d := ((I.stp u a i).rep c).1.1.deco with hd
  have hTP' : ∀ P : (B.primes X).vT u, (((B.T u : ℕ) : 𝓞 B.fields.E)) ∈ (P : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal := by
    intro P
    have hpi := mem_divs_of P.2
    rw [← l.pr.piT_norm u]
    exact Ideal.mul_mem_right _ _ hpi
  have hLN : ∀ x ∈ d.1.Lsh, ((B.T u : ℕ) : B.fields.E) • x ∈ d.1.N := by
    intro x hx
    have := d.2.smul_Lsh_mem_N (a := ((B.T u : ℕ) : 𝓞 B.fields.E)) (fun P => by rw [map_natCast]; exact hTP' P) hx
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul B.fields.E] at this
  unfold Formalism.L2.Forms.IsLocBasis
  refine forall_congr' fun x => iff_congr ⟨?_, ?_⟩ Iff.rfl
  · rintro ⟨s, hs, hx⟩
    refine ⟨B.T u * s, fun h => (hpP.dvd_mul.1 h).elim hpT hs, ?_⟩
    have h3 := hLN _ hx
    have e : ((B.T u * s : ℕ) : (I.rec7 l Z).host.E) • x = ((B.T u : ℕ) : (I.rec7 l Z).host.E) • ((s : (I.rec7 l Z).host.E) • x) := by
      rw [smul_smul, ← Nat.cast_mul]
    exact e ▸ h3
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, d.2.N_le_Lsh hx⟩

end GlobalTheory.DualOffLevel
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_localBasis_iff_unimodularCompanion : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (u : B.Word) (a : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u a w → ∀ (i : ℕ) (hi : i ≤ B.R.m) (c : (I.stp u a i).Cl) (Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (dualSet (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c))) Bm ↔ Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (((I.stp u a i).rep c).1.1.deco.1.N : Set (Sp B.fields.E (B.R.N i))) Bm := by
  atlas_forward_decl GlobalTheory.DualOffLevel.isLocBasis_dual_iff_N
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerValRat

theorem lamTG_add_sSharp {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C}
    {P : PeriodMap D.R C} (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)
    (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r : Fin (D.R.N i)) :
    (lamTG M i τ).w r + (D.chTw u μ).sSharp i τ = (nuT D u i τ r : ℤ) := by
  obtain ⟨a, ha⟩ := D.R.t_odd
  have hc : ((i * (D.R.t + 1) / 2 : ℕ) : ℝ) = (i : ℝ) * ((a : ℝ) + 1) := by
    rw [ha, show i * (2 * a + 1 + 1) = 2 * (i * (a + 1)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    push_cast; ring
  have ht : (D.R.t : ℝ) = 2 * a + 1 := by rw [ha]; push_cast; ring
  have h1 := congrArg (Rat.cast : ℚ → ℝ) (M.lam_eq i hi.le τ r)
  have h2 := congrArg (Rat.cast : ℚ → ℝ) ((D.chTw u μ).sSharp_eq i hi τ)
  have h3 := GlobalTheory.PdvKm.nuT_real u i hi τ r
  have he := D.hcW_e u τ
  suffices key : (((lamTG M i τ).w r : ℤ) : ℝ) + (((D.chTw u μ).sSharp i τ : ℤ) : ℝ) = ((nuT D u i τ r : ℕ) : ℝ) by
    exact_mod_cast key
  rw [h3]
  have e0 : (lamTG M i τ).w r = (M.lam i τ).w r - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ) := rfl
  have hl : (((lamTG M i τ).w r : ℤ) : ℝ) = ((((M.lam i τ).w r : ℤ) : ℚ) : ℝ) - (i : ℝ) * ((a : ℝ) + 1) := by
    rw [e0, Int.cast_sub, Int.cast_natCast, hc, Rat.cast_intCast]
  have hs : (((D.chTw u μ).sSharp i τ : ℤ) : ℝ) = ((((D.chTw u μ).sSharp i τ : ℤ) : ℚ) : ℝ) := by rw [Rat.cast_intCast]
  rw [hl, hs, h1, h2]
  have hw : DV.wSz D (i + 1) τ = (((D.hcW u τ).e ⟨i, hi⟩ : ℚ) : ℝ) := by
    unfold DV.wSz
    rw [dif_pos ⟨by omega, by omega⟩, he]
    rfl
  unfold DV.nuRow
  rw [hw]
  unfold DV.srcPar sExp' Ranks.N
  by_cases hk : r.1 < D.R.k
  · rw [dif_pos hk, dif_pos hk]
    unfold hcToWeightQ rhoVec
    push_cast
    rw [ht]
    ring
  · rw [dif_neg hk, dif_neg hk]
    have hr := r.2
    unfold Ranks.N at hr
    have hb : (r.1 - D.R.k) / (D.R.t + 1) < i := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      exact Nat.sub_lt_left_of_lt_add (by omega) hr
    have hbm : (r.1 - D.R.k) / (D.R.t + 1) < D.R.m := by omega
    rw [dif_pos hbm]
    have hdm := Nat.div_add_mod (r.1 - D.R.k) (D.R.t + 1)
    have hr' : (r.1 : ℝ) = D.R.k + (D.R.t + 1) * (((r.1 - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) + (((r.1 - D.R.k) % (D.R.t + 1) : ℕ) : ℝ) := by
      have : r.1 = D.R.k + ((D.R.t + 1) * ((r.1 - D.R.k) / (D.R.t + 1)) + (r.1 - D.R.k) % (D.R.t + 1)) := by omega
      conv_lhs => rw [this]
      push_cast; ring
    unfold wG
    push_cast
    rw [hr', ht]
    ring

end GlobalTheory.KerValRat

namespace GlobalTheory.KerValRat

open GlobalTheory.PdvKm in
theorem detShift_lamTG {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C}
    {P : PeriodMap D.R C} (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)
    (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    (lamTG M i τ).detShift = (nuT D u i τ (lastI D i) : ℤ) - (D.chTw u μ).sSharp i τ := by
  have h := lamTG_add_sSharp M μ i hi τ (lastI D i)
  unfold DomWeight.detShift
  rw [dif_pos (N_pos D i)]
  show (lamTG M i τ).w (lastI D i) = _
  omega

open GlobalTheory.PdvKm in
theorem natW_lamTG {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C}
    {P : PeriodMap D.R C} (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)
    (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r : Fin (D.R.N i)) :
    (M.lam i τ).natW r = nuT D u i τ r - nuT D u i τ (lastI D i) := by
  have h0 : (M.lam i τ).natW r = (lamTG M i τ).natW r := by
    show _ = (Formalism.L2.Forms.shW (M.lam i τ) _).natW r
    rw [Formalism.L2.Forms.natW_shW]
  rw [h0]
  have h1 := lamTG_add_sSharp M D.what₂.mu0 i hi τ r
  have h2 := detShift_lamTG M D.what₂.mu0 i hi τ
  have hle : nuT D u i τ (lastI D i) ≤ nuT D u i τ r :=
    antitone_kernelChain_nuT D u i τ hi (show r ≤ lastI D i by rw [Fin.le_def]; simp only [lastI]; omega)
  unfold DomWeight.natW
  rw [h2]
  omega

end GlobalTheory.KerValRat

namespace GlobalTheory.KerValRat

open GlobalTheory.PdvKm in
theorem evC_ratSpan_gen {D : D7} (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (u : D.what₂.Word) (μ : D.what₂.Tup)
    {A : ColumnsAtT D.R (D.chTw u μ)} {P : PeriodMap D.R (D.chTw u μ)}
    (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) (D.chTw u μ) A P)
    (i : ℕ) (hi : i < D.R.m) (eY : (D.chTw u μ).Y i ≃ Fr D i hi.le)
    (hfrm : ∀ y, (O u μ).frm i y = (eY y).1) (v : ValQ O u μ i) :
    ∃ Q ∈ Formalism.L2.Forms.RatSpan D (M.lam i), ∀ z, evC O u μ i v z =
      fnOf (gramC (gramN D i hi.le) (embT D)) (shiftOf (lamTG M i)) 1 Q (eY z) := by
  have hne : ∀ (z : (D.chTw u μ).Y i) τ, ((eY z).1 τ).det ≠ 0 := fun z τ => by
    rw [← hfrm z, ← (O u μ).frm_de i hi.le z τ]; exact (D.chTw u μ).de_ne i z τ
  have hev : ∀ z, evC O u μ i v z = (∏ τ, (((eY z).1 τ).det) ^ (-(twB D u μ i τ))) *
      MvPolynomial.eval₂ D.what₂.embLL (fun k => (eY z).1 k.1 k.2.1 k.2.2)
        (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL) := by
    intro z
    rw [evC_sec]
    show (∏ τ, ((D.chTw u μ).de i z τ) ^ (-(twB D u μ i τ))) *
      GL3Theta.evFr D (MvPolynomial.map D.what₂.embLL (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL)) ((O u μ).frm i z) = _
    simp only [(O u μ).frm_de i hi.le z, hfrm z, evFr_map]
  have hfn : ∀ (Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) ℂ) z,
      fnOf (gramC (gramN D i hi.le) (embT D)) (shiftOf (lamTG M i)) 1 Q (eY z) =
        (∏ τ, ((eY z).1 τ).det ^ (lamTG M i τ).detShift) * MvPolynomial.eval (fun x => (eY z).1 x.1 x.2.1 x.2.2) Q := by
    intro Q z
    show (∏ τ, ((1 : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ) τ * (eY z).1 τ).det ^ _) *
      MvPolynomial.eval (fun x => ((1 : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ) x.1 * (eY z).1 x.1) x.2.1 x.2.2) Q = _
    simp only [Pi.one_apply, one_mul]
    rfl

  haveI hLL : Infinite D.what₂.LL := Infinite.of_injective (fun n : ℕ => (n : D.what₂.LL)) (fun a b h => by
    have := congrArg D.what₂.embLL h; simp only [map_natCast] at this; exact_mod_cast this)
  have hmem : (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL) ∈ polV D u i := (secC O u μ i v).2
  rcases i with _ | j
  · have h0 : 0 < D.R.m := hi
    have hk : ∀ τ r, nuT D u 0 τ (lastI D 0) ≤ nuT D u 0 τ r := fun τ r =>
      antitone_kernelChain_nuT D u 0 τ h0 (show r ≤ lastI D 0 by rw [Fin.le_def]; simp only [lastI]; omega)
    obtain ⟨P0, hP0, hQe⟩ := frameWeightPolyDivByDet_proof D.what₂.LL D.what₂.Tau (D.R.N 0) (nuT D u 0) (fun τ => nuT D u 0 τ (lastI D 0)) hk _ hmem
    refine ⟨MvPolynomial.map D.what₂.embLL P0, GlobalTheory.LevelHecke.map_mem_ratSpan (M.lam 0) ?_, fun z => ?_⟩
    · rw [VV_eq_WtPol]
      have e : (fun τ r => (M.lam 0 τ).natW r) = fun τ r => nuT D u 0 τ r - nuT D u 0 τ (lastI D 0) :=
        funext fun τ => funext fun r => natW_lamTG M 0 h0 τ r
      rw [e]; exact hP0
    · have hd : ∀ τ, MvPolynomial.eval₂ D.what₂.embLL (fun k : GL3Theta.FrV D (D.R.N 0) => (eY z).1 k.1 k.2.1 k.2.2)
          (frDet D.what₂.LL (D.R.N 0) τ) = ((eY z).1 τ).det := by
        intro τ
        rw [← MvPolynomial.eval_map, Formalism.L2.Ker.map_frDet, Formalism.L2.Ker.eval_frDet]
        rfl
      rw [hev, hfn, hQe, MvPolynomial.eval_map, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_prod]
      simp only [MvPolynomial.eval₂_pow, hd]
      have hs : ∀ τ, (lamTG M 0 τ).detShift = ((nuT D u 0 τ (lastI D 0) : ℕ) : ℤ) - twB D u μ 0 τ :=
        fun τ => detShift_lamTG M μ 0 h0 τ
      simp only [hs]
      rw [prod_zpow_split _ (hne z) _ (fun τ => nuT D u 0 τ (lastI D 0))]
      ring
  · have hj : j < D.R.m := by omega
    refine ⟨MvPolynomial.map D.what₂.embLL (secC O u μ (j + 1) v : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) D.what₂.LL),
      GlobalTheory.LevelHecke.map_mem_ratSpan (M.lam (j + 1)) ?_, fun z => ?_⟩
    · rw [VV_eq_WtPol]
      have e : (fun τ r => (M.lam (j + 1) τ).natW r) = extNu (D.R.N (j + 1)) (nuT D u j) := by
        funext τ r
        rw [natW_lamTG M (j + 1) hi τ r, ← natW_succ (antitone_kernelChain_nuT D) u j hj τ r]
        have h1 := clause1 (antitone_kernelChain_nuT D) u (j + 1) hi τ r
        have h2 : nn D u (j + 1) τ = nuT D u (j + 1) τ (lastI D (j + 1)) := by unfold nn; rw [if_pos hi]
        omega
      rw [e]; exact hmem
    · rw [hev, hfn, MvPolynomial.eval_map]
      congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      congr 1
      rw [detShift_lamTG M μ (j + 1) hi τ]
      have h1 := last_real u μ j hi τ
      show -((D.chTw u μ).sDiv j τ) = _
      have h2 : ((nuT D u (j + 1) τ (lastI D (j + 1)) : ℕ) : ℤ) = (D.chTw u μ).sSharp (j + 1) τ - (D.chTw u μ).sDiv j τ := by
        exact_mod_cast h1
      omega

end GlobalTheory.KerValRat

namespace GlobalTheory.KerValRat

theorem evC_ratSpan : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → ∀ (u : B.Word) (μ : I.ι) (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ v : ValQ O u μ i, ∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, evC O u μ i v z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z) := by
  intro B X I hOk hPins l Z Y O hQ hS u μ i hi eY hId v
  exact evC_ratSpan_gen O u μ (I.fm l u μ) i hi eY (fun y => (hS.frm u μ i y).trans (hId y).symm) v

end GlobalTheory.KerValRat
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexValue_det_shift_mul_ratSpan : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → ∀ (u : B.Word) (μ : I.ι) (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ v : ValQ O u μ i, ∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, evC O u μ i v z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z) := by
  atlas_forward_decl GlobalTheory.KerValRat.evC_ratSpan
end

section
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylReproducing

open Formalism.GradedWeylDivisibility GlobalTheory.WeylMinorDual

theorem rowAct_leadMinor (N h : ℕ) (hh : h ≤ N) (x : Fin N × Fin N → ℚ) :
    rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)).transpose (initMinor ℚ (r := N) (n := N) (Fin.castLE hh) hh) =
      ∑ K : Fin h ↪o Fin N, C (eval x (initMinor ℚ (r := N) (n := N) (⇑K) hh)) *
        initMinor ℚ (r := N) (n := N) (⇑K) hh := by
  set A : Matrix (Fin h) (Fin N) (MvPolynomial (Fin N × Fin N) ℚ) :=
    Matrix.of fun p b => C (x (b, Fin.castLE hh p)) with hA
  set B : Matrix (Fin N) (Fin h) (MvPolynomial (Fin N × Fin N) ℚ) :=
    Matrix.of fun b q => X (b, Fin.castLE hh q) with hB
  have hM : rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)).transpose (initMinor ℚ (r := N) (n := N) (Fin.castLE hh) hh)
      = (A * B).det := by
    unfold initMinor
    rw [AlgHom.map_det]
    congr 1
    ext p q
    simp [rowAct, Matrix.mul_apply, hA, hB]
  rw [hM, PI.IsoDerivBFintype.cauchyBinet]
  refine Finset.sum_congr rfl fun K _ => ?_
  congr 1
  · rw [← Matrix.det_transpose (A.submatrix id K)]
    unfold initMinor
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext p k
    simp [hA]

theorem rowAct_hw_expand (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (x : Fin N × Fin N → ℚ) :
    rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)).transpose (hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) =
      ∑ J : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y, C (eval x (colProd ℚ N Y hY J)) * colProd ℚ N Y hY J := by
  have hwEq : hw ℚ le_rfl (fun r : Fin N => Y.rowLen r) =
      bideterminant ℚ (r := N) (n := N) (fun c : Fin (Y.rowLen 0) => Y.colLen c) (colLen_le hY)
        (fun c => Fin.castLE (colLen_le hY c)) := by
    rw [bidet_lead ℚ N (fun c : Fin (Y.rowLen 0) => Y.colLen c) (colLen_le hY) _ (fun c i => rfl), shapeDeg_colLen]
  rw [hwEq]
  unfold bideterminant
  rw [map_prod]
  simp_rw [rowAct_leadMinor]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, ← map_prod]
  rfl

theorem reproducing (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (h : MvPolynomial (Fin N × Fin N) ℚ)
    (hh : h ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r => Y.rowLen r)) :
    ∑ J : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y, Formalism.GradedWeylDivisibility.fockQ h (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) •
        GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J
      = Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r))
          (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) • h := by
  set μ : Fin N → ℕ := fun r => Y.rowLen r with hμ
  have hanti : Antitone μ := fun a b hab => Y.rowLen_anti a b hab

  let L : MvPolynomial (Fin N × Fin N) ℚ →ₗ[ℚ] ℚ :=
    { toFun := fun g => fockQ g h
      map_add' := fun f f' => (fockQBilin _ f f' h 1).1
      map_smul' := fun c f => (fockQBilin _ f 0 h c).2 }
  apply MvPolynomial.funext
  intro x
  set z : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun a s : Fin N => x (a, s) with hz
  have hev : eval (idFrame ℚ N N) (rowAct ℚ z h) = eval x h := by
    have : (eval (idFrame ℚ N N)).comp (rowAct ℚ z).toRingHom = eval x := by
      refine MvPolynomial.ringHom_ext (fun a => by simp [rowAct]) fun v => ?_
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rowAct, aeval_X, eval_X,
        map_sum, map_mul, eval_C, idFrame]
      rw [Finset.sum_eq_single v.2]
      · simp [hz]
      · intro b _ hb
        simp [Fin.val_inj, hb]
      · simp
    exact congrArg (fun f => f h) this
  have key1 : fockQ h (rowAct ℚ z.transpose (hw ℚ le_rfl μ)) =
      ∑ J : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y, fockQ h (colProd ℚ N Y hY J) * eval x (colProd ℚ N Y hY J) := by
    rw [hz, rowAct_hw_expand, (fockQPos _ _ _).1]
    change L _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [C_mul', L.map_smul, smul_eq_mul, mul_comm]
    change fockQ _ h * _ = _
    rw [(fockQPos _ _ _).1]
  have key2 : fockQ h (rowAct ℚ z.transpose (hw ℚ le_rfl μ)) = eval x h * fockQ (hw ℚ le_rfl μ) (hw ℚ le_rfl μ) := by
    rw [← fock_space_row_action, (fockQPos _ _ _).1,
      fock_space_highest_weight N N le_rfl μ hanti _ (dualWeylRowStable ℚ N N μ z h hh), hev]
  rw [map_sum, smul_eval]
  simp only [smul_eval]
  rw [← key1, key2, mul_comm]

end GlobalTheory.WeylReproducing
end
end

open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnMinorProducts_fock_reproducing_identity : ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (h : MvPolynomial (Fin N × Fin N) ℚ),
    h ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r => Y.rowLen r) →
    ∑ J : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y, Formalism.GradedWeylDivisibility.fockQ h (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J
      = Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) • h := by
  atlas_forward_decl GlobalTheory.WeylReproducing.reproducing
end

section
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylLatDualProof

def fockQRight {σ : Type} (f : MvPolynomial σ ℚ) : MvPolynomial σ ℚ →ₗ[ℚ] ℚ where
  toFun g := Formalism.GradedWeylDivisibility.fockQ f g
  map_add' g g' := by
    show Formalism.GradedWeylDivisibility.fockQ f (g + g') = Formalism.GradedWeylDivisibility.fockQ f g + Formalism.GradedWeylDivisibility.fockQ f g'
    rw [(Formalism.GradedWeylDivisibility.fockQPos σ f _).1, (Formalism.GradedWeylDivisibility.fockQBilin σ g g' f 1).1, (Formalism.GradedWeylDivisibility.fockQPos σ g f).1,
      (Formalism.GradedWeylDivisibility.fockQPos σ g' f).1]
  map_smul' c g := by
    show Formalism.GradedWeylDivisibility.fockQ f (c • g) = c • Formalism.GradedWeylDivisibility.fockQ f g
    rw [smul_eq_mul, (Formalism.GradedWeylDivisibility.fockQPos σ f _).1, (Formalism.GradedWeylDivisibility.fockQBilin σ g 0 f c).2, (Formalism.GradedWeylDivisibility.fockQPos σ g f).1]

theorem fockQRight_apply {σ : Type} (f g : MvPolynomial σ ℚ) : fockQRight f g = Formalism.GradedWeylDivisibility.fockQ f g := rfl

theorem dual_bases_colProd : (∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (h : MvPolynomial (Fin N × Fin N) ℚ),
    h ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r => Y.rowLen r) →
    ∑ J : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y, Formalism.GradedWeylDivisibility.fockQ h (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J
      = Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) • h) →
  ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N),
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b g : ι → MvPolynomial (Fin N × Fin N) ℚ)
    (c : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y → ι → ℤ) (d : ι → GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y → ℤ) (Nc : ℚ), Nc ≠ 0 ∧
    (∀ J, GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J = ∑ k, (c J k : ℚ) • b k) ∧
    (∀ k, b k = ∑ J, (d k J : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) ∧
    (∀ k, g k = ∑ J, (c J k : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) ∧
    (∀ i k, Formalism.GradedWeylDivisibility.fockQ (b i) (g k) = if i = k then Nc else 0) ∧
    Submodule.span ℤ (Set.range g) =
      (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl (fun r : Fin N => Y.rowLen r)).map (Formalism.GradedWeylDivisibility.intQ N N) := by
  classical
  intro H N Y hY
  have hanti : Antitone (fun r : Fin N => Y.rowLen r) := fun a b hab => Y.rowLen_anti _ _ hab
  haveI : Fintype (Formalism.GradedWeylDivisibility.ssIdx N N (fun r : Fin N => Y.rowLen r)) := (Formalism.GradedWeylDivisibility.sSIdxFinite N N _).fintype
  obtain ⟨b, d, hb, hd, hbd⟩ := GlobalTheory.StdDual.exists_dual_bases N (fun r : Fin N => Y.rowLen r) hanti
  set Nc := Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
    (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) with hNc
  have hNc0 : Nc ≠ 0 := ((Formalism.GradedWeylDivisibility.fockQPos _ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
    (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))).2 (Formalism.GradedWeylDivisibility.hwNe ℚ N N le_rfl _)).ne'
  have H' := H N Y hY
  clear H
  set C := GlobalTheory.WeylMinorDual.colProd ℚ N Y hY with hCdef
  have hspanC : Submodule.span ℤ (GlobalTheory.StdDual.bidSet ℚ N (fun r : Fin N => Y.rowLen r)) =
      Submodule.span ℤ (Set.range C) := by
    rw [← GlobalTheory.StdDual.dualWeyl_intQ, GlobalTheory.WeylMinorDual.dualWeyl_eq_span_colProd ℤ N Y hY, Submodule.map_span,
      ← Set.range_comp]
    congr 2
    funext J
    exact Formalism.L2.DIV.fk_map_bidet (Int.castRingHom ℚ) _ _ _
  have hbC : Submodule.span ℤ (Set.range b) = Submodule.span ℤ (Set.range C) := hb.trans hspanC
  have hCb : ∀ J, C J ∈ Submodule.span ℤ (Set.range b) := fun J => hbC ▸ Submodule.subset_span ⟨J, rfl⟩
  have hbCm : ∀ k, b k ∈ Submodule.span ℤ (Set.range C) := fun k => hbC ▸ Submodule.subset_span ⟨k, rfl⟩
  choose c hc using fun J => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hCb J)
  choose d' hd' using fun k => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hbCm k)
  have hcQ : ∀ J, C J = ∑ k, (c J k : ℚ) • b k := fun J => by
    rw [← hc J]; simp only [Int.cast_smul_eq_zsmul]
  have hdQ : ∀ k, b k = ∑ J, (d' k J : ℚ) • C J := fun k => by
    rw [← hd' k]; simp only [Int.cast_smul_eq_zsmul]
  set g := fun k => ∑ J, (c J k : ℚ) • C J with hg
  have hdb : ∀ j k, Formalism.GradedWeylDivisibility.fockQ (d j) (b k) = if k = j then Nc else 0 := fun j k =>
    (Formalism.GradedWeylDivisibility.fockQPos _ _ _).1.trans (hbd k j)
  have hdC : ∀ j J, Formalism.GradedWeylDivisibility.fockQ (d j) (C J) = (c J j : ℚ) * Nc := by
    intro j J
    rw [hcQ J, ← fockQRight_apply, map_sum]
    simp only [map_smul, fockQRight_apply, hdb, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hgi : ∀ i k, Formalism.GradedWeylDivisibility.fockQ (b i) (g k) = ∑ J, (c J k : ℚ) * Formalism.GradedWeylDivisibility.fockQ (b i) (C J) := by
    intro i k
    rw [← fockQRight_apply, hg, map_sum]
    simp only [map_smul, fockQRight_apply, smul_eq_mul]
  have key : ∀ i k, Formalism.GradedWeylDivisibility.fockQ (b i) (g k) = if i = k then Nc else 0 := by
    intro i k
    have hmem : b i ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r) := by
      rw [GlobalTheory.StdDual.dualWeyl_eq]
      exact Submodule.span_le_restrictScalars ℤ ℚ _ (hb ▸ Submodule.subset_span ⟨i, rfl⟩)
    have h1 := congrArg (fockQRight (d k)) (H' (b i) hmem)
    rw [map_sum, map_smul] at h1
    simp only [map_smul, fockQRight_apply, smul_eq_mul, hdC] at h1
    rw [hdb] at h1
    rw [hgi]
    apply mul_right_cancel₀ hNc0
    rw [Finset.sum_mul]
    exact Eq.trans (Finset.sum_congr rfl fun J _ => by ring) (h1.trans (mul_comm _ _))
  have hgd : ∀ k, g k = d k := by
    intro k
    have hg1 : g k ∈ Submodule.span ℤ (Set.range b) := by
      rw [hbC, hg]
      refine Submodule.sum_mem _ fun J _ => ?_
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨J, rfl⟩)
    have hd1 : d k ∈ Submodule.span ℤ (Set.range b) := by
      have h2 : d k ∈ (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl (fun r : Fin N => Y.rowLen r)).map (Formalism.GradedWeylDivisibility.intQ N N) := by
        rw [GlobalTheory.StdDual.weyl_intQ, ← hd]
        exact Submodule.subset_span ⟨k, rfl⟩
      have h3 := Submodule.map_mono (f := Formalism.GradedWeylDivisibility.intQ N N) (Formalism.GradedWeylDivisibility.weylLeDual ℤ N N le_rfl _ hanti) h2
      rwa [GlobalTheory.StdDual.dualWeyl_intQ, ← hb] at h3
    have hx := Submodule.sub_mem _ hg1 hd1
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    have horth : ∀ i, Formalism.GradedWeylDivisibility.fockQ (g k - d k) (b i) = 0 := by
      intro i
      rw [(Formalism.GradedWeylDivisibility.fockQPos _ _ _).1, ← fockQRight_apply, map_sub, fockQRight_apply, fockQRight_apply, key,
        ← (Formalism.GradedWeylDivisibility.fockQPos _ _ _).1, hdb]
      split_ifs with h1 h2 h2 <;> first | rfl | simp | (exact absurd h1.symm h2) | (exact absurd h2.symm h1)
    have h0 : Formalism.GradedWeylDivisibility.fockQ (g k - d k) (g k - d k) = 0 := by
      rw [← fockQRight_apply]
      nth_rewrite 2 [← ha]
      rw [map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_zsmul, fockQRight_apply, horth, smul_zero]
    by_contra hne
    exact (ne_of_gt ((Formalism.GradedWeylDivisibility.fockQPos _ (g k - d k) (g k - d k)).2 (sub_ne_zero.mpr hne))) h0
  refine ⟨Formalism.GradedWeylDivisibility.ssIdx N N (fun r : Fin N => Y.rowLen r), inferInstance, inferInstance, b, g, c, d', Nc, hNc0,
    hcQ, hdQ, fun k => rfl, key, ?_⟩
  have : g = d := funext hgd
  rw [this, hd, GlobalTheory.StdDual.weyl_intQ]

end GlobalTheory.WeylLatDualProof
end
end

open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_bases_colProd_alt : (∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (h : MvPolynomial (Fin N × Fin N) ℚ),
    h ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r => Y.rowLen r) →
    ∑ J : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y, Formalism.GradedWeylDivisibility.fockQ h (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J
      = Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) • h) →
  ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N),
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b g : ι → MvPolynomial (Fin N × Fin N) ℚ)
    (c : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y → ι → ℤ) (d : ι → GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y → ℤ) (Nc : ℚ), Nc ≠ 0 ∧
    (∀ J, GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J = ∑ k, (c J k : ℚ) • b k) ∧
    (∀ k, b k = ∑ J, (d k J : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) ∧
    (∀ k, g k = ∑ J, (c J k : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) ∧
    (∀ i k, Formalism.GradedWeylDivisibility.fockQ (b i) (g k) = if i = k then Nc else 0) ∧
    Submodule.span ℤ (Set.range g) =
      (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl (fun r : Fin N => Y.rowLen r)).map (Formalism.GradedWeylDivisibility.intQ N N) := by
  atlas_forward_decl GlobalTheory.WeylLatDualProof.dual_bases_colProd
end

section
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylLatDualProof

theorem prod_zsum_expand {A : Type*} [CommRing A] {L : Type*} [Fintype L] [DecidableEq L]
    {α β : L → Type*} [∀ s, Fintype (β s)] (f : ∀ s, α s → A) (g : ∀ s, β s → A)
    (c : ∀ s, α s → β s → ℤ) (h : ∀ s j, f s j = ∑ k, c s j k • g s k) (j : ∀ s, α s) :
    ∏ s, f s (j s) = ∑ κ : (∀ s, β s), (∏ s, c s (j s) (κ s)) • ∏ s, g s (κ s) := by
  simp only [h, zsmul_eq_mul]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [Finset.prod_mul_distrib]
  push_cast
  rfl

theorem norm_dual_zsum_le_one (p : ℕ) [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module ℂ_[p] M]
    (φ : Module.Dual ℂ_[p] M) {κ : Type*} [Fintype κ] (n : κ → ℤ) (x : κ → M)
    (hx : ∀ k, ‖φ (x k)‖ ≤ 1) : ‖φ (∑ k, n k • x k)‖ ≤ 1 := by
  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [map_zsmul, zsmul_eq_mul, norm_mul]
  calc ‖(n k : ℂ_[p])‖ * ‖φ (x k)‖ ≤ 1 * 1 :=
        mul_le_mul (IsUltrametricDist.norm_intCast_le_one _ _) (hx k) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem integral_minors_iff_basis : ∀ (p : ℕ) [Fact p.Prime] (Lt : Type) [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ)
    (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ) (d : ∀ s, ι s → GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, b s k = ∑ J, (d s k J : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
      (∀ J : WeylLatticeDuality.ColChoice N nu,
          ‖φ (MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J))‖ ≤ 1) ↔
        ∀ κ : (∀ s, ι s), ‖φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
          (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s))))‖ ≤ 1 := by
  intro p _ Lt _ N nu hY ι _ b c d hc hd φ
  classical
  let Ψ : Lt → MvPolynomial (Fin N × Fin N) ℚ →+* MvPolynomial (Lt × ℕ × Fin N) ℂ_[p] := fun s =>
    (MvPolynomial.map (algebraMap ℚ ℂ_[p])).comp (MvPolynomial.rename (sig N s)).toRingHom
  have hF : ∀ J : WeylLatticeDuality.ColChoice N nu,
      MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J) =
        ∏ s, Ψ s (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) (J s)) := by
    intro J
    have h1 : Int.castRingHom ℂ_[p] = (algebraMap ℚ ℂ_[p]).comp (Int.castRingHom ℚ) := RingHom.ext_int _ _
    rw [h1, ← MvPolynomial.map_map, map_nablaX ℚ N nu hY J, map_prod]
    rfl
  have hG : ∀ κ : (∀ s, ι s), MvPolynomial.map (algebraMap ℚ ℂ_[p])
      (∏ s, MvPolynomial.rename (sig N s) (b s (κ s))) = ∏ s, Ψ s (b s (κ s)) := by
    intro κ
    rw [map_prod]
    rfl
  have hc' : ∀ s J, Ψ s (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) = ∑ k, c s J k • Ψ s (b s k) := by
    intro s J
    rw [hc, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← map_zsmul, Int.cast_smul_eq_zsmul]
  have hd' : ∀ s k, Ψ s (b s k) = ∑ J, d s k J • Ψ s (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) := by
    intro s k
    conv_lhs => rw [hd]
    rw [map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [← map_zsmul, Int.cast_smul_eq_zsmul]
  constructor
  · intro h κ
    rw [hG, prod_zsum_expand (fun s k => Ψ s (b s k)) _ d hd' κ]
    refine norm_dual_zsum_le_one p φ _ _ fun J => ?_
    exact (le_of_eq (congrArg (fun x => ‖φ x‖) (hF J)).symm).trans (h J)
  · intro h J
    rw [hF, prod_zsum_expand (fun s J => Ψ s (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J)) _ c hc' J]
    refine norm_dual_zsum_le_one p φ _ _ fun κ => ?_
    have := h κ
    rw [hG] at this
    exact this

end GlobalTheory.WeylLatDualProof
end
end

open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_minors_iff_basis_alt : ∀ (p : ℕ) [Fact p.Prime] (Lt : Type) [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ)
    (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ) (d : ∀ s, ι s → GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, b s k = ∑ J, (d s k J : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
      (∀ J : WeylLatticeDuality.ColChoice N nu,
          ‖φ (MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J))‖ ≤ 1) ↔
        ∀ κ : (∀ s, ι s), ‖φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
          (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s))))‖ ≤ 1 := by
  atlas_forward_decl GlobalTheory.WeylLatDualProof.integral_minors_iff_basis
end

section
section
open MvPolynomial

noncomputable section
namespace GlobalTheory.WeylLatDualProof

theorem minY_colsOf_eq (p : ℕ) [Fact p.Prime] {Lt T : Type} [Fintype Lt] (e : Lt → T) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (y : T → Matrix (Fin N) (Fin N) ℂ_[p])
    (J : ∀ s, IncreasingRowChoicePerColumn N (nu s)) :
    PI.WwCauchyBinet.minY N nu J (fun s => WeylLatticeDuality.colsOf (y (e s))) =
      ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
        (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) (J s))) := by
  unfold PI.WwCauchyBinet.minY GlobalTheory.WeylMinorDual.colProd Formalism.GradedWeylDivisibility.bideterminant
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  have hj : (j : ℕ) < N := lt_of_lt_of_le j.2 (GlobalTheory.WeylMinorDual.colLen_le (hY s) c)
  simp [WeylLatticeDuality.colsOf, hj, Fin.castLE]

theorem map_nablaX_expand (p : ℕ) [Fact p.Prime] {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (c : ∀ s, IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ)
    (hb : ∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k)
    (J : ∀ s, IncreasingRowChoicePerColumn N (nu s)) :
    MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J) =
      ∑ κ : (∀ s, ι s), (∏ s, ((c s (J s) (κ s) : ℤ) : ℂ_[p])) •
        MvPolynomial.map (algebraMap ℚ ℂ_[p]) (∏ s, MvPolynomial.rename (sig N s) (b s (κ s))) := by
  have h0 : (Int.castRingHom ℂ_[p]) = (algebraMap ℚ ℂ_[p]).comp (Int.castRingHom ℚ) := RingHom.ext_int _ _
  rw [h0, ← MvPolynomial.map_map, map_nablaX ℚ N nu hY J]
  simp_rw [hb, map_sum, map_smul]
  rw [Fintype.prod_sum, map_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  simp only [smul_eq_C_mul, Finset.prod_mul_distrib, map_mul, map_prod, MvPolynomial.map_C]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  simp

theorem phi_DeX_expand : ∀ (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (e : Lt → T) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, g s k = ∑ J, (c s J k : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ (φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p])) (y : T → Matrix (Fin N) (Fin N) ℂ_[p]),
      φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s))) =
        ∑ κ : (∀ s, ι s), φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
            (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s)))) *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) := by
  intro p _ Lt T _ _ _ e N nu hY ι _ b g c hb hg φ y
  have h1 := cauchy_binet_minors Lt ℂ_[p] N nu (fun s => WeylLatticeDuality.colsOf (y (e s)))
  rw [finsum_eq_sum_of_fintype] at h1
  have h2 : WeylLatticeDuality.DeX N nu (fun s => WeylLatticeDuality.colsOf (y (e s))) =
      ∑ J : (∀ s, IncreasingRowChoicePerColumn N (nu s)), MvPolynomial.C (PI.WwCauchyBinet.minY N nu J
        (fun s => WeylLatticeDuality.colsOf (y (e s)))) *
        MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J) := by
    convert h1 using 2
    all_goals try rfl
  have hG : ∀ s k, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
      (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s k)) = ∑ J, ((c s J k : ℤ) : ℂ_[p]) *
        MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
          (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J)) := by
    intro s k
    rw [hg]
    simp [map_sum, smul_eq_C_mul]
  rw [h2, map_sum]
  simp_rw [MvPolynomial.C_mul', map_smul, map_nablaX_expand p N nu hY ι b c hb, minY_colsOf_eq p e N nu hY y,
    map_sum, map_smul, smul_eq_mul, hG, Fintype.prod_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

end GlobalTheory.WeylLatDualProof
end
end

open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_DeX_expand_alt : ∀ (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (e : Lt → T) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, g s k = ∑ J, (c s J k : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ (φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p])) (y : T → Matrix (Fin N) (Fin N) ℂ_[p]),
      φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s))) =
        ∑ κ : (∀ s, ι s), φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
            (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s)))) *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) := by
  atlas_forward_decl GlobalTheory.WeylLatDualProof.phi_DeX_expand
end

section
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylCombInt

open Formalism.L2.DIV

theorem weyl_eq (N : ℕ) (ν : Fin N → ℕ) :
    Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν = WeylLatticeDuality.weyl ℤ N N le_rfl ν := rfl

theorem eval_ten {K Lt : Type} [Field K] [Fintype Lt] {N : ℕ} (f : Lt → MvPolynomial (Fin N × Fin N) K)
    (z : Lt × Fin N × Fin N → K) : eval z (ten f) = ∏ s, eval (fun v => z (s, v)) (f s) := by
  unfold ten
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [Formalism.GradedWeylDivisibility.blockEmb, eval_rename]
  rfl

theorem fockB_ten_dual {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {K : Type} [Field K] [CharZero K]
    (ι : Lt → Type) [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (Nc : Lt → ℚ)
    (hbg : ∀ s i k, Formalism.GradedWeylDivisibility.fockQ (b s i) (g s k) = if i = k then Nc s else 0) (κ' κ : ∀ s, ι s) :
    fockB (ten fun s => map (algebraMap ℚ K) (b s (κ' s))) (ten fun s => map (algebraMap ℚ K) (g s (κ s))) =
      if κ' = κ then ∏ s, (Nc s : K) else 0 := by
  rw [GlobalTheory.WeylMinorDual.fockB_ten]
  simp only [GlobalTheory.WeylMinorDual.fockB_map, hbg]
  split_ifs with h
  · subst h; simp
  · obtain ⟨s, hs⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])

theorem coeff_unique (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T]
    (e : Lt → T) (he : Function.Bijective e) (N : ℕ) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    [∀ s, DecidableEq (ι s)] (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (Nc : Lt → ℚ)
    (hNc : ∀ s, Nc s ≠ 0) (hbg : ∀ s i k, Formalism.GradedWeylDivisibility.fockQ (b s i) (g s k) = if i = k then Nc s else 0)
    (c : (∀ s, ι s) → ℂ_[p])
    (h : ∀ y : T → Matrix (Fin N) (Fin N) ℂ_[p], ∑ κ, c κ * ∏ s, MvPolynomial.eval
      (fun k : Fin N × Fin N => y (e s) k.1 k.2) (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) = 0) :
    c = 0 := by
  set E := Equiv.ofBijective e he with hE
  set P : (∀ s, ι s) → MvPolynomial (Lt × Fin N × Fin N) ℂ_[p] :=
    fun κ => ten fun s => map (algebraMap ℚ ℂ_[p]) (g s (κ s)) with hP
  have h0 : ∑ κ, c κ • P κ = 0 := by
    apply MvPolynomial.funext
    intro z
    have hz := h (fun τ => Matrix.of fun i j => z (E.symm τ, i, j))
    rw [map_zero, map_sum]
    rw [← hz]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [smul_eval, hP]
    simp only [eval_ten]
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    have hs : E.symm (e s) = s := by
      rw [← Equiv.ofBijective_apply e he]; exact E.symm_apply_apply s
    simp only [Matrix.of_apply, hs]
  funext κ'
  have h1 := congrArg (fockB (ten fun s => map (algebraMap ℚ ℂ_[p]) (b s (κ' s)))) h0
  rw [← fockBL_apply, ← fockBL_apply, map_sum, map_zero] at h1
  simp only [map_smul, fockBL_apply, hP, fockB_ten_dual ι b g Nc hbg, smul_eq_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  have hne : ∏ s, (Nc s : ℂ_[p]) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun s _ => by exact_mod_cast hNc s
  simpa [hne] using h1

theorem map_intQ (p : ℕ) [Fact p.Prime] (N : ℕ) (w : MvPolynomial (Fin N × Fin N) ℤ) :
    map (algebraMap ℚ ℂ_[p]) (Formalism.GradedWeylDivisibility.intQ N N w) = map (Int.castRingHom ℂ_[p]) w := by
  have : Formalism.GradedWeylDivisibility.intQ N N w = map (Int.castRingHom ℚ) w := rfl
  rw [this, map_map, show (algebraMap ℚ ℂ_[p]).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ_[p] from
    RingHom.ext_int _ _]

theorem comb_mem_iff : ∀ (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (e : Lt → T), Function.Bijective e →
    ∀ (N : ℕ) (ν : T → Fin N → ℕ) (ι : Lt → Type) [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (Nc : Lt → ℚ), (∀ s, Nc s ≠ 0) →
    (∀ s i k, Formalism.GradedWeylDivisibility.fockQ (b s i) (g s k) = if i = k then Nc s else 0) →
    (∀ s, Submodule.span ℤ (Set.range (g s)) =
      (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl (ν (e s))).map (Formalism.GradedWeylDivisibility.intQ N N)) →
    ∀ a : (∀ s, ι s) → ℂ_[p],
      ((fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => ∑ κ : (∀ s, ι s), a κ *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s)))) ∈ WeylLatticeDuality.DelW p T N ν ↔
        ∀ κ, ‖a κ‖ ≤ 1) := by
  intro p _ Lt T _ _ _ e he N ν ι _ _ b g Nc hNc hbg hspan a
  set E := Equiv.ofBijective e he with hE
  have hs : ∀ s, E.symm (e s) = s := fun s => by
    rw [← Equiv.ofBijective_apply e he]; exact E.symm_apply_apply s
  set G : (∀ s, ι s) → (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p] := fun κ y =>
    ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
      (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) with hG
  constructor
  · intro hmem
    let S : AddSubgroup ((T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) :=
      { carrier := {F | ∃ a' : (∀ s, ι s) → ℂ_[p], (∀ κ, ‖a' κ‖ ≤ 1) ∧ F = fun y => ∑ κ, a' κ * G κ y}
        zero_mem' := ⟨0, fun _ => by simp, by funext y; simp⟩
        add_mem' := by
          rintro F F' ⟨a1, h1, rfl⟩ ⟨a2, h2, rfl⟩
          refine ⟨a1 + a2, fun κ => ?_, ?_⟩
          · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1 κ) (h2 κ))
          · funext y; simp [add_mul, Finset.sum_add_distrib]
        neg_mem' := by
          rintro F ⟨a1, h1, rfl⟩
          refine ⟨-a1, fun κ => by simpa using h1 κ, ?_⟩
          funext y; simp [neg_mul, Finset.sum_neg_distrib] }
    have hle : WeylLatticeDuality.DelW p T N ν ≤ S := by
      unfold WeylLatticeDuality.DelW
      rw [AddSubgroup.closure_le]
      rintro F ⟨r, f, hr, hf, rfl⟩
      have hn : ∀ s, ∃ n : ι s → ℤ, ∑ k, n k • g s k = Formalism.GradedWeylDivisibility.intQ N N (f (e s)) := by
        intro s
        rw [← Submodule.mem_span_range_iff_exists_fun, hspan s, weyl_eq]
        exact Submodule.mem_map_of_mem (hf (e s))
      choose n hn using hn
      refine ⟨fun κ => r * ∏ s, ((n s (κ s) : ℤ) : ℂ_[p]), fun κ => ?_, ?_⟩
      · rw [norm_mul, norm_prod]
        exact mul_le_one₀ hr (by positivity)
          (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun s _ => IsUltrametricDist.norm_intCast_le_one _ _)
      · funext y
        rw [← he.prod_comp]
        have hterm : ∀ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f (e s))) =
            ∑ k, ((n s k : ℤ) : ℂ_[p]) * MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
              (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s k)) := by
          intro s
          rw [← map_intQ, ← hn s, map_sum, map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_zsmul, map_zsmul, zsmul_eq_mul]
        simp only [hterm, Fintype.prod_sum, Finset.mul_sum, hG]
        refine Finset.sum_congr rfl fun κ _ => ?_
        rw [Finset.prod_mul_distrib]; ring
    obtain ⟨a', ha', heq⟩ := hle hmem
    have hc := coeff_unique p Lt T e he N ι b g Nc hNc hbg (a - a') (fun y => by
      have := congrFun heq y
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]; exact this)
    have : a = a' := sub_eq_zero.mp hc
    subst this; exact ha'
  · intro ha
    have hw : ∀ s k, ∃ w ∈ WeylLatticeDuality.weyl ℤ N N le_rfl (ν (e s)), Formalism.GradedWeylDivisibility.intQ N N w = g s k := by
      intro s k
      have : g s k ∈ Submodule.span ℤ (Set.range (g s)) := Submodule.subset_span (Set.mem_range_self k)
      rw [hspan s, weyl_eq] at this
      exact this
    choose w hw hwg using hw
    have hfun : (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => ∑ κ : (∀ s, ι s), a κ * G κ y) =
        ∑ κ : (∀ s, ι s), fun y => a κ * G κ y := by
      funext y; simp [Finset.sum_apply]
    show (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => ∑ κ : (∀ s, ι s), a κ * G κ y) ∈ _
    rw [hfun]
    refine AddSubgroup.sum_mem _ fun κ _ => AddSubgroup.subset_closure ?_
    refine ⟨a κ, fun τ => w (E.symm τ) (κ (E.symm τ)), ha κ, fun τ => ?_, ?_⟩
    · have := hw (E.symm τ) (κ (E.symm τ))
      rwa [show e (E.symm τ) = τ from E.apply_symm_apply τ] at this
    · funext y
      congr 1
      rw [← he.prod_comp]
      refine Finset.prod_congr rfl fun s _ => ?_
      dsimp only
      rw [hs s, ← hwg s (κ s), map_intQ]

end GlobalTheory.WeylCombInt
end
end

open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comb_mem_iff_alt : ∀ (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (e : Lt → T), Function.Bijective e →
    ∀ (N : ℕ) (ν : T → Fin N → ℕ) (ι : Lt → Type) [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (Nc : Lt → ℚ), (∀ s, Nc s ≠ 0) →
    (∀ s i k, Formalism.GradedWeylDivisibility.fockQ (b s i) (g s k) = if i = k then Nc s else 0) →
    (∀ s, Submodule.span ℤ (Set.range (g s)) =
      (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl (ν (e s))).map (Formalism.GradedWeylDivisibility.intQ N N)) →
    ∀ a : (∀ s, ι s) → ℂ_[p],
      ((fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => ∑ κ : (∀ s, ι s), a κ *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s)))) ∈ WeylLatticeDuality.DelW p T N ν ↔
        ∀ κ, ‖a κ‖ ≤ 1) := by
  atlas_forward_decl GlobalTheory.WeylCombInt.comb_mem_iff
end

section
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylLatDualProof

theorem mainProof : WeylLatticeDuality.Stmt := by
  intro p _ Lt T _ _ e he N nu ν hrow hzero φ
  classical
  have hY : ∀ s, (nu s).colLen 0 ≤ N := fun s => colLen_le_of_rowLen (hzero s N le_rfl)
  have hν : ∀ s, ν (e s) = fun r : Fin N => (nu s).rowLen r := fun s => funext fun r => (hrow s r).symm
  choose ι hι hdec b g c d Nc hNc h1 h2 h3 h4 h5 using fun s => GlobalTheory.T.dual_bases_colProd_alt GlobalTheory.T.columnMinorProducts_fock_reproducing_identity N (nu s) (hY s)
  rw [GlobalTheory.T.integral_minors_iff_basis_alt p Lt N nu hY ι b c d h1 h2 φ]
  have hfun : (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] =>
      φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s)))) = fun y =>
        ∑ κ : (∀ s, ι s), φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
            (∏ s, MvPolynomial.rename (sig N s) (b s (κ s)))) *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) :=
    funext fun y => GlobalTheory.T.phi_DeX_expand_alt p Lt T e N nu hY ι b g c h1 h3 φ y
  rw [hfun, GlobalTheory.T.comb_mem_iff_alt p Lt T e he N ν ι b g Nc hNc h4 (fun s => by rw [hν s]; exact h5 s)]

end GlobalTheory.WeylLatDualProof
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_lattice_duality : WeylLatticeDuality.Stmt := by
  atlas_forward_decl GlobalTheory.WeylLatDualProof.mainProof
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CmpEx

theorem lift_ratSpan (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)
    (hP : P ∈ RatSpan D lam) :
    ∃ Q0 : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL,
      Q0 ∈ WtPol D.what₂.LL (fun τ r => (lam τ).natW r) ∧ MvPolynomial.map D.what₂.embLL Q0 = P := by
  have hle : RatSpan D lam ≤ AddSubgroup.map
      (MvPolynomial.map D.what₂.embLL : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL →+* _).toAddMonoidHom
      (WtPol D.what₂.LL (fun τ r => (lam τ).natW r)).toAddSubgroup := by
    unfold RatSpan
    rw [AddSubgroup.closure_le]
    rintro p ⟨r, f, hf, rfl⟩
    refine ⟨r • Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)), ?_, ?_⟩
    · show _ ∈ WtPol _ _
      apply Submodule.smul_mem
      apply GlobalTheory.KerWt.VV_le_WtPol lam
      unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
      apply Submodule.subset_span
      refine ⟨fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ), fun τ => ?_, rfl⟩
      have h1 : MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ) ∈ delSq D.what₂.LL n (lam τ) := by
        rw [← GlobalTheory.Published.span_map_delSq ℤ D.what₂.LL (Int.castRingHom D.what₂.LL) n (lam τ)]
        exact Submodule.subset_span ⟨f τ, hf τ, rfl⟩
      exact Formalism.GradedWeylDivisibility.weylLeDual D.what₂.LL n n le_rfl _ (GlobalTheory.FormsSharpTie.natW_antitone (lam τ)) h1
    · have hc : D.what₂.embLL.comp (Int.castRingHom D.what₂.LL) = Int.castRingHom ℂ := RingHom.ext_int _ _
      simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, MvPolynomial.smul_eq_C_mul, map_mul,
        MvPolynomial.map_C, Formalism.L2.Forms.ten, map_prod, MvPolynomial.map_rename, MvPolynomial.map_map, hc]
  obtain ⟨Q0, hQ0, e⟩ := hle hP
  exact ⟨Q0, hQ0, e⟩

theorem wt0 : ∀ (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P) (τ : D.what₂.Tau), 0 ≤ shiftOf (lamTG M 0) τ + twB D u μ 0 τ ∧ ∀ r : Fin (D.R.N 0), (M.lam 0 τ).natW r + (shiftOf (lamTG M 0) τ + twB D u μ 0 τ).toNat = nuT D u 0 τ r := by
  intro D u μ C A P M τ
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  have hN : D.R.N 0 = D.R.k := by simp [Ranks.N]
  have hN0 : 0 < D.R.N 0 := hN ▸ hk
  have hw : ∀ r : Fin (D.R.N 0), (((M.lam 0 τ).w r : ℤ) : ℚ) =
      (D.hcW u τ).u ⟨r.1, by omega⟩ - (((D.R.k : ℚ) - 1) / 2 - (r.1 : ℚ)) := by
    intro r
    rw [M.lam_eq 0 (Nat.zero_le _) τ r, dif_pos (by omega)]
    rfl
  have hds0 : (M.lam 0 τ).detShift = (M.lam 0 τ).w ⟨D.R.N 0 - 1, by omega⟩ := by
    unfold DomWeight.detShift
    rw [dif_pos hN0]
  have hds : ((M.lam 0 τ).detShift : ℚ) = (D.hcW u τ).u ⟨D.R.k - 1, by omega⟩ + ((D.R.k : ℚ) - 1) / 2 := by
    rw [hds0, hw]
    have e1 : (D.hcW u τ).u ⟨D.R.N 0 - 1, by omega⟩ = (D.hcW u τ).u ⟨D.R.k - 1, by omega⟩ :=
      congrArg _ (Fin.ext (by simp only [hN]))
    simp only [e1]
    have e2 : ((D.R.N 0 - 1 : ℕ) : ℚ) = (D.R.k : ℚ) - 1 := by
      rw [hN, Nat.cast_sub (by omega)]
      simp
    rw [e2]
    ring
  have hsh : shiftOf (lamTG M 0) τ = (M.lam 0 τ).detShift := by
    simp [shiftOf, lamTG, Formalism.L2.Forms.shW, DomWeight.detShift]
  have htw : ((twB D u μ 0 τ : ℤ) : ℚ) = (D.hcW u τ).e ⟨0, hm⟩ - ((D.R.k : ℚ) + D.R.t + 1) / 2 := by
    show (((D.chTw u μ).sSharp 0 τ : ℤ) : ℚ) = _
    rw [(D.chTw u μ).sSharp_eq 0 hm τ]
    unfold sExp' Ranks.N
    push_cast
    ring
  have hpos : 0 ≤ shiftOf (lamTG M 0) τ + twB D u μ 0 τ := by
    have h1 := (D.hcW u τ).u_last_gt hk hm
    have h2 := (D.hcW u τ).gap_be ⟨0, hm⟩
    have h3 : (0 : ℚ) ≤ ((shiftOf (lamTG M 0) τ + twB D u μ 0 τ : ℤ) : ℚ) := by
      push_cast
      rw [hsh, hds, htw]
      have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
      linarith
    exact_mod_cast h3
  refine ⟨hpos, fun r => ?_⟩
  have hr : r.1 < D.R.k := by omega
  have hanti : (M.lam 0 τ).detShift ≤ (M.lam 0 τ).w r := by
    rw [hds0]
    exact (M.lam 0 τ).anti (Fin.mk_le_mk.2 (by omega))
  have hnu := (nu_t_identity D u 0 hm τ r).1
  have key : ((((M.lam 0 τ).natW r + (shiftOf (lamTG M 0) τ + twB D u μ 0 τ).toNat : ℕ) : ℤ) : ℚ) =
      (D.hcW u τ).u ⟨r.1, hr⟩ + (D.hcW u τ).e ⟨0, hm⟩ + r.1 - D.R.k - (D.R.t : ℚ) / 2 := by
    have z1 : ((((M.lam 0 τ).w r - (M.lam 0 τ).detShift).toNat : ℕ) : ℤ) = (M.lam 0 τ).w r - (M.lam 0 τ).detShift :=
      Int.toNat_of_nonneg (by omega)
    have z2 : (((shiftOf (lamTG M 0) τ + twB D u μ 0 τ).toNat : ℕ) : ℤ) = shiftOf (lamTG M 0) τ + twB D u μ 0 τ :=
      Int.toNat_of_nonneg hpos
    unfold DomWeight.natW
    rw [Nat.cast_add, z1, z2]
    push_cast
    rw [hsh, hw, htw]
    ring
  have hnu2 : ((nuT D u 0 τ r : ℕ) : ℝ) = (((D.hcW u τ).u ⟨r.1, hr⟩ + (D.hcW u τ).e ⟨0, hm⟩ + r.1 - D.R.k - (D.R.t : ℚ) / 2 : ℚ) : ℝ) := by
    rw [hnu]
    unfold DV.nuRow DV.srcPar DV.wSz
    rw [dif_pos hr, dif_pos ⟨le_rfl, by omega⟩, ← D.hcW_e u τ]
    unfold Ranks.N
    push_cast
    ring
  have key2 : ((((M.lam 0 τ).natW r + (shiftOf (lamTG M 0) τ + twB D u μ 0 τ).toNat : ℕ) : ℤ) : ℚ) = ((nuT D u 0 τ r : ℕ) : ℚ) := by
    rw [key]
    exact_mod_cast hnu2.symm
  exact_mod_cast key2

theorem wtS : ∀ (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P) (j : ℕ), j + 1 < D.R.m → ∀ (τ : D.what₂.Tau), 0 ≤ shiftOf (lamTG M (j + 1)) τ + twB D u μ (j + 1) τ ∧ ∀ r : Fin (D.R.N (j + 1)), (M.lam (j + 1) τ).natW r + (shiftOf (lamTG M (j + 1)) τ + twB D u μ (j + 1) τ).toNat = extNu (D.R.N (j + 1)) (nuT D u j) τ r := by
  intro D u μ C A P M j hj τ
  have hj' : j < D.R.m := by omega
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  have hNs : D.R.N (j + 1) = D.R.N j + (D.R.t + 1) := by unfold Ranks.N; ring
  have hNj : D.R.N j = D.R.k + j * (D.R.t + 1) := rfl
  have hN0 : 0 < D.R.N (j + 1) := by omega

  have hgen : ∀ r : Fin (D.R.N (j + 1)), ∀ h : D.R.k ≤ r.1, ((M.lam (j + 1) τ).w r : ℚ) =
      -wG D.R ((D.hcW u τ).e ⟨(r.1 - D.R.k) / (D.R.t + 1), by
        have h2 : r.1 < D.R.k + (j + 1) * (D.R.t + 1) := r.2
        have : (r.1 - D.R.k) / (D.R.t + 1) < j + 1 := by
          rw [Nat.div_lt_iff_lt_mul (by omega)]
          omega
        omega⟩) ((r.1 - D.R.k) / (D.R.t + 1) + 1) := by
    intro r h
    rw [M.lam_eq (j + 1) hj.le τ r, dif_neg (by omega)]
  have hblk : ∀ r : Fin (D.R.N (j + 1)), D.R.N j ≤ r.1 → ((M.lam (j + 1) τ).w r : ℚ) = -wG D.R ((D.hcW u τ).e ⟨j, hj'⟩) (j + 1) := by
    intro r hr
    have h2 : r.1 < D.R.k + (j + 1) * (D.R.t + 1) := r.2
    have hdiv : (r.1 - D.R.k) / (D.R.t + 1) = j := by
      apply Nat.div_eq_of_lt_le
      · rw [hNj] at hr; omega
      · omega
    rw [hgen r (by rw [hNj] at hr; omega)]
    have e1 : (D.hcW u τ).e ⟨(r.1 - D.R.k) / (D.R.t + 1), by omega⟩ = (D.hcW u τ).e ⟨j, hj'⟩ := congrArg _ (Fin.ext hdiv)
    rw [e1, hdiv]
  have hds0 : (M.lam (j + 1) τ).detShift = (M.lam (j + 1) τ).w ⟨D.R.N (j + 1) - 1, by omega⟩ := by
    unfold DomWeight.detShift
    rw [dif_pos hN0]
  have hds : ((M.lam (j + 1) τ).detShift : ℚ) = -wG D.R ((D.hcW u τ).e ⟨j, hj'⟩) (j + 1) := by
    rw [hds0]
    exact hblk _ (by simp only []; omega)
  have hc : ((((j + 1) * (D.R.t + 1) / 2 : ℕ) : ℤ) : ℚ) = ((j : ℚ) + 1) * ((D.R.t : ℚ) + 1) / 2 := by
    obtain ⟨a, ha⟩ := D.R.t_odd
    have e : (j + 1) * (D.R.t + 1) = 2 * ((j + 1) * (a + 1)) := by rw [ha]; ring
    rw [e, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [ha]
    push_cast
    ring
  have hsh : shiftOf (lamTG M (j + 1)) τ = (M.lam (j + 1) τ).detShift - ((((j + 1) * (D.R.t + 1) / 2 : ℕ)) : ℤ) := by
    simp [shiftOf, lamTG, Formalism.L2.Forms.shW, DomWeight.detShift, hN0]
  have htw : ((twB D u μ (j + 1) τ : ℤ) : ℚ) = (D.hcW u τ).e ⟨j, hj'⟩ - ((D.R.k : ℚ) + j * (D.R.t + 1)) / 2 := by
    show (((D.chTw u μ).sDiv j τ : ℤ) : ℚ) = _
    rw [(D.chTw u μ).sDiv_eq j hj' τ]
    unfold sExp Ranks.N
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  have hS : shiftOf (lamTG M (j + 1)) τ + twB D u μ (j + 1) τ = 0 := by
    have h3 : ((shiftOf (lamTG M (j + 1)) τ + twB D u μ (j + 1) τ : ℤ) : ℚ) = 0 := by
      rw [Int.cast_add, hsh, Int.cast_sub, hds, hc, htw]
      unfold wG
      push_cast
      ring
    exact_mod_cast h3
  refine ⟨hS.ge, fun r => ?_⟩
  rw [hS, Int.toNat_zero, add_zero]
  have hanti : (M.lam (j + 1) τ).detShift ≤ (M.lam (j + 1) τ).w r := by
    rw [hds0]
    exact (M.lam (j + 1) τ).anti (Fin.mk_le_mk.2 (by omega))
  have z1 : ((((M.lam (j + 1) τ).w r - (M.lam (j + 1) τ).detShift).toNat : ℕ) : ℤ) = (M.lam (j + 1) τ).w r - (M.lam (j + 1) τ).detShift :=
    Int.toNat_of_nonneg (by omega)
  unfold extNu
  by_cases hr : r.1 < D.R.N j
  · rw [dif_pos hr]
    have hnu := (nu_t_identity D u j hj' τ ⟨r.1, hr⟩).1
    have key : (((M.lam (j + 1) τ).natW r : ℕ) : ℝ) = ((nuT D u j τ ⟨r.1, hr⟩ : ℕ) : ℝ) := by
      rw [hnu]
      have q1 : (((M.lam (j + 1) τ).natW r : ℕ) : ℝ) = ((((M.lam (j + 1) τ).w r : ℚ) - ((M.lam (j + 1) τ).detShift : ℚ) : ℚ) : ℝ) := by
        unfold DomWeight.natW
        have : ((((M.lam (j + 1) τ).w r - (M.lam (j + 1) τ).detShift).toNat : ℕ) : ℝ) =
            ((((M.lam (j + 1) τ).w r - (M.lam (j + 1) τ).detShift : ℤ) : ℚ) : ℝ) := by
          rw [← z1]; push_cast; rfl
        rw [this]; push_cast; rfl
      rw [q1, hds]
      unfold DV.nuRow DV.srcPar DV.wSz
      rw [dif_pos (show 1 ≤ j + 1 ∧ j + 1 ≤ D.R.m from ⟨by omega, by omega⟩), ← D.hcW_e u τ]
      have ej : (D.hcW u τ).e ⟨j + 1 - 1, by omega⟩ = (D.hcW u τ).e ⟨j, hj'⟩ := rfl
      rw [ej]
      by_cases hrk : r.1 < D.R.k
      · rw [dif_pos hrk, M.lam_eq (j + 1) hj.le τ r, dif_pos hrk]
        unfold hcToWeightQ rhoVec wG Ranks.N
        simp only [Nat.add_sub_cancel]
        push_cast
        ring
      · rw [dif_neg hrk]
        have hb : (r.1 - D.R.k) / (D.R.t + 1) < D.R.m := by
          have : (r.1 - D.R.k) / (D.R.t + 1) < j := by
            rw [Nat.div_lt_iff_lt_mul (by omega)]
            rw [hNj] at hr; omega
          omega
        rw [dif_pos hb, hgen r (by omega)]
        have hdm := Nat.div_add_mod (r.1 - D.R.k) (D.R.t + 1)
        have hr_eq : (r.1 : ℝ) = D.R.k + ((D.R.t : ℝ) + 1) * (((r.1 - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) + (((r.1 - D.R.k) % (D.R.t + 1) : ℕ) : ℝ) := by
          have : r.1 = D.R.k + (D.R.t + 1) * ((r.1 - D.R.k) / (D.R.t + 1)) + (r.1 - D.R.k) % (D.R.t + 1) := by omega
          conv_lhs => rw [this]
          push_cast
          ring
        unfold wG Ranks.N
        simp only [Nat.add_sub_cancel]
        push_cast
        linear_combination (-1 : ℝ) * hr_eq
    exact_mod_cast key
  · rw [dif_neg hr]
    have h0 : ((M.lam (j + 1) τ).w r : ℚ) - ((M.lam (j + 1) τ).detShift : ℚ) = 0 := by
      rw [hblk r (by omega), hds]; ring
    have h1 : (M.lam (j + 1) τ).w r - (M.lam (j + 1) τ).detShift = 0 := by exact_mod_cast h0
    unfold DomWeight.natW
    rw [h1]
    rfl

theorem eval_mul_det {D : D7} {N : ℕ} (Q0 : MvPolynomial (GL3Theta.FrV D N) D.what₂.LL) (k : D.what₂.Tau → ℕ)
    (y : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) :
    GL3Theta.evFr D (MvPolynomial.map D.what₂.embLL (Q0 * ∏ τ, frDet D.what₂.LL N τ ^ k τ)) y =
      GL3Theta.evFr D (MvPolynomial.map D.what₂.embLL Q0) y * ∏ τ, (y τ).det ^ k τ := by
  unfold GL3Theta.evFr
  rw [map_mul, map_mul, map_prod, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, map_pow, eval_detP]

theorem core (D : D7) (O : ∀ u a, GL3Theta.LiftObj D (D.chTw u a)) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m)
    {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pp : PeriodMap D.R C}
    (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pp)
    (eY : (D.chTw u μ).Y i ≃ Formalism.L2.Forms.Fr D i hi.le)
    (hE : ∀ y, Subtype.val (eY y) = (O u μ).frm i y)
    (f : (D.chTw u μ).Y i → ℂ)
    (hP : ∃ P ∈ Formalism.L2.Forms.RatSpan D (M.lam i), ∀ z, f z = fnOf (gramC (gramN D i hi.le) (embT D)) (shiftOf (lamTG M i)) 1 P (eY z)) :
    ∃ v : ValQ O u μ i, evC O u μ i v = f := by
  obtain ⟨P, hP, hf⟩ := hP
  obtain ⟨Q0, hQ0, hmap⟩ := lift_ratSpan D (M.lam i) P hP
  have hwt : ∀ τ, 0 ≤ shiftOf (lamTG M i) τ + twB D u μ i τ := by
    intro τ
    cases i with
    | zero => exact (wt0 D u μ M τ).1
    | succ j => exact (wtS D u μ M j hi τ).1
  have hQ : Q0 * ∏ τ, frDet D.what₂.LL (D.R.N i) τ ^ (shiftOf (lamTG M i) τ + twB D u μ i τ).toNat ∈ polV D u i := by
    have h := wtPol_mul_det _ (fun τ => (shiftOf (lamTG M i) τ + twB D u μ i τ).toNat) hQ0
    cases i with
    | zero =>
      have e : (fun τ r => (M.lam 0 τ).natW r + (shiftOf (lamTG M 0) τ + twB D u μ 0 τ).toNat) = nuT D u 0 :=
        funext fun τ => funext fun r => (wt0 D u μ M τ).2 r
      rw [e] at h
      exact h
    | succ j =>
      have e : (fun τ r => (M.lam (j + 1) τ).natW r + (shiftOf (lamTG M (j + 1)) τ + twB D u μ (j + 1) τ).toNat) =
          extNu (D.R.N (j + 1)) (nuT D u j) := funext fun τ => funext fun r => (wtS D u μ M j hi τ).2 r
      rw [e] at h
      exact h
  refine ⟨Submodule.mkQ _ ⟨_, hQ⟩, ?_⟩
  funext z
  show evP O u μ i ⟨_, hQ⟩ z = f z
  rw [hf z]
  show (∏ τ, (D.chTw u μ).de i z τ ^ (-twB D u μ i τ)) *
      GL3Theta.evFr D (MvPolynomial.map D.what₂.embLL _) ((O u μ).frm i z) = _
  rw [eval_mul_det, hmap]
  have hde : ∀ τ, (D.chTw u μ).de i z τ = ((O u μ).frm i z τ).det := fun τ => (O u μ).frm_de i hi.le z τ
  have hne : ∀ τ, ((O u μ).frm i z τ).det ≠ 0 := fun τ => hde τ ▸ (D.chTw u μ).de_ne i z τ
  simp only [hde]
  unfold fnOf
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul, hE z]
  unfold GL3Theta.evFr
  rw [mul_comm (MvPolynomial.eval _ P), ← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_natCast, Int.toNat_of_nonneg (hwt τ), ← zpow_add₀ (hne τ)]
  congr 1
  ring

theorem exists_valQ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ (c : (I.stp u μ i).Cl) (f : (I.chain l u μ).Y i → ℂ), (∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z)) → ∃ v : ValQ O u μ i, evC O u μ i v = f := by
  intro B X I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hLev i hi eY hIdY c f hP
  exact core (I.rec7 l Z) O u μ i hi (I.fm l u μ) eY (fun y => (hIdY y).trans (hStd.frm u μ i y).symm) f hP

end GlobalTheory.CmpEx
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomialModel_value_rational_step : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ (c : (I.stp u μ i).Cl) (f : (I.chain l u μ).Y i → ℂ), (∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z)) → ∃ v : ValQ O u μ i, evC O u μ i v = f := by
  atlas_forward_decl GlobalTheory.CmpEx.exists_valQ
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatSCore

theorem prSC_int_iff (hW : WeylLatticeDuality.Stmt) {D : D7} (Pl : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (Bs : PlaceMatrixFamily D)
    (hC : CanOnto Pl) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (hi : i < D.R.m) (c : (D.chTw u μ).cls i)
    (v : ValQ O u μ i) :
    (∀ J : KM.ColChoice (D.R.N i) (nuD D u i),
        ‖prSC Pl O Bs u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX (D.R.N i) (nuD D u i) J))‖ ≤ 1) ↔
      srcFun Pl Bs u μ w i c (secC O u μ i v) ∈
        WeylLatticeDuality.DelW (D.what₂.places.resChar w) D.what₂.Tau (D.R.N i) (nuT D u i) := by
  have hS := canS_of Pl Bs hC u μ w i hi c (secC O u μ i v)
  have hcan : canM D w (D.R.N i) (nuD D u i) (prSC Pl O Bs u μ w i c v) = srcFun Pl Bs u μ w i c (secC O u μ i v) :=
    canInv_spec D w (D.R.N i) (nuD D u i) _ hS
  rw [← hcan]
  exact hW (D.what₂.places.resChar w) _ D.what₂.Tau (tauPl D) (tauPl_bij D) (D.R.N i) (nuD D u i) (nuT D u i)
    (diagram_fits_source_rank D u i hi).1 (diagram_fits_source_rank D u i hi).2 (prSC Pl O Bs u μ w i c v)

theorem latS_at_class : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ (c : (I.stp u μ i).Cl) (f : (I.chain l u μ).Y i → ℂ), (∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z)) → ∀ Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E, Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (((I.stp u μ i).rep c).1.1.deco.1.N : Set (Sp B.fields.E (B.R.N i))) Bm → ((∃ P ∈ Formalism.L2.Forms.IntSpan (I.rec7 l Z) w ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) (atInf (embT (I.rec7 l Z)) ((Bm⁻¹ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E)) P (eY z)) ↔ ∃ v : ValQ O u μ i, evC O u μ i v = f ∧ ∀ J : KM.ColChoice ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i), ‖prSC Pl O Bs u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i) J))‖ ≤ 1) := by
  intro B X I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi eY hId c f hrat Bm hBm
  have hi' : i < (I.rec7 l Z).R.m := hi
  have key := prSC_int_iff GlobalTheory.T.weyl_lattice_duality Pl O Bs (GlobalTheory.T.toy_entPl_canOnto _ Pl) u μ w i hi' c
  constructor
  · intro hL
    obtain ⟨v, hv⟩ := GlobalTheory.T.exists_polynomialModel_value_rational_step I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi eY hId c f hrat
    refine ⟨v, hv, ?_⟩
    rw [key v]
    exact (GlobalTheory.T.lattice_iff_integralWeyl_coordinates I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi eY hId c f hrat Bm hBm v hv).1 hL
  · rintro ⟨v, hv, hJ⟩
    rw [key v] at hJ
    exact (GlobalTheory.T.lattice_iff_integralWeyl_coordinates I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi eY hId c f hrat Bm hBm v hv).2 hJ

end GlobalTheory.LatSCore
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formsLattice_atClass_iff_twistedPolynomial : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ (c : (I.stp u μ i).Cl) (f : (I.chain l u μ).Y i → ℂ), (∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z)) → ∀ Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E, Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (((I.stp u μ i).rep c).1.1.deco.1.N : Set (Sp B.fields.E (B.R.N i))) Bm → ((∃ P ∈ Formalism.L2.Forms.IntSpan (I.rec7 l Z) w ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) (atInf (embT (I.rec7 l Z)) ((Bm⁻¹ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E)) P (eY z)) ↔ ∃ v : ValQ O u μ i, evC O u μ i v = f ∧ ∀ J : KM.ColChoice ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i), ‖prSC Pl O Bs u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i) J))‖ ≤ 1) := by
  atlas_forward_decl GlobalTheory.LatSCore.latS_at_class
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

namespace GlobalTheory.KerLatS

theorem charts_read_step {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hPins : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (him : i < B.R.m) :
    ∃ (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch)
      (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
        (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), I.ReadsK l Z u a i hi chOf K := by
  classical
  rcases Nat.eq_zero_or_pos i with rfl | h1
  · exact GlobalTheory.T.exists_charts_reading_step_zero I hOk hPins l Z u a
  · obtain ⟨Ch0, _, chOf0, K0, hK0, -⟩ := GlobalTheory.T.exists_memberStep_charts I hOk hPins l Z u i hi
    obtain ⟨Ch, _, chOf, K, -, hK, -⟩ := GlobalTheory.T.tupleChain_middleStage_charts_joined_member I hOk hPins l Z u a ((I.Q a).image fun P => P.under (𝓞 B.host.F)) i hi
      Ch0 chOf0 K0 h1 him (fun v => Finset.mem_image) hK0
    exact ⟨_, Ch, chOf, K, hK⟩

theorem kerEntHyp_latS : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ φ : ((I.rec7 l Z).chTw u μ).cls i → ((I.rec7 l Z).chTw u μ).Y i → ℂ, (∃ x ∈ locW (I.rec7 l Z).what₂.places w (((I.tw l l0 Z).fm u μ).lat i).L, ((I.tw l l0 Z).fm u μ).emb i x = φ) ↔ (φ ∈ ((I.tw l l0 Z).fm u μ).Fi i ∧ ∀ c, ∃ v : ValQ O u μ i, evC O u μ i v = φ c ∧ ∀ J : KM.ColChoice ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i), ‖prSC Pl O Bs u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i) J))‖ ≤ 1) := by
  intro B X I hOk hPins l Z l0 Y O Pl Bs hQp hStd hBas hEnt _hUnf _hJets u μ w hw i hi φ
  obtain ⟨bad, Ch, chOf, K, hK⟩ := charts_read_step I hOk hPins l Z u μ i hi.le hi
  have hY : I.IdY l Z u μ i hi.le (Equiv.refl _) := fun _ => rfl
  have V := GlobalTheory.T.hermitianChart_complex_rational_integral_forms I hOk hPins l Z u μ i hi.le bad Ch chOf K (Equiv.refl _) hK hY
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hrat := (V.rat ((I.fm l u μ).emb i x)).1 ⟨x, rfl⟩
    have hlat := (V.lat w trivial x).1 hx
    refine ⟨hrat.1, fun c => ?_⟩
    obtain ⟨Bm, hBm⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis ((I.rec7 l Z).what₂.places.resChar w) _ _
      ((I.stp u μ i).rep c).1.1.deco.2.lat.fg ((I.stp u μ i).rep c).1.1.deco.2.lat.span_eq_top
    have hBm' := (GlobalTheory.T.dualLattice_localBasis_iff_unimodularCompanion I hOk hPins l Z Y u μ w hw i hi.le c Bm).2 hBm
    exact (GlobalTheory.T.formsLattice_atClass_iff_twistedPolynomial I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi (Equiv.refl _) hY c _ (hrat.2 c) Bm
      hBm).1 (hlat c Bm hBm')
  · rintro ⟨hFi, hc⟩
    have hrat : ∀ c, ∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, φ c z =
        fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P
          ((Equiv.refl _) z) := by
      intro c
      obtain ⟨v, hv, -⟩ := hc c
      rw [← hv]
      exact GlobalTheory.T.complexValue_det_shift_mul_ratSpan I hOk hPins l Z Y O hQp hStd u μ i hi (Equiv.refl _) hY v
    obtain ⟨x, hx⟩ := (V.rat φ).2 ⟨hFi, hrat⟩
    refine ⟨x, (V.lat w trivial x).2 fun c Bm hBm => ?_, hx⟩
    have hBm' := (GlobalTheory.T.dualLattice_localBasis_iff_unimodularCompanion I hOk hPins l Z Y u μ w hw i hi.le c Bm).1 hBm
    have h1 := (GlobalTheory.T.formsLattice_atClass_iff_twistedPolynomial I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi (Equiv.refl _) hY c _ (hrat c) Bm
      hBm').2 (hc c)
    rw [hx]
    exact h1

end GlobalTheory.KerLatS
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueChains_kernelDatum_sourceSideLattice : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ φ : ((I.rec7 l Z).chTw u μ).cls i → ((I.rec7 l Z).chTw u μ).Y i → ℂ, (∃ x ∈ locW (I.rec7 l Z).what₂.places w (((I.tw l l0 Z).fm u μ).lat i).L, ((I.tw l l0 Z).fm u μ).emb i x = φ) ↔ (φ ∈ ((I.tw l l0 Z).fm u μ).Fi i ∧ ∀ c, ∃ v : ValQ O u μ i, evC O u μ i v = φ c ∧ ∀ J : KM.ColChoice ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i), ‖prSC Pl O Bs u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i) J))‖ ≤ 1) := by
  atlas_forward_decl GlobalTheory.KerLatS.kerEntHyp_latS
end
