import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairRecordCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecFockCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VPNeZeroCore

section
noncomputable section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.OverCore

set_option maxHeartbeats 800000 in

theorem coefMap_norm_equivariant_basis : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ‖O.c0' O.hw‖ = 1 ∧ (∀ (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E), Bridge.IsRatMat (Vc D i) γ γE → ∀ v, O.c0' (rhoM O.c' (fun τ => embF O.c' (tauE D τ)) (lamV D i) (γE : Matrix _ _ D.host.E) v) = (R.cV i).ρ γ (O.c0' v)) ∧ Submodule.span ℂ (Set.range O.c0') = ⊤ ∧ ∀ (m : ℕ) (b : Fin m → VsV D i O.c'.F), LinearIndependent O.c'.F b → LinearIndependent ℂ (fun j => O.c0' (b j)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ _ i Tp tup O hP
  obtain ⟨gramR, c0R, c0L, hT, hc⟩ := hP.lift.c0
  have hσ := hP.lift.field
  have hE : ∀ v, O.c0' (GlobalTheory.AdTh.CoefExt.up O.jL (lamV D i) v) = c0L i v := by
    intro v
    obtain ⟨w, hw, h⟩ := hc v
    rw [show GlobalTheory.AdTh.CoefExt.up O.jL (lamV D i) v = w from Subtype.ext hw.symm]
    exact h
  obtain ⟨h1, h2, h3⟩ := hT.mapL i
  refine ⟨?_, ?_, GlobalTheory.AdTh.CoefExt.span_top (W := (R.cV i).W) hE h3,
    fun m b hb => GlobalTheory.AdTh.CoefExt.linearIndependent (W := (R.cV i).W) hE h2 b hb⟩
  · have hn := GlobalTheory.StdFrame.neg_eq_false_of_vStd D i hP.lift.std
    have hg : (D.sp.V ((i : ℕ) + 1)).gram = 1 := hP.lift.std.1
    let v : VsV D i D.what₂.LL := ⟨Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal D.what₂.LL _ (lamV D i τ),
      GlobalTheory.Proof.TensorMapDescent.ten_mem _ _ fun τ => Formalism.GradedWeylDivisibility.hwMem _ _ _ le_rfl _ (Formalism.L2.DIV.natW_antitone _)⟩
    have hv : GlobalTheory.AdTh.CoefExt.up O.jL (lamV D i) v = O.hw := by
      apply Subtype.ext
      have hw := hP.io.1
      unfold hwOK at hw
      refine Eq.trans ?_ hw.symm
      show MvPolynomial.map O.jL (Formalism.L2.DIV.ten _) = _
      rw [GlobalTheory.Proof.TensorMapDescent.map_ten]
      congr 1
      funext τ
      exact Formalism.L2.DIV.map_extremal _ _ _
    have hG : (if D.sp.Vneg ((i : ℕ) + 1) then -(D.sp.V ((i : ℕ) + 1)).gram else (D.sp.V ((i : ℕ) + 1)).gram) = 1 := by
      rw [hn, hg]; rfl
    have hi := GlobalTheory.AdTh.inner_of_coefTie (hT.coefL i A.μ0) v v
    rw [hG] at hi
    replace hi := hi.trans ((congrArg D.what₂.embLL (GlobalTheory.AdTh.CoefExt.pairVr_extremal (labLL D) v rfl)).trans (map_one _))
    rw [← hv, hE]
    have hi' : inner ℂ (c0L i v : (R.cV i).W) (c0L i v : (R.cV i).W) = 1 := hi
    rw [inner_self_eq_norm_sq_to_K] at hi'
    have h4 : ‖(c0L i v : (R.cV i).W)‖ ^ 2 = 1 := by
      have h5 := congrArg norm hi'
      simpa using h5
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
  · intro γ γE hγ v
    have hu : IsUnit (γE.val).det := (Matrix.isUnit_iff_isUnit_det γE.val).1 γE.isUnit
    have hγE : Matrix.nonsingInvUnit γE.val hu = γE := Units.ext rfl
    have hemb : (fun τ => embF O.c' (tauE D τ)) = fun τ => O.jL.comp (labLL D τ) :=
      funext fun τ => (embV_eq_embF O.c' O.jL hσ τ).symm
    rw [rhoM, dif_pos hu, hγE, hemb]
    exact GlobalTheory.AdTh.CoefExt.equivariant (W := (R.cV i).W) hE ((R.cV i).ρ γ) (Formalism.L2.DIV.rhoVr (labLL D) (lamV D i) γE) _
      (GlobalTheory.AdTh.CoefExt.up_rhoVr O.jL (lamV D i) (labLL D) γE) (h1 γ γE hγ) v

end GlobalTheory.AdTh.OverCore

end
end

section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdTh.PhaseMapCore
open GlobalTheory.AdTh.PhaseMap

set_option maxHeartbeats 1600000 in

theorem io_eq_phase_smul_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∀ (lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank), (∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨ (ℓ.1 = conjEmb (tauE D (lt ℓ).1) ∧ ((lt ℓ).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1))) → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ (t : T0) (v : VsV D i O.c'.F), R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) (O.c0' v)) = ka • pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (R.vP i t) (MvPolynomial.rename lt (MvPolynomial.map (inC O.c') (O.io v))) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT hE i Tp tup O hO
  have hstd := hO.lift.std
  have hθ : IsInfFam R.θ := hR.models.inf
  have hc : (R.cV i).Is := hR.models.cV i
  have hP := (GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A _ R F hR i A.μ0 hstd).1
  have hψ := hP.weil.std
  have hF := fun t => GlobalTheory.AdTh.VecFockCore.vec_fock_core D G Pl0 T0 A _ R F hR i t hstd
  obtain ⟨f1, f2, f3, f4, f5⟩ := hF A.μ0
  obtain ⟨n1, n2, n3, n4⟩ := GlobalTheory.AdTh.OverCore.coefMap_norm_equivariant_basis D G Pl0 T0 A T R F κ v₀ hR hT i Tp tup O hO
  obtain ⟨r1, r2, -⟩ := GlobalTheory.RatGen.rational_points_generate D (Vc D i) (R.cV i) (hR.models.vpos i) hP.sigV hc
  obtain ⟨-, -, w1, w2, w3⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q hT.laws.pins _ (inR i) (κ i)
  have hty : IsTyp D T.Q.H := ⟨w1, w2⟩
  obtain ⟨d1, d2, -⟩ := hT.laws.pins.2.2.2 _ (inR i)
  have hsig : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := fun τ => D.sp.W_sigval _ (inR i).1 (inR i).2 _
  obtain ⟨-, cga, i1, i2, -, i3, -, -, i4, -⟩ := hO.io
  obtain ⟨u₀, w₀, hu₀, hw₀, hΔ⟩ : ExtremalVectorPairsToDelta R i (v₀ i (sg0 D A)) := (hT.hv₀ i (sg0 D A)).2 rfl (hE i)
  have hio := (hR.thP.ioP i A.μ0).1
  have hBV : ∀ τ, (R.BV i τ)ᴴ * R.BV i τ = 1 := fun τ => by
    obtain ⟨ε, hε, h1, -⟩ := hR.models.BV i τ
    rw [gramAt_one hP.std, Matrix.mul_one] at h1
    rw [h1, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with h | h
    · rw [h.1]; rfl
    · exact absurd a.2 (not_lt.2 h.2)
  have hon : ∀ τ, IsONBasis (gramAt D (Vc D i) τ) 1 1 (Vc D i).rank := fun τ =>
    ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, by simp [gramAt_one hP.std], by simp⟩
  let PT := fun t => pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1)
    (onb (R.MW i (sg0 D A))) (R.vP i t)
  have hsub : ∀ t (U : D.what₂.Tau → Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ), (∀ τ, (U τ)ᴴ * U τ = 1) → ∀ P,
      pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) U (onb (R.MW i (sg0 D A))) (R.vP i t) P =
        PT t (sub (fun τ => ((Wc D i).sig (tauE D τ)).1) U P) := fun t U hU P => by
    have h := GlobalTheory.AdTh.SourceBasis.pureTensorO_mul_source D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ (fun _ => 1) U _ _ _ f5
      (fun τ => (trace_parity (f5 τ)).1) (fun τ => by simp) (fun τ => det_ne_zero (hU τ)) _ (hF t).1 P
    simp only [Matrix.one_mul] at h
    exact h
  have hinj : Function.Injective (PT A.μ0) :=
    GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ _ _ _ _ _ _ f4 f3 hon f5 hP.sigV hP.sigW _ f1 f2
      (GlobalTheory.AdTh.VecNeCore.thetaVector_ne_zero_core D G Pl0 T0 A _ R F hR i hstd)
  obtain ⟨g, hg, hgB⟩ : ∃ g ∈ GinfC (Vc D i), ∀ τ, compAt R.θ τ (Formalism.L2.Theta.mt (Vc D i) g) = R.BV i τ :=
    (GlobalTheory.SmoothForms.RealPts.glue R.θ hθ (Vc D i)).2 (R.BV i) fun τ => by
      show (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = gramAt D (Vc D i) τ
      rw [gramAt_one hP.std, Matrix.mul_one, hBV]
  obtain ⟨χ, hχ, hχg⟩ := om_real hP f4 f3 f5 f1 f2 hg
  rw [funext hgB] at hχg
  have hχ0 : χ ≠ 0 := fun h => by simp [h] at hχ
  let A₀ : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) :=
    pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i A.μ0) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u₀)
  have hA₀ : ∀ a ∈ GinfC (Vc D i), ∀ w, A₀ ((R.cV i).ρ a w) = R.ωP i A.μ0 (a, 1) (A₀ w) :=
    fun a ha w => (hio a ha _ w).symm
  have hw₁ : A₀ ((R.cV i).ρ g⁻¹ (χ • w₀)) = PT A.μ0 (RealDat.Delta i) := by
    have h1 : A₀ (χ • w₀) = R.ωP i A.μ0 (g, 1) (PT A.μ0 (RealDat.Delta i)) := by
      rw [map_smul, hχg, ← hΔ]
      rfl
    rw [hA₀ _ (inv_mem hg), h1, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, mul_one]
    exact congrArg (fun T : Module.End ℂ _ => T _) (map_one (R.ωP i A.μ0))
  have hn₁ : ‖(R.cV i).ρ g⁻¹ (χ • w₀)‖ = 1 := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), hc.2.1, ← norm_eq_sqrt_re_inner, norm_smul, hχ, hw₀, mul_one]
  haveI := hc.2.2.2.1
  haveI : FiniteDimensional O.c'.F (VsV D i O.c'.F) := Module.Finite.of_basis (Formalism.L2.DIV.bVV O.c'.F (lamV D i))
  have main : ∀ lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank, IsLt lt →
      ∃ a : ℂ, a • (R.cV i).ρ g⁻¹ (χ • w₀) = O.c0' O.hw ∧ ∀ t v, R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u₀) (O.c0' v)) =
        a • PT t (toF O.c' lt (O.io v)) := fun lt hl => by
    have hsm : ∀ (a : O.c'.F) P, toF O.c' lt (a • P) = (a : ℂ) • toF O.c' lt P := fun a P => by
      rw [MvPolynomial.smul_eq_C_mul, map_mul, toF_C, MvPolynomial.smul_eq_C_mul]
    obtain ⟨B₀, hB₀⟩ := exists_ext O.c0' n4
      { toFun := fun v => toF O.c' lt (O.io v)
        map_add' := fun v w => by rw [map_add, map_add]
        map_smul' := fun a v => by rw [map_smul, hsm]; rfl }
    replace hB₀ : ∀ v, B₀ (O.c0' v) = toF O.c' lt (O.io v) := hB₀
    have hpG : toF O.c' lt (O.io O.hw) = RealDat.Delta i := by
      rw [i4]
      refine toF_pG O.c' hl hty i1 _ _ _ _ _ (fun τ => by rw [hsig, d1]) (fun τ => by rw [hsig, d2]) (fun τ k hk => ?_)
        fun τ k hk => ?_
      · rw [d1] at hk
        exact (w3 τ k).1.trans ((dif_pos hk).trans ((hT.kap i τ).1 ⟨k, hk⟩))
      · rw [d2] at hk
        exact (w3 τ k).2.trans ((dif_pos hk).trans ((hT.kap i τ).2.1 ⟨k, hk⟩))
    obtain ⟨a, ha, ha'⟩ := proportional ((R.cV i).ρ.comp (GQ (Vc D i)).subtype) _ r1 (fun γ hγ => hγ) r2 A₀ (PT A.μ0 ∘ₗ B₀)
      (fun γ => by
        obtain ⟨γE, a, k, h1, h2, h3, h4, h5, h6⟩ := rat_parts hθ hP.std γ
        obtain ⟨x, hx, hxa⟩ := om_real hP f4 f3 f5 f1 f2 h2
        have hx0 : x ≠ 0 := fun h => by simp [h] at hx
        have h7 : (R.cV i).ρ γ = (R.cV i).ρ a := by rw [h4, map_mul, hc.1 k h3, mul_one]
        refine ⟨R.ωP i A.μ0 (a, 1), (cga γE.val : ℂ) * x⁻¹, fun w => ?_, fun w => ?_⟩
        · show A₀ ((R.cV i).ρ γ w) = _
          rw [h7, hA₀ a h2]
        · have h8 : (PT A.μ0 ∘ₗ B₀) ∘ₗ (R.cV i).ρ γ =
              ((cga γE.val : ℂ) * x⁻¹) • (R.ωP i A.μ0 (a, 1) ∘ₗ (PT A.μ0 ∘ₗ B₀)) := by
            refine LinearMap.ext_on_range n3 fun v => ?_
            simp only [LinearMap.comp_apply, LinearMap.smul_apply]
            rw [← n2 γ γE h1, hB₀, hB₀, i3 _ h5, hsm, hxa, hsub _ _ (compAt_unitary hθ hP.std a), smul_smul,
              inv_mul_cancel_right₀ hx0, map_smul,
              toF_gaStar O.c' hl hty (fun τ => ((Wc D i).sig (tauE D τ)).1) (fun τ => by rw [hsig, d1]) _ _ h6]
          exact LinearMap.congr_fun h8 w)
      ((R.cV i).ρ g⁻¹ (χ • w₀)) (O.c0' O.hw) (by rw [hw₁, LinearMap.comp_apply, hB₀, hpG])
      (fun h => by
        rw [LinearMap.comp_apply, hB₀, map_eq_zero_iff _ hinj, map_eq_zero_iff _ (toF_injective O.c' hl hty),
          map_eq_zero_iff _ i2] at h
        rw [h, map_zero, norm_zero] at n1
        exact zero_ne_one n1)
    refine ⟨a, ha', fun t v => ?_⟩
    have h9 : sub (fun τ => ((Wc D i).sig (tauE D τ)).1) (R.BV i) (R.ioP i (PiTensorProduct.tprod ℂ u₀) (O.c0' v)) =
        a • toF O.c' lt (O.io v) := hinj (by rw [← hsub _ _ hBV, map_smul, ← hB₀]; exact ha _)
    rw [← map_smul, ← h9, ← hsub _ _ hBV]
    rfl
  by_cases hex : ∃ lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank, IsLt lt
  · obtain ⟨lt₀, hl₀⟩ := hex
    obtain ⟨a, ha, -⟩ := main lt₀ hl₀
    refine ⟨a, ?_, fun lt hl u hu t v => ?_⟩
    · rw [← n1, ← ha, norm_smul, hn₁, mul_one]
    · obtain rfl : u = u₀ := funext fun ρ => Subtype.ext ((hu ρ).trans (hu₀ ρ).symm)
      obtain ⟨b, hb, hb'⟩ := main lt hl
      obtain rfl : a = b := smul_left_injective ℂ (fun h => by simp [h] at hn₁) (ha.trans hb.symm)
      exact hb' t v
  · exact ⟨1, norm_one, fun lt hl => absurd ⟨lt, hl⟩ hex⟩

end GlobalTheory.AdTh.PhaseMapCore

end
end

section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockCoefficientMap_extremal_eq_phase_smul_letters : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∀ (lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank), (∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨ (ℓ.1 = conjEmb (tauE D (lt ℓ).1) ∧ ((lt ℓ).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1))) → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ (t : T0) (v : VsV D i O.c'.F), R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) (O.c0' v)) = ka • pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (R.vP i t) (MvPolynomial.rename lt (MvPolynomial.map (inC O.c') (O.io v))) := by
  first | exact @GlobalTheory.AdTh.PhaseMapCore.io_eq_phase_smul_core | exact GlobalTheory.AdTh.PhaseMapCore.io_eq_phase_smul_core | (intros; apply GlobalTheory.AdTh.PhaseMapCore.io_eq_phase_smul_core <;> assumption)
end
