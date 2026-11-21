import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHalfIdem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import BuildAid.ForwardExisting

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GaussSeriesVacuum

open GlobalTheory.HeisenbergGaussianSeries GlobalTheory.SplitScalar GlobalTheory.VacuumO

theorem series_inv_scalar {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℝ V]
    {p : G →+ V} {ι : V →+ G} {β : G → G → ℂ} {om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {J : V →ₗ[ℝ] V}
    {Γ : AddSubgroup G} {χ : G → ℂ}
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hd : ∀ x, β x x = 1)
    (hβ : ∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ)))
    (a : V) (u : G) (hu : p u = 0) (c : ℂ) (hχ : ∀ x, c * (β x u * χ (x + u)) = χ x) (w : G) :
    c * (β w u * series p ι β om J Γ χ a (w + u)) = series p ι β om J Γ χ a w := by
  unfold series
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun g => ?_
  have h1 : β (ι a) u = 1 := by
    have := swap_mul β hl hr hd (ι a) u
    rw [hβ u a, hu] at this
    simpa using this
  rw [← hχ (g + w), ← add_assoc (g : G) w u, hr (ι a) (g + w) u, h1, hr g w u, hl g w u,
    map_add p w u, hu, add_zero]
  ring

theorem series_regular {G V : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (p : G →+ V) (ι : V →+ G) (β : G → G → ℂ)
    (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V) (Γ U₀ U : AddSubgroup G) (χ : G → ℂ)
    (hpc : Continuous p) (hιc : Continuous ι) (hp : ∀ v, p (ι v) = v)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hd : ∀ x, β x x = 1) (hn : ∀ x y, ‖β x y‖ = 1) (hβc : Continuous fun q : G × G => β q.1 q.2)
    (hβ : ∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ)))
    (hJ : ∀ v, J (J v) = -v) (hsym : ∀ x y, om x (J y) = om y (J x)) (hpos : ∀ v, v ≠ 0 → 0 < om v (J v))
    (hinj : ∀ g ∈ Γ, p g = 0 → g = 0) (hfin : ∀ R : ℝ, {g : G | g ∈ Γ ∧ g ∈ U₀ ∧ ‖p g‖ ≤ R}.Finite)
    (hχ0 : ∀ x, x ∉ U₀ → χ x = 0) (hχ1 : ∀ x, ‖χ x‖ ≤ 1) (hχι : ∀ x v, χ (x + ι v) = χ x)
    (hU : IsOpen (U : Set G)) (hUinv : ∀ u ∈ U, ∀ x, β x (u - ι (p u)) * χ (x + (u - ι (p u))) = χ x) (a : V) :
    Continuous (series p ι β om J Γ χ a) ∧ (∀ w, ContDiff ℝ ∞ fun v : V => series p ι β om J Γ χ a (w + ι v)) ∧
      ∀ w z, deriv (fun t : ℝ => β w (ι (t • z)) * series p ι β om J Γ χ a (w + ι (t • z))) 0 +
        Complex.I * deriv (fun t : ℝ => β w (ι (t • J z)) * series p ι β om J Γ χ a (w + ι (t • J z))) 0 = 0 := by
  obtain ⟨M, hM⟩ := exists_exponent om J
  have hexp := fun w : G => GlobalTheory.expSeries_contDiff_and_hasDerivAt V Γ
    (fun g => β g w * β (ι a) (g + w) * χ (g + w) *
        Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ)))
    (fun g => M (p g + (a + p w)))
    (summable_coeff p om J Γ U₀ χ hpos hinj hfin hχ0 hχ1 (fun g => β g w * β (ι a) (g + w))
      (fun g => by rw [norm_mul, hn, hn, one_mul]) w (a + p w) M)
  have hexpand := series_expand (Γ := Γ) hp hl hr hβ hsym hχι (fun y v => M y v) hM a
  have hne : ∀ x y, β x y ≠ 0 := fun x y h => by simpa [h] using hn x y
  have hgauss : ContDiff ℝ ∞ fun v : V => Complex.exp (-(Real.pi / 2 : ℂ) * (om v (J v) : ℝ)) :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_bilin om J))).cexp
  have hsmooth : ∀ w, ContDiff ℝ ∞ fun v : V => series p ι β om J Γ χ a (w + ι v) := by
    intro w
    have h1 : ContDiff ℝ ∞ fun v : V => Complex.exp (Real.pi * Complex.I * (om (p w) v : ℝ)) :=
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (LinearMap.toContinuousLinearMap (om (p w))).contDiff)).cexp
    have h2 := h1.mul (hgauss.mul (hexp w).1)
    refine (congrArg (ContDiff ℝ ∞) (funext fun v => ?_)).mp h2
    rw [← hexpand w v, hβ, ← mul_assoc, ← Complex.exp_add]
    simp
  refine ⟨?_, hsmooth, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro w
    have hc1 : Continuous fun x : G => p (x - w) := hpc.comp (continuous_id.sub continuous_const)
    have hc2 : Continuous fun x : G => β (w + ι (p (x - w))) ((x - w) - ι (p (x - w))) :=
      hβc.comp (f := fun x : G => (w + ι (p (x - w)), (x - w) - ι (p (x - w))))
        ((continuous_const.add (hιc.comp hc1)).prodMk
          ((continuous_id.sub continuous_const).sub (hιc.comp hc1)))
    have hc3 : Continuous fun x : G => (β (w + ι (p (x - w))) ((x - w) - ι (p (x - w))))⁻¹ *
        series p ι β om J Γ χ a (w + ι (p (x - w))) :=
      (hc2.inv₀ fun x => hne _ _).mul ((hsmooth w).continuous.comp hc1)
    refine hc3.continuousAt.congr ?_
    have hnhds : ∀ᶠ x in nhds w, x - w ∈ U := by
      have : IsOpen {x : G | x - w ∈ U} := hU.preimage (continuous_id.sub continuous_const)
      exact this.mem_nhds (by simp)
    filter_upwards [hnhds] with x hx
    have h := series_inv (Γ := Γ) (J := J) hl hr hd hβ a ((x - w) - ι (p (x - w)))
      (by rw [map_sub p, hp, sub_self]) (hUinv _ hx) (w + ι (p (x - w)))
    rw [← h, ← mul_assoc, inv_mul_cancel₀ (hne _ _), one_mul]
    congr 1; abel
  · intro w z
    have hder : ∀ z : V, HasDerivAt
        (fun t : ℝ => β w (ι (t • z)) * series p ι β om J Γ χ a (w + ι (t • z)))
        (∑' g : Γ, (β g w * β (ι a) (g + w) * χ (g + w) *
          Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ))) *
          M (p g + (a + p w)) z) 0 := by
      intro z
      have g1 : HasDerivAt (fun t : ℝ =>
          Complex.exp (-(Real.pi / 2 : ℂ) * (om (t • z) (J (t • z)) : ℝ))) 0 0 := by
        have g0 : HasDerivAt (fun t : ℝ => om (t • z) (J (t • z))) 0 0 := by
          have := ((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const (om z (J z))
          refine (this.congr_deriv (by simp)).congr_of_eventuallyEq
            (Filter.Eventually.of_forall fun t => ?_)
          simp [mul_assoc]
        exact (g0.ofReal_comp.const_mul (-(Real.pi / 2 : ℂ))).cexp.congr_deriv (by simp)
      have g2 := g1.mul ((hexp w).2 z).2
      simp only [hexpand]
      exact g2.congr_deriv (by simp)
    rw [(hder z).deriv, (hder (J z)).deriv, ← tsum_mul_left,
      ← ((hexp w).2 z).1.tsum_add (((hexp w).2 (J z)).1.mul_left Complex.I)]
    refine (tsum_congr fun g => ?_).trans tsum_zero
    rw [hM, hM, hJ, map_neg]
    push_cast
    linear_combination (-(Real.pi : ℂ) * (β g w * β (ι a) (g + w) * χ (g + w) *
          Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ))) *
          (om (p g + (a + p w)) (J z) : ℝ)) * Complex.I_mul_I

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
  {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem fin_smul_of_real {v : WO S T} (hv : v.map (finPart D) = 0) : (1 - realIdem D) • v = 0 := by
  rw [sub_smul, one_smul, sub_eq_zero]
  exact Matrix.ext fun i j => (realIdem_mul_of_real (congrFun (congrFun hv i) j)).symm

theorem fin_smul_of_fin {u : WO S T} (hu : u.map (infPart D) = 0) : (1 - realIdem D) • u = u := by
  rw [sub_smul, one_smul, mem_finSub_iff.1 hu, sub_zero]

theorem chiLat_add_real (w : 𝓞 D.host.E) (x : WO S T) {v : WO S T} (hv : v.map (finPart D) = 0) :
    chiLat ψ S T LS LT w (x + v) = chiLat ψ S T LS LT w x := by
  have e : (1 - realIdem D) • (x + v) = (1 - realIdem D) • x := by rw [smul_add, fin_smul_of_real hv, add_zero]
  rw [chiLat, chiLat, e]

theorem quad_identity {w : 𝓞 D.host.E} (hw : w + GlobalTheory.FinWeil.sgO D w = 1) (y u : WO S T) :
    -symplOH S T (intA D w • u) u + (symplOH S T y u + symplOH S T (intA D w • (y + u)) (y + u)) =
      symplOH S T (intA D w • y) y + symplO S T (intA D w • y) u := by
  have h1 : intA D w • y + cA D (intA D w) • y = y := by
    rw [← add_smul, cA_intA, ← RingHom.map_add, hw, RingHom.map_one, one_smul]
  have h2 := congrArg (fun z => symplOH S T z u) h1
  simp only [symplOH_add_left] at h2
  have h3 := symplOH_smul (intA D w) u y
  rw [symplOH_skew S T (cA D (intA D w) • y) u] at h3
  rw [smul_add (intA D w) y u, symplOH_add_left, symplOH_add_right, symplOH_add_right, ← symplOH_add_self]
  linear_combination h3 - h2

theorem chiLat_add_lat (hA : SelfDual (gamF ψ S T) (latF S T LS LT)) {w : 𝓞 D.host.E}
    (hw : w + GlobalTheory.FinWeil.sgO D w = 1) {u : XF S T} (hu : u ∈ latF S T LS LT) (x : WO S T) :
    phase ψ w u * (ψ (symplOH S T x u) * chiLat ψ S T LS LT w (x + u)) = chiLat ψ S T LS LT w x := by
  have e : (1 - realIdem D) • (x + (u : WO S T)) = (1 - realIdem D) • x + u := by
    rw [smul_add, fin_smul_of_fin u.fin]
  have e2 : symplOH S T x u = symplOH S T ((1 - realIdem D) • x) u := by
    have hdec : x = realIdem D • x + (1 - realIdem D) • x := by rw [← add_smul, add_sub_cancel, one_smul]
    conv_lhs => rw [hdec]
    rw [symplOH_add_left, symplOH, symplO_real_fin S T (real_smul_real x) u.fin, mul_zero, zero_add]
  rw [chiLat, chiLat, e, e2]
  have hy := fin_smul_fin x
  generalize (1 - realIdem D) • x = y at hy ⊢
  by_cases h : y ∈ latO S T LS LT fun _ => True
  · rw [if_pos h, if_pos (add_mem h hu)]
    have h0 : ψ (symplO S T (intA D w • y) u) = 1 :=
      (hA _).1 ((latF S T LS LT).smul_mem w (show XF.mk y hy ∈ latF S T LS LT from h)) u hu
    rw [phase, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, quad_identity hw, AddChar.map_add_eq_mul, h0,
      mul_one]
  · have h2 : y + (u : WO S T) ∉ latO S T LS LT fun _ => True := fun h' => h (by
      have h3 := sub_mem h' (mem_latF.1 hu)
      rwa [add_sub_cancel_right] at h3)
    rw [if_neg h, if_neg h2, mul_zero, mul_zero]

theorem series_theta_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ w : 𝓞 D.host.E, w + GlobalTheory.FinWeil.sgO D w = 1 → ∀ a : RW T S, ∃ hf : IsThetaFunO ψ S T (serO ψ θ σ S T sS sT ΛS ΛT w a), Fixes (opF hψ.1 S T w) (latF S T ΛS ΛT) (⟨serO ψ θ σ S T sS sT ΛS ΛT w a, hf⟩ : thetaSub ψ S T) ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (serO ψ θ σ S T sS sT ΛS ΛT w a) := by
  classical
  intro D ψ hψ θ σ hσ S T sS sT hS hT ΛS ΛT dS dT w hw a
  have hθ := hσ.inf
  obtain ⟨hJJ, hskew, hinvJ, hneg⟩ := GlobalTheory.T.realSymplecticForm_alternating_invariant_definite D S T sS sT hS hT
  obtain ⟨aL, aR, a0, -, acont, arat, -, -, -⟩ := GlobalTheory.T.homSymplecticHalfForm_algebraic_laws_continuous D S T
  have hA := selfDual_latF (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ dS dT).1
  have htop : IsTopologicalAddGroup (WO S T) := (GlobalTheory.AdelicMatrixLattice.lattice D T S).1
  have hl : ∀ x y z : WO S T, ψ (symplOH S T (x + y) z) = ψ (symplOH S T x z) * ψ (symplOH S T y z) :=
    fun x y z => by rw [aL, AddChar.map_add_eq_mul]
  have hr : ∀ x y z : WO S T, ψ (symplOH S T x (y + z)) = ψ (symplOH S T x y) * ψ (symplOH S T x z) :=
    fun x y z => by rw [aR, AddChar.map_add_eq_mul]
  have hd : ∀ x : WO S T, ψ (symplOH S T x x) = 1 := fun x => by rw [a0, AddChar.map_zero_eq_one]
  have hβ : ∀ (x : WO S T) (v : RW T S), ψ (symplOH S T x (iotaW σ T S v)) =
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S x) v : ℝ)) := fun x v => by
    have e := GlobalTheory.T.stdCharacter_halfSymplecticForm_realPoint D θ ψ hθ hψ S T x (iotaW σ T S v) (Or.inr (hσ.real_iota T S v))
    rw [hσ.pi_iota] at e
    exact e
  have fl : ∀ u ∈ latF S T ΛS ΛT, ∀ x : WO S T, phase ψ w u * (ψ (symplOH S T x u) *
      serO ψ θ σ S T sS sT ΛS ΛT w a (x + u)) = serO ψ θ σ S T sS sT ΛS ΛT w a x := fun u hu x =>
    series_inv_scalar (G := WO S T) (β := fun x y => ψ (symplOH S T x y)) hl hr hd hβ a u (piW_of_inf θ u.fin) _
      (chiLat_add_lat hA hw hu) x
  set Λ : AddSubgroup (WO S T) := latO S T ΛS ΛT fun _ => True with hΛ
  have hlev : ∀ u ∈ thick Λ 2, ∃ l ∈ latF S T ΛS ΛT, u - iotaW σ T S (piW θ T S u) = ((2 • l : XF S T) : WO S T) := by
    rintro u ⟨l, hl, hu⟩
    refine ⟨XF.mk l (latO_fin hl), hl, ?_⟩
    have e := hσ.iota_pi (V := T) (W := S) (x := u - 2 • l) hu
    rw [map_sub, map_nsmul, piW_of_inf θ (latO_fin hl), smul_zero, sub_zero] at e
    rw [e, XF.coe_nsmul, XF.coe_mk]
    abel
  obtain ⟨fc, fs, fv⟩ := series_regular (G := WO S T) (piW θ T S) (iotaW σ T S)
    (fun x y => ψ (symplOH S T x y)) (omO S T) (jO S T sS sT) (ratL T S)
    (Λ.comap (AddMonoidHom.mk' (fun x : WO S T => (1 - realIdem D) • x) (smul_add _))) (thick Λ 2)
    (chiLat ψ S T ΛS ΛT w) (continuous_pi' hθ T S) (hσ.continuous_iota T S) (hσ.pi_iota T S) hl hr hd
    (fun x y => hψ.1.2.1 _) (hψ.1.1.comp acont) hβ hJJ
    (fun x y => by rw [← hinvJ x, hJJ, map_neg, ← hskew])
    (fun v hv => by rw [hskew]; exact neg_pos.2 (hneg v hv))
    (by
      rintro _ ⟨g, rfl⟩ h
      have : g = 0 := by
        funext i j
        have e : θ (D.eTau.symm 1) (infPart D (incA D (g i j))) = 0 :=
          congrFun (congrFun (congrFun h (D.eTau.symm 1)) i) j
        rw [comp_incA hθ] at e
        exact (tauE D _).injective (e.trans (RingHom.map_zero _).symm)
      rw [this, map_zero])
    (fun R => by
      refine ((GlobalTheory.T.finite_rational_points_completed_lattice D S T ΛS ΛT dS dT R).image (ratW T S)).subset ?_
      rintro _ ⟨⟨g, rfl⟩, h1, h2⟩
      refine ⟨g, ⟨⟨_, h1, ?_⟩, fun τ i j => ?_⟩, rfl⟩
      · have e : (ratW T S g : WO S T) - (1 - realIdem D) • (ratW T S g : WO S T) =
            realIdem D • (ratW T S g : WO S T) := by rw [sub_smul, one_smul, sub_sub_cancel]
        exact (congrArg (fun z : WO S T => z.map (finPart D)) e).trans (real_smul_real _)
      · rw [← comp_incA hθ]
        let y : RW T S := piW θ T S (ratW T S g)
        exact ((norm_le_pi_norm (y τ i) j).trans ((norm_le_pi_norm (y τ) i).trans (norm_le_pi_norm y τ))).trans h2)
    (fun x hx => if_neg hx)
    (fun x => by
      rw [chiLat]
      split_ifs
      · exact (hψ.1.2.1 _).le
      · rw [norm_zero]; exact zero_le_one)
    (fun x v => chiLat_add_real w x (hσ.real_iota T S v))
    (GlobalTheory.T.isOpen_nsmul_completedHomLattice_finiteAdelic D S T ΛS ΛT dS dT 2 two_pos)
    (fun u hu x => by
      obtain ⟨l, hl, e⟩ := hlev u hu
      have e2 := chiLat_add_lat hA hw (nsmul_mem hl 2) x
      rw [phase_two hA w hl, one_mul] at e2
      rw [e]
      exact e2) a
  refine ⟨⟨fun g x => ?_, ⟨thick Λ 2, GlobalTheory.T.isOpen_nsmul_completedHomLattice_finiteAdelic D S T ΛS ΛT dS dT 2 two_pos, fun u hu h => ?_⟩, fc,
    fun k L hL hL0 x => ?_⟩, fun u hu => Subtype.ext (funext fun x => fl u hu x), fun τ z => ?_⟩
  · have e : ψ (symplOH S T (ratW T S g) x) * serO ψ θ σ S T sS sT ΛS ΛT w a (ratW T S g + x) =
        serO ψ θ σ S T sS sT ΛS ΛT w a x :=
      series_quasi (G := WO S T) (Γ := ratL T S) (β := fun x y => ψ (symplOH S T x y)) hl hr (fun g hg g' hg' => by
        obtain ⟨b, hb⟩ := arat g hg g' hg'
        simp only [hb]
        exact hψ.1.2.2.1 b) a (ratW T S g) ⟨g, rfl⟩ x
    rw [← e, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  · obtain ⟨l, hl, e⟩ := hlev u hu
    rw [piW_of_inf θ h, map_zero, sub_zero] at e
    funext x
    have e2 := fl _ (nsmul_mem hl 2) x
    rw [phase_two hA w hl, one_mul, ← e] at e2
    exact e2
  · exact ((smooth_iff_sm_and_real_lines D θ σ hσ T S).1 _).2 fs k L hL hL0 x
  · funext x
    let v : RW T S := Pi.single τ z
    have v1 : v τ = z := Pi.single_eq_same _ _
    have v2 : ∀ τ', τ' ≠ τ → v τ' = 0 := fun τ' h => Pi.single_eq_of_ne h _
    have l1 := lineAt_eq hσ S T τ z v v1 v2
    have l2 := lineAt_eq hσ S T τ (cplxO (sS τ) (sT τ) z) (jO S T sS sT v) (by rw [jO_apply, v1]) (fun τ' h => by
      rw [jO_apply, v2 τ' h]
      have : cplxO (sS τ') (sT τ') (0 : Matrix (Fin T.rank) (Fin S.rank) ℂ) = 0 := by simp [cplxO]
      exact this)
    show deriv (fun t : ℝ => ψ (symplOH S T x (lineAt θ τ z t)) *
        serO ψ θ σ S T sS sT ΛS ΛT w a (x + lineAt θ τ z t)) 0 +
      Complex.I * deriv (fun t : ℝ => ψ (symplOH S T x (lineAt θ τ (cplxO (sS τ) (sT τ) z) t)) *
        serO ψ θ σ S T sS sT ΛS ΛT w a (x + lineAt θ τ (cplxO (sS τ) (sT τ) z) t)) 0 = 0
    simp only [l1, l2]
    exact fv x v

end GlobalTheory.GaussSeriesVacuum

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_poincare_series_theta_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ w : 𝓞 D.host.E, w + GlobalTheory.FinWeil.sgO D w = 1 → ∀ a : RW T S, ∃ hf : IsThetaFunO ψ S T (serO ψ θ σ S T sS sT ΛS ΛT w a), Fixes (opF hψ.1 S T w) (latF S T ΛS ΛT) (⟨serO ψ θ σ S T sS sT ΛS ΛT w a, hf⟩ : thetaSub ψ S T) ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (serO ψ θ σ S T sS sT ΛS ΛT w a) := by
  first | exact @GlobalTheory.GaussSeriesVacuum.series_theta_vacuum | exact GlobalTheory.GaussSeriesVacuum.series_theta_vacuum | (intros; apply GlobalTheory.GaussSeriesVacuum.series_theta_vacuum <;> assumption)
end

section
section
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory.PoincareUnfold

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]

open MeasureTheory in
open scoped Pointwise in
private lemma setIntegral_exp_linear_fundamentalDomain_eq_zero {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (L : Submodule ℤ V)
    [VAddInvariantMeasure L V μ] [Countable L] {D : Set V} (hD : IsAddFundamentalDomain L D μ)
    (hDm : MeasurableSet D) (φ : V →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) (hint : ∀ y ∈ L, ∃ z : ℤ, φ y = z) :
    ∫ v in D, Complex.exp (2 * Real.pi * Complex.I * (φ v : ℝ)) ∂μ = 0 := by
  set f : V → ℂ := fun v => Complex.exp (2 * Real.pi * Complex.I * (φ v : ℝ)) with hf
  have hper : ∀ (g : L) (v : V), f (g +ᵥ v) = f v := by
    intro g v
    obtain ⟨z, hz⟩ := hint g g.2
    have hgv : (g +ᵥ v : V) = (g : V) + v := rfl
    simp only [hf, hgv, map_add, hz]
    push_cast
    rw [mul_add, Complex.exp_add]
    have : Complex.exp (2 * Real.pi * Complex.I * (z : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I z]; ring_nf
    rw [this, one_mul]
  obtain ⟨u, hu⟩ : ∃ u, φ u ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ (LinearMap.ext h)
  set w : V := (1 / (2 * φ u)) • u with hw
  have hφw : φ w = 1 / 2 := by
    rw [hw, map_smul, smul_eq_mul]; field_simp
  have hshift : ∀ v, f (w + v) = -f v := by
    intro v
    simp only [hf, map_add, hφw]
    push_cast
    rw [mul_add, Complex.exp_add]
    have : Complex.exp (2 * Real.pi * Complex.I * (1 / 2 : ℂ)) = -1 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 / 2) = Real.pi * Complex.I by ring]
      exact Complex.exp_pi_mul_I
    rw [this, neg_one_mul]
  have hD' : IsAddFundamentalDomain L (w +ᵥ D) μ := hD.vadd_of_comm w
  have h1 : ∫ v in D, f v ∂μ = ∫ v in w +ᵥ D, f v ∂μ := hD.setIntegral_eq hD' hper
  have h2 : ∫ v in w +ᵥ D, f v ∂μ = ∫ v in D, f (w + v) ∂μ := by
    rw [← integral_indicator (hDm.const_vadd w), ← integral_indicator hDm]
    · rw [← integral_add_left_eq_self (μ := μ) _ w]
      congr 1
      ext v
      by_cases hv : v ∈ D
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (show w + v ∈ w +ᵥ D from Set.vadd_mem_vadd_set hv)]
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem]
        rwa [← vadd_eq_add, Set.vadd_mem_vadd_set_iff]

  have h3 : ∫ v in D, f v ∂μ = -∫ v in D, f v ∂μ := by
    calc ∫ v in D, f v ∂μ = ∫ v in D, f (w + v) ∂μ := h1.trans h2
      _ = ∫ v in D, -f v ∂μ := setIntegral_congr_fun hDm fun v _ => hshift v
      _ = -∫ v in D, f v ∂μ := integral_neg _
  have h4 : (2 : ℂ) * ∫ v in D, f v ∂μ = 0 := by
    rw [two_mul]; nth_rewrite 2 [h3]; ring
  simpa using h4

open MeasureTheory in
open scoped Pointwise in

theorem _root_.GlobalTheory.PoincareUnfold.unfold_poincare_fourier : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (Γ : Type) [AddCommGroup Γ] (j : Γ →+ V), Function.Injective j → ∀ C : AddSubgroup Γ,
    (∀ R : ℝ, {c : Γ | c ∈ C ∧ ‖j c‖ ≤ R}.Finite) → Submodule.span ℝ (j '' (C : Set Γ)) = ⊤ →
    ∀ (n : ℕ) (t : Fin n → Γ) (Q : Γ → ℂ), (∀ x, Q x ≠ 0 → ∃ k, x - t k ∈ C) →
    (∀ k k', t k - t k' ∈ C → k = k') → (∀ x, ∀ c ∈ C, Q (x + c) = Q x) →
    ∀ F : V → ℂ, Integrable F μ → ∀ (a : Γ → ℂ) (l : Γ → V →ₗ[ℝ] ℝ), Summable (fun x => ‖a x‖) →
    l 0 = 0 → (∀ x, x ≠ 0 → l x ≠ 0) → (∀ x, a x ≠ 0 → ∀ c ∈ C, ∃ z : ℤ, l x (j c) = z) →
    (∀ v, ∑' x, Q x * F (j x + v) =
      ∑' x, a x * Complex.exp (2 * Real.pi * Complex.I * (l x v : ℝ))) →
    ∃ r : ℝ, 0 < r ∧ (∑ k, Q (t k)) * ∫ v, F v ∂μ = r * a 0 := by
  intro V _ _ _ _ _ μ _ Γ _ j hj C hfin hspan n t Q hQsupp ht hQper F hF a l ha hl0 hl hint H
  classical
  set L : Submodule ℤ V := (C.map j).toIntSubmodule with hLdef
  have hmemL : ∀ y, y ∈ L ↔ ∃ c ∈ C, j c = y := fun y => by
    exact AddSubgroup.mem_map
  have hLset : (L : Set V) = j '' (C : Set Γ) := by
    ext y; simp only [SetLike.mem_coe, hmemL, Set.mem_image]
  have hj0 : ∀ c, j c = 0 ↔ c = 0 := fun c => ⟨fun h => hj (by rw [h, map_zero]), fun h => by
    rw [h, map_zero]⟩
  haveI : DiscreteTopology L := by
    rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
    set T : Finset ℝ := insert 1 (((hfin 1).toFinset.filter (· ≠ 0)).image fun c => ‖j c‖)
    have hTne : T.Nonempty := Finset.insert_nonempty _ _
    refine ⟨T.min' hTne, ?_, ?_⟩
    · show 0 < T.min' hTne
      rw [Finset.lt_min'_iff]
      intro y hy
      rw [Finset.mem_insert, Finset.mem_image] at hy
      rcases hy with rfl | ⟨c, hc, rfl⟩
      · exact one_pos
      · rw [Finset.mem_filter] at hc
        exact norm_pos_iff.2 fun h => hc.2 ((hj0 c).1 h)
    · rintro ⟨y, hy⟩ hdist
      obtain ⟨c, hc, rfl⟩ := (hmemL y).1 hy
      have hlt : ‖j c‖ < T.min' hTne := by simpa [dist_eq_norm] using hdist
      have hle1 : T.min' hTne ≤ 1 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
      by_cases hc0 : c = 0
      · ext; simp [hc0]
      · exfalso
        have hmem : ‖j c‖ ∈ T := Finset.mem_insert_of_mem (Finset.mem_image.2
          ⟨c, Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 ⟨hc, by linarith⟩, hc0⟩, rfl⟩)
        exact absurd (Finset.min'_le _ _ hmem) (not_le.2 hlt)
  haveI : IsZLattice ℝ L := ⟨by rw [hLset]; exact hspan⟩
  haveI : VAddInvariantMeasure L V μ := ⟨fun c s _ => measure_preimage_add μ (c : V) s⟩
  set ψ : C → L := fun c => ⟨j c, (hmemL _).2 ⟨c, c.2, rfl⟩⟩ with hψ
  have hψinj : Function.Injective ψ := fun c c' h => Subtype.ext (hj (congrArg Subtype.val h))
  have hψsurj : Function.Surjective ψ := fun y => by
    obtain ⟨c, hc, hcy⟩ := (hmemL y).1 y.2
    exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩
  haveI : Countable L := (Module.Free.chooseBasis ℤ L).repr.injective.countable
  haveI : Countable C := hψinj.countable
  set D := ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L) with hDdef
  have hD : IsAddFundamentalDomain L D μ := ZLattice.isAddFundamentalDomain _ μ
  have hDfin : μ D < ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top
  refine ⟨ZLattice.covolume L μ, ZLattice.covolume_pos L μ, ?_⟩
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L μ hD]
  have hR : ∫ v in D, (∑' x, a x * Complex.exp (2 * Real.pi * Complex.I * (l x v : ℝ))) ∂μ =
      ((μ.real D : ℝ) : ℂ) * a 0 := by
    have hDm : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet _
    set E : Γ → V → ℂ := fun x v => Complex.exp (2 * Real.pi * Complex.I * (l x v : ℝ)) with hE
    have hEnorm : ∀ x v, ‖E x v‖ₑ = 1 := by
      intro x v
      rw [← ofReal_norm_eq_enorm]
      simp only [hE]
      rw [show (2 * Real.pi * Complex.I * ((l x v : ℝ) : ℂ)) = ((2 * Real.pi * l x v : ℝ) : ℂ) *
        Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, ENNReal.ofReal_one]
    have hEcont : ∀ x, Continuous (E x) := fun x => by
      simp only [hE]
      fun_prop
    set s := Function.support a with hs
    have hscount : s.Countable := ha.of_norm.countable_support
    haveI : Countable s := hscount.to_subtype
    have hsub : ∀ v, ∑' x, a x * E x v = ∑' x : s, a x * E x v := fun v =>
      (tsum_subtype_eq_of_support_subset fun x hx => by
        simp only [Function.mem_support] at hx ⊢
        intro h; exact hx (by rw [h, zero_mul])).symm
    have hchar : ∀ x, ∫ v in D, a x * E x v ∂μ =
        if x = 0 then ((μ.real D : ℝ) : ℂ) * a 0 else 0 := by
      intro x
      rw [integral_const_mul]
      split_ifs with hx
      · subst hx
        simp only [hE, hl0, LinearMap.zero_apply, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
          setIntegral_const, Complex.real_smul, mul_one]
        ring
      · by_cases hax : a x = 0
        · rw [hax, zero_mul]
        · rw [setIntegral_exp_linear_fundamentalDomain_eq_zero μ L hD hDm (l x) (hl x hx)
            (fun y hy => by
              obtain ⟨c, hc, rfl⟩ := (hmemL y).1 hy
              exact hint x hax c hc), mul_zero]
    show ∫ v in D, (∑' x, a x * E x v) ∂μ = _
    simp_rw [hsub]
    rw [integral_tsum]
    · rw [tsum_subtype_eq_of_support_subset (f := fun x => ∫ v in D, a x * E x v ∂μ)]
      · simp_rw [hchar]
        exact tsum_ite_eq 0 _
      · intro x hx
        rw [Function.mem_support, hchar] at hx
        split_ifs at hx with h0
        · subst h0
          intro h; exact hx (by rw [h, mul_zero])
        · exact absurd rfl hx
    · intro x
      exact ((hEcont x).const_mul (a x) |>.aestronglyMeasurable)
    · simp_rw [enorm_mul, hEnorm, mul_one, lintegral_const, Measure.restrict_apply_univ]
      rw [ENNReal.tsum_mul_right]
      refine ENNReal.mul_ne_top ?_ hDfin.ne
      simp_rw [enorm_eq_nnnorm]
      refine ENNReal.tsum_coe_ne_top_iff_summable.2 ?_
      rw [← NNReal.summable_coe]
      exact ha.subtype s
  have hLHS : ∫ v in D, (∑' x, Q x * F (j x + v)) ∂μ = (∑ k, Q (t k)) * ∫ v, F v ∂μ := by
    have hDm : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet _
    set e : Fin n × C → Γ := fun p => t p.1 + p.2 with he
    have heinj : Function.Injective e := by
      rintro ⟨k, c⟩ ⟨k', c'⟩ h
      simp only [he] at h
      have hk : k = k' := ht k k' (by
        rw [show t k - t k' = c' - c by rw [sub_eq_sub_iff_add_eq_add, h, add_comm]]
        exact C.sub_mem c'.2 c.2)
      subst hk
      exact Prod.ext rfl (Subtype.ext (add_left_cancel h))
    have hsupp : ∀ v, Function.support (fun x => Q x * F (j x + v)) ⊆ Set.range e := by
      intro v x hx
      have hQx : Q x ≠ 0 := fun h => hx (by simp [h])
      obtain ⟨k, hk⟩ := hQsupp x hQx
      exact ⟨(k, ⟨x - t k, hk⟩), by simp [he]⟩
    set g : Fin n × C → V → ℂ := fun p v => Q (t p.1) * F (j (t p.1) + (j p.2 + v)) with hg
    have hrw : ∀ v, ∑' x, Q x * F (j x + v) = ∑' p, g p v := by
      intro v
      rw [← heinj.tsum_eq (hsupp v)]
      refine tsum_congr fun p => ?_
      simp only [he, hg, map_add, hQper _ _ p.2.2, add_assoc]
    have hunf : ∀ G : V → ℂ, Integrable G μ → ∫ v, G v ∂μ = ∑' c : C, ∫ v in D, G (j c + v) ∂μ := by
      intro G hG
      rw [hD.integral_eq_tsum' G hG,
        ← ((Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩).trans (Equiv.neg L)).tsum_eq]
      refine tsum_congr fun c => ?_
      rw [Equiv.trans_apply, Equiv.neg_apply, neg_neg]
      rfl
    have hunfl : ∀ G : V → ENNReal, ∫⁻ v, G v ∂μ = ∑' c : C, ∫⁻ v in D, G (j c + v) ∂μ := by
      intro G
      rw [hD.lintegral_eq_tsum' G,
        ← ((Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩).trans (Equiv.neg L)).tsum_eq]
      refine tsum_congr fun c => ?_
      rw [Equiv.trans_apply, Equiv.neg_apply, neg_neg]
      rfl
    have hfinite : ∑' p, ∫⁻ v in D, ‖g p v‖ₑ ∂μ ≠ ⊤ := by
      simp_rw [hg, enorm_mul]
      simp_rw [lintegral_const_mul' _ _ enorm_ne_top]
      rw [ENNReal.tsum_prod (f := fun k (c : C) =>
        ‖Q (t k)‖ₑ * ∫⁻ v in D, ‖F (j (t k) + (j c + v))‖ₑ ∂μ), tsum_fintype]
      refine (ENNReal.sum_lt_top.2 fun k _ => ?_).ne
      rw [ENNReal.tsum_mul_left, ← hunfl (fun v => ‖F (j (t k) + v)‖ₑ)]
      exact ENNReal.mul_lt_top enorm_lt_top (hF.comp_add_left (j (t k))).hasFiniteIntegral
    have hmeas : ∀ p, AEStronglyMeasurable (g p) (μ.restrict D) := fun p =>
      (((hF.comp_add_left (j (t p.1))).comp_add_left (j p.2)).aestronglyMeasurable.const_mul
        _).restrict
    have hsumm : Summable (fun p => ∫ v in D, g p v ∂μ) := by
      refine Summable.of_norm_bounded (ENNReal.summable_toReal hfinite) fun p => ?_
      refine (norm_integral_le_lintegral_norm _).trans_eq ?_
      simp_rw [ofReal_norm_eq_enorm]
    simp_rw [hrw]
    rw [integral_tsum hmeas hfinite, hsumm.tsum_prod, tsum_fintype, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hg, integral_const_mul]
    rw [tsum_mul_left, ← hunf _ (hF.comp_add_left (j (t k))), integral_add_left_eq_self]
  rw [← hLHS, ← hR]
  exact setIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _) fun v _ => H v

end GlobalTheory.PoincareUnfold
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfold_poincareSeries_lattice_fourier : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (Γ : Type) [AddCommGroup Γ] (j : Γ →+ V), Function.Injective j → ∀ C : AddSubgroup Γ, (∀ R : ℝ, {c : Γ | c ∈ C ∧ ‖j c‖ ≤ R}.Finite) → Submodule.span ℝ (j '' (C : Set Γ)) = ⊤ → ∀ (n : ℕ) (t : Fin n → Γ) (Q : Γ → ℂ), (∀ x, Q x ≠ 0 → ∃ k, x - t k ∈ C) → (∀ k k', t k - t k' ∈ C → k = k') → (∀ x, ∀ c ∈ C, Q (x + c) = Q x) → ∀ F : V → ℂ, Integrable F μ → ∀ (a : Γ → ℂ) (l : Γ → V →ₗ[ℝ] ℝ), Summable (fun x => ‖a x‖) → l 0 = 0 → (∀ x, x ≠ 0 → l x ≠ 0) → (∀ x, a x ≠ 0 → ∀ c ∈ C, ∃ z : ℤ, l x (j c) = z) → (∀ v, ∑' x, Q x * F (j x + v) = ∑' x, a x * Complex.exp (2 * Real.pi * Complex.I * (l x v : ℝ))) → ∃ r : ℝ, 0 < r ∧ (∑ k, Q (t k)) * ∫ v, F v ∂μ = r * a 0 := by
  atlas_forward_decl GlobalTheory.PoincareUnfold.unfold_poincare_fourier
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatTrace

open GlobalTheory.SplitScalar

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem beta_iota_right (hψ : IsStdChar D ψ (-1)) (hσ : Chart θ σ) (x : WO S T) (v : RW T S) :
    ψ (symplOH S T x (iotaW σ T S v)) = Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S x) v : ℝ)) := by
  rw [GlobalTheory.OrientedChar.char_symplOH D θ ψ hσ.inf hψ S T _ _ (Or.inr (hσ.real_iota T S v)), hσ.pi_iota]

theorem beta_iota_left (hψ : IsStdChar D ψ (-1)) (hσ : Chart θ σ) (v : RW T S) (x : WO S T) :
    ψ (symplOH S T (iotaW σ T S v) x) = Complex.exp (-(Real.pi * Complex.I) * (omO S T v (piW θ T S x) : ℝ)) := by
  rw [GlobalTheory.OrientedChar.char_symplOH D θ ψ hσ.inf hψ S T _ _ (Or.inl (hσ.real_iota T S v)), hσ.pi_iota]

theorem beta_fin (hψ : IsStdChar D ψ (-1)) (hσ : Chart θ σ) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ψ (symplOH S T (finRat S T x) (finRat S T y)) *
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (infRat S T x) (infRat S T y) : ℝ)) = 1 := by
  obtain ⟨c, hc⟩ := (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.2.2.1 (ratW T S x) ⟨x, rfl⟩ (ratW T S y) ⟨y, rfl⟩
  have h1 : ψ (symplOH S T (ratW T S x) (ratW T S y)) = 1 := by
    rw [hc]; exact hψ.1.2.2.1 c
  have h2 := beta_iota_left hψ hσ (infRat S T x) (ratW T S y)
  have h3 := beta_iota_right hψ hσ (finRat S T x) (infRat S T y)
  rw [piW_of_inf θ (finRat_inf S T x), LinearMap.map_zero, LinearMap.zero_apply, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero] at h3
  have d1 : symplOH S T (ratW T S x) (ratW T S y) =
      symplOH S T (iotaW σ T S (infRat S T x)) (ratW T S y) + symplOH S T (finRat S T x) (ratW T S y) :=
    (congrArg (fun w => symplOH S T w (ratW T S y)) (ratW_eq hσ S T x)).trans (symplOH_add_left S T _ _ _)
  have d2 : symplOH S T (finRat S T x) (ratW T S y) =
      symplOH S T (finRat S T x) (iotaW σ T S (infRat S T y)) + symplOH S T (finRat S T x) (finRat S T y) :=
    (congrArg (fun w => symplOH S T (finRat S T x) w) (ratW_eq hσ S T y)).trans (symplOH_add_right S T _ _ _)
  rw [d1, d2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h2, h3, one_mul, mul_comm, piW_ratW hσ.inf] at h1
  exact h1

theorem fin_smul_iota (hσ : Chart θ σ) (v : RW T S) : (1 - realIdem D) • (iotaW σ T S v : WO S T) = 0 := by
  rw [sub_smul, one_smul, sub_eq_zero]
  exact (Matrix.ext fun i j => realIdem_mul_of_real (congrFun (congrFun (hσ.real_iota T S v) i) j)).symm

theorem fin_smul_XF (y : XF S T) : (1 - realIdem D) • (y : WO S T) = y := by
  rw [sub_smul, one_smul, mem_finSub_iff.1 y.fin, sub_zero]

theorem chiLat_add_iota (hσ : Chart θ σ) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (w : 𝓞 D.host.E) (x : WO S T) (v : RW T S) :
    chiLat ψ S T LS LT w (x + iotaW σ T S v) = chiLat ψ S T LS LT w x := by
  unfold chiLat
  rw [smul_add, fin_smul_iota hσ, add_zero]

theorem ratW_injective (hθ : IsInfFam θ) : Function.Injective (ratW T S) := fun x y h =>
  infRat_injective S T (by rw [← piW_ratW hθ, ← piW_ratW hθ, h])

def ratEquiv (hθ : IsInfFam θ) (S T : HSp D) : Matrix (Fin T.rank) (Fin S.rank) D.host.E ≃ ratL T S :=
  Equiv.ofBijective (fun y => ⟨ratW T S y, y, rfl⟩)
    ⟨fun _ _ h => ratW_injective hθ (congrArg Subtype.val h), by rintro ⟨_, y, rfl⟩; exact ⟨y, rfl⟩⟩

theorem coe_ratEquiv (hθ : IsInfFam θ) (y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (ratEquiv hθ S T y : WO S T) = ratW T S y := rfl

theorem serO_eq (hθ : IsInfFam θ) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Set (Fin S.rank → D.host.E))
    (LT : Set (Fin T.rank → D.host.E)) (w : 𝓞 D.host.E) (a : RW T S) (x : WO S T) :
    serO ψ θ σ S T sS sT LS LT w a x = ∑' y : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      ψ (symplOH S T (ratW T S y) x) * ψ (symplOH S T (iotaW σ T S a) (ratW T S y + x)) *
        chiLat ψ S T LS LT w (ratW T S y + x) *
        Complex.exp (-(Real.pi / 2 : ℂ) * (omO S T (infRat S T y + (a + piW θ T S x))
          (jO S T sS sT (infRat S T y + (a + piW θ T S x))) : ℝ)) := by
  unfold serO GlobalTheory.HeisenbergGaussianSeries.series
  rw [← (ratEquiv hθ S T).tsum_eq]
  simp only [coe_ratEquiv, piW_ratW hθ]

section Act

variable {g : GA D S} {h : GA D T} {a : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
  {b : Matrix (Fin T.rank) (Fin T.rank) D.host.E} (hg : Formalism.L2.Theta.mt S g = a.map (incA D))
  (hh : Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D))
include hg hh

theorem act_eq (x : WO S T) : actO S T g⁻¹ h⁻¹ x =
    HMul.hMul (HMul.hMul (b.map (incA D)) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (a.map (incA D)) := by
  rw [actO, inv_inv, hg, hh]

theorem act_ratW (y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    actO S T g⁻¹ h⁻¹ (ratW T S y) = ratW T S (b * y * a) := by
  rw [act_eq hg hh, ratW, ratW, Matrix.map_mul, Matrix.map_mul]

theorem act_finRat (y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    actO S T g⁻¹ h⁻¹ (finRat S T y) = finRat S T (b * y * a) := by
  rw [finRat_eq, finRat_eq, actO_smul, act_ratW hg hh]

theorem piW_act (hθ : IsInfFam θ) (x : WO S T) : piW θ T S (actO S T g⁻¹ h⁻¹ x) =
    actR S T (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) (piW θ T S x) := by
  funext τ
  have hi : ∀ {n : ℕ} (m : Matrix (Fin n) (Fin n) D.host.E),
      (m.map (incA D)).map ((θ τ).comp (infPart D)) = m.map (tauE D τ) := fun m => by
    funext i j
    exact comp_incA hθ τ _
  rw [act_eq hg hh]
  show (HMul.hMul (HMul.hMul (b.map (incA D)) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (a.map (incA D))).map
      ((θ τ).comp (infPart D)) =
    HMul.hMul (HMul.hMul (b.map (tauE D τ)) (x.map ((θ τ).comp (infPart D)))) (a.map (tauE D τ))
  rw [Matrix.map_mul, Matrix.map_mul, hi, hi]

theorem act_iota (hσ : Chart θ σ) (v : RW T S) : actO S T g⁻¹ h⁻¹ (iotaW σ T S v) =
    iotaW σ T S (actR S T (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) v) := by
  refine hσ.real_ext (V := T) (W := S) ?_ (hσ.real_iota T S _) ?_
  · have e : (iotaW σ T S v : WO S T) = realIdem D • iotaW σ T S v := by
      have := fin_smul_iota hσ v
      rwa [sub_smul, one_smul, sub_eq_zero] at this
    rw [e, actO_smul]
    exact real_smul_real _
  · rw [piW_act hg hh hσ.inf, hσ.pi_iota, hσ.pi_iota]

theorem omO_act (hσ : Chart θ σ) (u v : RW T S) :
    omO S T (actR S T (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) u)
      (actR S T (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) v) = omO S T u v := by
  rw [← hσ.pi_iota T S u, ← hσ.pi_iota T S v, ← piW_act hg hh hσ.inf, ← piW_act hg hh hσ.inf, omO_apply, omO_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← GlobalTheory.OrientedChar.valTau_symplO hσ.inf, ← GlobalTheory.OrientedChar.valTau_symplO hσ.inf, GlobalTheory.T.symplecticForm_unitaryPairAction]

theorem actR_add_infRat (hσ : Chart θ σ) (y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (v : RW T S) :
    actR S T (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) (infRat S T y + v) =
      infRat S T (b * y * a) + actR S T (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) v := by
  rw [← piW_ratW hσ.inf, ← piW_ratW hσ.inf, ← act_ratW hg hh, ← hσ.pi_iota T S v, ← map_add,
    ← piW_act hg hh hσ.inf, ← piW_act hg hh hσ.inf, actO_add, map_add]

end Act

theorem phase_identity {W : AE D} (hW : W + cA D W = 1) (U Y : WO S T)
    (hi : symplOH S T (W • (U + Y)) (U + Y) = symplOH S T (W • Y) Y) :
    symplOH S T (W • U) U + symplOH S T (U + Y) Y = symplO S T (cA D W • U) Y := by
  have h1 : symplOH S T Y Y = 0 := by rw [symplOH, symplO_self, mul_zero]
  have h2 : symplOH S T U Y = symplOH S T (W • U) Y + symplOH S T (cA D W • U) Y := by
    rw [← symplOH_add_left, ← add_smul, hW, one_smul]
  have h3 : symplOH S T (W • Y) U = -symplOH S T (cA D W • U) Y := by
    rw [symplOH_smul, symplOH_skew]
  rw [smul_add, symplOH_add_left, symplOH_add_right, symplOH_add_right] at hi
  rw [symplOH_add_left, ← symplOH_add_self]
  linear_combination hi + h1 + h2 - h3

theorem gam_periodic {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {s : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (H : IsHeis s w γ W) {A : Submodule R X}
    (hA : SelfDual γ A) (φ : X →ₗ[R] X) (hφ : ∀ x y, γ (φ x) (φ y) = γ x y) (r : R) {y c : X} (hy : φ y - y ∈ A)
    (hc : c ∈ A) (hc' : φ c ∈ A) : γ (r • (φ (y + c) - (y + c))) (y + c) = γ (r • (φ y - y)) y := by
  have e1 : φ (y + c) - (y + c) = (φ y - y) + (φ c - c) := by rw [map_add]; abel
  have e2 : γ (r • c) y = γ (r • φ c) y := by
    rw [← hφ, map_smul, ← sub_add_cancel (φ y) y, H.add_right, H.iso hA (A.smul_mem r hc') hy, one_mul]
  have e3 : γ (r • (φ c - c)) y = 1 := by
    rw [smul_sub, sub_eq_add_neg, H.add_left, H.neg_left, e2, mul_inv_cancel₀ (H.ne_zero _ _)]
  rw [H.add_right, H.iso hA (A.smul_mem r (e1 ▸ A.add_mem hy (A.sub_mem hc' hc))) hc, mul_one, e1, smul_add,
    H.add_left, e3, mul_one]

def finX (S T : HSp D) : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[𝓞 D.host.E] XF S T where
  toFun y := XF.mk (finRat S T y) (finRat_inf S T y)
  map_add' x y := XF.ext (map_add (finRat S T) x y)
  map_smul' r x := XF.ext (finRat_smul S T (r : D.host.E) x)

theorem gamQ_eq (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    gamQ ψ S T x y = gamF ψ S T (finX S T x) (finX S T y) := rfl

open Classical in

def gaussQ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E))
    (LT : Set (Fin T.rank → D.host.E)) (w : 𝓞 D.host.E) (a : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (b : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : ℂ :=
  if b * y * a - y ∈ latQ S T LS LT then gamQ ψ S T (GlobalTheory.FinWeil.sgO D w • (b * y * a - y)) y else 0

section Left

variable {g : GA D S} {h : GA D T} {a : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
  {b : Matrix (Fin T.rank) (Fin T.rank) D.host.E} (hg : Formalism.L2.Theta.mt S g = a.map (incA D))
  (hh : Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D))
include hg hh

theorem rhoF_finX (y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    rhoF S T (g⁻¹, h⁻¹) (finX S T y) = finX S T (b * y * a) := XF.ext (act_finRat hg hh y)

theorem chiLat_mul_exp (hψ : IsStdChar D ψ (-1)) (hσ : Chart θ σ) (LS : Set (Fin S.rank → D.host.E))
    (LT : Set (Fin T.rank → D.host.E)) {w : 𝓞 D.host.E} (hw : w + GlobalTheory.FinWeil.sgO D w = 1)
    (y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    chiLat ψ S T LS LT w (ratW T S (b * y * a - y)) = gaussQ ψ S T LS LT w a b y *
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (infRat S T (b * y * a)) (infRat S T y) : ℝ)) := by
  unfold chiLat gaussQ
  rw [← finRat_eq]
  by_cases hy : b * y * a - y ∈ latQ S T LS LT
  · rw [if_pos hy, if_pos (mem_latQ.1 hy)]
    have e : finRat S T (b * y * a - y) + finRat S T y = finRat S T (b * y * a) := by
      rw [← map_add, sub_add_cancel]
    have h1 := phase_identity (W := intA D w) (by rw [cA_intA, ← RingHom.map_add, hw, RingHom.map_one])
      (finRat S T (b * y * a - y)) (finRat S T y)
      (by rw [e, ← act_finRat hg hh, ← actO_smul, symplOH, symplOH, GlobalTheory.T.symplecticForm_unitaryPairAction])
    have h2 : gamQ ψ S T (GlobalTheory.FinWeil.sgO D w • (b * y * a - y)) y =
        ψ (symplO S T (cA D (intA D w) • finRat S T (b * y * a - y)) (finRat S T y)) := by
      rw [gamQ_eq, map_smul, cA_intA]
      rfl
    rw [h2, ← h1, e, AddChar.map_add_eq_mul, mul_assoc, beta_fin hψ hσ, mul_one]
  · rw [if_neg hy, if_neg (fun h => hy (mem_latQ.2 h)), zero_mul]

theorem left_side (hψ : IsStdChar D ψ (-1)) (hσ : Chart θ σ) (halt : ∀ x y, omO S T x y = -omO S T y x)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) {w : 𝓞 D.host.E}
    (hw : w + GlobalTheory.FinWeil.sgO D w = 1)
    (hb : Function.Bijective fun x : Matrix (Fin T.rank) (Fin S.rank) D.host.E => b * x * a - x) (v : RW T S) :
    serO ψ θ σ S T sS sT LS LT w (-v) (actO S T g⁻¹ h⁻¹ (iotaW σ T S v)) =
      ∑' y, gaussQ ψ S T LS LT w a b y *
        gaussR S T sS sT (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) (infRat S T y + v) := by
  rw [act_iota hg hh hσ, serO_eq hσ.inf, ← (Equiv.ofBijective _ hb).tsum_eq]
  refine tsum_congr fun y => ?_
  have h0 := omO_act hg hh hσ (infRat S T y) v
  have h1 := actR_add_infRat hg hh hσ y 0
  have h2 : actR S T (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) 0 = 0 := by
    funext τ
    exact (congrArg (· * a.map (tauE D τ)) (Matrix.mul_zero _)).trans (Matrix.zero_mul _)
  rw [h2, add_zero, add_zero] at h1
  rw [h1] at h0
  rw [Equiv.ofBijective_apply, chiLat_add_iota hσ, chiLat_mul_exp hg hh hψ hσ LS LT hw, beta_iota_right hψ hσ,
    beta_iota_left hψ hσ, gaussR, actR_add_infRat hg hh hσ, map_add (piW θ T S), hσ.pi_iota, piW_ratW hσ.inf,
    map_sub (infRat S T)]
  generalize actR S T (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) v = u at h0 ⊢
  generalize infRat S T (b * y * a) = z at h0 ⊢
  generalize infRat S T y = x at h0 ⊢
  have e1 : z - x + (-v + u) = z + u - (x + v) := by abel
  have e2 : Complex.exp (-(Real.pi * Complex.I) * (omO S T (z - x) u : ℝ)) *
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (-v) (z - x + u) : ℝ)) *
      Complex.exp (-(Real.pi * Complex.I) * (omO S T z x : ℝ)) =
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (z + u) (x + v) : ℝ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← mul_add, ← mul_add, ← Complex.ofReal_add, ← Complex.ofReal_add]
    congr 3
    simp only [map_add, map_sub, map_neg, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply]
    linarith [halt x u, halt v z, halt v x, halt v u]
  rw [e1, ← e2]
  ring

end Left

def coefQ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Set (Fin S.rank → D.host.E))
    (LT : Set (Fin T.rank → D.host.E)) (w : 𝓞 D.host.E) (u : XF S T) (y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : ℂ :=
  phase ψ w u * (ψ (symplOH S T (ratW T S y) u) * chiLat ψ S T LS LT w (ratW T S y + u) *
    Complex.exp (-(Real.pi / 2 : ℂ) * (omO S T (infRat S T y) (jO S T sS sT (infRat S T y)) : ℝ)))

theorem right_side (hψ : IsStdChar D ψ (-1)) (hσ : Chart θ σ) (halt : ∀ x y, omO S T x y = -omO S T y x)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (w : 𝓞 D.host.E) (u : XF S T) (v : RW T S) :
    (phase ψ w u • heisO ψ S T u (serO ψ θ σ S T sS sT LS LT w (-v))) (iotaW σ T S v) =
      ∑' y, coefQ ψ S T sS sT LS LT w u y *
        Complex.exp (2 * Real.pi * Complex.I * ((-omO S T (infRat S T y)) v : ℝ)) := by
  have hu : piW θ T S (u : WO S T) = 0 := piW_of_inf θ u.fin
  rw [Pi.smul_apply, smul_eq_mul, heisO, beta_iota_left hψ hσ, hu, LinearMap.map_zero, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul, serO_eq hσ.inf, ← tsum_mul_left]
  refine tsum_congr fun y => ?_
  have e1 : ratW T S y + (iotaW σ T S v + (u : WO S T)) = (ratW T S y + (u : WO S T)) + iotaW σ T S v := by abel
  have e2 : omO S T v v = 0 := by linarith [halt v v]
  have e3 : Complex.exp (-(Real.pi * Complex.I) * (omO S T (infRat S T y) v : ℝ)) *
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (-v) (infRat S T y + v) : ℝ)) =
      Complex.exp (2 * Real.pi * Complex.I * ((-omO S T (infRat S T y)) v : ℝ)) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [map_add, map_neg, LinearMap.neg_apply, e2, halt v (infRat S T y)]
    push_cast
    ring
  rw [coefQ, symplOH_add_right, AddChar.map_add_eq_mul, beta_iota_right hψ hσ, beta_iota_left hψ hσ,
    map_add (piW θ T S), map_add (piW θ T S), hu, hσ.pi_iota, piW_ratW hσ.inf, add_zero, neg_add_cancel, add_zero, e1,
    chiLat_add_iota hσ, ← e3]
  ring

theorem finite_latQ {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) (R : ℝ) :
    {y | y ∈ latQ S T ΛS ΛT ∧ ‖infRat S T y‖ ≤ R}.Finite := by
  refine (GlobalTheory.CompletedLatticeFinite.finite_rational_points D S T ΛS ΛT dS dT R).subset ?_
  rintro y ⟨h1, h2⟩
  refine ⟨⟨_, h1, ?_⟩, fun τ i j => ?_⟩
  · funext i j
    have e1 : finPart D (finRat S T y i j) = finPart D (ratW T S y i j) := rfl
    show finPart D (ratW T S y i j - finRat S T y i j) = 0
    rw [RingHom.map_sub, e1, sub_self]
  · let z : RW T S := infRat S T y
    exact ((norm_le_pi_norm (z τ i) j).trans ((norm_le_pi_norm (z τ) i).trans (norm_le_pi_norm z τ))).trans h2

theorem summable_coefQ (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hpos : ∀ v, v ≠ 0 → 0 < omO S T v (jO S T sS sT v)) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT)
    (w : 𝓞 D.host.E) (u : XF S T) : Summable fun y => ‖coefQ ψ S T sS sT ΛS ΛT w u y‖ := by
  have h := GlobalTheory.HeisenbergGaussianSeries.summable_coeff (G := WO S T) (piW θ T S) (omO S T) (jO S T sS sT) (ratL T S)
    ((latO S T ΛS ΛT fun _ => True).comap (DistribSMul.toAddMonoidHom (WO S T) (1 - realIdem D)))
    (chiLat ψ S T ΛS ΛT w) hpos
    (by
      rintro _ ⟨y, rfl⟩ hy
      have : y = 0 := infRat_injective S T (((piW_ratW hθ S T y).symm.trans hy).trans (map_zero _).symm)
      rw [this, map_zero])
    (fun R => by
      refine ((finite_latQ dS dT R).image (ratW T S)).subset ?_
      rintro _ ⟨⟨y, rfl⟩, h1, h2⟩
      exact ⟨y, ⟨mem_latQ.2 (by rw [finRat_eq]; exact h1), by rw [← piW_ratW hθ]; exact h2⟩, rfl⟩)
    (fun x hx => if_neg hx)
    (fun x => by
      unfold chiLat
      split_ifs
      · exact (hψ.1.2.1 _).le
      · simp)
    (fun y => ψ (symplOH S T y u)) (fun y => hψ.1.2.1 _) u 0 0 0
  rw [← (ratEquiv hθ S T).summable_iff] at h
  refine h.congr fun y => ?_
  have e : ‖phase ψ w u‖ = 1 := hψ.1.2.1 _
  simp only [Function.comp_apply, coe_ratEquiv, piW_ratW hθ, add_zero, zero_mul, Real.exp_zero, mul_one]
  rw [coefQ, norm_mul (phase ψ w u), e, one_mul]

theorem mem_of_coefQ_ne_zero {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {LS : Set (Fin S.rank → D.host.E)}
    {LT : Set (Fin T.rank → D.host.E)} {w : 𝓞 D.host.E} {u : XF S T} {y : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (h : coefQ ψ S T sS sT LS LT w u y ≠ 0) : finX S T y + u ∈ latF S T LS LT := by
  by_contra hn
  apply h
  have e : chiLat ψ S T LS LT w (ratW T S y + u) = 0 := by
    unfold chiLat
    rw [smul_add, ← finRat_eq, fin_smul_XF]
    exact if_neg hn
  rw [coefQ, e, mul_zero, zero_mul, mul_zero]

theorem coefQ_zero (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {LS : Set (Fin S.rank → D.host.E)}
    {LT : Set (Fin T.rank → D.host.E)} (w : 𝓞 D.host.E) {u : XF S T} (hu : u ∈ latF S T LS LT) :
    coefQ ψ S T sS sT LS LT w u 0 = 1 := by
  have e : ratW T S 0 = 0 := Matrix.map_zero _ (incA D).map_zero
  rw [coefQ, e, zero_add, map_zero, symplOH, symplO_zero_left, mul_zero, AddChar.map_zero_eq_one, one_mul, map_zero,
    LinearMap.zero_apply, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, chiLat, fin_smul_XF,
    if_pos (mem_latF.1 hu), phase, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

theorem gauss_mul_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ w : 𝓞 D.host.E, w + GlobalTheory.FinWeil.sgO D w = 1 → ∀ (g : GA D S) (h : GA D T) (a : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (b : Matrix (Fin T.rank) (Fin T.rank) D.host.E), Formalism.L2.Theta.mt S g = a.map (incA D) → Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D) → Function.Bijective (fun x : Matrix (Fin T.rank) (Fin S.rank) D.host.E => b * x * a - x) → Integrable (gaussR S T sS sT (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ))) volume → ∀ κ : ℂ, (∀ f : thetaSub ψ S T, Fixes (opF hψ.1 S T w) (latF S T ΛS ΛT) f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ x, (f : WO S T → ℂ) (actO S T g⁻¹ h⁻¹ x) = κ * ((sumOp (opF hψ.1 S T w) (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T (g, h))) f : thetaSub ψ S T) : WO S T → ℂ) x) → ∀ (n : ℕ) (t : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E), (∀ k, b * t k * a - t k ∈ latQ S T ΛS ΛT) → (∀ y, b * y * a - y ∈ latQ S T ΛS ΛT → ∃! k, y - t k ∈ latQ S T ΛS ΛT) → ∃ r : ℝ, 0 < r ∧ (∑ k, gamQ ψ S T (GlobalTheory.FinWeil.sgO D w • (b * t k * a - t k)) (t k)) * ∫ v, gaussR S T sS sT (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) v = r * κ := by
  intro D ψ hψ θ hθ S T sS sT hS hT ΛS ΛT dS dT w hw g h a b hg hh hb hF κ hκ n t ht hu
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, halt, -, hneg⟩ := GlobalTheory.RealSymplForm.form_alt_inv_def D S T sS sT hS hT
  have hpos : ∀ v, v ≠ 0 → 0 < omO S T v (jO S T sS sT v) := fun v hv => by
    rw [halt]; exact neg_pos.2 (hneg v hv)
  have H := isHeis_opF hψ.1 S T hw
  obtain ⟨lam, hlam, -⟩ := exists_goodNorm D
  obtain ⟨w', Om, hL⟩ := exists_isLatRep hψ dS dT hlam
  have hA := hL.sd
  have hB := hL.sd' (g, h)
  obtain ⟨m, u, huB, huT⟩ := exists_transversal_of_idx_ne_zero _ _ (hL.fin (g, h))
  let C : AddSubgroup (Matrix (Fin T.rank) (Fin S.rank) D.host.E) :=
    (latQ S T ΛS ΛT).toAddSubgroup ⊓ (latQ S T ΛS ΛT).toAddSubgroup.comap (sandw b a).toAddMonoidHom
  have hC : ∀ x, x ∈ C ↔ x ∈ latQ S T ΛS ΛT ∧ b * x * a ∈ latQ S T ΛS ΛT := fun x => Iff.rfl
  have hX : ∀ x, x ∈ latQ S T ΛS ΛT ↔ finX S T x ∈ latF S T ΛS ΛT := fun x => Iff.rfl
  have hQ : ∀ y, b * y * a - y ∈ latQ S T ΛS ΛT →
      gaussQ ψ S T ΛS ΛT w a b y = gamQ ψ S T (GlobalTheory.FinWeil.sgO D w • (b * y * a - y)) y := fun y hy => if_pos hy
  have hQ0 : ∀ y, b * y * a - y ∉ latQ S T ΛS ΛT → gaussQ ψ S T ΛS ΛT w a b y = 0 := fun y hy => if_neg hy
  have h0 : κ * ∑ i, coefQ ψ S T sS sT ΛS ΛT w (u i) 0 = κ := by
    obtain ⟨i, hi, hi'⟩ := huT 0 (zero_mem _)
    rw [Finset.sum_eq_single i, coefQ_zero sS sT w (by simpa using hi), mul_one]
    · intro j _ hj
      by_contra hn
      exact hj (hi' j (by simpa using mem_of_coefQ_ne_zero hn))
    · exact fun hn => (hn (Finset.mem_univ _)).elim
  haveI : (volume : Measure (Fin S.rank → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin T.rank → Fin S.rank → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (RW T S)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have key := GlobalTheory.T.unfold_poincareSeries_lattice_fourier (RW T S) volume _ (infRat S T) (infRat_injective S T) C
    (fun R => (finite_latQ dS dT R).subset fun c hc => ⟨hc.1.1, hc.2⟩) ?_ n t (gaussQ ψ S T ΛS ΛT w a b) ?_ ?_ ?_ _ hF
    (fun y => κ * ∑ i, coefQ ψ S T sS sT ΛS ΛT w (u i) y) (fun y => -omO S T (infRat S T y)) ?_ ?_ ?_ ?_ ?_
  · obtain ⟨r, hr, e⟩ := key
    refine ⟨r, hr, ?_⟩
    rw [h0, Finset.sum_congr rfl fun k _ => hQ _ (ht k)] at e
    exact e
  · rw [eq_top_iff]
    have hsp : Submodule.span ℝ (Set.range (infRat S T)) = ⊤ := by
      simpa only [piW_ratW hθ] using span_piW_ratW_eq_top D θ σ hσ T S
    rw [← hsp, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨N, hN, h1⟩ := GlobalTheory.VacUnique.Den.exists_nsmul_finRat_mem D S T ΛS ΛT dS.1 dT.1 y
    obtain ⟨M, hM, h2⟩ := GlobalTheory.VacUnique.Den.exists_nsmul_finRat_mem D S T ΛS ΛT dS.1 dT.1 (b * y * a)
    have h3 : (M * N) • y ∈ C := by
      refine ⟨?_, ?_⟩
      · show finRat S T ((M * N) • y) ∈ latO S T ΛS ΛT fun _ => True
        rw [map_nsmul, mul_smul]
        exact nsmul_mem h1 M
      · show finRat S T (sandw b a ((M * N) • y)) ∈ latO S T ΛS ΛT fun _ => True
        rw [map_nsmul, map_nsmul, mul_comm, mul_smul]
        exact nsmul_mem h2 N
    have h4 : infRat S T y = ((M * N : ℕ) : ℝ)⁻¹ • infRat S T ((M * N) • y) := by
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ (Nat.cast_ne_zero.2 (Nat.mul_pos hM hN).ne')]
    rw [h4]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h3, rfl⟩)
  · intro y hy
    have h1 : b * y * a - y ∈ latQ S T ΛS ΛT := by_contra fun hn => hy (hQ0 y hn)
    obtain ⟨k, hk, -⟩ := hu y h1
    refine ⟨k, hk, ?_⟩
    have e : b * (y - t k) * a = (b * y * a - y) - (b * t k * a - t k) + (y - t k) := by
      rw [Matrix.mul_sub, Matrix.sub_mul]; abel
    show b * (y - t k) * a ∈ latQ S T ΛS ΛT
    rw [e]
    exact add_mem (sub_mem h1 (ht k)) hk
  · intro k k' hk
    exact ((hu (t k) (ht k)).unique (by rw [sub_self]; exact zero_mem _) hk.1)
  · intro y c hc
    have e : b * (y + c) * a - (y + c) = (b * y * a - y) + (b * c * a - c) := by
      rw [Matrix.mul_add, Matrix.add_mul]; abel
    have hc' : b * c * a - c ∈ latQ S T ΛS ΛT := sub_mem ((hC c).1 hc).2 hc.1
    by_cases hy : b * y * a - y ∈ latQ S T ΛS ΛT
    · rw [hQ _ hy, hQ _ (e ▸ add_mem hy hc'), gamQ_eq, gamQ_eq, map_smul, map_smul, map_sub, map_sub,
        ← rhoF_finX hg hh, ← rhoF_finX hg hh, map_add (finX S T)]
      refine gam_periodic H hA _ (gamF_rhoF _) _ ?_ ((hX c).1 hc.1) ?_
      · rw [rhoF_finX hg hh, ← map_sub]; exact hy
      · rw [rhoF_finX hg hh]; exact hc.2
    · rw [hQ0 _ hy, hQ0]
      intro hn
      rw [e] at hn
      exact hy ((add_mem_cancel_right hc').1 hn)
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun y => ?_)
      ((summable_sum fun i (_ : i ∈ Finset.univ) => summable_coefQ hψ hθ hpos dS dT w (u i)).mul_left ‖κ‖)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
  · simp
  · intro y hy hn
    have h1 : infRat S T y ≠ 0 := fun h => hy (infRat_injective S T (h.trans (map_zero _).symm))
    have h2 := hpos _ h1
    rw [neg_eq_zero.1 hn] at h2
    exact lt_irrefl _ h2
  · intro y hy c hc
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hy)
    have h1 : finX S T c ∈ (latF S T ΛS ΛT).map (rhoF S T (g, h)) := by
      refine ⟨finX S T (b * c * a), hc.2, ?_⟩
      rw [← rhoF_finX hg hh, ← Module.End.mul_apply, ← map_mul,
        show ((g, h) : GA D S × GA D T) * (g⁻¹, h⁻¹) = 1 from mul_inv_cancel (g, h), map_one, Module.End.one_apply]
    have h2 := H.iso hA (mem_of_coefQ_ne_zero hi) ((hX c).1 hc.1)
    rw [H.add_left, H.iso hB (huB i) h1, mul_one] at h2
    obtain ⟨z, hz⟩ := (GlobalTheory.RatSelfDual.psi_fin_iff hψ S T y c).1 h2
    exact ⟨-z, by rw [LinearMap.neg_apply, hz, Int.cast_neg]⟩
  · intro v
    obtain ⟨hf, hfix, hvac⟩ := GlobalTheory.T.gaussian_poincare_series_theta_vacuum D ψ hψ θ σ hσ S T sS sT hS hT ΛS ΛT dS dT w hw (-v)
    have e := hκ ⟨_, hf⟩ hfix hvac (iotaW σ T S v)
    rw [(sumOp_eq_sum_transversal H _ _ hB _ hfix _ u huB huT).1, Submodule.coe_sum, Finset.sum_apply] at e
    simp only [coe_opF, right_side hψ hσ halt, left_side hg hh hψ hσ halt sS sT _ _ hw hb] at e
    rw [e, ← Summable.tsum_finsetSum, ← tsum_mul_left]
    · refine tsum_congr fun y => ?_
      beta_reduce
      rw [← Finset.sum_mul, mul_assoc κ]
    · intro i _
      refine Summable.of_norm ((summable_coefQ hψ hθ hpos dS dT w (u i)).congr fun y => ?_)
      have e1 : (2 * Real.pi * Complex.I * ((-omO S T (infRat S T y)) v : ℝ) : ℂ) =
          ((2 * Real.pi * (-omO S T (infRat S T y)) v : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [norm_mul, e1, Complex.norm_exp_ofReal_mul_I, mul_one]

end GlobalTheory.RatTrace

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalIsometry_vacuumScalar_gaussSum_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ w : 𝓞 D.host.E, w + GlobalTheory.FinWeil.sgO D w = 1 → ∀ (g : GA D S) (h : GA D T) (a : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (b : Matrix (Fin T.rank) (Fin T.rank) D.host.E), Formalism.L2.Theta.mt S g = a.map (incA D) → Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D) → Function.Bijective (fun x : Matrix (Fin T.rank) (Fin S.rank) D.host.E => b * x * a - x) → Integrable (gaussR S T sS sT (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ))) volume → ∀ κ : ℂ, (∀ f : thetaSub ψ S T, Fixes (opF hψ.1 S T w) (latF S T ΛS ΛT) f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ x, (f : WO S T → ℂ) (actO S T g⁻¹ h⁻¹ x) = κ * ((sumOp (opF hψ.1 S T w) (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T (g, h))) f : thetaSub ψ S T) : WO S T → ℂ) x) → ∀ (n : ℕ) (t : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E), (∀ k, b * t k * a - t k ∈ latQ S T ΛS ΛT) → (∀ y, b * y * a - y ∈ latQ S T ΛS ΛT → ∃! k, y - t k ∈ latQ S T ΛS ΛT) → ∃ r : ℝ, 0 < r ∧ (∑ k, gamQ ψ S T (GlobalTheory.FinWeil.sgO D w • (b * t k * a - t k)) (t k)) * ∫ v, gaussR S T sS sT (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) v = r * κ := by
  atlas_forward_decl GlobalTheory.RatTrace.gauss_mul_integral
end
