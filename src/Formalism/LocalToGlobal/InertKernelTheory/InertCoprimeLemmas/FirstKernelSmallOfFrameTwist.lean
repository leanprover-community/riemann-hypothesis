import Formalism.LocalToGlobal.InertKernelTheory.TranslatesOfInertKernelAtPlace
import Formalism.LocalToGlobal.InertKernelTheory.ScalG
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepAsm
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepScal
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepDataRec
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AlgKleinPf
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepFrame
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepTrace
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepFrob
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMRead
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FormalExponentialAgree
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ExistsWittSeriesInverseFormalGroupIso
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.JetsModel
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.JetsOrth
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GlobalOrthonormalBasisFour
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces
import Formalism.LocalToGlobal.InertKernelTheory.KernelsIntegralInert
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepLt

section
noncomputable section

namespace Formalism.L2.KerInert

namespace AlgTP

open NumberField Formalism.BasicNotions Formalism.L2.Ker

theorem exists_inert_prime (d : ℕ) (hd : d.Prime) (hd4 : d % 4 = 3) (n : ℕ) :
    ∃ p, n < p ∧ p.Prime ∧ jacobiSym (-(d : ℤ)) p = -1 := by
  have : NeZero (4 * d) := ⟨by have := hd.pos; omega⟩
  have hu : IsUnit (-1 : ZMod (4 * d)) := isUnit_one.neg
  obtain ⟨p, hpn, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu n
  refine ⟨p, hpn, hp, ?_⟩
  have hmod : (p : ℤ) ≡ -1 [ZMOD ((4 * d : ℕ) : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    exact hpa
  have hm4 : (p : ℤ) ≡ -1 [ZMOD 4] := by
    have h : (p : ℤ) ≡ -1 [ZMOD 4 * (d : ℤ)] := by simpa using hmod
    exact Int.ModEq.of_mul_right _ h
  have hmd : (p : ℤ) ≡ -1 [ZMOD (d : ℤ)] := by
    have h : (p : ℤ) ≡ -1 [ZMOD 4 * (d : ℤ)] := by simpa using hmod
    exact Int.ModEq.of_mul_left _ h
  have hp4 : p % 4 = 3 := by
    unfold Int.ModEq at hm4
    omega
  have hodd : Odd p := Nat.odd_iff.2 (by omega)
  have hdodd : Odd d := Nat.odd_iff.2 (by omega)
  rw [jacobiSym.neg _ hodd, ZMod.χ₄_nat_three_mod_four hp4,
    jacobiSym.quadratic_reciprocity_three_mod_four hd4 hp4, jacobiSym.mod_left' hmd,
    jacobiSym.at_neg_one hdodd, ZMod.χ₄_nat_three_mod_four hd4]
  norm_num

theorem mem_one_iff {E : Type} [Field E] [NumberField E] (w : E) :
    w ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ w := by
  rw [Submodule.mem_one]
  exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).symm

theorem mem_range_iff {E : Type} [Field E] [NumberField E] (w : E) :
    w ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ w := by
  rw [RingHom.mem_range]
  exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).symm

theorem exists_den (D : D7) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L) :
    ∃ s : ℕ, 0 < s ∧ (∀ x ∈ L, (s : D.host.E) • x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N) ∧
      ∀ x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N, (s : D.host.E) • x ∈ L := by
  let _ := D.host.cmStar
  classical
  obtain ⟨S, hS⟩ := hL.1
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (S.biUnion fun v => Finset.univ.image v)
  have hint : ∀ w ∈ S.biUnion (fun v => Finset.univ.image v), IsIntegral ℤ ((y.natAbs : D.host.E) * w) := by
    intro w hw
    have h := hy w hw
    rw [zsmul_eq_mul] at h
    rcases Int.natAbs_eq y with e | e
    · have : ((y.natAbs : ℤ) : D.host.E) = (y : D.host.E) := by rw [← e]
      rw [← this] at h
      simpa using h
    · have : ((y.natAbs : ℤ) : D.host.E) = -(y : D.host.E) := by
        rw [show ((y.natAbs : ℤ)) = -y by omega]; push_cast; ring
      have h' := h.neg
      rw [show -((y : D.host.E) * w) = ((y.natAbs : ℤ) : D.host.E) * w by rw [this]; ring] at h'
      simpa using h'
  have hfirst : ∀ x ∈ L, ((y.natAbs : ℕ) : D.host.E) • x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
    have hgen : ∀ v ∈ (S : Set (Fin N → D.host.E)), ((y.natAbs : ℕ) : D.host.E) • v ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
      intro v hv
      rw [Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi]
      intro i _
      rw [mem_one_iff, Pi.smul_apply, smul_eq_mul]
      exact hint (v i) (Finset.mem_biUnion.2 ⟨v, hv, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
    intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem v hv => exact hgen v hv
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ r ha
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, hfirst, ?_⟩
  intro x hx
  refine (hL.2.2 _).2 ?_
  intro z hz
  have hz' := hfirst z hz
  rw [Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi] at hx hz'
  have e : stdH D.host.E N z (((y.natAbs : ℕ) : D.host.E) • x) =
      stdH D.host.E N (((y.natAbs : ℕ) : D.host.E) • z) x := by
    unfold stdH
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, star_mul', star_natCast]
    ring
  rw [e, mem_range_iff]
  unfold stdH
  refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ ?_
  · have h := (mem_one_iff _).1 (hz' i (Set.mem_univ i))
    have h2 := h.map (starRingEnd D.host.E).toIntAlgHom
    convert h2 using 1 <;> rfl
  · exact (mem_one_iff _).1 (hx i (Set.mem_univ i))

theorem algebraic_translates_all_data : AlgTAll := by
  intro D cc δ B χ hcc hδ hχ N N' L L' hA t ⟨a, ha, hat⟩ α
  obtain ⟨s, hs, hsL1, hsL2⟩ := exists_den D L hA.2.2.1
  obtain ⟨s', hs', hsL1', hsL2'⟩ := exists_den D L' hA.2.2.2
  have hd := D.host.hyp
  obtain ⟨p, hpn, hp, hJ⟩ :=
    exists_inert_prime D.host.d hd.2.1 (by have := hd.2.2.2.1; omega) (a * s * s' + 4)
  have : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < a * s * s' := by positivity
  have hcop : ∀ m : ℕ, m ∣ a * s * s' → Nat.Coprime m p := fun m hm =>
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h =>
      absurd (Nat.le_of_dvd hpos (h.trans hm)) (by omega))
  have H := (AlgP.algebraic_fact_kernels D cc δ B hcc hδ χ hχ p (by omega) hJ N N').1 L L' hA
    ⟨s, hcop s (Dvd.intro_left _ rfl |>.mul_right _), hsL2, hsL1⟩
    ⟨s', hcop s' (Dvd.intro_left _ rfl), hsL2', hsL1'⟩ t
    ⟨a, ha, hcop a ((Dvd.intro _ rfl).mul_right _), hat⟩
  exact H.2 α

theorem algT_of {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) {χ : Formalism.MainNotions.TaylorLogMetric.IdE D → ℂ}
    (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : Formalism.MainNotions.TaylorLogMetric.IsChi D χ) : B.AlgT χ :=
  algebraic_translates_all_data D cc δ B χ hcc hδ hχ

end AlgTP

end Formalism.L2.KerInert
end
end

section
noncomputable section

namespace Formalism.L2.KerInert.WeierstrassScaling

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.KerInert.ParameterChangeLemmas Formalism.L2.KerInert.IntegralOrthonormalChange

variable {p : ℕ} [Fact p.Prime]

def scC (ν : ℂ_[p]) (hν : ν ≠ 0) : WeierstrassCurve.VariableChange ℂ_[p] := ⟨Units.mk0 ν hν, 0, 0, 0⟩

section Scale

variable (ν : ℂ_[p]) (hν : ν ≠ 0)

theorem scC_uinv : (((scC ν hν).u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = ν⁻¹ := by simp [scC]

theorem scale_weierstrass_a1 (W : WeierstrassCurve ℂ_[p]) : (scC ν hν • W).a₁ = ν⁻¹ * W.a₁ := by
  rw [WeierstrassCurve.variableChange_a₁, scC_uinv]; simp [scC]

theorem scale_weierstrass_a2 (W : WeierstrassCurve ℂ_[p]) : (scC ν hν • W).a₂ = ν⁻¹ ^ 2 * W.a₂ := by
  rw [WeierstrassCurve.variableChange_a₂, scC_uinv]; simp [scC]

theorem scale_weierstrass_a3 (W : WeierstrassCurve ℂ_[p]) : (scC ν hν • W).a₃ = ν⁻¹ ^ 3 * W.a₃ := by
  rw [WeierstrassCurve.variableChange_a₃, scC_uinv]; simp [scC]

theorem scale_weierstrass_a4 (W : WeierstrassCurve ℂ_[p]) : (scC ν hν • W).a₄ = ν⁻¹ ^ 4 * W.a₄ := by
  rw [WeierstrassCurve.variableChange_a₄, scC_uinv]; simp [scC]

theorem scale_weierstrass_a6 (W : WeierstrassCurve ℂ_[p]) : (scC ν hν • W).a₆ = ν⁻¹ ^ 6 * W.a₆ := by
  rw [WeierstrassCurve.variableChange_a₆, scC_uinv]; simp [scC]

theorem rescale_C' (c a : ℂ_[p]) : PowerSeries.rescale c (PowerSeries.C a) = PowerSeries.C a := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with hn
  · rw [hn, pow_zero, one_mul]
  · rw [mul_zero]

theorem rescale_alg (c a : ℂ_[p]) :
    PowerSeries.rescale c (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a) = algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a := by
  rw [PowerSeries.algebraMap_eq]; exact rescale_C' c a

theorem cc_rescale (c : ℂ_[p]) (f : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (PowerSeries.rescale c f) = PowerSeries.constantCoeff f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem rescale_inv (c : ℂ_[p]) (f : PowerSeries ℂ_[p]) :
    PowerSeries.rescale c f⁻¹ = (PowerSeries.rescale c f)⁻¹ := by
  by_cases hf : PowerSeries.constantCoeff f = 0
  · rw [PowerSeries.inv_eq_zero.mpr hf, map_zero, PowerSeries.inv_eq_zero.mpr ((cc_rescale c f).trans hf)]
  · rw [PowerSeries.eq_inv_iff_mul_eq_one (by rw [cc_rescale]; exact hf), ← map_mul,
      PowerSeries.inv_mul_cancel _ hf, map_one]

theorem X_dX_rescale (c : ℂ_[p]) (f : PowerSeries ℂ_[p]) :
    PowerSeries.X * dX (PowerSeries.rescale c f) = PowerSeries.rescale c (PowerSeries.X * dX f) := by
  ext n
  rw [PowerSeries.coeff_rescale]
  cases n with
  | zero => simp [PowerSeries.coeff_zero_X_mul]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
    simp only [dX, PowerSeries.coeff_mk, PowerSeries.coeff_rescale]
    ring

theorem isWq_scale (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) (h : IsWq W wq) :
    IsWq (scC ν hν • W) (PowerSeries.rescale ν⁻¹ wq) := by
  unfold IsWq at h ⊢
  dsimp only at h ⊢
  conv_lhs => rw [h]
  rw [scale_weierstrass_a1, scale_weierstrass_a2, scale_weierstrass_a3, scale_weierstrass_a4, scale_weierstrass_a6]
  simp only [map_add, map_mul, map_pow, map_one, PowerSeries.rescale_X, PowerSeries.algebraMap_eq, rescale_C']
  ring

theorem omegaW_scale (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    omegaW (scC ν hν • W) (PowerSeries.rescale ν⁻¹ wq) = PowerSeries.rescale ν⁻¹ (omegaW W wq) := by
  unfold omegaW
  dsimp only
  rw [scale_weierstrass_a1, scale_weierstrass_a3]
  have hnum : (-(2 : PowerSeries ℂ_[p]) * PowerSeries.rescale ν⁻¹ wq - PowerSeries.X * dX (PowerSeries.rescale ν⁻¹ wq)) =
      PowerSeries.rescale ν⁻¹ (-(2 : PowerSeries ℂ_[p]) * wq - PowerSeries.X * dX wq) := by
    rw [X_dX_rescale, map_sub]
    congr 1
    simp only [map_mul, map_neg, map_ofNat]
  have hden : PowerSeries.rescale ν⁻¹ wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) (ν⁻¹ * W.a₁) * PowerSeries.X +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) (ν⁻¹ ^ 3 * W.a₃) * PowerSeries.X ^ 3 * PowerSeries.rescale ν⁻¹ wq - 2) =
      PowerSeries.rescale ν⁻¹ (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
        algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2)) := by
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, PowerSeries.rescale_X,
      PowerSeries.algebraMap_eq, rescale_C']
    ring
  rw [hnum, hden, ← rescale_inv, ← map_mul]

theorem flog_scale (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    flog (scC ν hν • W) (PowerSeries.rescale ν⁻¹ wq) = PowerSeries.C ν * PowerSeries.rescale ν⁻¹ (flog W wq) := by
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale]
  unfold flog
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, omegaW_scale]
  rcases n with _ | n
  · simp
  · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, PowerSeries.coeff_rescale]
    have h1 : ν * ν⁻¹ = 1 := mul_inv_cancel₀ hν
    rw [pow_succ]
    linear_combination (-(ν⁻¹ ^ n * PowerSeries.coeff n (omegaW W wq) / ((n + 1 : ℕ) : ℂ_[p]))) * h1

end Scale

section Subst

theorem hasSubst_cX (c : ℂ_[p]) : PowerSeries.HasSubst (c • (PowerSeries.X : PowerSeries ℂ_[p])) :=
  (PowerSeries.HasSubst.X' (R := ℂ_[p])).smul' c

theorem subst_rescale_arg (c : ℂ_[p]) (A f : PowerSeries ℂ_[p]) (hA : PowerSeries.constantCoeff A = 0) :
    PowerSeries.subst (PowerSeries.rescale c A) f = PowerSeries.rescale c (PowerSeries.subst A f) := by
  rw [PowerSeries.rescale_eq_subst, PowerSeries.rescale_eq_subst,
    PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hA) (hasSubst_cX c)]

theorem subst_Cmul_rescale (a : ℂ_[p]) (ha : a ≠ 0) (h f : PowerSeries ℂ_[p])
    (h0 : PowerSeries.constantCoeff h = 0) :
    PowerSeries.subst (PowerSeries.C a * h) (PowerSeries.rescale a⁻¹ f) = PowerSeries.subst h f := by
  have h1 : PowerSeries.constantCoeff (PowerSeries.C a * h) = 0 := by rw [map_mul, h0, mul_zero]
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' h1
  rw [PowerSeries.rescale_eq_subst, PowerSeries.subst_comp_subst_apply (hasSubst_cX a⁻¹) hs]
  congr 1
  rw [PowerSeries.subst_smul hs, PowerSeries.subst_X hs, PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ ha, map_one, one_mul]

end Subst

theorem scC_mul_uinv (ν : ℂ_[p]) (hν : ν ≠ 0) (C : WeierstrassCurve.VariableChange ℂ_[p]) :
    (((scC ν hν * C).u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = ν⁻¹ * ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) := by
  rw [WeierstrassCurve.VariableChange.mul_def]
  simp [scC, mul_comm]

theorem ePhi1_scale (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ) (C : WeierstrassCurve.VariableChange ℂ_[p])
    (wq : PowerSeries ℂ_[p]) (ν : ℂ_[p]) (hν : ν ≠ 0) :
    ePhi1 lam Λ (scC ν hν * C) (PowerSeries.rescale ν⁻¹ wq) = PowerSeries.rescale ν⁻¹ (ePhi1 lam Λ C wq) := by
  have hW : (scC ν hν * C) • wModel lam Λ = scC ν hν • (C • wModel lam Λ) := mul_smul _ _ _
  set ep : ℂ_[p] := ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hep
  have hep0 : ep ≠ 0 := Units.ne_zero _
  set fl := flog (C • wModel lam Λ) wq with hfl
  have hA0 : PowerSeries.constantCoeff (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) ep * fl) = 0 := by
    rw [map_mul, hfl, flog_constantCoeff, mul_zero]
  have harg : algebraMap ℂ_[p] (PowerSeries ℂ_[p]) (ν⁻¹ * ep) * flog (scC ν hν • (C • wModel lam Λ))
      (PowerSeries.rescale ν⁻¹ wq) = PowerSeries.rescale ν⁻¹ (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) ep * fl) := by
    rw [flog_scale ν hν, map_mul (PowerSeries.rescale ν⁻¹) _ _, rescale_alg, PowerSeries.algebraMap_eq, ← hfl,
      ← mul_assoc, ← map_mul, show ν⁻¹ * ep * ν = ep by field_simp]
  ext n
  unfold ePhi1
  dsimp only
  rw [hW, scC_mul_uinv, ← hep, harg, subst_rescale_arg _ _ _ hA0, PowerSeries.coeff_mk, PowerSeries.coeff_rescale,
    PowerSeries.coeff_rescale, PowerSeries.coeff_mk, mul_inv, inv_inv]
  have h1 : ν * ν⁻¹ = 1 := mul_inv_cancel₀ hν
  rw [pow_succ]
  linear_combination (ν⁻¹ ^ n * ep⁻¹ * PowerSeries.coeff (n + 1)
    (PowerSeries.subst (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) ep * fl) (sgSer lam Λ))) * h1

theorem isModel_scale (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ) (C : WeierstrassCurve.VariableChange ℂ_[p])
    (hU : Formalism.MainNotions.GL3Theta.IsModelU lam Λ C) (ν : ℂ_[p]) (hν : ν ≠ 0) (hν1 : ‖ν‖ = 1)
    (hν12 : ν ^ 12 = (C • wModel lam Λ).Δ) : IsModel lam Λ (scC ν hν * C) := by
  obtain ⟨h1, h2, h3, h4, h6, -⟩ := hU
  have hW : (scC ν hν * C) • wModel lam Λ = scC ν hν • (C • wModel lam Λ) := mul_smul _ _ _
  have hn : ‖ν⁻¹‖ = 1 := by rw [norm_inv, hν1, inv_one]
  show IsIntP ((scC ν hν * C) • wModel lam Λ).a₁ ∧ IsIntP ((scC ν hν * C) • wModel lam Λ).a₂ ∧
    IsIntP ((scC ν hν * C) • wModel lam Λ).a₃ ∧ IsIntP ((scC ν hν * C) • wModel lam Λ).a₄ ∧
    IsIntP ((scC ν hν * C) • wModel lam Λ).a₆ ∧ ((scC ν hν * C) • wModel lam Λ).Δ = 1
  rw [hW]
  unfold IsIntP at h1 h2 h3 h4 h6 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [scale_weierstrass_a1, norm_mul, hn, one_mul]; exact h1
  · rw [scale_weierstrass_a2, norm_mul, norm_pow, hn, one_pow, one_mul]; exact h2
  · rw [scale_weierstrass_a3, norm_mul, norm_pow, hn, one_pow, one_mul]; exact h3
  · rw [scale_weierstrass_a4, norm_mul, norm_pow, hn, one_pow, one_mul]; exact h4
  · rw [scale_weierstrass_a6, norm_mul, norm_pow, hn, one_pow, one_mul]; exact h6
  · rw [WeierstrassCurve.variableChange_Δ, scC_uinv, ← hν12, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hν)]

theorem dict_core (hp2 : p ≠ 2) (D : D7) {N N' r : ℕ} (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p])
    (h : PowerSeries ℂ_[p]) (h0 : PowerSeries.constantCoeff h = 0) (hI : ∀ n, IsIntP (PowerSeries.coeff n h))
    (κ : ℂ_[p])
    (hlog : PowerSeries.subst h (flog (C • wModel lam Λ) wq) =
      PowerSeries.C κ * PowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (Formalism.MainNotions.FormalGroupSystem.logF p))
    (ph V : PowerSeries ℂ_[p]) (hph0 : PowerSeries.constantCoeff ph = 0) (hV : ∀ n, IsIntP (PowerSeries.coeff n V))
    (hexp : (Formalism.L2.Th1.C.mvExp ph : PowerSeries ℂ_[p]) = V * (PowerSeries.subst h (ePhi1 lam Λ C wq))⁻¹)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p])
    (hInt : IntegralMv (atLog D lam Λ C wq b G * ePh lam Λ C wq r)) :
    Formalism.DworkPowerSeriesWeights.Integral (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries (Fin r) ℂ_[p]) *
      @Formalism.MainNotions.FormalGroupSystem.inParamK p _ (Fin r) ℂ_[p] _ (Formalism.L2.G.Pend.wittFractionAlgebraCp p)
        (Formalism.L2.KerInert.Rep.thOrth D lam (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * κ) b G)) := by
  set S : Fin r → MvPowerSeries (Fin r) ℂ_[p] :=
    fun i => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) h with hS
  have hS0 : ∀ i, MvPowerSeries.constantCoeff (S i) = 0 := fun i => constantCoeff_inVar_eq_zero i h h0
  have hSs : MvPowerSeries.HasSubst S := MvPowerSeries.hasSubst_of_constantCoeff_zero hS0
  have hSI : ∀ i, IntegralMv (S i) := fun i => integral_subst_single_variable i h hI
  have hh : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hl0 := flog_constantCoeff (C • wModel lam Λ) wq
  set L : PowerSeries ℂ_[p] := PowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (Formalism.MainNotions.FormalGroupSystem.logF p) with hL
  have hL0 : PowerSeries.constantCoeff L = 0 := by
    rw [hL, Formalism.L2.KerInert.BeCob.lgF_eq_logF]; exact Formalism.L2.KerInert.BeCob.cc_lgF' _ _
  have hCalg : ∀ x : ℂ_[p], (MvPowerSeries.C x : MvPowerSeries (Fin r) ℂ_[p]) =
      algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) x := fun x => by rw [MvPowerSeries.algebraMap_apply]; rfl

  have hA : MvPowerSeries.subst S (atLog D lam Λ C wq b G) =
      @Formalism.MainNotions.FormalGroupSystem.inParamK p _ (Fin r) ℂ_[p] _ (Formalism.L2.G.Pend.wittFractionAlgebraCp p)
        (Formalism.L2.KerInert.Rep.thOrth D lam (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * κ) b G) := by
    have hXfl : ∀ i : Fin r, MvPowerSeries.constantCoeff (PowerSeries.subst
        (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) = 0 :=
      fun i => constantCoeff_inVar_eq_zero i _ hl0
    have hΦ : MvPowerSeries.HasSubst (fun k : D.what₂.Tau × Fin N' × Fin N =>
        ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p])
          (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
          PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro k
      simp [map_sum, hXfl]
    have hT : MvPowerSeries.HasSubst (fun k : D.what₂.Tau × Fin N' × Fin N =>
        ∑ i, MvPowerSeries.C ((((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * κ) * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
          (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p])) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro k
      simp [map_sum]
    have hP : MvPowerSeries.HasSubst (fun i : Fin r => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) L) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => constantCoeff_inVar_eq_zero i L hL0)
    unfold atLog Formalism.L2.KerInert.Rep.thOrth Formalism.MainNotions.FormalGroupSystem.inParamK
    dsimp only
    rw [MvPowerSeries.subst_comp_subst_apply hΦ hSs]
    erw [MvPowerSeries.subst_comp_subst_apply hT hP]
    congr 1
    funext k
    rw [← MvPowerSeries.coe_substAlgHom hSs, map_sum]
    erw [← MvPowerSeries.coe_substAlgHom hP, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hCalg]
    simp only [map_mul, AlgHom.commutes, MvPowerSeries.coe_substAlgHom, subst_single_var S hSs, MvPowerSeries.subst_X hP]
    rw [hS]
    dsimp only
    rw [← PowerSeries.subst_comp_subst_apply hh (PowerSeries.HasSubst.X i), hlog,
      PowerSeries.subst_mul (PowerSeries.HasSubst.X i), PowerSeries.subst_C]
    have hid : ∀ x : ℂ_[p], algebraMap ℂ_[p] ℂ_[p] x = x := fun _ => rfl
    simp only [MvPowerSeries.algebraMap_apply, hid]
    rw [hL]
    ring

  have hB : MvPowerSeries.subst S (ePh lam Λ C wq r) =
      ∏ i, PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p])
        (PowerSeries.subst h (ePhi1 lam Λ C wq))⁻¹ := by
    unfold ePh
    rw [if_neg hp2, ← MvPowerSeries.coe_substAlgHom hSs, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [MvPowerSeries.coe_substAlgHom, ← subst_inv _ (MvPowerSeries.constantCoeff_X i), subst_single_var S hSs, hS]
    dsimp only
    rw [← subst_inv h h0, PowerSeries.subst_comp_subst_apply hh (PowerSeries.HasSubst.X i)]

  have hE : Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries (Fin r) ℂ_[p]) =
      (∏ i, PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) V) *
        MvPowerSeries.subst S (ePh lam Λ C wq r) := by
    rw [hB, ← Finset.prod_mul_distrib]
    change Formalism.L2.Th1.C.mvExp (∑ i, Formalism.InvariantFactorPaths.G7.at1 i ph) = _
    simp only [Formalism.InvariantFactorPaths.G7.at1]
    rw [Formalism.L2.Th1.C.mvExp_sum _ _ (fun i _ => constantCoeff_inVar_eq_zero i ph hph0)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Formalism.L2.Th1.C.subst_mvExp hph0 (MvPowerSeries.constantCoeff_X i), hexp,
      PowerSeries.subst_mul (PowerSeries.HasSubst.X i)]

  have hSG := integral_subst S hS0 hSI hInt
  rw [← MvPowerSeries.coe_substAlgHom hSs, map_mul, MvPowerSeries.coe_substAlgHom, hA] at hSG
  have hU : IntegralMv (∏ i, PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) V) :=
    integral_prod _ _ fun i _ => integral_subst_single_variable i V hV
  have key := integral_mul hU hSG
  rw [hE]
  have e : (∏ i, PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) V) *
      MvPowerSeries.subst S (ePh lam Λ C wq r) *
      @Formalism.MainNotions.FormalGroupSystem.inParamK p _ (Fin r) ℂ_[p] _ (Formalism.L2.G.Pend.wittFractionAlgebraCp p)
        (Formalism.L2.KerInert.Rep.thOrth D lam (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * κ) b G) =
      (∏ i, PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) V) *
      (@Formalism.MainNotions.FormalGroupSystem.inParamK p _ (Fin r) ℂ_[p] _ (Formalism.L2.G.Pend.wittFractionAlgebraCp p)
        (Formalism.L2.KerInert.Rep.thOrth D lam (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * κ) b G) *
        MvPowerSeries.subst S (ePh lam Λ C wq r)) := by ring
  rw [e]
  exact key

end Formalism.L2.KerInert.WeierstrassScaling

namespace Formalism.L2.KerInert.BeCob

open NumberField Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D
open Formalism.MainNotions.GL3Theta (G1 At InertK ModelOverW)
open Formalism.L2.G.Pend (k0ToC wToC LTIso beLT epOf BeRat)
open Formalism.InvariantFactorPaths.G7 (cob lgF UnrOK IsLawOfLog at1)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension omegaK)
open Formalism.DworkPowerSeriesWeights (Integral)

theorem rdictMain : Formalism.L2.KerInert.Rep.CurveDict := by
  have hInv := Sigma.invAlg'
  have hS2 := Sigma.secondEisensteinAlgebraic
  have hPhW : PhWAll := Dict.phWAll_of (Sigma.sigmaCurveInert_of Sigma.invAlg' Sigma.secondEisensteinAlgebraic)
  have hBC := beta_coefficients
  have hCE := coboundary_exact
  have hCS := coboundary_equivalence
  have hPT := phase_compatibility
  have hTT := thetaTie_of short_exact_isomorphism
  intro D cc δ l _ g hLT hAt h5 hIn hOW
  have hp : l.Prime := Fact.out
  obtain ⟨hcurve, -, hδ12, hLam, hOk⟩ := id hAt
  have hcc : cc ≠ ⊥ := hcurve.1
  have hδ : δ ≠ 0 := by
    intro h0
    obtain ⟨⟨L1, hL1⟩, -⟩ := Formalism.L2.Th1.F2.lamOfLat D cc 1 hcc one_ne_zero
    obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L1 (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hL1)
    have hd := Formalism.L2.Th1.F.discNeZero L1
    apply hd
    have h12 := hδ12
    unfold Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice Formalism.MainNotions.TaylorLogMetric.discr at h12
    rw [h0, e2, e3] at h12
    rw [← h12]; norm_num
  obtain ⟨⟨L, hL⟩, hCM⟩ := Formalism.L2.Th1.F2.lamOfLat D cc δ hcc hδ
  have hLg : g.abelian₂ = L.lattice.toAddSubgroup := hLam.trans hL.symm
  obtain ⟨hg2, hg3⟩ := hInv D cc δ hcurve hδ12 L hL
  have hs := hS2 D cc δ hcurve hδ12 L hL
  set a2 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₂, hg2⟩ with ha2
  set a3 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₃, hg3⟩ with ha3
  set s0 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨Formalism.L2.Th1.F.s2 L, hs⟩ with hs0
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hLg.symm)
  have hser : Formalism.MainNotions.TaylorLogMetric.sgSer g.lam g.abelian₂ =
      Formalism.L2.Th1.B.sgStar (g.lam s0) (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) := by
    rw [hLg]; exact Sigma.sgSer_eq g.lam L a2 a3 s0 rfl rfl rfl
  have hW0 := Sigma.wModel_g g.lam g.abelian₂ a2 a3 e2 e3
  set εu : ℂ_[l] := ((g.C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l]) with hεu
  have hεne : εu ≠ 0 := Units.ne_zero _
  obtain ⟨c2, c3⟩ := Sigma.g_change g.C (Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂)
  have gW2 : Formalism.L2.Th1.A.g₂ g.W = εu ^ 4 * g.lam a2 := by rw [← hW0.1]; exact c2
  have gW3 : Formalism.L2.Th1.A.g₃ g.W = εu ^ 6 * g.lam a3 := by rw [← hW0.2]; exact c3
  have hwp : Formalism.L2.Th1.A.wpReg g.W =
      PowerSeries.C (εu ^ 2) * PowerSeries.rescale εu (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) := by
    rw [Sigma.wpReg_eq, gW2, gW3]
    exact (Formalism.L2.Th1.F.seriesScale ℂ_[l] (g.lam a2) (g.lam a3) εu).2.2.2.1
  set s2 : ℂ_[l] := εu ^ 2 * g.lam s0 with hs2def
  have hR : PowerSeries.rescale εu (Formalism.MainNotions.TaylorLogMetric.sgSer g.lam g.abelian₂) = PowerSeries.C εu * Formalism.L2.Th1.B.sgW g.W s2 := by
    unfold Formalism.L2.Th1.B.sgW
    rw [hser, hwp]
    exact ((Formalism.L2.Th1.F.sigmaScale ℂ_[l] (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) (g.lam s0) εu).2).symm
  have hph : g.ph = Formalism.L2.Th1.B.phW g.W s2 := Dict.formal_phase_agree l g s2 hOk hR
  have hcc0 : PowerSeries.constantCoeff g.ph = 0 := by
    rw [hph]; exact (Formalism.L2.Th1.B.curveSigma ℂ_[l] g.W s2).1

  obtain ⟨ι, hι⟩ := Formalism.L2.KerInert.lamExt l g.lam
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hsqf : Squarefree D.host.d := hdp.squarefree
  have hd4 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  have hns : ¬ IsSquare ((-(D.host.d : ℤ) : ℤ) : ZMod l) := ZMod.nonsquare_of_jacobiSym_eq_neg_one hIn
  have hsq' : ¬ ∃ a : ZMod l, a ^ 2 = -(D.host.d : ZMod l) := by
    rintro ⟨a, ha⟩; apply hns; exact ⟨a, by push_cast; rw [← ha]; ring⟩
  have hpd : ¬ l ∣ D.host.d := by
    intro h; apply hsq'; refine ⟨0, ?_⟩
    rw [(ZMod.natCast_eq_zero_iff _ _).2 h]; ring
  have hcmby : Formalism.L2.Th1.CM.HasCMBy D.host.d L := by
    intro ω hω
    have h1 := hCM ω (by rw [← hL]; exact hω)
    rw [← hL] at h1
    have e : Formalism.L2.Th1.CM.omegaK D.host.d = Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
      unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring
    rw [e]; exact h1
  have hιg2 : ι L.g₂ = g.lam a2 := hι a2
  have hιg3 : ι L.g₃ = g.lam a3 := hι a3
  have hιs : ι (Formalism.L2.Th1.F.s2 L) = g.lam s0 := hι s0
  obtain ⟨i1, i2, i3, i4, i6, hΔ⟩ := hOk.1
  obtain ⟨w1, w2, w3, w4, w6⟩ := hOW
  obtain ⟨k2, k3, n2, n3, nd⟩ := Sigma.inv_good g.W h5 i1 i2 i3 i4 i6 hΔ w1 w2 w3 w4 w6
  have ks : s2 ∈ MaximalUnramifiedExtension l := by
    have k2' := k2; have k3' := k3; have n2' := n2; have n3' := n3; have nd' := nd
    rw [gW2, ← hιg2] at k2' n2'
    rw [gW3, ← hιg3] at k3' n3'
    rw [gW2, gW3, ← hιg2, ← hιg3] at nd'
    rw [hs2def, ← hιs]
    exact Sigma.s2_in_unramified_closure D.host.d L hsqf hd4 hcmby l h5 hpd ι εu hεne k2' k3' n2' n3' nd'
  have heW : eLT hLT ∈ Formalism.MainNotions.GL3Theta.Wp l := Formalism.L2.G.Pend.wToC_mem_Wp l _
  have he1 : ‖eLT hLT‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have ke : (eLT hLT)⁻¹ ∈ MaximalUnramifiedExtension l := inv_mem (Sigma.wp_sub_kur _ heW)
  set G2 : MaximalUnramifiedExtension l := ⟨_, k2⟩ with hG2
  set G3 : MaximalUnramifiedExtension l := ⟨_, k3⟩ with hG3
  set S2 : MaximalUnramifiedExtension l := ⟨s2, ks⟩ with hS2d
  set E : MaximalUnramifiedExtension l := ⟨(eLT hLT)⁻¹, ke⟩ with hEd
  have hE1 : ‖E‖ = 1 := by
    show ‖(eLT hLT)⁻¹‖ = 1
    rw [norm_inv, he1, inv_one]
  have hth : ∀ n, ‖PowerSeries.coeff n (thetaS l G2 G3 E)‖ ≤ 1 := by
    intro n
    have hm := FAux.thetaS_map (MaximalUnramifiedExtension l).subtype (l := l) hp.two_le G2 G3 E
    rw [← FAux.norm_coe l, ← PowerSeries.coeff_map, hm]
    exact hTT l h5 g hLT hOk n

  have hgood : Formalism.L2.Th1.CM.IsGoodModel l L ι (G2 : ℂ_[l]) (G3 : ℂ_[l]) := by
    refine ⟨k2, k3, n2, n3, nd, εu, hεne, ?_, ?_⟩
    · show Formalism.L2.Th1.A.g₂ g.W = _
      rw [hιg2]; exact gW2
    · show Formalism.L2.Th1.A.g₃ g.W = _
      rw [hιg3]; exact gW3
  set c : ℂ := ι.symm εu⁻¹ with hcdef
  have hιc : ι c = εu⁻¹ := by rw [hcdef]; exact ι.apply_symm_apply _
  have hc : c ≠ 0 := by
    intro h0; rw [h0, map_zero] at hιc; exact inv_ne_zero hεne hιc.symm
  obtain ⟨-, -, -, -, -, -, hs2c, -, -, hg2c, hg3c⟩ := Formalism.L2.Th1.F.homogeneity L c hc
  have h2c : (G2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ := by
    show Formalism.L2.Th1.A.g₂ g.W = _
    rw [hg2c, map_mul, map_inv₀, map_pow, hιc, hιg2, gW2, inv_pow, inv_inv]
  have h3c : (G3 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ := by
    show Formalism.L2.Th1.A.g₃ g.W = _
    rw [hg3c, map_mul, map_inv₀, map_pow, hιc, hιg3, gW3, inv_pow, inv_inv]
  have hsc : (S2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc)) := by
    show s2 = _
    rw [hs2c, map_mul, map_inv₀, map_pow, hιc, hιs, hs2def, inv_pow, inv_inv]
  have hNR : ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
      ∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l G2 G3 S2 E) α := by
    intro σ hσ α hα hσα
    have hw := (sqrtKur D.host.d hsqf hd4 l h5 hsq' ι).1
    have hmem : ∀ m n : ℤ, ι ((m : ℂ) + (n : ℂ) * omegaK D.host.d) ∈ MaximalUnramifiedExtension l := by
      intro m n
      rw [map_add, map_mul, map_intCast, map_intCast]
      exact add_mem (intCast_mem _ m) (mul_mem (intCast_mem _ n) hw)
    let S : Set (MaximalUnramifiedExtension l) := {a | ∃ m n : ℤ, ¬ (l : ℤ) ∣ normInt D.host.d m n ∧
      (a : ℂ_[l]) = ι ((m : ℂ) + (n : ℂ) * omegaK D.host.d)}
    refine normUnits (MaximalUnramifiedExtension l) l σ hσ (phFF l G2 G3 S2 E) (FAux.cc_phFF (by omega) _ _ _ _) S ?_ α ?_
    · rintro a ⟨m, n, hmn, ha⟩
      exact nrDense Formalism.L2.Th1.CM.cm4 D.host.d L hsqf hd4 hcmby l h5 hpd hsq' ι G2 G3 E S2 hgood hE1 hth
        c hc h2c h3c hsc σ hσ m n hmn a ha
    · intro e he
      obtain ⟨m, n, hmn, hclose⟩ := denseOK D.host.d hsqf hd4 l h5 hsq' ι σ hσ α hα hσα e he
      exact ⟨⟨_, hmem m n⟩, ⟨m, n, hmn, rfl⟩, by simpa using hclose⟩

  have hBR : BeRat g (eLT hLT) := by
    have hphW := hPhW D l cc δ g hAt h5 hIn ⟨w1, w2, w3, w4, w6⟩
    have hB := hBC l g hOk ⟨w1, w2, w3, w4, w6⟩ hphW
    show BeRat g (wToC l (epOf hLT : Formalism.MainNotions.FormalGroupSystem.WW l))
    rw [← Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap l]
    exact Formalism.L2.G.Pend.beRat_of g hOk.2.2.1 hB (Formalism.L2.G.Pend.exRat_of g hOk ⟨w1, w2, w3, w4, w6⟩) _
  obtain ⟨σ0, hσ0⟩ := Formalism.L2.Th1.Top.frobExistsH l h5
  obtain ⟨F0, hF0⟩ := (Formalism.InvariantFactorPaths.G7.Top.lawExists (MaximalUnramifiedExtension l) l hσ0.1 hσ0.2.2.1).1
  have tie : ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
      Formalism.InvariantFactorPaths.G7.Simeq (MvPowerSeries.map (k0ToC l) (inParam l (beLT hLT)))
        (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (cob F (phFF l G2 G3 S2 E))) := by
    intro F hF
    rw [hCE l g hLT hOk hBR F hF, map_cob (MaximalUnramifiedExtension l).subtype F hF.1,
      Formalism.L2.Th1.E.Joints.map_phFF (MaximalUnramifiedExtension l).subtype hp.two_le]
    refine hCS ℂ_[l] _ (by rw [MvPowerSeries.constantCoeff_map, hF.1, map_zero]) ?_ _ _ (hPT l g hLT hOk s2 hph)
    intro n
    rw [MvPowerSeries.coeff_map]
    exact hF.2.1 n

  have hlamg : g.abelian₂ = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ := hLam
  have hΔW : g.W.Δ = εu ^ 12 := by
    show (g.C • Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂).Δ = εu ^ 12
    rw [WeierstrassCurve.variableChange_Δ, hlamg,
      Formalism.L2.KerInert.JetsModel.wModel_Δ D cc δ hcurve hδ12 g.lam, mul_one]
  have hΔ1 : ‖g.W.Δ‖ = 1 := hOk.1.2.2.2.2.2
  have hεu1 : ‖εu‖ = 1 := by
    have := hΔ1
    rw [hΔW, norm_pow] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
  have hnorm : ‖εu * (eLT hLT)⁻¹‖ = 1 := by rw [norm_mul, norm_inv, he1, hεu1, inv_one, one_mul]

  obtain ⟨ν, hν⟩ := IsAlgClosed.exists_pow_nat_eq g.W.Δ (show 0 < 12 by norm_num)
  have hν1 : ‖ν‖ = 1 := by
    have := congrArg norm hν
    rw [norm_pow, hΔ1] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
  have hν0 : ν ≠ 0 := by
    intro h; rw [h, norm_zero] at hν1; exact zero_ne_one hν1
  have hp2 : l ≠ 2 := by omega
  set C' := Formalism.L2.KerInert.WeierstrassScaling.scC ν hν0 * g.C with hC'
  set wq' := PowerSeries.rescale ν⁻¹ g.wq with hwq'
  have hC'W : C' • Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂ = Formalism.L2.KerInert.WeierstrassScaling.scC ν hν0 • g.W := mul_smul _ _ _
  have hM : Formalism.MainNotions.TaylorLogMetric.IsModel g.lam g.abelian₂ C' :=
    Formalism.L2.KerInert.WeierstrassScaling.isModel_scale g.lam g.abelian₂ g.C hOk.1 ν hν0 hν1 hν
  have hWq : Formalism.MainNotions.TaylorLogMetric.IsWq (C' • Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂) wq' := by
    rw [hC'W]; exact Formalism.L2.KerInert.WeierstrassScaling.isWq_scale ν hν0 _ _ hOk.2.1

  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set v := vLT hLT with hvdef
  set A : PowerSeries ℂ_[l] := PowerSeries.C (eLT hLT)⁻¹ * lgF ℂ_[l] l with hAdef
  have hA0 : PowerSeries.constantCoeff A = 0 := by rw [hAdef, map_mul, cc_lgF', mul_zero]
  have hAs : PowerSeries.HasSubst A := PowerSeries.HasSubst.of_constantCoeff_zero' hA0
  have hexs : PowerSeries.HasSubst g.ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  have hv0 : PowerSeries.constantCoeff v = 0 := by
    rw [hvdef, vLT]
    exact PowerSeries.constantCoeff_subst_eq_zero hA0 _ hex
  have hvs : PowerSeries.HasSubst v := PowerSeries.HasSubst.of_constantCoeff_zero' hv0
  have hvl : PowerSeries.subst v g.l = A := by
    rw [hvdef, vLT, ← hAdef, ← PowerSeries.subst_comp_subst_apply hexs hAs, hinv, PowerSeries.subst_X hAs]
  set hh : PowerSeries ℂ_[l] := PowerSeries.C ν * v with hhdef
  have hh0 : PowerSeries.constantCoeff hh = 0 := by rw [hhdef, map_mul, hv0, mul_zero]
  have hhI : ∀ n, Formalism.MainNotions.TaylorLogMetric.IsIntP (PowerSeries.coeff n hh) := by
    intro n
    unfold Formalism.MainNotions.TaylorLogMetric.IsIntP
    rw [hhdef, PowerSeries.coeff_C_mul, norm_mul, hν1, one_mul]
    exact v_integral hOk hLT n
  have hlog : PowerSeries.subst hh (Formalism.MainNotions.TaylorLogMetric.flog (C' • Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂) wq') =
      PowerSeries.C (ν * (eLT hLT)⁻¹) * PowerSeries.map (k0ToC l) (Formalism.MainNotions.FormalGroupSystem.logF l) := by
    have hs : PowerSeries.HasSubst hh := PowerSeries.HasSubst.of_constantCoeff_zero' hh0
    rw [hC'W, hwq', Formalism.L2.KerInert.WeierstrassScaling.flog_scale ν hν0, ← PowerSeries.smul_eq_C_mul,
      PowerSeries.subst_smul hs, hhdef, Formalism.L2.KerInert.WeierstrassScaling.subst_Cmul_rescale ν hν0 v _ hv0]
    change ν • PowerSeries.subst v g.l = _
    rw [hvl, hAdef, lgF_eq_logF, PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul]

  set phC : PowerSeries ℂ_[l] := phFF l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) s2 (eLT hLT)⁻¹ with hphC
  have hphL : Formalism.L2.Th1.Top.phL l G2 G3 S2 E = phC := by
    unfold Formalism.L2.Th1.Top.phL
    rw [Formalism.L2.Th1.E.Joints.map_phFF (MaximalUnramifiedExtension l).subtype hp.two_le]
    rfl
  have hphC0 : PowerSeries.constantCoeff phC = 0 := by
    rw [← hphL]; unfold Formalism.L2.Th1.Top.phL
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, FAux.cc_phFF (by omega) _ _ _ _, map_zero]
  set ψ : PowerSeries ℂ_[l] := psiLT hLT with hψdef
  have hψ0 : PowerSeries.constantCoeff ψ = 0 := by
    rw [hψdef, psiLT]; exact PowerSeries.constantCoeff_subst_eq_zero hv0 _ hcc0
  have hsym := (Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[l] Unit).2.1 _ _ (hPT l g hLT hOk s2 hph)
  set V : PowerSeries ℂ_[l] := Formalism.L2.Th1.C.mvExp (phC - ψ) with hVdef
  have hV : ∀ n, Formalism.MainNotions.TaylorLogMetric.IsIntP (PowerSeries.coeff n V) := fun n => ips hsym.2 n
  have hsubE : PowerSeries.subst hh (Formalism.MainNotions.TaylorLogMetric.ePhi1 g.lam g.abelian₂ C' wq') = Formalism.L2.Th1.C.mvExp (-ψ) := by
    rw [hC', hwq', Formalism.L2.KerInert.WeierstrassScaling.ePhi1_scale, hhdef,
      Formalism.L2.KerInert.WeierstrassScaling.subst_Cmul_rescale ν hν0 v _ hv0, Dict.ePhi1_eq g s2 hOk hR, ← hph]
    have hn : PowerSeries.constantCoeff (-g.ph) = 0 := by rw [map_neg, hcc0, neg_zero]
    change PowerSeries.subst v (Formalism.L2.Th1.C.mvExp (-g.ph) : PowerSeries ℂ_[l]) = _
    rw [Formalism.L2.Th1.C.subst_mvExp hn hv0, hψdef, psiLT, ← PowerSeries.coe_substAlgHom hvs, map_neg]
  have hexp : (Formalism.L2.Th1.C.mvExp phC : PowerSeries ℂ_[l]) =
      V * (PowerSeries.subst hh (Formalism.MainNotions.TaylorLogMetric.ePhi1 g.lam g.abelian₂ C' wq'))⁻¹ := by
    have hn : PowerSeries.constantCoeff (Formalism.L2.Th1.C.mvExp (-ψ) : PowerSeries ℂ_[l]) ≠ 0 := by
      have h1 := Formalism.L2.Th1.C.constantCoeff_mvExp (show MvPowerSeries.constantCoeff (-ψ : PowerSeries ℂ_[l]) = 0 by
        rw [map_neg]; exact (neg_eq_zero.mpr hψ0))
      intro h0
      exact one_ne_zero (h1.symm.trans h0)
    have hinvE : (Formalism.L2.Th1.C.mvExp ψ : PowerSeries ℂ_[l]) = (Formalism.L2.Th1.C.mvExp (-ψ) : PowerSeries ℂ_[l])⁻¹ :=
      (PowerSeries.eq_inv_iff_mul_eq_one hn).mpr (Formalism.L2.Th1.C.mvExp_mul_neg hψ0)
    rw [hsubE, ← hinvE, hVdef]
    exact (Formalism.L2.Th1.C.mvExp_sub_mul hphC0 hψ0).symm
  have hcEq : (((C'.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l])) * (ν * (eLT hLT)⁻¹) = εu * (eLT hLT)⁻¹ := by
    rw [hC', Formalism.L2.KerInert.WeierstrassScaling.scC_mul_uinv, ← hεu]
    field_simp
  refine ⟨G2, G3, E, S2, rfl, rfl, rfl, hR, hnorm,
    ⟨n2, n3, hE1, hth, hNR, cc_beLT hOk hLT hBR hcc0, F0, hF0, tie F0 hF0⟩, ?_⟩
  intro D'
  refine ⟨C', wq', hM, hWq, ?_⟩
  intro N N' r b G hInt
  have key := Formalism.L2.KerInert.WeierstrassScaling.dict_core hp2 D' g.lam g.abelian₂ C' wq' hh hh0 hhI (ν * (eLT hLT)⁻¹) hlog
    phC V hphC0 hV hexp b G hInt
  rw [hcEq] at key
  rw [hphL]
  exact key

end Formalism.L2.KerInert.BeCob

namespace Formalism.L2.KerInert.Rep

theorem curve_dictionary : CurveDict := Formalism.L2.KerInert.BeCob.rdictMain

end Formalism.L2.KerInert.Rep
end
end

section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.KG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.PairingIndexBounds.F

theorem linSub_scl {σ R : Type} [Fintype σ] [CommRing R] (c : R) (A : σ → σ → R) (G : MvPowerSeries σ R) :
    Formalism.MainNotions.FormalGroupSystem.linSub (fun x y => c * A x y) G = Formalism.MainNotions.FormalGroupSystem.linSub A (Formalism.L2.KerInert.Rep.sclY c G) := by
  have ha : MvPowerSeries.HasSubst (fun k : σ =>
      (MvPowerSeries.C c * MvPowerSeries.X k : MvPowerSeries σ R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  have hb : MvPowerSeries.HasSubst (fun x : σ =>
      (∑ y, MvPowerSeries.C (A x y) * MvPowerSeries.X y : MvPowerSeries σ R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  unfold Formalism.MainNotions.FormalGroupSystem.linSub Formalism.L2.KerInert.Rep.sclY
  rw [MvPowerSeries.subst_comp_subst_apply ha hb]
  congr 1
  funext k
  rw [← MvPowerSeries.coe_substAlgHom hb, map_mul, MvPowerSeries.coe_substAlgHom hb, MvPowerSeries.subst_C,
    MvPowerSeries.subst_X hb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, ← map_mul]

variable {p : ℕ} [Fact p.Prime]

theorem subBG_eq {X : Sys p} {D : D7} (E : CEmbC X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (fd : FData X D) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1))
    (x y : D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) :
    subBG E.toCEmb pos fd j La La' x y = Formalism.L2.KerInert.RepFrame.subGen X E pos fd.frM j La La' x y := by
  unfold subBG Formalism.L2.KerInert.RepFrame.subGen
  split_ifs <;> rfl

theorem ltC_eq (g : GL3Theta.G1 p) (hLT : LTIso g) :
    ltC g hLT = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹ := by
  unfold ltC Formalism.L2.KerInert.BeCob.eLT
  rw [mul_inv, Units.val_inv_eq_inv_val]

theorem twInt_all (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) : Formalism.L2.KerInert.RepFrame.TwInt X E := by
  intro v s w
  rw [Formalism.L2.KerInert.RepFrob.twE_eq, Formalism.L2.KerInert.RepFrob.twT_alg]
  exact Formalism.L2.G.Pend.norm_wToC_le p _

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in

theorem first_kernel_law_global : K1G := by
  intro D p _ h5 X _ E hfin hst g hLT pos fd cc δ B χ lam SS cl Ξ₀ muT ρ hAt hIn hM hcc hδ hχ hlam hLam hAdm hCl hXi hSc
    hρ hMI hL
  subst hlam

  let large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E) :=
    fun j La _ => fd.kerN j La
  let Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E) :=
    fun j _ La' => fd.kerN (j + 1) La'
  let Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ :=
    fun j La La' => movD (Ξ₀ j La La') (fd.trG j La) (fd.trG (j + 1) La')
  let G : ∀ j, X.Lt j → X.Lt (j + 1) → TaylorLogMetric.VC D ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ :=
    fun j La La' => kerTh B χ SS cl (large₂ j La La') (Lg' j La La') (Ξ j La La')
  let F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p] :=
    fun j La La' => ((p : ℂ_[p]) ^ expG X j La La') •
      TaylorLogMetric.pSer D g.lam (fun z => scalG fd χ muT j La La' * G j La La' z)
  let Fr : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p] :=
    fun j La La' => Formalism.L2.KerInert.Rep.sclY (ltC g hLT) (F j La La')
  let S := fun j (La : X.Lt j) (La' : X.Lt (j + 1)) => Formalism.L2.KerInert.RepFrame.subGen X E pos fd.frM j La La'
  have hFam : FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₀ muT (ltC g hLT) =
      fun j La La' => Formalism.MainNotions.FormalGroupSystem.linSub (S j La La') (Fr j La La') := by
    funext j La La'
    have hS : S j La La' = subBG E.toCEmb pos fd j La La' :=
      funext fun x => funext fun y => (subBG_eq E pos fd j La La' x y).symm
    rw [hS]
    exact linSub_scl _ _ _

  have hB : BeProp p (beLT hLT) := Formalism.L2.KerInert.beProp_ofA Formalism.L2.KerInert.inert_facts_first_hold D cc δ p g hLT hAt h5 hIn hM
  have hComb0 : Formalism.L2.KerInert.Rep.CombAt X hfin D large₂ Lg'
      (fun j La La' => TaylorLogMetric.pSer D g.lam (G j La La')) B.tor (B.eNat χ) g.lam :=
    Formalism.L2.KerInert.RepRec.combAt_of_dataRec X hfin D B χ SS cl g.lam hcc hδ
      (Formalism.L2.KerInert.AlgTP.algT_of B hcc hδ hχ) large₂ Lg' Ξ
      (Formalism.L2.KerInert.RepRec.dataRec_movD X D cl Ξ₀ (fun j La _ => fd.trG j La) (fun j _ La' => fd.trG (j + 1) La')
        ((Formalism.L2.KerInert.RepRec.dataRec_iff X D cl Ξ₀).2 ⟨hCl, hXi⟩)) hAdm
  have hComb : Formalism.L2.KerInert.Rep.CombAt X hfin D large₂ Lg' F B.tor (B.eNat χ) g.lam :=
    Formalism.L2.KerInert.Rep.combAt_scalar X hfin D large₂ Lg' B.tor (B.eNat χ) g.lam G
      (fun j La La' => scalG fd χ muT j La La') (fun j La La' => expG X j La La') hComb0 hSc
  have hOnb : Formalism.L2.KerInert.RepFrame.OnbEx X hfin D large₂ Lg' :=
    Formalism.L2.KerInert.RepFrame.onbEx_of X hfin D large₂ Lg'
      (Formalism.L2.KerInert.orthBasisExists_of Formalism.L2.KerInert.global_orthonormal_basis_four Formalism.L2.KerInert.weakApprox_of_approx_and_separation) h5 hIn hAdm
  have hTr : Formalism.L2.KerInert.RepFrame.LamTrace X hfin D large₂ Lg' g.lam :=
    Formalism.L2.KerInert.RepFrame.lamTrace_of X hfin D large₂ Lg' g.lam
      (Formalism.L2.KerInert.RepFrame.rankTie_of X hfin D large₂ Lg' hAdm)
      (Formalism.L2.KerInert.RepFrame.colTie_of X hfin D large₂ Lg' (Formalism.L2.KerInert.RepFrame.trace_tau_sum D) g.lam)
  have hFH : Formalism.L2.KerInert.Rep.FrameHyp X E hfin D pos large₂ Lg' Fr S g.lam 1 :=
    Formalism.L2.KerInert.RepFrame.frameHyp_of_lat X E hfin D pos large₂ Lg' fd.frM g.lam ρ hOnb hTr hρ
      (Formalism.L2.KerInert.RepFrob.frobTw_of X E h5) hMI (twInt_all X E) hL Fr
  have h2b : adm2b D X (pendT X E hfin hst hLT pos (fun j La La' => Formalism.MainNotions.FormalGroupSystem.linSub (S j La La') (Fr j La La'))) :=
    Formalism.L2.KerInert.Rep.adm2b_of_curve_dictionary_one Formalism.L2.KerInert.Rep.curve_dictionary Formalism.L2.KerInert.kernels_integral_inert D h5 X E hfin
      hst hLT cc δ hAt hIn hM B hcc hδ χ hχ hIn hLam pos large₂ Lg' F Fr
      (fun j La La' => by simp only [Fr]; rw [ltC_eq]) S hB hComb hFH
  rw [hFam]
  refine ⟨Formalism.L2.KerInert.admissible_second_of_variant D X E hfin hst hLT pos _ h2b, h2b,
    Formalism.L2.KerInert.admissible_third_of_second_eleventh D X E hfin hst hLT pos _ h2b
      (Formalism.L2.KerInert.admissible_eleventh_inert D cc δ p g hLT hAt h5 hIn hM X _ rfl)⟩

end Formalism.L2.KerInert.KG
end
end

section
noncomputable section

open scoped Matrix

namespace Formalism.L2.KerInert.RepLt

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.KerInert.RepFrame Formalism.L2.KerInert.RepTwLat
open Formalism.L2.G.Pend (Frm)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

section Lat

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

end Lat

section Int

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

theorem frameIntLt_of (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) (hM : MInv X M) (hT : TwInt X E)
    (hL : FrameLatMapLt X M hfin D large₂ Lg' ρ) : FrameIntLt X E hfin D large₂ Lg' M ρ := by
  intro j hj L0 hL0 La' hLa' φ r b hb ho i v s b0 a0
  obtain ⟨h1, h2⟩ := hL j hj L0 hL0 La' hLa' φ r b hb ho i v
  constructor
  · obtain ⟨w, hw⟩ := entry_int (W := X.G.P.W v) (Gm X M φ v) (Gmi X M φ v) (Gmi_mul_Gm X M φ (hM j L0) v)
      ((b i).map (fun y => ρ v (D.host.conj y)))ᵀ (Gp X M φ v) h2 a0 b0
    have e1 : ∑ B, ∑ A, ρ v (D.host.conj (b i B A)) * Gp X M φ v B b0 * Gmi X M φ v a0 A =
        (Gmi X M φ v * ((b i).map (fun y => ρ v (D.host.conj y)))ᵀ * Gp X M φ v) a0 b0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun B _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun A _ => ?_
      simp only [Matrix.transpose_apply, Matrix.map_apply]
      ring
    rw [e1, hw]
    exact hT v s w
  · obtain ⟨w, hw⟩ := entry_int (W := X.G.P.W v) (Gp X M φ v) (Gpi X M φ v) (Gpi_mul_Gp X M φ (hM (j + 1) La') v)
      ((b i).map (ρ v)) (Gm X M φ v) h1 b0 a0
    have e1 : ∑ B, ∑ A, ρ v (b i B A) * Gm X M φ v A a0 * Gpi X M φ v b0 B =
        (Gpi X M φ v * (b i).map (ρ v) * Gm X M φ v) b0 a0 := by
      rw [Matrix.mul_apply, Finset.sum_comm]
      refine Finset.sum_congr rfl fun B _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun A _ => ?_
      simp only [Matrix.map_apply]
      ring
    rw [e1, hw]
    exact hT v s w

end Int

end Formalism.L2.KerInert.RepLt

namespace Formalism.L2.KerInert.RepLt

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1 Formalism.L2.KerInert.RepFrame
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (Frm)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))

theorem hypCoordLt_of (lam : Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (hT : LamTraceLt X hfin D large₂ Lg' lam) (hρ : LamPosG X E D pos lam ρ) (hF : FrobTw X E)
    (hev : ∀ v, Even (X.G.P.n' v)) (hconj : ∀ x, D.host.conj (D.host.conj x) = x) (hM : MInv X M)
    (hI : FrameIntLt X E hfin D large₂ Lg' M ρ) :
    HypCoordLt X E hfin D pos large₂ Lg' M lam 1 := by
  intro j hj L0 hL0 La' hLa' r b hb ho φ
  obtain ⟨σ, twK, wK, hσ, htwK, hσtw, hwK, hσw, hwn⟩ := hF
  have hL := hT j hj L0 hL0 La' hLa' r b hb ho
  have hH : IsHypPair σ (fK X D M φ b ρ twK wK) (fK' X D M φ b ρ twK wK) := by
    unfold IsHypPair
    refine ⟨fun e i => ⟨?_, ?_⟩, fun e i => ⟨?_, ?_⟩, fun e e' => ?_, fun e e' => ?_, fun e e' => ?_⟩
    · exact norm_fK X E D M φ b ρ twK wK htwK hwn
        (fun i v s b0 a0 => (hI j hj L0 hL0 La' hLa' φ r b hb ho i v s b0 a0).1) e i
    · exact sigma2_fK X D M φ b ρ twK wK σ hσtw hσw hev hconj e i
    · exact norm_fK' X E D M φ b ρ twK wK htwK hconj hwn
        (fun i v s b1 a1 => (hI j hj L0 hL0 La' hLa' φ r b hb ho i v s b1 a1).2) e i
    · exact sigma2_fK' X D M φ b ρ twK wK σ hσtw hσw hev hconj e i
    · exact iso_fK X E D pos lam M φ b ρ twK wK hρ htwK σ hσtw hσw hev hconj hL e e'
    · exact iso_fK' X E D pos lam M φ b ρ twK wK hρ htwK σ hσtw hσw hev hconj hL e e'
    · rw [dual_fK X E D pos lam M φ b ρ twK wK hρ htwK σ hσtw hσw hev hconj hL (hM j L0) (hM (j + 1) La') e e']
  refine ⟨σ, fK X D M φ b ρ twK wK, fK' X D M φ b ρ twK wK, hσ, hH, fun e i => ?_, fun e i => ?_⟩
  · rw [inv_one, one_mul]
    exact coe_fK X E D pos lam M φ b ρ twK wK hρ htwK hwK e i
  · rw [inv_one, one_mul]
    exact coe_fK' X E D pos lam M φ b ρ twK wK hρ htwK hwK hconj e i

theorem frameStdLt_of (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) (hc0 : c ≠ 0) (h1 : OnbExLt X hfin D large₂ Lg')
    (h2 : LamTraceLt X hfin D large₂ Lg' lam) (h3 : HypCoordLt X E hfin D pos large₂ Lg' M lam c) :
    FrameStdLt X E hfin D pos large₂ Lg' M lam c := by
  intro j hj L0 hL0 La' hLa' φ
  obtain ⟨r, b, hb, ho⟩ := h1 j hj L0 hL0 La' hLa'
  obtain ⟨σ, f, f', hσ, hH, hf, hf'⟩ := h3 j hj L0 hL0 La' hLa' r b hb ho φ
  have hL := h2 j hj L0 hL0 La' hLa' r b hb ho
  refine ⟨r, b, hb, ho, σ, f, f', hσ, hH, fun k => ?_⟩
  rw [(isLin_stdLin X E pos M φ k).repr, Fintype.sum_sum_type]
  simp only [hypLin, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun i e => MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
        (MvPowerSeries.C (f e i : ℂ_[p]) * MvPowerSeries.X (Sum.inl e))),
    Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun i e => MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
        (MvPowerSeries.C (f' e i : ℂ_[p]) * MvPowerSeries.X (Sum.inr e)))]
  congr 1
  · refine Finset.sum_congr rfl fun e _ => ?_
    simp only [← mul_assoc, ← map_mul]
    rw [← Finset.sum_mul, ← map_sum]
    congr 2
    simp only [hf]
    exact (coord_recon D lam b hL hc0 (fun k' => frVec X E pos M φ (Sum.inl e) k') k).symm
  · refine Finset.sum_congr rfl fun e _ => ?_
    simp only [← mul_assoc, ← map_mul]
    rw [← Finset.sum_mul, ← map_sum]
    congr 2
    simp only [hf']
    exact (coord_recon D lam b hL hc0 (fun k' => frVec X E pos M φ (Sum.inr e) k') k).symm

theorem frameLinLt_of_std (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) (h : FrameStdLt X E hfin D pos large₂ Lg' M lam c) :
    FrameLinLt X E hfin D pos large₂ Lg' (fun j La La' => subGen X E pos M j La La') lam c := by
  intro j hj L0 hL0 La' hLa' φ
  obtain ⟨r, b, hb, ho, σ, f, f', hσ, hH, hk⟩ := h j hj L0 hL0 La' hLa' φ
  exact ⟨r, b, hb, ho, σ, f, f', hσ, hH, fun k => (linFrame_subGen X E pos M φ k).trans (hk k)⟩

theorem frameHypLt_of_lin (S : ∀ j, X.Lt j → X.Lt (j + 1) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) (h : FrameLinLt X E hfin D pos large₂ Lg' S lam c)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    FrameHypLt X E hfin D pos large₂ Lg' F S lam c := by
  intro j hj L0 hL0 La' hLa' φ
  obtain ⟨r, b, hb, ho, σ, f, f', hσ, hH, hk⟩ := h j hj L0 hL0 La' hLa' φ
  refine ⟨r, b, hb, ho, σ, f, f', hσ, hH, ?_⟩
  rw [thA_thFOf_linSub X E pos φ S F, subst_hypLin_thOrth]
  congr 1
  funext k
  exact hk k

theorem onbExLt_of (hO : Formalism.L2.KerInert.OrthBasisExists) (h5 : 5 ≤ p) (hin : jacobiSym (-(D.host.d : ℤ)) p = -1)
    (hadm : ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
      (X.Pj (j + 1)).IsLatTup La'.2 → admitted D _ _ (large₂ j L0 La') (Lg' j L0 La')) :
    OnbExLt X hfin D large₂ Lg' :=
  fun j hj L0 hL0 La' hLa' => hO D p h5 hin _ _ _ _ (hadm j hj L0 hL0 La' hLa')

theorem rankTieLt_of (hadm : ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
      (X.Pj (j + 1)).IsLatTup La'.2 → admitted D _ _ (large₂ j L0 La') (Lg' j L0 La')) :
    RankTieLt X hfin D large₂ Lg' :=
  fun j hj L0 hL0 La' hLa' _ b hb =>
    rank_of_locBasis _ _ (hadm j hj L0 hL0 La' hLa').2.2.1 (hadm j hj L0 hL0 La' hLa').2.2.2 b hb

theorem lamTraceLt_of (lam : Qbar →+* ℂ_[p]) (h1 : RankTieLt X hfin D large₂ Lg') (h2 : ColTie X hfin D large₂ Lg' lam) :
    LamTraceLt X hfin D large₂ Lg' lam :=
  fun j hj L0 hL0 La' hLa' r b hb ho =>
    lamONB_of_cols D lam b (h1 j hj L0 hL0 La' hLa' r b hb) (h2 j L0 hL0 La' hLa' r b hb ho)

theorem frameHypLt_of_lat (lam : Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (h1 : OnbExLt X hfin D large₂ Lg') (hT : LamTraceLt X hfin D large₂ Lg' lam) (hρ : LamPosG X E D pos lam ρ)
    (hF : FrobTw X E) (hM : MInv X M) (hTw : TwInt X E) (hL : FrameLatMapLt X M hfin D large₂ Lg' ρ)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    FrameHypLt X E hfin D pos large₂ Lg' F (fun j La La' => subGen X E pos M j La La') lam 1 :=
  frameHypLt_of_lin X E hfin D pos large₂ Lg' _ lam 1
    (frameLinLt_of_std X E hfin D pos large₂ Lg' M lam 1
      (frameStdLt_of X E hfin D pos large₂ Lg' M lam 1 one_ne_zero h1 hT
        (hypCoordLt_of X E hfin D pos large₂ Lg' M lam ρ hT hρ hF (fun v => (X.G.P.setting v).even) (conj_conj D) hM
          (frameIntLt_of X E M hfin D large₂ Lg' ρ hM hTw hL)))) F

end Formalism.L2.KerInert.RepLt

namespace Formalism.L2.KerInert.RepLt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H Formalism.L2.KerInert.RepComb

theorem combAtLt_of_dataRec {p : ℕ} [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p) [IsFractionRing X.G.O X.G.Kf]
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)
    (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
    (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hAlg : B.AlgT χ)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (hD : Formalism.L2.KerInert.RepRec.DataRec X D cl Ξ)
    (hA : ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
      (X.Pj (j + 1)).IsLatTup La'.2 → TaylorLogMetric.admitted D _ _ (large₂ j L0 La') (Lg' j L0 La')) :
    CombAtLt X hfin D large₂ Lg'
      (fun j La La' => Formalism.L2.PairingIndexBounds.F.serP lam (Formalism.L2.PairingIndexBounds.F.kerTh B χ SS cl (large₂ j La La') (Lg' j La La') (Ξ j La La')))
      B.tor (B.eNat χ) lam := by
  obtain ⟨S, hS, hpS, hΞ⟩ := hD
  have hTA : TransAlg D B.tor (B.eNat χ) :=
    transcendence_algebraic_eigen D cc δ B χ hcc hδ (KS.Lat.delta_ne hcc hδ) (B.stdOK hcc hδ) hAlg
  intro j hj L0 h0 La' hL'
  have h := hA j hj L0 h0 La' hL'
  exact ⟨h, combined_kernel_twisted D cc δ B χ _ _ SS cl _ _ _ S p lam h h.2.2.2.1 h.2.2.1.2.1 (aaOf_fg cc)
    (laFacts_of_adm B hcc hδ h) hS.1 hS (hΞ j L0 La') hpS (lambda_in_lattice_pair cc δ _ _) hTA⟩

theorem combAtLt_scalar {p : ℕ} [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (T : TaylorLogMetric.Tor D) (e : TaylorLogMetric.FamE D) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
    (G : ∀ j, X.Lt j → X.Lt (j + 1) → TaylorLogMetric.VC D ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (s : ∀ j, X.Lt j → X.Lt (j + 1) → ℂ) (k : ∀ j, X.Lt j → X.Lt (j + 1) → ℤ)
    (h : CombAtLt X hfin D large₂ Lg' (fun j La La' => TaylorLogMetric.pSer D lam (G j La La')) T e lam)
    (hs : ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
      (X.Pj (j + 1)).IsLatTup La'.2 → s j L0 La' ∈ TaylorLogMetric.Qbar ∧ ‖(p : ℂ_[p]) ^ k j L0 La' * TaylorLogMetric.lamC lam (s j L0 La')‖ ≤ 1) :
    CombAtLt X hfin D large₂ Lg'
      (fun j La La' => ((p : ℂ_[p]) ^ k j La La') • TaylorLogMetric.pSer D lam (fun z => s j La La' * G j La La' z)) T e lam := by
  intro j hj L0 h0 La' hL'
  obtain ⟨hA, hC⟩ := h j hj L0 h0 La' hL'
  exact ⟨hA, Formalism.L2.KerInert.Rep.isComb_scalar D T e lam _ hC (hs j hj L0 h0 La' hL').1 _ (hs j hj L0 h0 La' hL').2⟩

end Formalism.L2.KerInert.RepLt

namespace Formalism.L2.KerInert.RepLt

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1 Formalism.L2.KerInert.Rep
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp OcC Frm thA thFOf)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem firstKernelLawSmallSteps_of_curve_orthAllLt {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
    (E : Formalism.L2.G.Pend.CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (be : MvPowerSeries (Fin 2) (K0 p))
    {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (hB : BeProp p be) (g2 g3 ε s2 : MaximalUnramifiedExtension p) (hC : CurveAt p be g2 g3 ε s2)
    (hO : OrthAllLt X E hfin pos F g2 g3 s2 ε) :
    FirstKernelLawLocalPowerSeries X E hfin be pos F := by
  intro j hj L0 h0 La' hL' φ
  exact k1gen_of_orth h5 hB hC (hO j hj L0 h0 La' hL' φ)

theorem K1_representatives_LT_of_dictionary (hCD : CurveDict) (hInt : Formalism.L2.KerInert.IntInert) (D : D7) {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p)
    (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
    {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : Formalism.L2.G.Pend.LTIso g)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hA : Formalism.MainNotions.GL3Theta.At D cc δ g) (hIn : Formalism.MainNotions.GL3Theta.InertK D p)
    (hM : Formalism.MainNotions.GL3Theta.ModelOverW g.lam g.abelian₂ g.C) (B : Base D cc δ) (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (χ : IdE D → ℂ) (hχ : IsChi D χ) (hin : jacobiSym (-(D.host.d : ℤ)) p = -1) (hLam : g.abelian₂ = B.tor.abelian₂)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (F Fr : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (hFr : ∀ j La La', Fr j La La' =
      sclY (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) (F j La La'))
    (S : ∀ j, X.Lt j → X.Lt (j + 1) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (hB : BeProp p (Formalism.L2.G.Pend.beLT hLT))
    (hComb : CombAtLt X hfin D large₂ Lg' F B.tor (B.eNat χ) g.lam)
    (hFH : FrameHypLt X E hfin D pos large₂ Lg' Fr S g.lam 1) :
    FirstKernelLawLocalPowerSeries X E hfin (Formalism.L2.G.Pend.beLT hLT) pos (fun j La La' => linSub (S j La La') (Fr j La La')) := by
  obtain ⟨g2, g3, ε, s2, hC, hD⟩ := curveDict_data hCD D cc δ hLT hA h5 hIn hM
  have hD' : DictInt D g.lam B.tor.abelian₂ (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) g2 g3 s2 ε := by
    rw [← hLam]
    exact hD D
  obtain ⟨C, wq, hMod, hW, hDi⟩ := hD'
  refine firstKernelLawSmallSteps_of_curve_orthAllLt h5 X E hfin _ pos _ hB g2 g3 ε s2 hC ?_
  intro j hj L0 h0 La' hL' φ
  obtain ⟨r, b, hLB, hON, σ, f, f', hσ, hP, hEq⟩ := hFH j hj L0 h0 La' hL' φ
  obtain ⟨hAdm, hCb⟩ := hComb j hj L0 h0 La' hL'
  refine ⟨r, thOrth D g.lam (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) b (F j L0 La'), σ, f, f', hσ,
    hP, ?_, hDi _ _ r b _ (hInt D cc δ B hcc hδ χ hχ p h5 hin g.lam _ _ _ _ hAdm (F j L0 La') hCb C wq r b hMod hW hLB hON)⟩
  rw [hEq, hFr, thOrth_sclY]

end Formalism.L2.KerInert.RepLt

set_option pp.fullNames true
end
end

section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.KGLt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert.KG

variable {p : ℕ} [Fact p.Prime]

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in

theorem first_kernel_small_of_frame (D : D7) (h5 : 5 ≤ p) (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (g : GL3Theta.G1 p) (hLT : LTIso g)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)
    (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (hAt : GL3Theta.At D cc δ g) (hIn : GL3Theta.InertK D p) (hM : GL3Theta.ModelOverW g.lam g.abelian₂ g.C)
    (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : TaylorLogMetric.IsChi D χ) (hLam : g.abelian₂ = B.tor.abelian₂)
    (hAdm : Formalism.L2.KerInert.RepLt.AdmGLt X hfin D fd) (hCl : Formalism.L2.KerInert.RepRec.ClAway p cl)
    (hXi : Formalism.L2.KerInert.RepRec.XiAway X D Ξ₀) (hSc : Formalism.L2.KerInert.RepLt.ScalGLt X hfin fd χ muT g.lam)
    (hρ : Formalism.L2.KerInert.RepFrame.LamPosG X E D pos g.lam ρ) (hMI : Formalism.L2.KerInert.RepFrame.MInv X fd.frM)
    (hL : Formalism.L2.KerInert.RepLt.FrameLatMapLt X fd.frM hfin D (fun j La _ => fd.kerN j La)
        (fun j _ La' => fd.kerN (j + 1) La') ρ) :
    Formalism.L2.KerInert.RepLt.FirstKernelLawLocalPowerSeries X E hfin (beLT hLT) pos (FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₀ muT (ltC g hLT)) := by

  let large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E) :=
    fun j La _ => fd.kerN j La
  let Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E) :=
    fun j _ La' => fd.kerN (j + 1) La'
  let Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ :=
    fun j La La' => movD (Ξ₀ j La La') (fd.trG j La) (fd.trG (j + 1) La')
  let G : ∀ j, X.Lt j → X.Lt (j + 1) → TaylorLogMetric.VC D ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ :=
    fun j La La' => kerTh B χ SS cl (large₂ j La La') (Lg' j La La') (Ξ j La La')
  let F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p] :=
    fun j La La' => ((p : ℂ_[p]) ^ expG X j La La') •
      TaylorLogMetric.pSer D g.lam (fun z => scalG fd χ muT j La La' * G j La La' z)
  let Fr : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p] :=
    fun j La La' => Formalism.L2.KerInert.Rep.sclY (ltC g hLT) (F j La La')
  let S := fun j (La : X.Lt j) (La' : X.Lt (j + 1)) => Formalism.L2.KerInert.RepFrame.subGen X E pos fd.frM j La La'
  have hFam : FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₀ muT (ltC g hLT) =
      fun j La La' => Formalism.MainNotions.FormalGroupSystem.linSub (S j La La') (Fr j La La') := by
    funext j La La'
    have hS : S j La La' = subBG E.toCEmb pos fd j La La' :=
      funext fun x => funext fun y => (subBG_eq E pos fd j La La' x y).symm
    rw [hS]
    exact linSub_scl _ _ _

  have hB : BeProp p (beLT hLT) := Formalism.L2.KerInert.beProp_ofA Formalism.L2.KerInert.inert_facts_first_hold D cc δ p g hLT hAt h5 hIn hM
  have hComb0 : Formalism.L2.KerInert.RepLt.CombAtLt X hfin D large₂ Lg'
      (fun j La La' => TaylorLogMetric.pSer D g.lam (G j La La')) B.tor (B.eNat χ) g.lam :=
    Formalism.L2.KerInert.RepLt.combAtLt_of_dataRec X hfin D B χ SS cl g.lam hcc hδ
      (Formalism.L2.KerInert.AlgTP.algT_of B hcc hδ hχ) large₂ Lg' Ξ
      (Formalism.L2.KerInert.RepRec.dataRec_movD X D cl Ξ₀ (fun j La _ => fd.trG j La) (fun j _ La' => fd.trG (j + 1) La')
        ((Formalism.L2.KerInert.RepRec.dataRec_iff X D cl Ξ₀).2 ⟨hCl, hXi⟩)) hAdm
  have hComb : Formalism.L2.KerInert.RepLt.CombAtLt X hfin D large₂ Lg' F B.tor (B.eNat χ) g.lam :=
    Formalism.L2.KerInert.RepLt.combAtLt_scalar X hfin D large₂ Lg' B.tor (B.eNat χ) g.lam G
      (fun j La La' => scalG fd χ muT j La La') (fun j La La' => expG X j La La') hComb0 hSc
  have hOnb : Formalism.L2.KerInert.RepLt.OnbExLt X hfin D large₂ Lg' :=
    Formalism.L2.KerInert.RepLt.onbExLt_of X hfin D large₂ Lg'
      (Formalism.L2.KerInert.orthBasisExists_of Formalism.L2.KerInert.global_orthonormal_basis_four Formalism.L2.KerInert.weakApprox_of_approx_and_separation) h5 hIn hAdm
  have hTr : Formalism.L2.KerInert.RepLt.LamTraceLt X hfin D large₂ Lg' g.lam :=
    Formalism.L2.KerInert.RepLt.lamTraceLt_of X hfin D large₂ Lg' g.lam
      (Formalism.L2.KerInert.RepLt.rankTieLt_of X hfin D large₂ Lg' hAdm)
      (Formalism.L2.KerInert.RepFrame.colTie_of X hfin D large₂ Lg' (Formalism.L2.KerInert.RepFrame.trace_tau_sum D) g.lam)
  have hFH : Formalism.L2.KerInert.RepLt.FrameHypLt X E hfin D pos large₂ Lg' Fr S g.lam 1 :=
    Formalism.L2.KerInert.RepLt.frameHypLt_of_lat X E hfin D pos large₂ Lg' fd.frM g.lam ρ hOnb hTr hρ
      (Formalism.L2.KerInert.RepFrob.frobTw_of X E h5) hMI (twInt_all X E) hL Fr
  rw [hFam]
  exact Formalism.L2.KerInert.RepLt.K1_representatives_LT_of_dictionary Formalism.L2.KerInert.Rep.curve_dictionary Formalism.L2.KerInert.kernels_integral_inert D h5 X E
    hfin hLT cc δ hAt hIn hM B hcc hδ χ hχ hIn hLam pos large₂ Lg' F Fr
    (fun j La La' => by simp only [Fr]; rw [ltC_eq]) S hB hComb hFH

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in

theorem first_kernel_small_of_frame_twist (D : D7) (h5 : 5 ≤ p) (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (g : GL3Theta.G1 p) (hLT : LTIso g)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)
    (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (hAt : GL3Theta.At D cc δ g) (hIn : GL3Theta.InertK D p) (hM : GL3Theta.ModelOverW g.lam g.abelian₂ g.C)
    (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : TaylorLogMetric.IsChi D χ) (hLam : g.abelian₂ = B.tor.abelian₂)
    (hAdm : Formalism.L2.KerInert.RepLt.AdmGLt X hfin D fd) (hCl : Formalism.L2.KerInert.RepRec.ClAway p cl)
    (hXi : XiAwayLt X hfin D Ξ₀) (hSc : Formalism.L2.KerInert.RepLt.ScalGLt X hfin fd χ muT g.lam)
    (hρ : Formalism.L2.KerInert.RepFrame.LamPosG X E D pos g.lam ρ) (hMI : Formalism.L2.KerInert.RepFrame.MInv X fd.frM)
    (hL : Formalism.L2.KerInert.RepLt.FrameLatMapLt X fd.frM hfin D (fun j La _ => fd.kerN j La)
        (fun j _ La' => fd.kerN (j + 1) La') ρ) :
    Formalism.L2.KerInert.RepLt.FirstKernelLawLocalPowerSeries X E hfin (beLT hLT) pos (FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₀ muT (ltC g hLT)) := by
  classical
  let Ξ₁ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ :=
    fun j La La' => if j < X.mm ∧ La ∈ repOf X.Lv hfin j ∧ (X.Pj (j + 1)).IsLatTup La'.2 then Ξ₀ j La La' else fun _ => 0
  have hXi1 : Formalism.L2.KerInert.RepRec.XiAway X D Ξ₁ := by
    obtain ⟨S₀, hp, hS⟩ := hXi
    refine ⟨S₀, hp, fun j La La' y => ?_⟩
    by_cases h : j < X.mm ∧ La ∈ repOf X.Lv hfin j ∧ (X.Pj (j + 1)).IsLatTup La'.2
    · simp only [Ξ₁, if_pos h]
      exact hS j h.1 La h.2.1 La' h.2.2 y
    · simp only [Ξ₁, if_neg h]
      exact IntOff.zero
  have hK := first_kernel_small_of_frame D h5 X E hfin g hLT pos fd cc δ B χ SS cl Ξ₁ muT ρ hAt hIn hM hcc hδ hχ hLam
    hAdm hCl hXi1 hSc hρ hMI hL
  intro j hj L0 h0 La' hLa' φ
  have hEq : thFOf X pos (FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₁ muT (ltC g hLT)) j L0 La' =
      thFOf X pos (FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₀ muT (ltC g hLT)) j L0 La' := by
    simp only [thFOf, FrecG, Ξ₁, if_pos (And.intro hj (And.intro h0 hLa'))]
  have := hK j hj L0 h0 La' hLa' φ
  rwa [hEq] at this

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in

theorem first_kernel_law_global_small : TranslatesOfInertKernelAtPlace := by
  intro D p _ h5 X _ E hfin hst g hLT pos fd cc δ B χ lam SS cl Ξ₀ muT ρ hAt hIn hM hcc hδ hχ hlam hLam hAdm hCl hXi hSc
    hρ hMI hL
  subst hlam
  have hK := first_kernel_small_of_frame_twist D h5 X E hfin g hLT pos fd cc δ B χ SS cl Ξ₀ muT ρ hAt hIn hM hcc hδ hχ hLam hAdm hCl hXi hSc
    hρ hMI hL
  have h2b := (Formalism.L2.PairingIndexBounds.PowerSeriesNecessity.adm_two_pendant_iff_representative D X E hfin hst hLT pos _).2 hK
  exact ⟨Formalism.L2.KerInert.admissible_second_of_variant D X E hfin hst hLT pos _ h2b, h2b,
    Formalism.L2.KerInert.admissible_third_of_second_eleventh D X E hfin hst hLT pos _ h2b
      (Formalism.L2.KerInert.admissible_eleventh_inert D cc δ p g hLT hAt h5 hIn hM X _ rfl)⟩

end Formalism.L2.KerInert.KGLt
end
end
