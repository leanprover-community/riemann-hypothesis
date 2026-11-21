import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LatticeAreaPositivity.ThetaTranslationOperatorApply
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Th0TranslateProduct
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdChar
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.GoodModelLattice

section
noncomputable section
open scoped ComplexConjugate

namespace Formalism.L2.Th1.F2

open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem altE_twist (L : PeriodPair) (c x y : ℂ) (hc : c.re = 1 / 2) :
    F.altE L (c * x) y - F.altE L (c * y) x = F.altE L x y := by
  unfold F.altE F.herm
  simp only [Complex.div_ofReal_im, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, hc]
  ring

theorem altE_half (L : PeriodPair) (c x y : ℂ) : F.altE L (c * x) y = 2 * F.altE L (c * (x / 2)) y := by
  unfold F.altE F.herm
  simp only [Complex.div_ofReal_im]
  have : c * x * conj y = 2 * (c * (x / 2) * conj y) := by ring
  rw [this]
  simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

theorem not_all_killed (L : PeriodPair) (c : ℂ) (hc : c.re = 1 / 2) : ∃ x ∈ L.lattice, c * (x / 2) ∉ L.lattice := by
  by_contra h
  push_neg at h
  have h1 := h _ L.ω₁_mem_lattice
  have h2 := h _ L.ω₂_mem_lattice
  obtain ⟨k1, hk1⟩ := F.altEInt L _ _ h1 L.ω₂_mem_lattice
  obtain ⟨k2, hk2⟩ := F.altEInt L _ _ h2 L.ω₁_mem_lattice
  have h3 := altE_twist L c L.ω₁ L.ω₂ hc
  rw [altE_half L c L.ω₁, altE_half L c L.ω₂, hk1, hk2, F.altEBasis L] at h3
  split_ifs at h3
  · have : (2 * k1 - 2 * k2 : ℤ) = -1 := by exact_mod_cast h3
    omega
  · have : (2 * k1 - 2 * k2 : ℤ) = 1 := by exact_mod_cast h3
    omega

theorem two_torsion_off_kernels_exists : ExistsTwoTorsionOffKernels := by
  intro d L
  have hre : (F.cmTheta 1 d).re = 1 / 2 := by simp [F.cmTheta]
  have hre' : (1 - F.cmTheta 1 d).re = 1 / 2 := by rw [Complex.sub_re, hre]; norm_num
  obtain ⟨x, hx, hx1⟩ := not_all_killed L _ hre
  obtain ⟨y, hy, hy1⟩ := not_all_killed L _ hre'
  by_cases hx2 : (1 - F.cmTheta 1 d) * (x / 2) ∈ L.lattice
  · by_cases hy2 : F.cmTheta 1 d * (y / 2) ∈ L.lattice
    · refine ⟨x + y, add_mem hx hy, fun h => hx1 ?_, fun h => hy1 ?_⟩
      · have := sub_mem h hy2
        convert this using 1; ring
      · have := sub_mem h hx2
        convert this using 1; ring
    · exact ⟨y, hy, hy2, hy1⟩
  · exact ⟨x, hx, hx1, hx2⟩

theorem exp_pi_int (m : ℤ) : Complex.exp ((Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) = (-1 : ℂ) ^ m := by
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem cm_sign_eq_period_sign (d : ℕ) (L : PeriodPair) (hst : HasCM d L.lattice.toAddSubgroup) (x : ℂ) (hx : x ∈ L.lattice) :
    al1 d L.lattice.toAddSubgroup x = SC.aa L d x := by
  obtain ⟨m, hm⟩ := (SC.semi (L := L) (d := d) hst).1 x hx
  unfold al1 SC.aa
  rw [koszul_homology_eq, hm, exp_pi_int]
  have : Real.sqrt d / 2 * (F.herm L x x).re = (m : ℝ) := hm
  rw [this, round_intCast]

theorem theta_zero_witness_holds : ThetaZeroWitness := by
  intro d L ω₀ hd hst h0 hθ hθ'
  have hhalf : ω₀ / 2 ∉ L.lattice := SC.half_notMem (L := L) (d := d) hst h0 hθ hθ'
  obtain ⟨hdiff, hone, -, -, hq⟩ := F.th0Basic L ω₀ h0 hhalf
  refine ⟨hdiff, fun x hx z => ?_, hone⟩
  have hx' : x ∈ L.lattice := hx
  have hchar := SC.char_eq (L := L) (d := d) hst h0 hθ hθ' hd x hx'
  have hpm := (SC.semi (L := L) (d := d) hst).2.1 x hx'
  rw [cm_sign_eq_period_sign d L hst x hx', thetaTranslationOperator_apply]
  unfold F.opU
  rw [hq x hx' z]
  have hc : F.semiChar L x * Complex.exp ((Real.pi : ℂ) * Complex.I * (F.altE L x ω₀ : ℂ)) = SC.aa L d x := hchar.symm
  rw [hc]
  have hsq : SC.aa L d x * SC.aa L d x = 1 := by
    rcases hpm with h | h <;> rw [h] <;> norm_num
  have hexp : Complex.exp ((Real.pi : ℂ) * F.herm L z x + (Real.pi : ℂ) * F.herm L x x / 2)
      * Complex.exp (-(Real.pi : ℂ) * F.herm L z x - (Real.pi : ℂ) * F.herm L x x / 2) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    ring
  calc _ = (SC.aa L d x * SC.aa L d x) * (Complex.exp ((Real.pi : ℂ) * F.herm L z x + (Real.pi : ℂ) * F.herm L x x / 2)
      * Complex.exp (-(Real.pi : ℂ) * F.herm L z x - (Real.pi : ℂ) * F.herm L x x / 2)) * F.th0 L (ω₀ / 2) z := by ring
    _ = _ := by rw [hsq, hexp]; ring

theorem theta_zero_exists_holds : ThetaZeroExistence := by
  rintro d Λ hd ⟨L, rfl⟩ hst
  obtain ⟨ω₀, h0, hθ, hθ'⟩ := two_torsion_off_kernels_exists d L
  exact ⟨_, theta_zero_witness_holds d L ω₀ hd hst h0 hθ hθ'⟩

end Formalism.L2.Th1.F2
end
end

section
noncomputable section
open scoped ComplexConjugate Pointwise
open MeasureTheory

namespace Formalism.L2.Th1.F2

open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions

def dens (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) (z : ℂ) : ℝ := ‖G z‖ ^ 2 * Real.exp (-Real.pi * (H1 Λ z z).re)

theorem hermitian_form_re_eq (Λ : AddSubgroup ℂ) (z w : ℂ) : (H1 Λ z w).re = (z.re * w.re + z.im * w.im) / TaylorLogMetric.area Λ := by
  unfold H1
  rw [Complex.div_ofReal_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem norm_cm_sign_eq_one (d : ℕ) (Λ : AddSubgroup ℂ) (x : ℂ) : ‖al1 d Λ x‖ = 1 := by
  unfold al1
  rw [norm_zpow, norm_neg, norm_one, one_zpow]

theorem density_periodic_holds : DensityPeriodic := by
  intro d Λ G hG x hx z
  have h := congrArg norm (hG.2.1 x hx z)
  unfold U1 at h
  rw [norm_mul, norm_cm_sign_eq_one, one_mul, norm_mul, Complex.norm_exp] at h
  have hr : (-(Real.pi : ℂ) * H1 Λ z x - (Real.pi : ℂ) * H1 Λ x x / 2).re
      = -Real.pi * (H1 Λ z x).re - Real.pi / 2 * (H1 Λ x x).re := by
    have : (-(Real.pi : ℂ) * H1 Λ z x - (Real.pi : ℂ) * H1 Λ x x / 2)
        = ((-Real.pi : ℝ) : ℂ) * H1 Λ z x - ((Real.pi / 2 : ℝ) : ℂ) * H1 Λ x x := by push_cast; ring
    rw [this, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  rw [hr] at h
  rw [← h, mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  congr 2
  simp only [hermitian_form_re_eq, Complex.add_re, Complex.add_im]
  push_cast
  ring

theorem dens_continuous (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) (hG : Continuous G) : Continuous (dens Λ G) := by
  unfold dens
  simp only [hermitian_form_re_eq]
  fun_prop

theorem dens_nonneg (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) (z : ℂ) : 0 ≤ dens Λ G z := by
  unfold dens; positivity

theorem dens_vadd (d : ℕ) (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) (hG : IsTheta0 d Λ G) (g : Λ) (z : ℂ) :
    dens Λ G (g +ᵥ z) = dens Λ G z := by
  have : g +ᵥ z = z + (g : ℂ) := by rw [add_comm]; rfl
  rw [this]
  exact density_periodic_holds d Λ G hG g g.2 z

theorem fd0 (L : PeriodPair) :
    IsAddFundamentalDomain L.lattice.toAddSubgroup (ZSpan.fundamentalDomain L.basis) volume := by
  have h := ZSpan.isAddFundamentalDomain' L.basis (volume : Measure ℂ)
  rw [← L.lattice_eq_span_range_basis] at h
  exact h

theorem vol_real (L : PeriodPair) (Fd : Set ℂ) (h : IsAddFundamentalDomain L.lattice.toAddSubgroup Fd volume) :
    (volume : Measure ℂ).real Fd = F.area L := by
  rw [← F.areaCovolume L]
  exact (ZLattice.covolume_eq_measure_fundamentalDomain L.lattice volume h).symm

instance (L : PeriodPair) : Countable L.lattice.toAddSubgroup := (inferInstance : Countable L.lattice)

theorem density_integrable_fundDomain (L : PeriodPair) (G : ℂ → ℂ) (hG : Continuous G) :
    IntegrableOn (dens L.lattice.toAddSubgroup G) (ZSpan.fundamentalDomain L.basis) volume := by
  have hb := ZSpan.fundamentalDomain_isBounded L.basis
  exact ((dens_continuous _ G hG).continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure

theorem normSq1_eq (L : PeriodPair) (G : ℂ → ℂ) :
    ∃ Fd, IsAddFundamentalDomain L.lattice.toAddSubgroup Fd volume ∧
      normSq1 L.lattice.toAddSubgroup G = (F.area L)⁻¹ * ∫ z in Fd, dens L.lattice.toAddSubgroup G z := by
  have hs := Classical.epsilon_spec (p := fun Fd : Set ℂ => IsAddFundamentalDomain L.lattice.toAddSubgroup Fd volume) ⟨_, fd0 L⟩
  refine ⟨_, hs, ?_⟩
  unfold normSq1
  simp only
  rw [setAverage_eq, vol_real L _ hs, smul_eq_mul]
  rfl

theorem norm_any_holds : NormAny := by
  rintro d Λ G Fd ⟨L, rfl⟩ hG hFd
  have hv := vol_real L Fd hFd
  have hpos := F.areaPos L
  refine ⟨?_, ?_, ?_⟩
  · rw [area_eq_holds L, ← hv]
    refine (ENNReal.ofReal_toReal ?_).symm
    intro htop
    rw [Measure.real, htop, ENNReal.toReal_top] at hv
    exact absurd hv hpos.ne
  · exact (hFd.integrableOn_iff (fd0 L) (dens_vadd d _ G hG)).mpr (density_integrable_fundDomain L G hG.1.continuous)
  · obtain ⟨Fe, hFe, he⟩ := normSq1_eq L G
    rw [he, area_eq_holds L, hFe.setIntegral_eq hFd (dens_vadd d _ G hG)]
    rfl

theorem norm_pos_holds : NormPos := by
  rintro d Λ G ⟨L, rfl⟩ hG
  obtain ⟨-, hint, he⟩ := norm_any_holds d _ G _ ⟨L, rfl⟩ hG (fd0 L)
  rw [he]
  refine mul_pos (inv_pos.mpr (area_pos_lattice_holds _ ⟨L, rfl⟩)) ?_
  change 0 < ∫ z in ZSpan.fundamentalDomain L.basis, dens L.lattice.toAddSubgroup G z
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall (dens_nonneg _ G)) hint]
  rw [pos_iff_ne_zero]
  intro h0
  have hinv : ∀ g : L.lattice.toAddSubgroup, g +ᵥ Function.support (dens L.lattice.toAddSubgroup G)
      = Function.support (dens L.lattice.toAddSubgroup G) := by
    intro g
    ext x
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, Function.mem_support, Function.mem_support, dens_vadd d _ G hG]
  have hz := (fd0 L).measure_zero_of_invariant _ hinv h0
  have hopen : IsOpen (Function.support (dens L.lattice.toAddSubgroup G)) :=
    (dens_continuous _ G hG.1.continuous).isOpen_support
  have hne : (Function.support (dens L.lattice.toAddSubgroup G)).Nonempty := by
    refine ⟨0, ?_⟩
    rw [Function.mem_support]
    unfold dens
    rw [hG.2.2, norm_one, one_pow, one_mul]
    exact (Real.exp_pos _).ne'
  exact (hopen.measure_pos volume hne).ne' hz

end Formalism.L2.Th1.F2
end
end

section
noncomputable section

namespace Formalism.L2.Th1.F2

open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions


end Formalism.L2.Th1.F2
end
end
