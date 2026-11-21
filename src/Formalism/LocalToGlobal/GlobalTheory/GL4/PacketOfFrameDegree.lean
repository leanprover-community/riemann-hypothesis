import Formalism.LocalToGlobal.GlobalTheory.GL4.LowerSlopeInequalityFamily
import Formalism.LocalToGlobal.Columns.BrzoPairAtZeroRight
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Formalism.LocalToGlobal.Columns.MultiFactorialEqTripleProd
import Formalism.SharpRestriction.GlobalSchurBounds.SlopeMaxOpenOfHookTwoLeV
import Formalism.GL3MeanSquares.HookFormulaTorsion.ColumnParametrizationOffDiagonal
import Formalism.LocalToGlobal.Columns.MaxSlopeSummandOfFock
import Mathlib
import Formalism.LocalToGlobal.Columns.FockNormSubstitutionBound
import Formalism.LocalToGlobal.Columns.TwistedLocalisationComparable

section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps

theorem hTV0 (D : D7) (u : D.what₂.Word) : TSpan D.what₂.LL ((D.fm u).lam 0) = VV D.what₂.LL ((D.fm u).lam 0) :=
  translate_span_eq D.what₂.LL D.what₂.Tau (D.R.N 0) ((D.fm u).lam 0)

section Orth

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

open Classical in

def prjC (c : (D.mem u).C.cls 0) : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] ((D.fm u).lat 0).V :=
  ((coE CV (hTV0 D u)).symm : ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)) →ₗ[D.what₂.LL] ((D.fm u).lat 0).V) ∘ₗ
    (LinearMap.single D.what₂.LL (fun _ : (D.mem u).C.cls 0 => VV D.what₂.LL ((D.fm u).lam 0)) c ∘ₗ
      (LinearMap.proj c ∘ₗ (coE CV (hTV0 D u) : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)))))

open Classical in
theorem co_prjC (c c' : (D.mem u).C.cls 0) (x : ((D.fm u).lat 0).V) :
    CV.co (prjC CV c x) c' = if c' = c then CV.co x c else 0 := by
  have hE : ∀ (y : ((D.fm u).lat 0).V) (c'' : (D.mem u).C.cls 0),
      CV.co y c'' = ((coE CV (hTV0 D u) y c'' : VV D.what₂.LL ((D.fm u).lam 0)) : _) := fun _ _ => rfl
  have hP : coE CV (hTV0 D u) (prjC CV c x) = Pi.single c (coE CV (hTV0 D u) x c) := by
    simp [prjC]
  rw [hE, hP, hE x c]
  by_cases h : c' = c
  · subst h
    simp
  · simp [h]

private theorem coE_prjC_self (c : (D.mem u).C.cls 0) (x : ((D.fm u).lat 0).V) :
    coE CV (hTV0 D u) (prjC CV c x) c = coE CV (hTV0 D u) x c := by
  classical
  simp [prjC]

private theorem coE_prjC_of_ne_eq_zero (c c' : (D.mem u).C.cls 0) (x : ((D.fm u).lat 0).V) (h : c' ≠ c) :
    coE CV (hTV0 D u) (prjC CV c x) c' = 0 := by
  classical
  simp [prjC, h]

theorem prjC_sum (x : ((D.fm u).lat 0).V) : ∑ c, prjC CV c x = x := by
  apply (coE CV (hTV0 D u)).injective
  funext c'
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single c']
  · exact coE_prjC_self CV c' x
  · intro b _ hb
    exact coE_prjC_of_ne_eq_zero CV b c' x (Ne.symm hb)
  · intro h
    exact absurd (Finset.mem_univ _) h

def NC (c : (D.mem u).C.cls 0) : Submodule (𝓞 D.what₂.LL) ((D.fm u).lat 0).V :=
  ((D.fm u).lat 0).L.map ((prjC CV c).restrictScalars (𝓞 D.what₂.LL))

theorem prjC_mem (c : (D.mem u).C.cls 0) {x : ((D.fm u).lat 0).V} (hx : x ∈ ((D.fm u).lat 0).L) :
    prjC CV c x ∈ ((D.fm u).lat 0).L := by
  refine Formalism.L2.Ker.mem_of_forall_locP _ fun Q => ?_
  obtain ⟨w, rfl⟩ : ∃ w, D.plEq w = Q := ⟨D.plEq.symm Q, D.plEq.apply_symm_apply Q⟩
  rw [mem_localization_iff_localizationAtPlace]
  have hγ : ∀ c τ, ∃ γ, LocBasis D w (CV.Q c τ) (CV.eQ c τ) γ := fun c τ =>
    exists_locBasis w (CV.Q c τ) (CV.Q_good c τ) (CV.eQ c τ)
  choose γ hγ using hγ
  have hxw : x ∈ locW D.what₂.places w ((D.fm u).lat 0).L := Submodule.subset_span hx
  rw [CV.fin w γ hγ] at hxw
  rw [CV.fin w γ hγ]
  intro c'
  rw [co_prjC]
  split_ifs with h
  · subst h
    exact hxw c'
  · have e : actAll ((D.fm u).lam 0) (fun τ => (γ c' τ)⁻¹) (0 : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL) = 0 := by
      simp [actAll]
    rw [e]
    exact zero_mem _

theorem iSup_NC : (⨆ c, NC CV c) = ((D.fm u).lat 0).L := by
  apply le_antisymm
  · refine iSup_le fun c => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact prjC_mem CV c hx
  · intro x hx
    rw [← prjC_sum CV x]
    exact Submodule.sum_mem _ fun c _ => Submodule.mem_iSup_of_mem c ⟨x, hx, rfl⟩

theorem tcAt_eq_zero {v : InfinitePlace D.what₂.LL} {c : (D.mem u).C.cls 0} {x : ((D.fm u).lat 0).V} (h : CV.co x c = 0) :
    tcAt CV v c x = 0 := by
  simp [tcAt, h]

theorem NC_orth (c c' : (D.mem u).C.cls 0) (hcc : c ≠ c') :
    ∀ x ∈ NC CV c, ∀ y ∈ NC CV c', ∀ v, majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y = 0 := by
  rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ v
  simp only [LinearMap.restrictScalars_apply]
  rw [majorant_lattice_eq_sum CV]
  refine Finset.sum_eq_zero fun c'' _ => ?_
  by_cases h : c'' = c
  · subst h
    have : tcAt CV v c'' (prjC CV c' y) = 0 := tcAt_eq_zero CV (by rw [co_prjC, if_neg hcc])
    rw [this, nfAll_zero_left]
  · have : tcAt CV v c'' (prjC CV c x) = 0 := tcAt_eq_zero CV (by rw [co_prjC, if_neg h])
    rw [this, nfAll_zero_right]

theorem injOn_NC (c : (D.mem u).C.cls 0) {W : Type} [AddCommGroup W] [Module D.what₂.LL W]
    (ψ : VV D.what₂.LL ((D.fm u).lam 0) →ₗ[D.what₂.LL] W) (hψ : Function.Injective ψ) :
    Set.InjOn (ψ ∘ₗ (LinearMap.proj c ∘ₗ (coE CV (hTV0 D u) : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0))))) (NC CV c) := by
  rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ hxy
  have h := hψ hxy
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
    LinearMap.coe_proj, Function.eval] at h ⊢
  apply (coE CV (hTV0 D u)).injective
  funext c'
  by_cases hc : c' = c
  · subst hc
    exact h
  · rw [coE_prjC_of_ne_eq_zero CV c c' x hc, coE_prjC_of_ne_eq_zero CV c c' y hc]

end Orth

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps

section Rank

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem vv_finite_pos (D : D7) (u : D.what₂.Word) :
    Module.Finite D.what₂.LL (VV D.what₂.LL ((D.fm u).lam 0)) ∧ 0 < finrank D.what₂.LL (VV D.what₂.LL ((D.fm u).lam 0)) := by
  obtain ⟨Z, -, hne, -, -⟩ := standard_basis_z D.what₂.Tau (D.R.N 0) ((D.fm u).lam 0)
  have := Z.fin
  exact ⟨Module.Finite.of_basis (Z.basis D.what₂.LL), by rw [Module.finrank_eq_card_basis (Z.basis D.what₂.LL)]; exact Fintype.card_pos⟩

theorem range_prjC (c : (D.mem u).C.cls 0) :
    finrank D.what₂.LL (LinearMap.range (prjC CV c)) = finrank D.what₂.LL (VV D.what₂.LL ((D.fm u).lam 0)) := by
  classical
  have hsurj : LinearMap.range (LinearMap.proj c ∘ₗ (coE CV (hTV0 D u) : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)))) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro z
    refine ⟨(coE CV (hTV0 D u)).symm (Pi.single c z), ?_⟩
    simp
  unfold prjC
  rw [← LinearMap.comp_assoc, LinearMap.range_comp_of_range_eq_top _ hsurj]
  apply LinearMap.finrank_range_of_inj
  rw [LinearMap.coe_comp]
  exact (coE CV (hTV0 D u)).symm.injective.comp (by simpa using Pi.single_injective c)

theorem rk_NC (c : (D.mem u).C.cls 0) : rkK (NC CV c) = finrank D.what₂.LL (VV D.what₂.LL ((D.fm u).lam 0)) := by
  unfold Formalism.HN.rkK NC
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, ((D.fm u).lat_good 0).2.2, Submodule.map_top]
  exact range_prjC CV c

theorem rank_lattice_level_zero (CV : ColVal D u) : rkK ((D.fm u).lat 0).L =
    Fintype.card ((D.mem u).C.cls 0) * finrank D.what₂.LL (VV D.what₂.LL ((D.fm u).lam 0)) := by
  obtain ⟨hfin, -⟩ := vv_finite_pos D u
  unfold Formalism.HN.rkK
  rw [((D.fm u).lat_good 0).2.2, finrank_top, LinearEquiv.finrank_eq (coE CV (hTV0 D u)), Module.finrank_pi_fintype,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem NC_ne_bot (c : (D.mem u).C.cls 0) : NC CV c ≠ ⊥ := by
  intro h0
  have h1 := rk_NC CV c
  rw [h0] at h1
  have h2 : Formalism.HN.rkK (⊥ : Submodule (𝓞 D.what₂.LL) ((D.fm u).lat 0).V) = 0 := by
    unfold Formalism.HN.rkK
    rw [Submodule.bot_coe, Submodule.span_zero_singleton, finrank_bot]
  have := (vv_finite_pos D u).2
  omega

theorem muMax_le_class : ∃ c, ((D.fm u).lat 0).muMax ≤ (withL ((D.fm u).lat 0) (NC CV c)).muMax := by
  classical
  have : Nonempty ((D.mem u).C.cls 0) := CV.ne
  have key := Formalism.L2.Col.hlat_orth_sum (A := (D.fm u).lat 0) (NC CV) ((D.fm u).lat_good 0).1
    (fun c => ((D.fm u).lat_good 0).2.1.map _) (NC_ne_bot CV) (NC_orth CV)
    (finrank D.what₂.LL (VV D.what₂.LL ((D.fm u).lam 0))) (vv_finite_pos D u).2 (rk_NC CV)
    (by rw [iSup_NC CV]; exact rank_lattice_level_zero CV)
  obtain ⟨c, hc⟩ := key.2
  rw [iSup_NC CV] at hc
  exact ⟨c, hc⟩

end Rank

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SlopeMaxClass (D : D7) : Prop :=
  ∀ u (CV : ColVal D u) (c : (D.mem u).C.cls 0), (∃ y : Fin (D.R.N 0) → (D.sp.X 0).V, Formalism.MainNotions.flipTwoThree.ShortAt D u c y) →
    (withL ((D.fm u).lat 0) (NC CV c)).muMax ≤
      ∑ τ, (colAbsP D u τ * Real.log (4 * (D.R.k : ℝ) ^ 4 * D.host.v ^ 2) +
        Real.log (cNu ((D.fm u).lam 0 τ).natW) - (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u))

theorem slopeMaxGiven_of_class (D : D7) (h : SlopeMaxClass D) : SlopeMaxGiven D := by
  intro u CV hs
  obtain ⟨c, hc⟩ := muMax_le_class CV
  exact hc.trans (h u CV c (hs c))




end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
open MvPolynomial

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.L2.Col Formalism.MainNotions.flipTwoThree Formalism.L2.DIV

section Mono

variable {ι : Type} [Fintype ι] {n : ℕ}

private theorem map_algebraMap_rat_complex_hw {N : ℕ} (ν : Fin N → ℕ) :
    MvPolynomial.map (algebraMap ℚ ℂ) (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) ν) = Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν := by
  unfold Formalism.GradedWeylDivisibility.hw Formalism.GradedWeylDivisibility.lpMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext p q
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.map_X]

theorem fockN_ext_cNu (lam : DomWeight n) :
    fockN (extremal ℂ n lam) = cNu lam.natW * ∏ s, ((lam.natW s).factorial : ℝ) := by
  have hprod : (∏ s, ((lam.natW s).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun s _ => by exact_mod_cast (Nat.factorial_pos _).ne'
  unfold extremal cNu
  rw [← map_algebraMap_rat_complex_hw, Formalism.L2.Col.fock_norm_rational_eq, div_mul_cancel₀ _ hprod]

theorem cNu_natW_pos (lam : DomWeight n) : 0 < cNu lam.natW := by
  have hnn : (0 : ℚ) ≤ Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl lam.natW) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl lam.natW) := by
    unfold Formalism.GradedWeylDivisibility.fockQ
    exact Finset.sum_nonneg fun m _ => mul_nonneg (mul_self_nonneg _) (Nat.cast_nonneg _)
  have hpos : (0 : ℚ) < Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl lam.natW) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl lam.natW) :=
    lt_of_le_of_ne hnn (Formalism.L2.DIV.we_hw_norm_ne le_rfl lam.natW).symm
  unfold cNu
  apply div_pos
  · exact_mod_cast hpos
  · exact Finset.prod_pos fun s _ => by exact_mod_cast Nat.factorial_pos _

def monCnu (lam : ι → DomWeight n) : ℝ := ((n : ℝ) ^ (∑ τ, dW (lam τ)) * ∏ τ, cNu (lam τ).natW)⁻¹

private theorem sub_one_mul_padicValNat_factorial_le' {n : ℕ} (g : Fin n → ℕ) :
    (∑ a, g a).factorial ≤ n ^ (∑ a, g a) * ∏ a, (g a).factorial := by
  classical
  have hmul := Nat.multinomial_spec Finset.univ g
  have hle : Nat.multinomial Finset.univ g ≤ n ^ (∑ a, g a) := by
    have h := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin n)) (fun _ => (1 : ℕ)) (∑ a, g a)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, one_pow,
      Finset.prod_const_one, Nat.cast_id] at h
    rw [h]
    apply Finset.single_le_sum (f := fun k => Nat.multinomial Finset.univ k) (fun _ _ => Nat.zero_le _)
    rw [Finset.mem_piAntidiag]
    exact ⟨rfl, fun i _ => Finset.mem_univ i⟩
  calc (∑ a, g a).factorial = (∏ a, (g a).factorial) * Nat.multinomial Finset.univ g := hmul.symm
    _ ≤ (∏ a, (g a).factorial) * n ^ (∑ a, g a) := Nat.mul_le_mul_left _ hle
    _ = _ := mul_comm _ _

theorem monW_ge_cNu (lam : ι → DomWeight n) (m : MonI lam) : monCnu lam ≤ monW lam m := by
  classical
  have hC : 0 < ∏ τ, cNu (lam τ).natW := Finset.prod_pos fun τ _ => cNu_natW_pos (lam τ)
  have hF : (0 : ℝ) < ∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ) :=
    Finset.prod_pos fun τ _ => Finset.prod_pos fun s _ => by exact_mod_cast Nat.factorial_pos _
  have hND : (0 : ℝ) < (n : ℝ) ^ (∑ τ, dW (lam τ)) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [dW]
    · exact pow_pos (by exact_mod_cast hn) _
  have hext : extremalFockNormProduct lam = (∏ τ, cNu (lam τ).natW) * ∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ) := by
    unfold extremalFockNormProduct
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => fockN_ext_cNu (lam τ)
  have hcombN : ∏ τ, ∏ s, ((lam τ).natW s).factorial ≤ Formalism.L2.DIV.mfact m.1 * n ^ (∑ τ, dW (lam τ)) := by
    have hmf : Formalism.L2.DIV.mfact m.1 = ∏ τ, ∏ s, ∏ a, (m.1 (τ, a, s)).factorial := by
      unfold Formalism.L2.DIV.mfact
      rw [Finset.prod_subset (Finset.subset_univ _) (fun k _ hk => by
        rw [show m.1 k = 0 from by simpa using hk, Nat.factorial_zero])]
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [Fintype.prod_prod_type, Finset.prod_comm]
    have hpow : n ^ (∑ τ, dW (lam τ)) = ∏ τ, ∏ s, n ^ ((lam τ).natW s) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun τ _ => ?_
      unfold dW
      rw [← Finset.prod_pow_eq_pow_sum]
    rw [hmf, hpow, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    intro τ _
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    intro s _
    have h := sub_one_mul_padicValNat_factorial_le' (fun a => m.1 (τ, a, s))
    rw [m.2 τ s] at h
    exact h.trans (le_of_eq (mul_comm _ _))
  have hcomb : (∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ)) ≤
      (Formalism.L2.DIV.mfact m.1 : ℝ) * (n : ℝ) ^ (∑ τ, dW (lam τ)) := by
    exact_mod_cast hcombN
  unfold monCnu monW
  rw [hext, inv_eq_one_div, div_le_div_iff₀ (mul_pos hND hC) (mul_pos hC hF)]
  calc 1 * ((∏ τ, cNu (lam τ).natW) * ∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ))
      = (∏ τ, cNu (lam τ).natW) * ∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ) := one_mul _
    _ ≤ (∏ τ, cNu (lam τ).natW) * ((Formalism.L2.DIV.mfact m.1 : ℝ) * (n : ℝ) ^ (∑ τ, dW (lam τ))) :=
      mul_le_mul_of_nonneg_left hcomb hC.le
    _ = _ := by ring

theorem monCnu_pos (lam : ι → DomWeight n) : 0 < monCnu lam := by
  unfold monCnu
  apply inv_pos.mpr
  apply mul_pos
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [dW]
    · exact pow_pos (by exact_mod_cast hn) _
  · exact Finset.prod_pos fun τ _ => cNu_natW_pos (lam τ)

theorem log_monCnu (lam : ι → DomWeight n) (hn : 0 < n) :
    -Real.log (monCnu lam) = ∑ τ, ((dW (lam τ) : ℝ) * Real.log n + Real.log (cNu (lam τ).natW)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : ∀ τ, cNu (lam τ).natW ≠ 0 := fun τ => (cNu_natW_pos (lam τ)).ne'
  unfold monCnu
  rw [Real.log_inv, neg_neg, Real.log_mul (pow_ne_zero _ hn'.ne') (Finset.prod_ne_zero_iff.mpr fun τ _ => hc τ),
    Real.log_pow, Real.log_prod (fun τ _ => hc τ), Finset.sum_add_distrib]
  push_cast
  rw [Finset.sum_mul]

end Mono

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.L2.Forms Formalism.L2.Col

section Gen

variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

theorem muMax_le_mon {V κ : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype κ] [DecidableEq κ]
    (b : Basis κ K V) (X : InfinitePlace K → Matrix κ κ ℂ) (hX : ∀ v, IsUnit (X v).det)
    (N : Submodule (𝓞 K) V) (hN : N.FG) (φ : V →ₗ[K] (MonI lam → K)) (hinj : Set.InjOn φ N)
    (hne : N.map (φ.restrictScalars (𝓞 K)) ≠ ⊥)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI0 : I ≠ 0)
    (hint : ∀ x ∈ N, ∀ m, φ x m ∈ (I : Submodule (𝓞 K) K))
    (B : InfinitePlace K → ℝ) (hB : ∀ v, 0 < B v)
    (hnorm : ∀ v x, normAt (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) v (φ x) ^ 2 ≤ B v * normAt b X v x ^ 2)
    (c0 : ℝ) (hc0 : 0 < c0) (hc : ∀ m, c0 ≤ monW lam m) :
    muMaxDef b X N ≤ -Real.log c0 - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ)
      + (1 / (nPl K : ℝ)) * ∑ v, Real.log (B v) := by
  have hX' : ∀ v : InfinitePlace K, IsUnit ((fun _ : InfinitePlace K => (monD lam)⁻¹) v).det :=
    fun v => (Matrix.isUnit_nonsing_inv_det_iff).mpr (monD_det lam)
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    apply hne
    rw [eq_bot_iff]
    rintro y hy
    obtain ⟨x, -, rfl⟩ := Submodule.mem_map.mp hy
    simp
  obtain ⟨L0, hL0⟩ : ∃ L0 : Submodule (𝓞 K) (MonI lam → K),
      L0 = ⨆ m ∈ (Finset.univ : Finset (MonI lam)), (𝓞 K ∙ (Pi.single m (1 : K) : MonI lam → K)) := ⟨_, rfl⟩
  have hmemL0 : ∀ m, (Pi.single m (1 : K) : MonI lam → K) ∈ L0 := fun m => by
    rw [hL0]
    exact Submodule.mem_iSup_of_mem m (Submodule.mem_iSup_of_mem (Finset.mem_univ m)
      (Submodule.mem_span_singleton_self _))
  have hmapT : N.map (φ.restrictScalars (𝓞 K)) ≤ idealSmul (I : Submodule (𝓞 K) K) L0 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    have hdec : φ x = ∑ m, (φ x m) • (Pi.single m (1 : K) : MonI lam → K) := by
      ext m'
      simp [Finset.sum_apply, Pi.single_apply]
    show φ x ∈ _
    rw [hdec]
    exact Submodule.sum_mem _ fun m _ => Formalism.LFunctionChainParameters.slopeLatticeData.mem_idealSmul (hint x hx m) (hmemL0 m)
  have horth : ∀ s t : MonI lam, s ≠ t → Formalism.BranchingDeterminantCap.OrthAt (Pi.basisFun K (MonI lam))
      (fun _ : InfinitePlace K => (monD lam)⁻¹) (𝓞 K ∙ (Pi.single s (1 : K) : MonI lam → K))
      (𝓞 K ∙ (Pi.single t (1 : K) : MonI lam → K)) := by
    intro s t hst v x hx y hy
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨r', rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp only [majAt, monH_fcoord]
    apply Finset.sum_eq_zero
    intro m _
    by_cases hm : m = s
    · subst hm
      simp [Pi.single_apply, hst]
    · simp [Pi.single_apply, hm]
  have hline : ∀ m, muMaxDef (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹)
      (𝓞 K ∙ (Pi.single m (1 : K) : MonI lam → K)) ≤ -Real.log c0 := by
    intro m
    refine max_slope_line_neg_log _ _ hX' _ ?_ c0 hc0 fun v => ?_
    · simp
    · rw [monH_norm, Finset.sum_eq_single m (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
      simpa using hc m
  have hmain := Formalism.BranchingDeterminantCap.OrthogonalSumAlt.main (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) hX'
    (fun m => 𝓞 K ∙ (Pi.single m (1 : K) : MonI lam → K)) (fun m => Submodule.fg_span_singleton _) horth
    Finset.univ
  rw [← hL0] at hmain
  have hL0ne : L0 ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, -, rfl⟩ := Submodule.mem_map.mp hy
    have h1 : ∀ m, (Pi.single m (1 : K) : MonI lam → K) = 0 := fun m => by
      have := hmemL0 m
      rwa [h, Submodule.mem_bot] at this
    rw [Submodule.mem_bot]
    funext m
    exact absurd (h1 m) (by simp)
  have hL0mu : muMaxDef (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) L0 ≤ -Real.log c0 := by
    have h2 := hmain.2.2.2 ((-Real.log c0 - slopeNormalisingConstant K) / 2) (fun m _ _ => by
      have := hline m
      rw [frameB_muMaxDef] at this
      linarith) hL0ne
    rw [frameB_muMaxDef]
    linarith
  have hT := Formalism.LFunctionChainParameters.slopeLatticeData.muMaxDef_fractional_le (Pi.basisFun K (MonI lam))
    (fun _ : InfinitePlace K => (monD lam)⁻¹) hX' hmain.1 hL0ne hI0
  have hS := ((Formalism.HN.slopeIneqMean K V κ (MonI lam → K) (MonI lam) b X (Pi.basisFun K (MonI lam))
    (fun _ : InfinitePlace K => (monD lam)⁻¹) hX hX' φ N hN hne).2 (idealSmul (I : Submodule (𝓞 K) K) L0)
    (Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_fg I hmain.1) hmapT).2 hinj
  have hht : htMap b X (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) φ ≤
      1 / (nPl K : ℝ) * ∑ v, Real.log (B v) := by
    unfold htMap
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro v _
    have hpos := Formalism.HN.PlaceOperatorNorms.opNormAt_pos b X (Pi.basisFun K (MonI lam))
      (fun _ : InfinitePlace K => (monD lam)⁻¹) hX hX' v φ hφ0
    have hle : opNormAt b X (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) v φ ≤ √(B v) := by
      apply Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points b X _ _ hX φ v _ (Real.sqrt_nonneg _)
      intro f
      have h0 : 0 ≤ normAt (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) v (φ f) :=
        Real.sqrt_nonneg _
      have h1 : 0 ≤ normAt b X v f := Real.sqrt_nonneg _
      have := Real.sqrt_le_sqrt (hnorm v f)
      rwa [Real.sqrt_sq h0, Real.sqrt_mul (hB v).le, Real.sqrt_sq h1] at this
    apply Real.log_le_log (by positivity)
    calc opNormAt b X (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) v φ ^ 2
        ≤ √(B v) ^ 2 := pow_le_pow_left₀ hpos.le hle 2
      _ = B v := Real.sq_sqrt (hB v).le
  linarith [hS, hT, hL0mu, hht]

end Gen

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
open NumberField

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree Formalism.HN

theorem trace_re_sum (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ w : InfinitePlace E, 2 * (w.embedding z).re := by
  classical
  have h1 : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ φ : E →+* ℂ, φ z := by
    have h : algebraMap ℚ ℂ (Algebra.trace ℚ E z) = ∑ σ : E →ₐ[ℚ] ℂ, σ z := by
      first
      | exact trace_eq_sum_embeddings ℂ (x := z)
      | exact trace_eq_sum_embeddings (E := ℂ) (x := z)
      | exact trace_eq_sum_embeddings (F := ℂ) (x := z)
      | exact (trace_eq_sum_embeddings ℂ : _)
    rw [show ((Algebra.trace ℚ E z : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E z) from
      (eq_ratCast _ _).symm, h]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ z)
      (fun σ : E →ₐ[ℚ] ℂ => σ z) (fun _ => rfl)).symm
  have h2 : ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ φ : E →+* ℂ, (φ z).re := by
    rw [← Complex.re_sum, ← h1, Complex.ratCast_re]
  rw [h2, ← Finset.sum_fiberwise Finset.univ (fun φ : E →+* ℂ => InfinitePlace.mk φ)
    (fun φ : E →+* ℂ => (φ z).re)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hfib : ∀ φ ∈ Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w),
      (φ z).re = (w.embedding z).re := by
    intro φ hφ
    have hw := (Finset.mem_filter.mp hφ).2
    subst hw
    rcases InfinitePlace.embedding_mk_eq φ with h | h
    · rw [h]
    · rw [h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]
  have hm : w.mult = 2 := InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩
  rw [hm]
  norm_num

theorem two_nPl (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] : 2 * nPl E = Module.finrank ℚ E := by
  classical
  rw [← InfinitePlace.sum_mult_eq]
  have h : ∀ w : InfinitePlace E, w.mult = 2 := fun w =>
    InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  unfold nPl
  ring

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private lemma sum_log_le_card_mul_log_mean_of_pos {ι : Type*} [Fintype ι] (S : ι → ℝ) (hS : ∀ i, 0 < S i)
    (hn : 0 < (Fintype.card ι : ℝ)) :
    ∑ i, Real.log (S i) ≤ (Fintype.card ι : ℝ) * Real.log ((∑ i, S i) / Fintype.card ι) := by
  have hT : 0 < ∑ i, S i := by
    have : Nonempty ι := Fintype.card_pos_iff.mp (by exact_mod_cast hn)
    exact Finset.sum_pos (fun i _ => hS i) Finset.univ_nonempty
  set M := (∑ i, S i) / (Fintype.card ι : ℝ) with hM
  have hMpos : 0 < M := div_pos hT hn
  have h1 : ∀ i, Real.log (S i) - Real.log M ≤ S i / M - 1 := by
    intro i
    rw [← Real.log_div (hS i).ne' hMpos.ne']
    exact Real.log_le_sub_one_of_pos (div_pos (hS i) hMpos)
  have h2 : ∑ i, (Real.log (S i) - Real.log M) ≤ ∑ i, (S i / M - 1) :=
    Finset.sum_le_sum fun i _ => h1 i
  have h3 : (∑ i, S i) / M = (Fintype.card ι : ℝ) := by
    have := hT.ne'
    have := hn.ne'
    rw [hM]
    field_simp
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, h3, Finset.sum_const,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, mul_one] at h2
  linarith

theorem shortAt_mean_log (D : D7) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) [IsTotallyComplex D.host.E]
    (y : Fin (D.R.N 0) → (D.sp.X 0).V) (hy : Formalism.MainNotions.flipTwoThree.ShortAt D u c y)
    (hpos : ∀ (w : InfinitePlace D.host.E) a, 0 < (w.embedding ((D.sp.X 0).hT (y a) (y a))).re) :
    (∑ w : InfinitePlace D.host.E, Real.log (∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re)) / (nPl D.host.E : ℝ) ≤
      Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) := by
  classical
  obtain ⟨-, -, htr⟩ := hy
  have hk : D.R.N 0 = D.R.k := Formalism.BasicNotions.Ranks.N_zero D.R
  have hfin := Formalism.MainNotions.flipTwoThree.b_finrank_host D
  have hnf : nPl D.host.E = D.R.f := by
    have h2 := two_nPl D.host.E
    rw [hfin] at h2
    omega
  have hfo : D.R.f = 2 * D.R.ord := by
    first
    | exact Formalism.BasicNotions.Ranks.f_eq_ord
    | exact Formalism.BasicNotions.Ranks.f_eq_ord D.R
    | exact Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)
  have hf : 0 < D.R.f := by
    have := D.R.m_le_f
    have := D.R.two_le_m
    omega
  have hfR : (0 : ℝ) < D.R.f := by exact_mod_cast hf
  have hbound : ∀ a, ∑ w : InfinitePlace D.host.E, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re ≤
      (D.R.f : ℝ) * ((D.R.k : ℝ) ^ 2 * (2 * D.host.v) ^ 2) := by
    intro a
    have h := htr a
    rw [trace_re_sum, div_le_iff₀ (by linarith), ← Finset.mul_sum] at h
    nlinarith [h]
  have hS : ∀ w : InfinitePlace D.host.E, 0 < ∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re := by
    intro w
    have hne : (Finset.univ : Finset (Fin (D.R.N 0))).Nonempty := by
      refine ⟨⟨0, ?_⟩, Finset.mem_univ _⟩
      rw [hk]
      have := D.R.m_add_three_le_k
      omega
    exact Finset.sum_pos (fun a _ => hpos w a) hne
  have htot : ∑ w : InfinitePlace D.host.E, ∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re ≤
      (D.R.k : ℝ) * ((D.R.f : ℝ) * ((D.R.k : ℝ) ^ 2 * (2 * D.host.v) ^ 2)) := by
    rw [Finset.sum_comm]
    calc _ ≤ ∑ _a : Fin (D.R.N 0), (D.R.f : ℝ) * ((D.R.k : ℝ) ^ 2 * (2 * D.host.v) ^ 2) :=
          Finset.sum_le_sum fun a _ => hbound a
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hk, nsmul_eq_mul]
  have hcard : (nPl D.host.E : ℝ) = (Fintype.card (InfinitePlace D.host.E) : ℝ) := rfl
  have hcf : (Fintype.card (InfinitePlace D.host.E) : ℝ) = D.R.f := by
    rw [← hcard]
    exact_mod_cast hnf
  have hnpos : (0 : ℝ) < (Fintype.card (InfinitePlace D.host.E) : ℝ) := by rw [hcf]; exact hfR
  have key := sum_log_le_card_mul_log_mean_of_pos _ hS hnpos
  have hTpos : 0 < ∑ w : InfinitePlace D.host.E, ∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re :=
    Finset.sum_pos (fun w _ => hS w)
      (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by exact_mod_cast hnpos)))
  rw [hcard, div_le_iff₀ hnpos]
  refine key.trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ hnpos.le
  apply Real.log_le_log (div_pos hTpos hnpos)
  rw [div_le_iff₀ hnpos, hcf]
  nlinarith [htot]

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ClassMap (D : D7) : Prop :=
  ∀ u (CV : ColVal D u) (c : (D.mem u).C.cls 0), (∃ y : Fin (D.R.N 0) → (D.sp.X 0).V, Formalism.MainNotions.flipTwoThree.ShortAt D u c y) →
    ∃ (φ : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] (MonI ((D.fm u).lam 0) → D.what₂.LL))
      (I : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) (B : InfinitePlace D.what₂.LL → ℝ),
      Set.InjOn φ (NC CV c) ∧ I ≠ 0 ∧ (∀ x ∈ NC CV c, ∀ m, φ x m ∈ (I : Submodule (𝓞 D.what₂.LL) D.what₂.LL)) ∧ (∀ v, 0 < B v) ∧
      (∀ v x, normAt (Pi.basisFun D.what₂.LL (MonI ((D.fm u).lam 0))) (fun _ => (monD ((D.fm u).lam 0))⁻¹) v (φ x) ^ 2 ≤
        B v * normAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x ^ 2) ∧
      -(2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ D.what₂.LL : ℝ)) +
          (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (B v) ≤
        ∑ τ, (colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) - (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u))

theorem slopeMaxClass_of_map (D : D7) (h : ClassMap D) : SlopeMaxClass D := by
  intro u CV c hy
  have := (columnHypotheses D u).tc
  obtain ⟨φ, I, B, hinj, hI0, hint, hB, hnorm, hnum⟩ := h u CV c hy
  have hne : (NC CV c).map (φ.restrictScalars (𝓞 D.what₂.LL)) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (NC_ne_bot CV c)
    intro h0
    have hm : φ.restrictScalars (𝓞 D.what₂.LL) x ∈ (NC CV c).map (φ.restrictScalars (𝓞 D.what₂.LL)) := ⟨x, hx, rfl⟩
    rw [h0, Submodule.mem_bot] at hm
    exact hx0 (hinj hx (zero_mem _) (by rw [map_zero]; exact hm))
  have hm := muMax_le_mon D.what₂.LL ((D.fm u).lam 0) ((D.fm u).lat 0).b ((D.fm u).lat 0).X ((D.fm u).lat_good 0).1 (NC CV c)
    (((D.fm u).lat_good 0).2.1.map _) φ hinj hne I hI0 hint B hB hnorm (monCnu ((D.fm u).lam 0))
    (monCnu_pos _) (monW_ge_cNu _)
  have hl := log_monCnu ((D.fm u).lam 0) (rank_zero_pos D)
  rw [hl] at hm
  have hdW : ∀ τ, (dW ((D.fm u).lam 0 τ) : ℝ) = colAbsP D u τ := fun τ => by
    unfold dW
    push_cast
    exact sum_natWeight_eq_colAbsShifted D u τ
  have hN : ((D.R.N 0 : ℕ) : ℝ) = (D.R.k : ℝ) := by rw [Ranks.N_zero]
  simp only [hdW, hN] at hm
  have hk : (0 : ℝ) < D.R.k := by exact_mod_cast columnCount_pos D
  have hv : (0 : ℝ) < D.host.v := by have := two_le_half_rootDiscr D; linarith
  have hR : (∑ τ, (colAbsP D u τ * Real.log (4 * (D.R.k : ℝ) ^ 4 * D.host.v ^ 2) +
        Real.log (cNu ((D.fm u).lam 0 τ).natW) - (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u))) =
      (∑ τ, (colAbsP D u τ * Real.log (D.R.k : ℝ) + Real.log (cNu ((D.fm u).lam 0 τ).natW))) +
      ∑ τ, (colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) - (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u)) := by
    have e4 : Real.log (4 * (D.R.k : ℝ) ^ 4 * D.host.v ^ 2) =
        Real.log (D.R.k : ℝ) + Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) := by
      rw [← Real.log_mul hk.ne' (by positivity)]
      congr 1
      ring
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [e4]
    ring
  show muMaxDef ((D.fm u).lat 0).b ((D.fm u).lat 0).X (NC CV c) ≤ _
  rw [hR]
  linarith


end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem shortAt_pos (D : D7) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V)
    (hy : Formalism.MainNotions.flipTwoThree.ShortAt D u c y) (w : InfinitePlace D.host.E) (a : Fin (D.R.N 0)) :
    0 < (w.embedding ((D.sp.X 0).hT (y a) (y a))).re := by
  obtain ⟨r, hr, he⟩ := (columnHypotheses D u).pos w.embedding (y a) (hy.2.1.ne_zero a)
  rw [he, Complex.ofReal_re]
  exact hr

def ClassMapT (D : D7) : Prop :=
  ∀ u (CV : ColVal D u) (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V), Formalism.MainNotions.flipTwoThree.ShortAt D u c y →
    ∃ (φ : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] (MonI ((D.fm u).lam 0) → D.what₂.LL))
      (I : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) (Dv : InfinitePlace D.what₂.LL → ℝ),
      Set.InjOn φ (NC CV c) ∧ I ≠ 0 ∧ (∀ x ∈ NC CV c, ∀ m, φ x m ∈ (I : Submodule (𝓞 D.what₂.LL) D.what₂.LL)) ∧ (∀ v, 0 < Dv v) ∧
      (∀ v x, normAt (Pi.basisFun D.what₂.LL (MonI ((D.fm u).lam 0))) (fun _ => (monD ((D.fm u).lam 0))⁻¹) v (φ x) ^ 2 ≤
        ((∏ τ, (∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re) ^ dW ((D.fm u).lam 0 τ)) * Dv v) *
          normAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x ^ 2) ∧
      -(2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ D.what₂.LL : ℝ)) +
          (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (Dv v) ≤
        -∑ τ, (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u)

theorem class_map_of_archimedean (D : D7) (h : ClassMapT D) : ClassMap D := by
  intro u CV c hy
  obtain ⟨y, hy⟩ := hy
  have := (columnHypotheses D u).tc
  have := (columnHypotheses D u).tcE
  have hposE := shortAt_pos D u c y hy
  obtain ⟨φ, I, Dv, hinj, hI0, hint, hD, hnorm, hnum⟩ := h u CV c y hy
  set G : InfinitePlace D.what₂.LL → D.what₂.Tau → ℝ := fun v τ => ∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re with hG
  have hN0 : 0 < D.R.N 0 := rank_zero_pos D
  have hGc : ∀ v τ, G v τ = ∑ a, ((v.comap (CV.rho τ)).embedding ((D.sp.X 0).hT (y a) (y a))).re := fun v τ =>
    Finset.sum_congr rfl fun a _ => (re_comap (CV.rho τ) v _).symm
  have hGpos : ∀ v τ, 0 < G v τ := fun v τ => by
    rw [hGc]
    exact Finset.sum_pos (fun a _ => hposE _ a) ⟨⟨0, hN0⟩, Finset.mem_univ _⟩
  refine ⟨φ, I, fun v => (∏ τ, G v τ ^ dW ((D.fm u).lam 0 τ)) * Dv v, hinj, hI0, hint,
    fun v => mul_pos (Finset.prod_pos fun τ _ => pow_pos (hGpos v τ) _) (hD v), hnorm, ?_⟩
  have hlog : ∀ v, Real.log ((∏ τ, G v τ ^ dW ((D.fm u).lam 0 τ)) * Dv v) =
      (∑ τ, (dW ((D.fm u).lam 0 τ) : ℝ) * Real.log (G v τ)) + Real.log (Dv v) := fun v => by
    rw [Real.log_mul (Finset.prod_pos fun τ _ => pow_pos (hGpos v τ) _).ne' (hD v).ne',
      Real.log_prod (fun τ _ => (pow_pos (hGpos v τ) _).ne')]
    congr 1
    exact Finset.sum_congr rfl fun τ _ => Real.log_pow _ _
  have hmean : ∀ τ, (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (G v τ) ≤ Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) := by
    intro τ
    have h1 := mean_over_places_comap D.host.E D.what₂.LL (CV.rho τ)
      (fun w => Real.log (∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re))
    have h2 : (∑ v, Real.log (G v τ)) = ∑ v : InfinitePlace D.what₂.LL,
        Real.log (∑ a, ((v.comap (CV.rho τ)).embedding ((D.sp.X 0).hT (y a) (y a))).re) :=
      Finset.sum_congr rfl fun v _ => by rw [hGc]
    rw [h2, h1]
    exact shortAt_mean_log D u c y hy hposE
  have hdW : ∀ τ, (dW ((D.fm u).lam 0 τ) : ℝ) = colAbsP D u τ := fun τ => by
    unfold dW
    push_cast
    exact sum_natWeight_eq_colAbsShifted D u τ
  have hsplit : (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log ((∏ τ, G v τ ^ dW ((D.fm u).lam 0 τ)) * Dv v) =
      (∑ τ, (dW ((D.fm u).lam 0 τ) : ℝ) * ((1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (G v τ))) +
        (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (Dv v) := by
    simp only [hlog, Finset.sum_add_distrib, mul_add]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun v _ => by ring
  have hbound : (∑ τ, (dW ((D.fm u).lam 0 τ) : ℝ) * ((1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (G v τ))) ≤
      ∑ τ, colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) :=
    Finset.sum_le_sum fun τ _ => by
      rw [← hdW τ]
      exact mul_le_mul_of_nonneg_left (hmean τ) (Nat.cast_nonneg _)
  rw [hsplit]
  have e : (∑ τ, (colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) -
      (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u))) =
      (∑ τ, colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2)) -
        ∑ τ, (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u) := Finset.sum_sub_distrib _ _
  rw [e]
  linarith



end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
open Module NumberField

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions.flipTwoThree

section Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem bc_sum_repr (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (z : (D.sp.X 0).V) :
    CV.bc c τ z = ∑ i, CV.rho τ ((D.sp.X 0).frame.repr z i) • CV.bc c τ ((D.sp.X 0).frame i) := by
  conv_lhs => rw [← (D.sp.X 0).frame.sum_repr z]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => CV.bc_smul c τ _ _

theorem span_bc_frame (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    ⊤ ≤ Submodule.span D.what₂.LL (Set.range fun i => CV.bc c τ ((D.sp.X 0).frame i)) := by
  rw [← (CV.Q_good c τ).2.2]
  refine Submodule.span_le.2 ?_
  intro x hx
  have hx' : x ∈ (Submodule.span D.what₂.LL (Set.range fun i => CV.bc c τ ((D.sp.X 0).frame i))).restrictScalars (𝓞 D.what₂.LL) := by
    rw [CV.bc_L c τ] at hx
    refine (Submodule.span_le.2 ?_) hx
    rintro _ ⟨z, -, rfl⟩
    rw [SetLike.mem_coe, Submodule.restrictScalars_mem, bc_sum_repr CV c τ z]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  exact hx'

theorem card_frame_eq (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    Fintype.card (Fin (D.sp.X 0).rank) = finrank D.what₂.LL (CV.Q c τ).V := by
  rw [Fintype.card_fin, finrank_eq_card_basis (CV.Q c τ).b, Fintype.card_congr (CV.eQ c τ), Fintype.card_fin, D.sp.rank0, Ranks.N_zero]

def bcBasis (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : Basis (Fin (D.sp.X 0).rank) D.what₂.LL (CV.Q c τ).V :=
  basisOfTopLeSpanOfCardEqFinrank (fun i => CV.bc c τ ((D.sp.X 0).frame i)) (span_bc_frame CV c τ) (card_frame_eq CV c τ)

theorem bcBasis_apply (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (i : Fin (D.sp.X 0).rank) :
    bcBasis CV c τ i = CV.bc c τ ((D.sp.X 0).frame i) := by
  unfold bcBasis
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]

def bcFun (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (y : (D.sp.X 0).V) : (CV.Q c τ).V →ₗ[D.what₂.LL] D.what₂.LL :=
  (bcBasis CV c τ).constr D.what₂.LL fun i => CV.rho τ ((D.sp.X 0).hT y ((D.sp.X 0).frame i))

theorem bcFun_bc (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (y z : (D.sp.X 0).V) :
    bcFun CV c τ y (CV.bc c τ z) = CV.rho τ ((D.sp.X 0).hT y z) := by
  rw [bc_sum_repr CV c τ z, map_sum]
  simp_rw [map_smul]
  have h1 : ∀ i, bcFun CV c τ y (CV.bc c τ ((D.sp.X 0).frame i)) = CV.rho τ ((D.sp.X 0).hT y ((D.sp.X 0).frame i)) := fun i => by
    unfold bcFun
    rw [← bcBasis_apply CV c τ i, Basis.constr_basis]
  simp_rw [h1, smul_eq_mul, ← map_mul]
  rw [← map_sum]
  congr 1
  conv_rhs => rw [← (D.sp.X 0).frame.sum_repr z]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]

theorem bcFun_int (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) {y : (D.sp.X 0).V}
    (hy : y ∈ dualSub (D.sp.X 0) (D.clsLat u 0 c)) {x : (CV.Q c τ).V} (hx : x ∈ (CV.Q c τ).L) :
    IsIntegral ℤ (bcFun CV c τ y x) := by
  rw [CV.bc_L c τ] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    rw [bcFun_bc]
    obtain ⟨o, ho⟩ := hy z hz
    have e : (D.sp.X 0).hT y z = starRingEnd D.host.E ((D.sp.X 0).hT z y) := ((D.sp.X 0).herm.eq z y).symm
    rw [e, ← ho]
    exact ((o.isIntegral_coe.map (starRingEnd D.host.E).toIntAlgHom).map (CV.rho τ).toIntAlgHom)
  | zero => rw [map_zero]; exact isIntegral_zero
  | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
  | smul a x _ hx =>
    rw [← algebraMap_smul D.what₂.LL a x, map_smul, smul_eq_mul]
    exact a.isIntegral_coe.mul hx

end Fun

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col Formalism.BasicNotions.SkeletonIndexLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section G

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

def crdQ (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : (CV.Q c τ).V ≃ₗ[D.what₂.LL] (Fin (D.R.N 0) → D.what₂.LL) :=
  ((CV.Q c τ).b.reindex (CV.eQ c τ)).equivFun

def MQ (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : Submodule (𝓞 D.what₂.LL) (Fin (D.R.N 0) → D.what₂.LL) :=
  (CV.Q c τ).L.map ((crdQ CV c τ : (CV.Q c τ).V →ₗ[D.what₂.LL] (Fin (D.R.N 0) → D.what₂.LL)).restrictScalars (𝓞 D.what₂.LL))

def gM (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (τ : D.what₂.Tau) :
    Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL :=
  Matrix.of fun a i => bcFun CV c τ (y a) ((CV.Q c τ).b ((CV.eQ c τ).symm i))

theorem gM_mulVec (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (τ : D.what₂.Tau) (z : (CV.Q c τ).V)
    (a : Fin (D.R.N 0)) : (gM CV c y τ *ᵥ crdQ CV c τ z) a = bcFun CV c τ (y a) z := by
  show ∑ i, gM CV c y τ a i * crdQ CV c τ z i = _
  conv_rhs => rw [← ((CV.Q c τ).b.reindex (CV.eQ c τ)).sum_equivFun z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, Basis.reindex_apply, mul_comm]
  rfl

theorem gM_int (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V)
    (hy : ∀ a, y a ∈ dualSub (D.sp.X 0) (D.clsLat u 0 c)) (τ : D.what₂.Tau) :
    ∀ x ∈ MQ CV c τ, ∀ a, (gM CV c y τ *ᵥ x) a ∈ (1 : Submodule (𝓞 D.what₂.LL) D.what₂.LL) := by
  rintro _ ⟨z, hz, rfl⟩ a
  rw [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, gM_mulVec]
  exact Submodule.mem_one.2 ⟨⟨_, bcFun_int CV c τ (hy a) hz⟩, rfl⟩

theorem gM_unit (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (hli : LinearIndependent D.host.E y)
    (τ : D.what₂.Tau) : IsUnit (gM CV c y τ).det := by
  classical
  have hn : Fintype.card (Fin (D.R.N 0)) = finrank D.host.E (D.sp.X 0).V := by
    rw [Fintype.card_fin, (D.sp.X 0).rank_eq, D.sp.rank0, Ranks.N_zero]
  haveI : Nonempty (Fin (D.R.N 0)) := ⟨⟨0, rank_zero_pos D⟩⟩
  haveI : FiniteDimensional D.host.E (D.sp.X 0).V :=
    Module.finite_of_finrank_pos (by rw [← hn]; exact Fintype.card_pos)
  have hspan := hli.span_eq_top_of_card_eq_finrank hn
  let Φ : (D.sp.X 0).V →ₗ[D.host.E] (Fin (D.R.N 0) → D.host.E) := LinearMap.pi fun a => (D.sp.X 0).hT (y a)
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    have h0 : ∀ a, (D.sp.X 0).hT (y a) z = 0 := fun a => congrFun (LinearMap.mem_ker.1 hz) a
    refine (D.sp.X 0).nondeg.2 z fun x => ?_
    have hx : x ∈ Submodule.span D.host.E (Set.range y) := hspan ▸ Submodule.mem_top
    have hx' := (Submodule.span_le (p := LinearMap.ker ((D.sp.X 0).hT.flip z))).2 (by
      rintro _ ⟨a, rfl⟩
      exact LinearMap.mem_ker.2 (by rw [LinearMap.flip_apply]; exact h0 a)) hx
    have := LinearMap.mem_ker.1 hx'
    rwa [LinearMap.flip_apply] at this
  have hfin : finrank D.host.E (D.sp.X 0).V = finrank D.host.E (Fin (D.R.N 0) → D.host.E) := by
    rw [Module.finrank_fin_fun, ← hn, Fintype.card_fin]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 hinj
  rw [← Matrix.isUnit_iff_isUnit_det]
  refine Matrix.linearIndependent_rows_iff_isUnit.1 ?_
  rw [Fintype.linearIndependent_iff]
  intro t ht b
  obtain ⟨z, hz⟩ := hsurj (Pi.single b 1)
  have hz' : ∀ a, (D.sp.X 0).hT (y a) z = (Pi.single b (1 : D.host.E) : Fin (D.R.N 0) → D.host.E) a := fun a => congrFun hz a
  have hi : ∀ i, ∑ a, t a * gM CV c y τ a i = 0 := fun i => by
    have := congrFun ht i
    simpa [Finset.sum_apply] using this
  have key : ∑ a, t a * CV.rho τ ((D.sp.X 0).hT (y a) z) = 0 := by
    have e1 : ∀ a, CV.rho τ ((D.sp.X 0).hT (y a) z) = ∑ i, gM CV c y τ a i * crdQ CV c τ (CV.bc c τ z) i := by
      intro a
      rw [← bcFun_bc CV c τ (y a) z, ← gM_mulVec CV c y τ]
      rfl
    simp_rw [e1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hi i, zero_mul]
  simpa [hz', Pi.single_apply] using key

def gG (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (hli : LinearIndependent D.host.E y) :
    D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL :=
  fun τ => Matrix.nonsingInvUnit _ (gM_unit CV c y hli τ)

theorem gG_coe (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (hli : LinearIndependent D.host.E y)
    (τ : D.what₂.Tau) : ((gG CV c y hli τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) =
      gM CV c y τ := rfl

end G

section Loc

variable {D : D7}

theorem coeff_mem_of_intSpanAt {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n)
    {p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL} (hp : p ∈ IntSpanAt D w lam) (m : (D.what₂.Tau × Fin n × Fin n) →₀ ℕ) :
    coeff m p ∈ intW D.what₂.places w := by
  unfold IntSpanAt at hp
  induction hp using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, f, hr, -, rfl⟩ := hx
    have hten : Formalism.MainNotions.flipTwoThree.ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)) =
        MvPolynomial.map (Int.castRingHom D.what₂.LL) (∏ τ, rename (fun v => (τ, v)) (f τ)) := by
      unfold Formalism.MainNotions.flipTwoThree.ten
      rw [map_prod]
      all_goals exact Finset.prod_congr rfl fun τ _ => by rw [MvPolynomial.map_rename]
    rw [MvPolynomial.coeff_smul, hten, MvPolynomial.coeff_map, smul_eq_mul]
    exact (intW D.what₂.places w).mul_mem hr (intCast_mem _ _)
  | zero =>
    rw [MvPolynomial.coeff_zero]
    exact (intW D.what₂.places w).zero_mem
  | add x y _ _ hx hy =>
    rw [MvPolynomial.coeff_add]
    exact (intW D.what₂.places w).add_mem hx hy
  | neg x _ hx =>
    rw [MvPolynomial.coeff_neg]
    exact (intW D.what₂.places w).neg_mem hx

theorem intW_mem_locRing (w : D.what₂.places.Pl) {x : D.what₂.LL} (hx : x ∈ intW D.what₂.places w) : x ∈ locRing (D.plEq w) := by
  show x ∈ localization₂ (D.plEq w).asIdeal (1 : Submodule (𝓞 D.what₂.LL) D.what₂.LL)
  have h1 : (1 : Submodule (𝓞 D.what₂.LL) D.what₂.LL) = latOf (K := D.what₂.LL) (fun _ : Unit => (1 : D.what₂.LL)) := by
    rw [Submodule.one_eq_span]
    unfold latOf
    rw [Set.range_const]
  rw [h1, mem_localization_latticeOf_iff, Set.range_const, Submodule.mem_span_singleton]
  exact ⟨⟨x, hx⟩, by rw [Subring.smul_def, smul_eq_mul, mul_one]⟩

theorem mem_localization_map_equiv {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (P : Ideal (𝓞 K)) [P.IsPrime] (e : V ≃ₗ[K] W) (A : Submodule (𝓞 K) V) (x : V) :
    e x ∈ localization₂ P (A.map ((e : V →ₗ[K] W).restrictScalars (𝓞 K))) ↔ x ∈ localization₂ P A := by
  show (∃ s ∈ P.primeCompl, s • e x ∈ A.map ((e : V →ₗ[K] W).restrictScalars (𝓞 K))) ↔
    ∃ s ∈ P.primeCompl, s • x ∈ A
  have key : ∀ (s : 𝓞 K) (x : V), e (s • x) = s • e x := fun s x =>
    (e : V →ₗ[K] W).map_smul_of_tower s x
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨z, hz, hze⟩ := Submodule.mem_map.mp hx
    refine ⟨s, hs, ?_⟩
    have hzx : z = s • x := e.injective (by rw [key]; exact hze)
    rwa [← hzx]
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, Submodule.mem_map.mpr ⟨s • x, hx, by
      rw [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, key]⟩⟩

end Loc

section Int

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem colLat_eq_map (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (B : GL (Fin (D.R.N 0)) D.what₂.LL) :
    colLat B = (latOf (K := D.what₂.LL) fun a : Fin (D.R.N 0) =>
      ∑ i, (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) i a • (CV.Q c τ).b ((CV.eQ c τ).symm i)).map
        ((crdQ CV c τ : (CV.Q c τ).V →ₗ[D.what₂.LL] (Fin (D.R.N 0) → D.what₂.LL)).restrictScalars (𝓞 D.what₂.LL)) := by
  have hb : ∀ i, crdQ CV c τ ((CV.Q c τ).b ((CV.eQ c τ).symm i)) = Pi.single i 1 := by
    intro i
    unfold crdQ
    rw [← Basis.reindex_apply]
    ext j
    simp [Basis.equivFun_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
  unfold latOf colLat
  rw [Submodule.map_span, ← Set.range_comp]
  refine congrArg (Submodule.span _) (congrArg Set.range ?_)
  funext j a
  simp only [Function.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, map_sum, map_smul, hb]
  simp [Pi.single_apply]

theorem locBasis_of_isBasisAt (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (w : D.what₂.places.Pl) (B : GL (Fin (D.R.N 0)) D.what₂.LL)
    (hB : IsBasisAt (D.plEq w) (MQ CV c τ) B) :
    LocBasis D w (CV.Q c τ) (CV.eQ c τ) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) := by
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).mp B.isUnit, ?_⟩
  ext x
  rw [← mem_localization_iff_localizationAtPlace, ← mem_localization_latticeOf_iff D w,
    ← mem_localization_map_equiv (D.plEq w).asIdeal (crdQ CV c τ) (CV.Q c τ).L x,
    ← mem_localization_map_equiv (D.plEq w).asIdeal (crdQ CV c τ)
      (latOf (K := D.what₂.LL) fun a : Fin (D.R.N 0) =>
        ∑ i, (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) i a • (CV.Q c τ).b ((CV.eQ c τ).symm i)) x,
    ← colLat_eq_map CV c τ B]
  change crdQ CV c τ x ∈ localization₂ (D.plEq w).asIdeal (MQ CV c τ) ↔ _
  rw [hB]

end Int

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col Formalism.BasicNotions.SkeletonIndexLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Int2

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem cf_mem_twId (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V)
    (hy : ∀ a, y a ∈ dualSub (D.sp.X 0) (D.clsLat u 0 c)) (g : D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL)
    (hg : ∀ τ, ((g τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) = gM CV c y τ)
    {x : ((D.fm u).lat 0).V} (hx : x ∈ NC CV c) (m : MonI ((D.fm u).lam 0)) :
    cfMap ((D.fm u).lam 0) g (coE CV (hTV0 D u) x c) m ∈ twId ((D.fm u).lam 0) (MQ CV c) := by
  classical
  rw [mem_twId]
  intro w B hB
  set w' := D.plEq.symm w with hw'
  have hw : D.plEq w' = w := D.plEq.apply_symm_apply w
  have hLB : ∀ τ, LocBasis D w' (CV.Q c τ) (CV.eQ c τ) (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) :=
    fun τ => locBasis_of_isBasisAt CV c τ w' (B τ) (by rw [hw]; exact hB τ)
  let γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL := fun c' τ =>
    if c' = c then (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)
    else Classical.choose (exists_locBasis w' (CV.Q c' τ) (CV.Q_good c' τ) (CV.eQ c' τ))
  have hγ : ∀ c' τ, LocBasis D w' (CV.Q c' τ) (CV.eQ c' τ) (γ c' τ) := by
    intro c' τ
    by_cases h : c' = c
    · simp only [γ, if_pos h]
      rw [h]
      exact hLB τ
    · simp only [γ, if_neg h]
      exact Classical.choose_spec (exists_locBasis w' (CV.Q c' τ) (CV.Q_good c' τ) (CV.eQ c' τ))
  have hxL : x ∈ ((D.fm u).lat 0).L := by
    obtain ⟨x', hx', rfl⟩ := hx
    exact prjC_mem CV c hx'
  have hxW : x ∈ locW D.what₂.places w' ((D.fm u).lat 0).L := Submodule.subset_span hxL
  have hP := (CV.fin w' γ hγ x).1 hxW c
  simp only [γ, if_pos rfl] at hP
  set F : Pol D.what₂.LL D.what₂.Tau (D.R.N 0) := ((coE CV (hTV0 D u) x c : VV D.what₂.LL ((D.fm u).lam 0)) :
    Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) with hF
  have hFco : F = CV.co x c := coE_coe CV (hTV0 D u) x c
  have hinvB : (fun τ => (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)⁻¹) =
      fun τ => (((B⁻¹) τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) := by
    funext τ
    rw [Pi.inv_apply, Matrix.coe_units_inv]
  rw [← hFco, hinvB, actAll_eq_actP] at hP
  have hF0 : actP ((D.fm u).lam 0) B⁻¹ F ∈ (map (σ := D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) (locRing w).subtype).range := by
    refine mem_range_of_coeff_mem _ fun m' => ?_
    rw [← hw]
    exact intW_mem_locRing w' (coeff_mem_of_intSpanAt w' _ hP m')
  have hU : ∀ τ a b, (((g * B) τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ a b ∈
      locRing w := by
    intro τ a b
    have hcol : (fun c => (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) c a) ∈ localization₂ w.asIdeal (MQ CV c τ) := by
      rw [hB τ]
      exact le_localisation w _ (Submodule.subset_span ⟨a, rfl⟩)
    obtain ⟨s, hs, hsx⟩ := hcol
    rw [mem_locRing]
    refine ⟨s, hs, ?_⟩
    have := gM_int CV c y hy τ _ hsx b
    rw [← hg τ, Matrix.mulVec_smul] at this
    have e : (((g * B) τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ a b =
        ((g τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) *ᵥ fun c => (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) c a) b := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [e]
    exact this
  have hkey := coeff_mem_of_mem_range _ (block_action_integral (locRing w) _ hU hF0) m.1
  have e : Formalism.GradedWeylDivisibility.blockAct D.what₂.LL (fun τ => (((g * B) τ : GL (Fin (D.R.N 0)) D.what₂.LL) :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ) (actP ((D.fm u).lam 0) B⁻¹ F) =
      detTwK ((D.fm u).lam 0) B⁻¹ • trAct g F := by
    show trAct (g * B) (actP ((D.fm u).lam 0) B⁻¹ F) = _
    rw [trAct_mul]
    simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, map_smul, transpose_action_inv_right]
  rw [e, coeff_smul, smul_eq_mul, mem_locRing] at hkey
  exact hkey

end Int2

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col Formalism.BasicNotions.SkeletonIndexLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SlopeTestRemainingChoices

theorem emb_nonreal {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (φ : E →+* ℂ) : ∃ a : E, (φ a).im ≠ 0 := by
  by_contra h
  push_neg at h
  have hr : NumberField.ComplexEmbedding.IsReal φ :=
    NumberField.ComplexEmbedding.isReal_iff.mpr (RingHom.ext fun x => by
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      exact Complex.conj_eq_iff_im.mpr (h x))
  exact NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
    (IsTotallyComplex.isComplex (NumberField.InfinitePlace.mk φ))
    (NumberField.InfinitePlace.isReal_mk_iff.mpr hr)

theorem map_mem_VV {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {K : Type} [Field K] [CharZero K] (s : K →+* ℂ)
    {F : Pol K ι n} (hF : F ∈ VV K lam) : MvPolynomial.map s F ∈ VV ℂ lam := by
  obtain ⟨Z, -⟩ := standard_basis_z ι n lam
  rw [← Z.span_F K] at hF
  rw [← Z.span_F ℂ]
  induction hF using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    rw [MvPolynomial.map_map, show s.comp (Int.castRingHom K) = Int.castRingHom ℂ from RingHom.ext_int _ _]
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [map_add]; exact add_mem hp hq
  | smul a p _ hp =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hp

theorem fockN_smul {σ : Type} (d : ℂ) (f : MvPolynomial σ ℂ) : fockN (d • f) = ‖d‖ ^ 2 * fockN f := by
  unfold fockN
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  · rw [MvPolynomial.support_smul_eq hd, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_smul, smul_eq_mul, norm_mul, mul_pow, mul_assoc]

theorem nfAll_self_eq {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (p : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam p p = ((fockN p / extremalFockNormProduct lam : ℝ) : ℂ) := by
  exact nfL_self lam p

end SlopeTestRemainingChoices

section Nrm

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem maj_bc (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (v : InfinitePlace D.what₂.LL) (y z : (D.sp.X 0).V) :
    majAt (CV.Q c τ).b (CV.Q c τ).X v (CV.bc c τ y) (CV.bc c τ z) = v.embedding (CV.rho τ ((D.sp.X 0).hT y z)) := by
  have := (columnHypotheses D u).tcE
  have hcm : ∀ (φ : D.host.E →+* ℂ) (a : D.host.E), φ (star a) = starRingEnd ℂ (φ a) := D.sp.cm.cmUnram.2.1
  set φ : D.host.E →+* ℂ := v.embedding.comp (CV.rho τ) with hφ
  obtain ⟨s1, s2, s3, s4⟩ := isSesq_maj (CV.Q c τ).b (CV.Q c τ).X v
  beta_reduce at s1 s2 s3 s4
  refine sesq_ext (F := fun y z => majAt (CV.Q c τ).b (CV.Q c τ).X v (CV.bc c τ y) (CV.bc c τ z))
    (G := fun y z => φ ((D.sp.X 0).hT y z)) (σ := φ) (emb_nonreal φ) ⟨?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ ?_ y z
  · intro x x' y
    show majAt _ _ v (CV.bc c τ (x + x')) _ = _
    rw [map_add, s1]
  · intro x y y'
    show majAt _ _ v _ (CV.bc c τ (y + y')) = _
    rw [map_add, s2]
  · intro a x y
    show majAt _ _ v (CV.bc c τ (a • x)) _ = _
    rw [CV.bc_smul, s3]
    rfl
  · intro a x y
    show majAt _ _ v _ (CV.bc c τ (a • y)) = _
    rw [CV.bc_smul, s4]
    rfl
  · intro x x' y
    show φ ((D.sp.X 0).hT (x + x') y) = φ ((D.sp.X 0).hT x y) + φ ((D.sp.X 0).hT x' y)
    rw [map_add, LinearMap.add_apply, map_add]
  · intro x y y'
    show φ ((D.sp.X 0).hT x (y + y')) = φ ((D.sp.X 0).hT x y) + φ ((D.sp.X 0).hT x y')
    rw [map_add, map_add]
  · intro a x y
    show φ ((D.sp.X 0).hT (a • x) y) = starRingEnd ℂ (φ a) * φ ((D.sp.X 0).hT x y)
    rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, map_mul, starRingEnd_apply, hcm]
  · intro a x y
    show φ ((D.sp.X 0).hT x (a • y)) = φ a * φ ((D.sp.X 0).hT x y)
    rw [map_smul, smul_eq_mul, map_mul]
  · intro x
    show majAt _ _ v (CV.bc c τ x) (CV.bc c τ x) = φ ((D.sp.X 0).hT x x)
    have hre := CV.bc_norm c τ v x
    have hreal : (φ ((D.sp.X 0).hT x x)).im = 0 := by
      have e : starRingEnd D.host.E ((D.sp.X 0).hT x x) = (D.sp.X 0).hT x x := (D.sp.X 0).herm.eq x x
      have e2 : starRingEnd ℂ (φ ((D.sp.X 0).hT x x)) = φ ((D.sp.X 0).hT x x) := by
        rw [← hcm, ← starRingEnd_apply, e]
      exact Complex.conj_eq_iff_im.1 e2
    apply Complex.ext
    · exact hre
    · rw [majAt_self, Complex.ofReal_im]
      exact hreal.symm

theorem riesz_bc (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (v : InfinitePlace D.what₂.LL) (y : (D.sp.X 0).V)
    (q : (CV.Q c τ).V) : v.embedding (bcFun CV c τ y q) = majAt (CV.Q c τ).b (CV.Q c τ).X v (CV.bc c τ y) q := by
  obtain ⟨s1, s2, s3, s4⟩ := isSesq_maj (CV.Q c τ).b (CV.Q c τ).X v
  beta_reduce at s1 s2 s3 s4
  have hq : q ∈ Submodule.span D.what₂.LL (Set.range fun i => CV.bc c τ ((D.sp.X 0).frame i)) :=
    span_bc_frame CV c τ Submodule.mem_top
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨i, rfl⟩ := hq
    rw [bcFun_bc, maj_bc]
  | zero =>
    rw [map_zero, map_zero]
    have := s2 (CV.bc c τ y) 0 0
    rw [add_zero] at this
    linear_combination this
  | add q q' _ _ h1 h2 => rw [map_add, map_add, s2, h1, h2]
  | smul a q _ h1 => rw [map_smul, smul_eq_mul, map_mul, s4, h1]

theorem gM_map (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (τ : D.what₂.Tau) (v : InfinitePlace D.what₂.LL) :
    (gM CV c y τ).map v.embedding =
      Matrix.of (fun a k => star (fcoord (CV.Q c τ).b (CV.Q c τ).X v (CV.bc c τ (y a)) ((CV.eQ c τ).symm k))) *
        Matrix.reindex (CV.eQ c τ) (CV.eQ c τ) ((CV.Q c τ).X v)⁻¹ := by
  classical
  ext a j
  simp only [Matrix.map_apply, gM, Matrix.of_apply]
  rw [riesz_bc, Matrix.mul_apply]
  unfold majAt
  refine Fintype.sum_equiv (CV.eQ c τ) _ _ fun i => ?_
  simp only [Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  congr 1
  simp [fcoord, vecAt, Matrix.mulVec, dotProduct, Basis.repr_self, Finsupp.single_apply]

theorem invFr_coe (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    ((invFr CV v c τ : GL (Fin (D.R.N 0)) ℂ) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ) =
      Matrix.reindex (CV.eQ c τ) (CV.eQ c τ) ((CV.Q c τ).X v)⁻¹ := rfl

theorem hsN_gM (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (τ : D.what₂.Tau) (v : InfinitePlace D.what₂.LL) :
    hsN (((gM CV c y τ).map v.embedding *
        (((invFr CV v c τ)⁻¹ : GL (Fin (D.R.N 0)) ℂ) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ))ᵀ) =
      ∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re := by
  have hdet : IsUnit (Matrix.reindex (CV.eQ c τ) (CV.eQ c τ) ((CV.Q c τ).X v)⁻¹).det := by
    rw [← invFr_coe]
    exact Matrix.isUnits_det_units _
  rw [gM_map, Matrix.coe_units_inv, invFr_coe, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
  unfold hsN
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← CV.bc_norm c τ v (y a), majAt_self, Complex.ofReal_re]
  unfold normAt cnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  refine Fintype.sum_equiv (CV.eQ c τ).symm _ _ fun k => ?_
  simp only [Matrix.transpose_apply, Matrix.of_apply, norm_star]

theorem tcAt_mem_VV (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (x : ((D.fm u).lat 0).V) :
    tcAt CV v c x ∈ VV ℂ ((D.fm u).lam 0) := by
  unfold tcAt
  refine polyAction_mem_VV _ _ (map_mem_VV _ v.embedding ?_)
  rw [← coE_coe CV (hTV0 D u) x c]
  exact (coE CV (hTV0 D u) x c).2

theorem class_norm (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (hli : LinearIndependent D.host.E y)
    (v : InfinitePlace D.what₂.LL) (x : ((D.fm u).lat 0).V) :
    normAt (Pi.basisFun D.what₂.LL (MonI ((D.fm u).lam 0))) (fun _ => (monD ((D.fm u).lam 0))⁻¹) v
        (cfMap ((D.fm u).lam 0) (gG CV c y hli) (coE CV (hTV0 D u) x c)) ^ 2 ≤
      ((∏ τ, (∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re) ^ dW ((D.fm u).lam 0 τ)) *
          ‖detTwK ((D.fm u).lam 0) (invFr CV v c)⁻¹‖ ^ 2) *
        normAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x ^ 2 := by
  set lam := (D.fm u).lam 0 with hlam
  set g := gG CV c y hli with hg
  set F : Pol D.what₂.LL D.what₂.Tau (D.R.N 0) :=
    ((coE CV (hTV0 D u) x c : VV D.what₂.LL lam) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) with hF
  set P := tcAt CV v c x with hP
  set d : ℂ := detTwK lam (invFr CV v c)⁻¹ with hd
  set U : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ := fun τ =>
    ((((g τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL).map v.embedding) *
      (((invFr CV v c τ)⁻¹ : GL (Fin (D.R.N 0)) ℂ) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ))ᵀ with hU
  set G := MvPolynomial.map v.embedding (trAct g F) with hGdef
  set Gp := ∏ τ, (∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re) ^ dW (lam τ) with hGp
  have h1 : normAt (Pi.basisFun D.what₂.LL (MonI lam)) (fun _ => (monD lam)⁻¹) v (cfMap lam g (coE CV (hTV0 D u) x c)) ^ 2 ≤
      fockN G / extremalFockNormProduct lam := by
    rw [monH_norm]
    have e1 : ∑ m, monW lam m * ‖v.embedding (cfMap lam g (coE CV (hTV0 D u) x c) m)‖ ^ 2 =
        (∑ m : MonI lam, ‖coeff m.1 G‖ ^ 2 * (mfact m.1 : ℝ)) / extremalFockNormProduct lam := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hGdef, coeff_map, cfMap_apply, monW]
      ring
    have e2 : ∑ m : MonI lam, ‖coeff m.1 G‖ ^ 2 * (mfact m.1 : ℝ) ≤ fockN G := by
      have := fockN_sum_le G ((Finset.univ : Finset (MonI lam)).map ⟨fun m : MonI lam => m.1, fun a b h => Subtype.ext h⟩)
      rwa [Finset.sum_map] at this
    rw [e1]
    exact div_le_div_of_nonneg_right e2 (extR_pos lam).le
  have hVt : ∀ τ, (((invFr CV v c τ : GL (Fin (D.R.N 0)) ℂ) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ))ᵀ * U τ =
      (((g τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ).map v.embedding := by
    intro τ
    simp only [hU]
    rw [← Matrix.transpose_mul, Matrix.coe_units_inv, Matrix.nonsing_inv_mul_cancel_right _ _ (Matrix.isUnits_det_units _),
      Matrix.transpose_map]
  have eP : P = detTwK lam (invFr CV v c) • Formalism.GradedWeylDivisibility.blockAct ℂ
      (fun τ => ((invFr CV v c τ : GL (Fin (D.R.N 0)) ℂ) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ)ᵀ)
      (MvPolynomial.map v.embedding F) := by
    simp only [hP, tcAt, actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, trAct]
    rfl
  have ecomp : Formalism.GradedWeylDivisibility.blockAct ℂ U (Formalism.GradedWeylDivisibility.blockAct ℂ
      (fun τ => ((invFr CV v c τ : GL (Fin (D.R.N 0)) ℂ) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ)ᵀ)
      (MvPolynomial.map v.embedding F)) = G := by
    rw [← AlgHom.comp_apply, blockAct_comp]
    simp only [hVt]
    rw [hGdef]
    unfold trAct
    rw [map_blockAct]
  have hd1 : d * detTwK lam (invFr CV v c) = 1 := by rw [hd, ← detTwK_mul, inv_mul_cancel, detTwK_one]
  have h2 : G = d • Formalism.GradedWeylDivisibility.blockAct ℂ U P := by
    rw [eP, map_smul, ecomp, smul_smul, hd1, one_smul]
  have hPV : P ∈ VV ℂ lam := tcAt_mem_VV CV v c x
  have h3 : fockN (Formalism.GradedWeylDivisibility.blockAct ℂ U P) ≤ (∏ τ, hsN (U τ) ^ dW (lam τ)) * fockN P := by
    refine fockSubNorm D.what₂.Tau (D.R.N 0) U (fun τ => dW (lam τ)) P fun m hm τ => ?_
    have hm' := coefficient_space_support ℂ lam hPV m hm
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => hm' τ s
  have h4 : ∀ τ, hsN (U τ) = ∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re := fun τ =>
    hsN_gM CV c y τ v
  have h5 : fockN P / extremalFockNormProduct lam ≤ normAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x ^ 2 := by
    have e := majorant_lattice_eq_sum CV v x x
    rw [majAt_self] at e
    have e2 : normAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x ^ 2 = ∑ c', fockN (tcAt CV v c' x) / extremalFockNormProduct lam := by
      have := congrArg Complex.re e
      rw [Complex.ofReal_re, Complex.re_sum] at this
      rw [this]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [nfAll_self_eq, Complex.ofReal_re]
    rw [e2]
    exact Finset.single_le_sum (f := fun c' => fockN (tcAt CV v c' x) / extremalFockNormProduct lam)
      (fun c' _ => div_nonneg (fockN_nonneg _) (extR_pos _).le) (Finset.mem_univ c)
  have hGn : fockN G ≤ ‖d‖ ^ 2 * (Gp * fockN P) := by
    rw [h2, fockN_smul]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have := h3
    simp only [h4] at this
    exact this
  have hprod : 0 ≤ Gp :=
    Finset.prod_nonneg fun τ _ => pow_nonneg (by rw [← h4 τ]; exact hsN_nonneg _) _
  calc normAt (Pi.basisFun D.what₂.LL (MonI lam)) (fun _ => (monD lam)⁻¹) v (cfMap lam g (coE CV (hTV0 D u) x c)) ^ 2
      ≤ fockN G / extremalFockNormProduct lam := h1
    _ ≤ ‖d‖ ^ 2 * (Gp * fockN P) / extremalFockNormProduct lam := div_le_div_of_nonneg_right hGn (extR_pos lam).le
    _ = (Gp * ‖d‖ ^ 2) * (fockN P / extremalFockNormProduct lam) := by ring
    _ ≤ (Gp * ‖d‖ ^ 2) * normAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x ^ 2 :=
      mul_le_mul_of_nonneg_left h5 (mul_nonneg hprod (sq_nonneg _))

end Nrm

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section
open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col Formalism.BasicNotions.SkeletonIndexLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def QFrameDeg (D : D7) : Prop :=
  ∀ u (CV : ColVal D u) c τ,
    (D.R.N 0 : ℝ) * (CV.Q c τ).mu =
      (D.R.N 0 : ℝ) * (latK D.what₂.LL (MQ CV c τ)).mu +
        (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (‖((CV.Q c τ).X v).det‖ ^ 2)

section T

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem MQ_lattice (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : Submodule.IsLattice D.what₂.LL (MQ CV c τ) := by
  refine ⟨(CV.Q_good c τ).2.1.map _, ?_⟩
  unfold MQ
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars]
  rw [show ⇑(crdQ CV c τ : (CV.Q c τ).V →ₗ[D.what₂.LL] (Fin (D.R.N 0) → D.what₂.LL)) = ⇑(crdQ CV c τ) from rfl]
  rw [← LinearEquiv.coe_coe, Submodule.span_image, (CV.Q_good c τ).2.2, Submodule.map_top]
  exact LinearEquiv.range _

theorem detTwK_inv_ne (c : (D.mem u).C.cls 0) (v : InfinitePlace D.what₂.LL) :
    detTwK ((D.fm u).lam 0) (invFr CV v c)⁻¹ ≠ 0 := by
  unfold detTwK
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => ?_
  unfold detPow
  exact Units.ne_zero _

theorem det_invFr_inv (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    ((Matrix.GeneralLinearGroup.det ((invFr CV v c)⁻¹ τ) : ℂˣ) : ℂ) = ((CV.Q c τ).X v).det := by
  simp only [Pi.inv_apply, map_inv, Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply, invFr,
    brpGL]
  show ((Matrix.reindex (CV.eQ c τ) (CV.eQ c τ)) ((CV.Q c τ).X v)⁻¹).det⁻¹ = _
  rw [Matrix.det_reindex_self, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, inv_inv]

theorem log_detTw (c : (D.mem u).C.cls 0) (v : InfinitePlace D.what₂.LL) :
    Real.log (‖detTwK ((D.fm u).lam 0) (invFr CV v c)⁻¹‖ ^ 2) =
      ∑ τ, (((D.fm u).lam 0 τ).detShift : ℝ) * Real.log (‖((CV.Q c τ).X v).det‖ ^ 2) := by
  unfold detTwK
  simp only [detPow, Units.val_zpow_eq_zpow_val, det_invFr_inv, norm_prod, norm_zpow]
  have hne : ∀ τ, ((CV.Q c τ).X v).det ≠ 0 := fun τ => by
    rw [← det_invFr_inv CV v c τ]
    exact Units.ne_zero _
  rw [← Finset.prod_pow, Real.log_prod]
  · refine Finset.sum_congr rfl fun τ _ => ?_
    rw [show (‖((CV.Q c τ).X v).det‖ ^ ((D.fm u).lam 0 τ).detShift) ^ 2 =
        (‖((CV.Q c τ).X v).det‖ ^ 2) ^ ((D.fm u).lam 0 τ).detShift by rw [sq, sq, mul_zpow], Real.log_zpow]
  · intro τ _
    exact pow_ne_zero _ (zpow_ne_zero _ (norm_ne_zero_iff.mpr (hne τ)))

theorem detShift_eq (τ : D.what₂.Tau) :
    ((((D.fm u).lam 0 τ).detShift : ℤ) : ℝ) = ((lamCol D u τ (D.R.k - 1) : ℚ) : ℝ) := by
  have hn := rank_zero_pos D
  have hk := columnCount_pos D
  unfold DomWeight.detShift
  rw [dif_pos hn]
  have := weight_eq_lamCol D u τ ⟨D.R.N 0 - 1, by omega⟩
  rw [this]
  congr 3
  simp [Ranks.N_zero]

theorem classMapT_of (h : QFrameDeg D) : ClassMapT D := by
  intro u CV c y hy
  obtain ⟨hyd, hli, -⟩ := hy
  have := (columnHypotheses D u).tc
  have hn : 0 < D.R.N 0 := rank_zero_pos D
  have hM : ∀ τ, Submodule.IsLattice D.what₂.LL (MQ CV c τ) := MQ_lattice CV c
  refine ⟨cfMap ((D.fm u).lam 0) (gG CV c y hli) ∘ₗ (LinearMap.proj c ∘ₗ (coE CV (hTV0 D u) : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)))), twIdeal ((D.fm u).lam 0) (MQ CV c) hM,
    fun v => ‖detTwK ((D.fm u).lam 0) (invFr CV v c)⁻¹‖ ^ 2, ?_, twIdeal_ne_zero _ _ hM, ?_, ?_, ?_, ?_⟩
  · exact injOn_NC CV c _ (cfMap_injective _ _)
  · intro x hx m
    rw [twIdeal_coe]
    exact cf_mem_twId CV c y hyd (gG CV c y hli) (fun τ => gG_coe CV c y hli τ) hx m
  · intro v
    exact pow_pos (norm_pos_iff.2 (detTwK_inv_ne CV c v)) 2
  · intro v x
    exact class_norm CV c y hli v x
  · rw [twisted_ideal_norm_formula D.what₂.LL hn _ _ hM]
    simp_rw [log_detTw CV c]
    have hQ := fun τ => h u CV c τ
    have hslope := fun τ => q_lattice_slope D u CV c τ
    have hk : (D.R.N 0 : ℝ) = (D.R.k : ℝ) := by rw [Ranks.N_zero]
    have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast columnCount_pos D
    have e1 : (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, ∑ τ, (((D.fm u).lam 0 τ).detShift : ℝ) * Real.log (‖((CV.Q c τ).X v).det‖ ^ 2) =
        ∑ τ, (((D.fm u).lam 0 τ).detShift : ℝ) * ((1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (‖((CV.Q c τ).X v).det‖ ^ 2)) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← Finset.mul_sum]
      ring
    rw [e1, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine le_of_eq (Finset.sum_congr rfl fun τ _ => ?_)
    rw [← mul_add, ← hQ τ, hslope τ, hk, detShift_eq]
    field_simp

end T



end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end
