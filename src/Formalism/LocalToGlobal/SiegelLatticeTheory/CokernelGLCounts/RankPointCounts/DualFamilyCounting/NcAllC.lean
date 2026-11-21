import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcArithG
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IndexTypC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValDiffProd
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.CondAllPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowLatticeMass
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSSplitPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittOEv
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittSt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXConditions
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTieIdx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTHoldsX
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcReal
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTieLG
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.RealBracketHolds

section
noncomputable section

namespace Formalism.L2.SG.Pf.HasProdFiniteSupport

open Filter Topology

variable {ι : Type*}

theorem hasProd_inv₀' {f : ι → ℝ} {a : ℝ} (h : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => (f i)⁻¹) a⁻¹ := by
  unfold HasProd at h ⊢
  refine (h.inv₀ ha).congr (fun s => ?_)
  exact (Finset.prod_inv_distrib f).symm

theorem hasProd_rpow' {f : ι → ℝ} {a : ℝ} (p : ℝ) (hf : ∀ i, 0 ≤ f i) (h : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => f i ^ p) (a ^ p) := by
  unfold HasProd at h ⊢
  refine (h.rpow_const (Or.inl ha)).congr (fun s => ?_)
  exact (Real.finsetProd_rpow s f (fun i _ => hf i) p).symm



theorem hasProd_of_finite_support {f : ι → ℝ} (s : Set ι) (hs : s.Finite) (h1 : ∀ i ∉ s, f i = 1) :
    HasProd f (∏ i ∈ hs.toFinset, f i) :=
  hasProd_prod_of_ne_finset_one (fun i hi => h1 i (by simpa using hi))

theorem hasProd_of_compl' (s : Finset ι) {f : ι → ℝ} {a : ℝ}
    (h : HasProd (fun i : {i // i ∉ s} => f i) a) : HasProd f (a * ∏ i : s, f i) := by
  classical
  have h1 : HasProd ((↑s : Set ι)ᶜ.mulIndicator f) a :=
    (hasProd_subtype_iff_mulIndicator (s := (↑s : Set ι)ᶜ)).mp h
  have h2 : HasProd ((↑s : Set ι).mulIndicator f) (∏ i : s, f i) :=
    (hasProd_subtype_iff_mulIndicator (s := (↑s : Set ι))).mp (hasProd_fintype _)
  have h3 := h1.mul h2
  convert h3 using 1
  · funext i
    by_cases hp : i ∈ s <;> simp [Set.mulIndicator, hp]

theorem hasProd_compl_of' (s : Finset ι) {f : ι → ℝ} {a : ℝ} (h : HasProd f a) (hf : ∀ i ∈ s, f i ≠ 0) :
    HasProd (fun i : {i // i ∉ s} => f i) (a * (∏ i : s, f i)⁻¹) := by
  classical
  have h2 : HasProd (fun i => ((↑s : Set ι).mulIndicator f i)⁻¹) (∏ i : s, f i)⁻¹ := by
    have h0 : HasProd ((↑s : Set ι).mulIndicator f) (∏ i : s, f i) :=
      (hasProd_subtype_iff_mulIndicator (s := (↑s : Set ι))).mp (hasProd_fintype _)
    exact hasProd_inv₀' h0 (Finset.prod_ne_zero_iff.mpr fun i _ => hf i i.2)
  have h3 := h.mul h2
  have h4 : HasProd ((↑s : Set ι)ᶜ.mulIndicator f) (a * (∏ i : s, f i)⁻¹) := by
    convert h3 using 1
    funext i
    by_cases hp : i ∈ s
    · simp [Set.mulIndicator, hp, hf i hp]
    · simp [Set.mulIndicator, hp]
  exact (hasProd_subtype_iff_mulIndicator (s := (↑s : Set ι)ᶜ)).mpr h4

end Formalism.L2.SG.Pf.HasProdFiniteSupport
end
end

section
noncomputable section

open Classical

namespace Formalism.L2.SG.Pf.NcGlob

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField
  Formalism.L2.SG.Pf.HasProdFiniteSupport Formalism.L2.SG.Pf.NcVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {D : D7} (X : HidaSetting D)

def fac (i : ℕ) (v : PlX X) : ℝ :=
  1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i

def tf (k t : ℕ) (v : PlX X) : ℝ :=
  if ((t : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal then fac X k v else 1

theorem absNorm_gt_one (v : PlX X) : (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.2 v.isPrime.ne_top
  have : 1 < Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast this

theorem fac_pos (i : ℕ) (hi : 1 ≤ i) (v : PlX X) : 0 < fac X i v := by
  unfold fac
  have hq := absNorm_gt_one X v
  have hq0 : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by linarith
  have habs : |((etaV (E := X.B.I.E) v : ℤ) : ℝ)| = 1 := by
    unfold etaV; split_ifs <;> simp
  have hη : ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i ≤ 1 := by
    calc ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i ≤ |((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i| := le_abs_self _
      _ = 1 := by rw [abs_pow, habs, one_pow]
  have hqi : (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i := one_lt_pow₀ hq (by omega)
  have : ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i < 1 :=
    (div_lt_one (by positivity)).mpr (lt_of_le_of_lt hη hqi)
  linarith

theorem tf_pos (k t : ℕ) (hk : 1 ≤ k) (v : PlX X) : 0 < tf X k t v := by
  unfold tf; split_ifs
  · exact fac_pos X k hk v
  · exact one_pos

theorem aP_split (k N t : ℕ) (hk : k + 1 ≤ N) (v : PlX X) :
    aP (E := X.B.I.E) v k N t = (∏ i ∈ Finset.Icc (k + 1) N, fac X i v) * tf X k t v := by
  unfold aP tf
  by_cases ht : ((t : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal
  · rw [if_pos ht, if_pos ht, Finset.Icc_eq_cons_Ioc (show k ≤ N by omega), Finset.prod_cons]
    have hIo : Finset.Ioc k N = Finset.Icc (k + 1) N := by
      ext i; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [hIo, mul_comm]
    rfl
  · rw [if_neg ht, if_neg ht, mul_one]
    rfl

theorem aPlus_pos (k N t : ℕ) (hk : 1 ≤ k) (v : PlX X) : 0 < aP (E := X.B.I.E) v k N t := by
  unfold aP
  apply Finset.prod_pos
  intro i hi
  have : 1 ≤ i := by
    simp only [Finset.mem_Icc] at hi
    split_ifs at hi <;> omega
  exact fac_pos X i this v

theorem finite_dvd (t : ℕ) (ht : t ≠ 0) :
    {v : PlX X | ((t : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {((t : ℕ) : 𝓞 X.B.I.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast ht
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  exact Ideal.dvd_span_singleton.mpr hv

theorem absV_nonneg (v : PlX X) : 0 ≤ absV v (dV v) := by
  unfold absV; split_ifs
  · exact le_rfl
  · positivity

end Loc

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem normalizing_arithmetic_holds : NcArith := by
  intro D X hb hK FdN FdN' u u' X0 ψ τ Rw I H H₁ i1 i2 i3 i4 i5 T sd C Th F0 what₂ vR Q M δ i0 i0' νq a'
    ha hRR hS hR hχ hstd hcong hVo hVt hIx hOm hDP hRMp hFD hPC hP
  obtain ⟨hd, hfc, hEul, hTfac, hvI, hfE, hn, htδ, htaP, hgprod⟩ := hFD
  obtain ⟨hKc, hFc, -⟩ := Formalism.L2.SG.Pf.Cnt.field_dictionary_holds D
  have hk5 : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hm : D.R.m = 2 * (D.R.rS + 1) := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hr : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
    show D.R.k + D.R.m - 1 = D.R.k + 2 * D.R.rS + 1
    omega

  have hLpos : ∀ i, 2 ≤ i → 0 < Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i := by
    intro i hi
    rw [← Formalism.HermitianLattices.Ext.L3.lValEta_eq_lValEtaF hKc hFc i hi]
    exact Formalism.HermitianLattices.Ext.L3.lValEta_pos hKc i hi
  set PiL : ℝ := ∏ i ∈ Finset.Icc (D.R.k + 1) D.R.r, Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i with hPiL
  have hPiLpos : 0 < PiL := by
    apply Finset.prod_pos
    intro i hi
    exact hLpos i (by simp only [Finset.mem_Icc] at hi; omega)
  have hfacHP : HasProd (fun v : PlX X => ∏ i ∈ Finset.Icc (D.R.k + 1) D.R.r, fac X i v) PiL⁻¹ := by
    rw [hPiL, ← Finset.prod_inv_distrib]
    apply hasProd_prod
    intro i hi
    have hi2 : 2 ≤ i := by simp only [Finset.mem_Icc] at hi; omega
    have h1 := hasProd_inv₀' (hEul i hi2) (hLpos i hi2).ne'
    convert h1 using 1
    funext v
    simp only [fac, inv_inv]

  set PT : ℝ := ∏' 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal},
      (if (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ 𝔭.1 then
        1 - Formalism.HermitianLattices.Ext.L3.etaF D.host.E D.host.F 𝔭.1 ^ D.R.k * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(D.R.k : ℤ)) else 1)
    with hPT
  have hTHP : HasProd (tf X D.R.k (Tw u)) PT := by
    convert hTfac using 1
    funext v
    simp only [tf, fac, Tw]
    by_cases hv : (((D.mem u).A.T : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal <;> simp [hv]
  have hT0 : (Tw u) ≠ 0 := (D.mem u).A.T_prime.ne_zero
  have hT0' : (Tw u') ≠ 0 := (D.mem u').A.T_prime.ne_zero
  have hSf := finite_dvd X (Tw u) hT0
  have hSf' := finite_dvd X (Tw u') hT0'
  have hTHPf : HasProd (tf X D.R.k (Tw u)) (∏ v ∈ hSf.toFinset, tf X D.R.k (Tw u) v) :=
    hasProd_of_finite_support _ hSf (fun v hv => by simp only [tf, Set.mem_ofPred_eq] at hv ⊢; rw [if_neg hv])
  have hTHP' : HasProd (tf X D.R.k (Tw u')) (∏ v ∈ hSf'.toFinset, tf X D.R.k (Tw u') v) :=
    hasProd_of_finite_support _ hSf' (fun v hv => by simp only [tf, Set.mem_ofPred_eq] at hv ⊢; rw [if_neg hv])
  have hPTpos : 0 < PT := by
    rw [hTHP.unique hTHPf]
    exact Finset.prod_pos fun v _ => tf_pos X D.R.k (Tw u) (by omega) v
  set PT' : ℝ := ∏ v ∈ hSf'.toFinset, tf X D.R.k (Tw u') v with hPT'
  have hPT'pos : 0 < PT' := Finset.prod_pos fun v _ => tf_pos X D.R.k (Tw u') (by omega) v

  have hn' : X.B.I.n = D.R.r := hn
  have hsplit : ∀ t v, aP (E := X.B.I.E) v D.R.k X.B.I.n t =
      (∏ i ∈ Finset.Icc (D.R.k + 1) D.R.r, fac X i v) * tf X D.R.k t v := by
    intro t v
    rw [aP_split X D.R.k X.B.I.n t (by omega) v, hn']
  set AT : ℝ := PiL⁻¹ * PT with hAT
  set A' : ℝ := PiL⁻¹ * PT' with hA'
  have hATHP : HasProd (fun v : PlX X => aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u)) AT := by
    have := hfacHP.mul hTHP
    convert this using 1
    funext v
    exact hsplit _ v
  have hA'HP : HasProd (fun v : PlX X => aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u')) A' := by
    have := hfacHP.mul hTHP'
    convert this using 1
    funext v
    exact hsplit _ v
  have hATpos : 0 < AT := mul_pos (inv_pos.mpr hPiLpos) hPTpos
  have hA'pos : 0 < A' := mul_pos (inv_pos.mpr hPiLpos) hPT'pos
  set ATyp : ℝ := ∏ p : TypX X, aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u) with hATyp
  have hATyppos : 0 < ATyp := Finset.prod_pos fun p _ => aPlus_pos X D.R.k X.B.I.n (Tw u) (by omega) p.1

  have hG5 : AT * PiL = PT := by rw [hAT]; field_simp

  have hal_def : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).al =
      (∏ p : TypX X, alX X u u' p.1) * ∏' v : OrdX X, alX X u u' v.1 := rfl
  have halT : ∀ v : PlX X, TypAt X v → alX X u u' v = aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u) := by
    intro v hv; unfold alX; rw [if_pos hv]
  have halO : ∀ v : PlX X, ¬ TypAt X v → alX X u u' v =
      aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u) * aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u') := by
    intro v hv; unfold alX; rw [if_neg hv]
  have hordHP := hasProd_compl_of' (typSet X.B.I.F (D.host.g 0) (D.host.g 1)) (hATHP.mul hA'HP)
    (fun v _ => (mul_pos (aPlus_pos X D.R.k X.B.I.n (Tw u) (by omega) v)
      (aPlus_pos X D.R.k X.B.I.n (Tw u') (by omega) v)).ne')
  have hord : ∏' v : OrdX X, alX X u u' v.1 = AT * A' *
      (∏ i : TypX X, (aP (E := X.B.I.E) i.1 D.R.k X.B.I.n (Tw u) *
        aP (E := X.B.I.E) i.1 D.R.k X.B.I.n (Tw u')))⁻¹ := by
    rw [← hordHP.tprod_eq]
    exact tprod_congr (fun v => halO v.1 v.2)
  have hTypProd : (∏ i : TypX X, (aP (E := X.B.I.E) i.1 D.R.k X.B.I.n (Tw u) *
        aP (E := X.B.I.E) i.1 D.R.k X.B.I.n (Tw u'))) = ATyp * ATyp := by
    rw [Finset.prod_mul_distrib, Fintype.prod_congr _ _ (fun p : TypX X => htaP p), hATyp]
  have hG4 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).al * ATyp = AT * A' := by
    rw [hal_def, Fintype.prod_congr _ _ (fun p : TypX X => halT p.1 p.2), ← hATyp, hord, hTypProd]
    field_simp

  have hdX : 0 < |(NumberField.discr X.B.I.F : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero X.B.I.F)
  have hδHP := hasProd_rpow' ((X.B.I.n : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2)
    (fun v => absV_nonneg X v) hDP (inv_ne_zero hdX.ne')
  have hωHP := hδHP.mul hA'HP
  have hG3 : (∏' v : PlX X,
        (omAt X.B.I.cm.sig X.B.I.J ψ v
          ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
          {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
            Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal) =
      |(NumberField.discr D.host.F : ℝ)| ^
        (-((D.R.r : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2)) * A' := by
    have hωHP' : HasProd (fun v : PlX X =>
        (omAt X.B.I.cm.sig X.B.I.J ψ v
          ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
          {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
            Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal)
        ((|(NumberField.discr X.B.I.F : ℝ)|⁻¹) ^
          ((X.B.I.n : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2) * A') := by
      convert hωHP using 1
      funext v
      exact hOm hχ hstd v
    rw [hωHP'.tprod_eq, Real.inv_rpow (abs_nonneg _), ← Real.rpow_neg (abs_nonneg _), hd, hn']

  have hU_def : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).unitLevelVolume =
      (∏' v : OrdX X, localVolumeUnit X ψ v.1) * ∏ p : TypX X, localVolumeUnit X ψ p.1 := rfl
  have hZ_def : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volZZ =
      ∏' v : PlX X, ZZX X u u' ψ v := rfl
  obtain ⟨-, -, -, hU00m, -, hZZm, hZZpos, -⟩ := hPC
  have hUHP : HasProd (fun v => localVolumeUnit X ψ v)
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).unitLevelVolume := by
    rw [hU_def]
    exact hasProd_of_compl' (typSet X.B.I.F (D.host.g 0) (D.host.g 1)) hU00m.hasProd
  have hZHP : HasProd (fun v => ZZX X u u' ψ v)
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volZZ := by
    rw [hZ_def]
    exact hZZm.hasProd
  have hratHP := hUHP.mul (hasProd_inv₀' hZHP (by rw [hZ_def]; exact hZZpos.ne'))
  have hpp : ∀ v : PlX X, localVolumeUnit X ψ v * (ZZX X u u' ψ v)⁻¹ =
      absV v (dV v) ^ (-(((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3)) *
        (if TypAt X v then (gAt X v : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) else 1) := by
    intro v
    by_cases hv : TypAt X v
    · rw [if_pos hv, ← div_eq_mul_inv, hVt hχ hstd hcong v hv, htδ ⟨v, hv⟩, Real.one_rpow, one_mul]
    · rw [if_neg hv, ← div_eq_mul_inv, hVo hχ hstd v hv, mul_one]
  have hgHP : HasProd (fun v : PlX X => if TypAt X v then (gAt X v : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) else 1)
      (∏ p : TypX X, (gAt X p.1 : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3))) := by
    have h0 := hasProd_of_compl' (typSet X.B.I.F (D.host.g 0) (D.host.g 1))
      (f := fun v : PlX X => if TypAt X v then (gAt X v : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) else 1) (a := 1)
      (by
        convert (hasProd_one : HasProd (fun _ : {i // i ∉ typSet X.B.I.F (D.host.g 0) (D.host.g 1)} => (1 : ℝ)) 1)
          using 1
        funext v
        exact if_neg v.2)
    convert h0 using 1
    rw [one_mul]
    exact Fintype.prod_congr _ _ (fun p => (if_pos p.2).symm)
  have hδX := hasProd_rpow' (-(((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3))
    (fun v => absV_nonneg X v) hDP (inv_ne_zero hdX.ne')
  have hval : HasProd (fun v : PlX X => localVolumeUnit X ψ v * (ZZX X u u' ψ v)⁻¹)
      ((|(NumberField.discr X.B.I.F : ℝ)|⁻¹) ^ (-(((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3)) *
        ∏ p : TypX X, (gAt X p.1 : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3))) := by
    convert hδX.mul hgHP using 1
    funext v
    exact hpp v
  have hG1 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).unitLevelVolume /
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volZZ =
      |(NumberField.discr D.host.F : ℝ)| ^ (((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3) *
        ((Lat.gS D : ℕ) : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3) * Module.finrank ℚ D.host.F) := by
    rw [div_eq_mul_inv, hratHP.unique hval, Real.inv_rpow (abs_nonneg _), ← Real.rpow_neg (abs_nonneg _), neg_neg,
      hd, Finset.prod_pow, hgprod, ← pow_mul, mul_comm (Module.finrank ℚ D.host.F)]

  have hKo := hP.2.1
  have hKp : ∀ p, 0 < (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKp p :=
    fun p => (hP.1 p).2.2.2.2.2.1
  have hG2 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnat /
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK =
      ((Lat.gS D : ℕ) : ℝ) ^ (-(((D.R.rS + 1) * (2 * D.R.k + 2 * D.R.rS + 1) * Module.finrank ℚ D.host.F : ℕ) : ℤ)) /
        ATyp := by
    unfold Formalism.FourierDecayAlt.S3.MassData.μKnat Formalism.FourierDecayAlt.S3.MassData.μK
    rw [mul_div_mul_left _ _ hKo.ne', ← Finset.prod_div_distrib, Fintype.prod_congr _ _ hIx,
      Finset.prod_div_distrib, Finset.prod_zpow, hgprod, ← hATyp]
    congr 1
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring

  have hfinE : Module.finrank ℚ D.host.E = 2 * Module.finrank ℚ D.host.F := by
    rw [← Module.finrank_mul_finrank ℚ D.host.F D.host.E, D.sp.cm.deg2]
    ring
  have hng : ngFac D = ((Lat.gS D : ℕ) : ℝ) ^ (D.R.m * Module.finrank ℚ D.host.F * (D.R.k - 1)) := by
    unfold ngFac
    have hcast : (((Lat.gS D : ℕ) : D.host.E)) ^ D.R.m =
        algebraMap ℚ D.host.E (((Lat.gS D : ℕ) : ℚ) ^ D.R.m) := by simp
    rw [hcast, Algebra.norm_algebraMap, hfinE]
    have hg0 : (0 : ℝ) ≤ ((Lat.gS D : ℕ) : ℝ) := Nat.cast_nonneg _
    have hsq : |((((((Lat.gS D : ℕ) : ℚ) ^ D.R.m) ^ (2 * Module.finrank ℚ D.host.F) : ℚ)) : ℝ)| =
        (((Lat.gS D : ℕ) : ℝ) ^ (D.R.m * Module.finrank ℚ D.host.F)) ^ 2 := by
      push_cast
      rw [abs_of_nonneg (by positivity), ← pow_mul, ← pow_mul]
      ring_nf
    rw [hsq, Real.sqrt_sq (by positivity), ← pow_mul]

  rw [hd, hfc] at hR
  exact Formalism.L2.SG.Pf.NcArithG.ncValueC_of_global X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq
    a' _ ATyp A' AT PT hP ha hATyppos hA'pos hPTpos hS hR hG1 hG2 hG3 hG4 hG5
    (hRMp D u u' hcong F0 what₂ hRR) hvI hfE hng

end Formalism.L2.SG.Pf.NcGlob
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.NcLeaves

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem ncTieC_of_leaves (a' : ℝ) (ha : 0 < a')
    (hP : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos)
    (hM : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMass)
    (hMs : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMasses)
    (hL : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InLevelS)
    (hO : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InOrdinary)
    (hT : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InTyped)
    (hV : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InVolumes)
    (hVG : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG)
    (hχ : IsCharAF X.B.I.F ψ) (hstd : IsStdChar ψ)
    (hcong : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hRR : IsRowReps D F0 what₂)
    (hS : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK * a' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' *
        ∏' v : PlX X,
          (omAt X.B.I.cm.sig X.B.I.J ψ v
            ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
            {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
              Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal)
    (hR : Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN' =
      a' * 2 ^ (D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F)) *
        (Real.pi ^ D.R.k / (Nat.factorial (D.R.k - 1) : ℝ)) ^ Fintype.card (NumberField.InfinitePlace X.B.I.F) *
        ((Tw u : ℕ) : ℝ) ^ (-((D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F) : ℕ) : ℤ)) *
        |(NumberField.discr X.B.I.F : ℝ)| ^
          (-(8 * (D.R.rS : ℝ) ^ 3 + 6 * (D.R.rS : ℝ) ^ 2 + 6 * D.R.k * (D.R.rS : ℝ) ^ 2 + D.R.rS) / 3))
    (hVo : Formalism.L2.SG.Pf.NcVal.VolOrdV X u u' ψ) (hVt : Formalism.L2.SG.Pf.NcVal.VolTypV X u u' ψ)
    (hIx : Formalism.L2.SG.Pf.NcIdx.IndexTypC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hOm : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ) (hFD : Formalism.L2.SG.Pf.NcVal.FieldDict X u u')
    (hPC : ProdConv X u u' ψ) :
    NcTieC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂) :=
  Formalism.L2.SG.Pf.NcAsm.ncTieC_of' X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hP hM hMs hL hO hT hV hVG
    (Formalism.L2.SG.Pf.NcGlob.normalizing_arithmetic_holds X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq a' ha hRR hS hR
      hχ hstd hcong hVo hVt hIx hOm
      (Formalism.L2.SG.Pf.NcVal.diffProd_holds X) PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.row_lattice_mass hFD hPC hP)

end Formalism.L2.SG.Pf.NcLeaves
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittAlg

open Matrix Formalism.UG

private theorem s_inv_eq_of_s_eq_of_mul_eq_one {S : Type} [CommRing S] (s : S →+* S) (b b' : S) (hb : s b = b)
    (h : b * b' = 1) : s b' = b' := by
  have h1 : s b * s b' = 1 := by rw [← map_mul, h, map_one]
  rw [hb] at h1
  calc s b' = (b' * b) * s b' := by rw [mul_comm b' b, h, one_mul]
    _ = b' * (b * s b') := by ring
    _ = b' := by rw [h1, mul_one]

private theorem hform_transvection_preserves {S : Type} [CommRing S] (s : S →+* S) (hs : ∀ z, s (s z) = z) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) S) (hJ : IsHerm s J) (v : Fin n → S) (b b' lam : S)
    (hvv : hform s J v v = b) (hbb : b * b' = 1) (hb' : s b' = b') (hlam : lam * s lam = 1)
    (z w : Fin n → S) :
    hform s J (z + ((s lam - 1) * (b' * hform s J v z)) • v)
      (w + ((s lam - 1) * (b' * hform s J v w)) • v) = hform s J z w := by
  have hzv : hform s J z v = s (hform s J v z) := (hform_conj s J hs hJ v z).symm
  simp only [hform_add_left, hform_add_right, hform_smul_left, hform_smul_right]
  rw [hzv, hvv]
  simp only [map_mul, map_sub, map_one, hs, hb']
  linear_combination (b' * hform s J v w * s (hform s J v z)) * hlam +
    (b' * hform s J v w * s (hform s J v z) * (lam - 1) * (s lam - 1)) * hbb

theorem algWitt : Formalism.L2.SG.Pf.NcS.IntWittPf.AlgWitt := by
  unfold Formalism.L2.SG.Pf.NcS.IntWittPf.AlgWitt
  intro S _ s O hs hsO n J J' hJ hJJ' hJO hJ'O a β β' hβO hβ'O hββ' hH x y hxO hyO hxx hyy

  have key : ∀ k : ℕ, k ≤ a → ∃ M : Matrix (Fin n) (Fin n) S,
      (∀ z w, hform s J (M *ᵥ z) (M *ᵥ w) = hform s J z w) ∧ (∀ i j, M i j ∈ O) ∧
      ∀ i : Fin a, i.val < k → M *ᵥ y i = x i := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨1, fun z w => by rw [Matrix.one_mulVec, Matrix.one_mulVec],
        fun i j => Formalism.L2.SG.Pf.NcS.IntWittAlg.one_mem' O i j, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨M, hMp, hMO, hMy⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨i0, hi0⟩ : ∃ i0 : Fin a, i0.val = k := ⟨⟨k, hk⟩, rfl⟩
      obtain ⟨yy, hyy_def⟩ : ∃ yy : Fin n → S, yy = M *ᵥ y i0 := ⟨_, rfl⟩
      have hyyO : ∀ l, yy l ∈ O := fun l => by
        rw [hyy_def]; exact mulVec_mem O M hMO (y i0) (hyO i0) l
      have htO : hform s J (x i0) yy ∈ O := hform_mem O s hsO J hJO (x i0) yy (hxO i0) hyyO
      obtain ⟨lam, hlamO, hlam, c', hc'O, hc'⟩ := hH i0 (hform s J (x i0) yy) htO
      have hxx0 : hform s J (x i0) (x i0) = β i0 := by rw [hxx, if_pos rfl]
      have hyy0 : hform s J yy yy = β i0 := by rw [hyy_def, hMp, hyy, if_pos rfl]
      have hβr : s (β i0) = β i0 := by
        have h := hform_conj s J hs hJ (x i0) (x i0)
        rwa [hxx0] at h
      have hβ'r : s (β' i0) = β' i0 := s_inv_eq_of_s_eq_of_mul_eq_one s (β i0) (β' i0) hβr (hββ' i0)

      obtain ⟨u, hu_def⟩ : ∃ u : Fin n → S, u = yy - lam • x i0 := ⟨_, rfl⟩
      have huO : ∀ l, u l ∈ O := fun l => by
        rw [hu_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        exact O.sub_mem (hyyO l) (O.mul_mem hlamO (hxO i0 l))
      have huy : hform s J u yy = β i0 - s lam * hform s J (x i0) yy := by
        rw [hu_def, hform_sub_left, hform_smul_left, hyy0]
      have huu : hform s J u u =
          (β i0 - s lam * hform s J (x i0) yy) + s (β i0 - s lam * hform s J (x i0) yy) := by
        rw [hu_def]
        simp only [hform_sub_left, hform_sub_right, hform_smul_left, hform_smul_right]
        rw [hyy0, hxx0, ← hform_conj s J hs hJ (x i0) yy]
        simp only [map_sub, map_mul, hs, hβr]
        linear_combination (β i0) * hlam
      have hcc : c' * (β i0 - s lam * hform s J (x i0) yy) = 1 := by rw [mul_comm]; exact hc'
      obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin n) S, T = rT s J u c' 1 := ⟨_, rfl⟩
      have hT_mul : ∀ z, T *ᵥ z = z - (c' * hform s J u z) • u := fun z => by
        rw [hT, rT_mulVec, map_one, one_smul]
      have hT_pres : ∀ z w, hform s J (T *ᵥ z) (T *ᵥ w) = hform s J z w := fun z w => by
        rw [hT]
        exact rT_preserves s J hs hJ u _ c' 1 (by rw [map_one, one_mul]) huu hcc z w
      have hT_O : ∀ i j, T i j ∈ O := fun i j => by
        rw [hT]; exact rT_mem O s hsO J hJO u huO c' 1 hc'O O.one_mem i j
      have hT_yy : T *ᵥ yy = lam • x i0 := by
        rw [hT_mul, huy, hcc, one_smul, hu_def, sub_sub_cancel]

      obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin n) (Fin n) S,
          D = 1 + (s lam - 1) • pM s J {i0} x β' := ⟨_, rfl⟩
      have hD_mul : ∀ z, D *ᵥ z = z + ((s lam - 1) * (β' i0 * hform s J (x i0) z)) • x i0 :=
        fun z => by
          rw [hD, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, pM_mulVec,
            Finset.sum_singleton, smul_smul]
      have hD_pres : ∀ z w, hform s J (D *ᵥ z) (D *ᵥ w) = hform s J z w := fun z w => by
        rw [hD_mul, hD_mul]
        exact hform_transvection_preserves s hs J hJ (x i0) (β i0) (β' i0) lam hxx0 (hββ' i0) hβ'r hlam z w
      have hD_O : ∀ i j, D i j ∈ O := fun i j => by
        rw [hD, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        exact O.add_mem (Formalism.L2.SG.Pf.NcS.IntWittAlg.one_mem' O i j)
          (O.mul_mem (O.sub_mem (hsO lam hlamO) O.one_mem)
            (pM_mem O s hsO J hJO {i0} x hxO β' hβ'O i j))
      have hD_x : D *ᵥ (lam • x i0) = x i0 := by
        rw [hD_mul, hform_smul_right, hxx0]
        funext l
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination (x i0 l) * hlam + (x i0 l * (lam * s lam - lam)) * hββ' i0

      have hfix : ∀ i : Fin a, i.val < k → D *ᵥ (T *ᵥ x i) = x i := by
        intro i hi
        have hne : i0 ≠ i := fun h => by subst h; omega
        have h0 : hform s J u (x i) = 0 := by
          rw [hu_def, hform_sub_left, hform_smul_left, hxx i0 i, if_neg hne, ← hMy i hi, hyy_def,
            hMp, hyy i0 i, if_neg hne]
          ring
        rw [hT_mul, h0, mul_zero, zero_smul, sub_zero, hD_mul, hxx i0 i, if_neg hne, mul_zero,
          mul_zero, zero_smul, add_zero]
      refine ⟨D * T * M, fun z w => ?_, fun i j => ?_, fun i hi => ?_⟩
      · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, hD_pres, hT_pres, hMp]
      · exact Formalism.L2.SG.Pf.NcS.IntWittAlg.mul_mem' O (D * T) M
          (fun i j => Formalism.L2.SG.Pf.NcS.IntWittAlg.mul_mem' O D T hD_O hT_O i j) hMO i j
      · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
        · rw [hMy i hlt]; exact hfix i hlt
        · have hi' : i = i0 := Fin.ext (by omega)
          rw [hi', ← hyy_def, hT_yy, hD_x]
  obtain ⟨M, hMp, hMO, hMy⟩ := key a le_rfl
  have hU : cT s M * J * M = J := unitary_of s J M hMp
  have hNM : (J' * cT s M * J) * M = 1 := by
    calc (J' * cT s M * J) * M = J' * (cT s M * J * M) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, hJJ']
  have hMN : M * (J' * cT s M * J) = 1 := mul_eq_one_comm.mp hNM
  refine ⟨⟨M, J' * cT s M * J, hMN, hNM⟩, ?_, fun i j => hMO i j, fun i j => ?_, fun i => hMy i i.isLt⟩
  · show cT s M * J * M = J
    exact hU
  · show (J' * cT s M * J) i j ∈ O
    exact Formalism.L2.SG.Pf.NcS.IntWittAlg.mul_mem' O (J' * cT s M) J
      (fun i j => Formalism.L2.SG.Pf.NcS.IntWittAlg.mul_mem' O J' (cT s M) hJ'O
        (fun i j => cT_mem O s hsO M hMO i j) i j) hJO i j

end Formalism.L2.SG.Pf.NcS.IntWittAlg
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittAlg

open Matrix Formalism.UG

section GS

variable {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (J : Matrix (Fin n) (Fin n) K)

theorem exists_aniso (hσ : ∀ z, σ (σ z) = z) (hJ : IsHerm σ J) (h2 : (2 : K) ≠ 0) (u w : Fin n → K)
    (huw : hform σ J u w ≠ 0) : ∃ r t : K, hform σ J (r • u + t • w) (r • u + t • w) ≠ 0 := by
  by_contra H
  push Not at H
  have hexp : ∀ r t : K, hform σ J (r • u + t • w) (r • u + t • w) =
      σ r * r * hform σ J u u + σ r * t * hform σ J u w + σ t * r * hform σ J w u +
        σ t * t * hform σ J w w := by
    intro r t
    simp only [hform_add_left, hform_add_right, hform_smul_left, hform_smul_right]
    ring
  set q := hform σ J u w with hq
  set t : K := 2⁻¹ / q with htdef
  have h1 := H 1 0
  have h2' := H 0 1
  have h3 := H 1 t
  rw [hexp, map_one, map_zero] at h1 h2'
  rw [hexp, map_one] at h3
  have ht : t * q = 2⁻¹ := div_mul_cancel₀ _ huw
  have hst : σ t * hform σ J w u = 2⁻¹ := by
    rw [← hform_conj σ J hσ hJ u w, ← hq, ← map_mul, ht, map_inv₀, map_ofNat]
  have hinv : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  exact one_ne_zero (by linear_combination h3 - h1 - (σ t * t) * h2' - ht - hst - hinv : (1 : K) = 0)

end GS

theorem hermDiag : Formalism.L2.SG.Pf.NcS.IntWittPf.HermDiag := by
  intro K _ σ hσ h2 n J hJ a X0 hT
  classical
  have hconj := hform_conj σ J hσ hJ
  let W : Submodule K (Fin n → K) := Submodule.span K (Set.range X0)
  let comb : (Fin a → K) → (Fin n → K) := fun c => ∑ l, c l • X0 l
  have hN : ∀ c : Fin a → K, (∀ j, hform σ J (X0 j) (comb c) = 0) → c = 0 := by
    intro c hc
    refine Matrix.eq_zero_of_mulVec_eq_zero hT ?_
    funext j
    have e : hform σ J (X0 j) (∑ l, c l • X0 l) = 0 := hc j
    rw [hform_sum_right] at e
    simp only [mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← e]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hcW : ∀ c, comb c ∈ W := fun c => W.sum_mem fun l _ => W.smul_mem _ (Submodule.subset_span ⟨l, rfl⟩)
  have main : ∀ k ≤ a, ∃ Z : Fin k → Fin n → K, (∀ i, Z i ∈ W) ∧
      (∀ i j, i ≠ j → hform σ J (Z i) (Z j) = 0) ∧ ∀ i, hform σ J (Z i) (Z i) ≠ 0 := by
    intro k
    induction k with
    | zero => intro _; exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨Z, hZW, hZo, hZd⟩ := ih (by omega)
      let f : (Fin a → K) →ₗ[K] (Fin k → K) :=
        { toFun := fun c i => hform σ J (Z i) (comb c)
          map_add' := by
            intro c d
            funext i
            simp only [comb, Pi.add_apply, add_smul, Finset.sum_add_distrib, hform_add_right]
          map_smul' := by
            intro r c
            funext i
            simp only [comb, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← smul_smul, ← Finset.smul_sum,
              hform_smul_right] }
      have hlt : Module.finrank K (Fin k → K) < Module.finrank K (Fin a → K) := by
        simp only [Module.finrank_fin_fun]
        omega
      obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt)
      have hcZ : ∀ i, hform σ J (Z i) (comb c) = 0 := fun i => congrFun (LinearMap.mem_ker.1 hc) i
      obtain ⟨j, hj⟩ : ∃ j, hform σ J (X0 j) (comb c) ≠ 0 := by
        by_contra H
        push Not at H
        exact hc0 (hN c H)
      let w := X0 j - ∑ i, (hform σ J (Z i) (X0 j) / hform σ J (Z i) (Z i)) • Z i
      have hwZ : ∀ m, hform σ J (Z m) w = 0 := by
        intro m
        simp only [w, hform_sub_right, hform_sum_right]
        rw [Finset.sum_eq_single m]
        · rw [div_mul_cancel₀ _ (hZd m), sub_self]
        · intro i _ him
          rw [hZo m i (Ne.symm him), mul_zero]
        · simp
      have hwc : hform σ J w (comb c) ≠ 0 := by
        simp only [w, hform_sub_left, hform_sum_left]
        rw [Finset.sum_eq_zero, sub_zero]
        · exact hj
        · intro i _
          rw [hcZ i, mul_zero]
      have hwW : w ∈ W := W.sub_mem (Submodule.subset_span ⟨j, rfl⟩) (W.sum_mem fun i _ => W.smul_mem _ (hZW i))
      obtain ⟨r, t, hz⟩ := exists_aniso σ J hσ hJ h2 w (comb c) hwc
      set z := r • w + t • comb c with hzdef
      have hzZ : ∀ m, hform σ J (Z m) z = 0 := by
        intro m
        rw [hzdef, hform_add_right, hform_smul_right, hform_smul_right, hwZ, hcZ, mul_zero, mul_zero, add_zero]
      refine ⟨Fin.snoc Z z, ?_, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · rw [Fin.snoc_last]
          exact W.add_mem (W.smul_mem _ hwW) (W.smul_mem _ (hcW c))
        · rw [Fin.snoc_castSucc]
          exact hZW i
      · intro i j
        refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
        · intro h; exact absurd rfl h
        · intro _
          rw [Fin.snoc_last, Fin.snoc_castSucc, ← hconj, hzZ, map_zero]
        · intro _
          rw [Fin.snoc_last, Fin.snoc_castSucc]
          exact hzZ i
        · intro hij
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hZo i j (fun e => hij (by rw [e]))
      · intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · rw [Fin.snoc_last]
          exact hz
        · rw [Fin.snoc_castSucc]
          exact hZd i
  obtain ⟨Z, hZW, hZo, hZd⟩ := main a le_rfl
  have hex : ∀ i, ∃ c : Fin a → K, ∑ l, c l • X0 l = Z i :=
    fun i => (Submodule.mem_span_range_iff_exists_fun K).1 (hZW i)
  choose C hC using hex
  let P : Matrix (Fin a) (Fin a) K := Matrix.of C
  have hPX : ∀ i, ∑ l, P i l • X0 l = Z i := fun i => hC i
  have hdet : P.det ≠ 0 := by
    intro hd
    obtain ⟨c, hc0, hcP⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    apply hc0
    funext j
    have e : ∑ i, c i • Z i = 0 := by
      have hl : ∀ l, ∑ i, c i * P i l = 0 := fun l => by
        have := congrFun hcP l
        simpa [vecMul, dotProduct] using this
      simp_rw [← hPX, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, hl, zero_smul, Finset.sum_const_zero]
    have h := congrArg (hform σ J (Z j)) e
    rw [hform_sum_right, hform_zero_right, Finset.sum_eq_single j] at h
    · exact (mul_eq_zero.1 h).resolve_right (hZd j)
    · intro i _ hij
      rw [hZo j i (Ne.symm hij), mul_zero]
    · simp
  refine ⟨P, P⁻¹, Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.2 hdet), ?_, ?_⟩
  · intro i j hij
    rw [hPX, hPX]
    exact hZo i j hij
  · intro i
    rw [hPX]
    exact hZd i

end Formalism.L2.SG.Pf.NcS.IntWittAlg
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter
open scoped TensorProduct

theorem norm_id {S : Type} [CommRing S] (B p q a b D Θ : S) (h : Θ ^ 2 = D) :
    (B - (p - q * Θ) * (a + b * Θ)) * (B - (p + q * Θ) * (a - b * Θ)) =
      (B - p * a + q * b * D) ^ 2 - D * (q * a - p * b) ^ 2 := by
  linear_combination (q * b * (2 * (B - p * a) + q * b * (Θ ^ 2 + D)) - (p * b - q * a) ^ 2) * h

theorem norm_one {S : Type} [CommRing S] (p q D Θ : S) (h : Θ ^ 2 = D) :
    (p + q * Θ) * (p - q * Θ) = p ^ 2 - D * q ^ 2 := by
  linear_combination (-q ^ 2) * h

theorem core_loc {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] (ι : R →+* S) (s : S →+* S)
    (O : Subring S) (hιO : ∀ r, ι r ∈ O) (Θ : S) (hΘO : Θ ∈ O) (D Bt P Q a b : R)
    (hΘ : Θ ^ 2 = ι D) (hsΘ : s Θ = -Θ) (hsι : ∀ r, s (ι r) = ι r) (hPQ : P ^ 2 - D * Q ^ 2 = 1)
    (Bi K i4 : R) (hB : Bt * Bi = 1) (hK : Q * D * K = 1) (h4 : (4 : R) * i4 = 1) :
    ∃ lam ∈ O, lam * s lam = 1 ∧ ∃ c' ∈ O, (ι Bt - s lam * (ι a + ι b * Θ)) * c' = 1 := by
  let pp : Fin 4 → R := ![1, -1, P, -P]
  let qq : Fin 4 → R := ![0, 0, Q, -Q]
  let f : Fin 4 → R := fun i => (Bt - pp i * a + qq i * b * D) ^ 2 - D * (qq i * a - pp i * b) ^ 2
  have ef0 : f 0 = (Bt - a) ^ 2 - D * b ^ 2 := by simp [f, pp, qq] <;> ring
  have ef1 : f 1 = (Bt + a) ^ 2 - D * b ^ 2 := by simp [f, pp, qq] <;> ring
  have ef2 : f 2 = (Bt - P * a + Q * b * D) ^ 2 - D * (Q * a - P * b) ^ 2 := by simp [f, pp, qq] <;> ring
  have ef3 : f 3 = (Bt + P * a - Q * b * D) ^ 2 - D * (Q * a - P * b) ^ 2 := by simp [f, pp, qq] <;> ring
  have hspanTop : Ideal.span (Set.range f) = ⊤ := by
    have mem : ∀ i, f i ∈ Ideal.span (Set.range f) := fun i => Ideal.subset_span ⟨i, rfl⟩
    have ha : a ∈ Ideal.span (Set.range f) := by
      have : a = i4 * Bi * (f 1 - f 0) := by
        rw [ef1, ef0]; linear_combination (-a) * h4 + (-4 * i4 * a) * hB
      rw [this]; exact Ideal.mul_mem_left _ _ (sub_mem (mem 1) (mem 0))
    have hm : P * a - Q * D * b ∈ Ideal.span (Set.range f) := by
      have : P * a - Q * D * b = i4 * Bi * (f 3 - f 2) := by
        rw [ef3, ef2]
        linear_combination (-(P * a - Q * D * b)) * h4 + (-4 * i4 * (P * a - Q * D * b)) * hB
      rw [this]; exact Ideal.mul_mem_left _ _ (sub_mem (mem 3) (mem 2))
    have hb : b ∈ Ideal.span (Set.range f) := by
      have : b = K * (P * a - (P * a - Q * D * b)) := by linear_combination (-b) * hK
      rw [this]; exact Ideal.mul_mem_left _ _ (sub_mem (Ideal.mul_mem_left _ _ ha) hm)
    have hN : a ^ 2 - D * b ^ 2 ∈ Ideal.span (Set.range f) := by
      have : a ^ 2 - D * b ^ 2 = a * a - (D * b) * b := by ring
      rw [this]; exact sub_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
    have hB2 : Bt ^ 2 ∈ Ideal.span (Set.range f) := by
      have : Bt ^ 2 = f 0 + (2 * Bt) * a - (a ^ 2 - D * b ^ 2) := by rw [ef0]; ring
      rw [this]; exact sub_mem (add_mem (mem 0) (Ideal.mul_mem_left _ _ ha)) hN
    rw [Ideal.eq_top_iff_one]
    have : (1 : R) = Bi ^ 2 * Bt ^ 2 := by linear_combination (-(Bt * Bi + 1)) * hB
    rw [this]; exact Ideal.mul_mem_left _ _ hB2
  have hnorm : ∀ i, pp i ^ 2 - D * qq i ^ 2 = 1 := by
    intro i; fin_cases i <;> simp [pp, qq] <;> linear_combination hPQ
  obtain ⟨i, hi⟩ : ∃ i, IsUnit (f i) := by
    by_contra H
    push Not at H
    have hle : Ideal.span (Set.range f) ≤ IsLocalRing.maximalIdeal R := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).2 (H i)
    rw [hspanTop] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.1 hle)
  set L : S := ι (pp i) + ι (qq i) * Θ with hL
  set M : S := ι (pp i) - ι (qq i) * Θ with hM
  have hsL : s L = M := by rw [hL, hM, map_add, map_mul, hsι, hsι, hsΘ]; ring
  have hsM : s M = L := by rw [hL, hM, map_sub, map_mul, hsι, hsι, hsΘ]; ring
  have hLM : L * M = 1 := by
    rw [hL, hM, norm_one _ _ _ _ hΘ, ← map_pow, ← map_pow, ← map_mul, ← map_sub, hnorm i, map_one]
  set c : S := ι Bt - M * (ι a + ι b * Θ) with hc
  set sc : S := ι Bt - L * (ι a - ι b * Θ) with hsc
  have hcc : c * sc = ι (f i) := by
    rw [hc, hsc, hL, hM]
    simp only [f, map_sub, map_add, map_mul, map_pow]
    exact norm_id _ _ _ _ _ _ _ hΘ
  obtain ⟨u, hu⟩ := hi
  have hLO : L ∈ O := O.add_mem (hιO _) (O.mul_mem (hιO _) hΘO)
  have hMO : M ∈ O := O.sub_mem (hιO _) (O.mul_mem (hιO _) hΘO)
  refine ⟨L, hLO, by rw [hsL]; exact hLM, sc * ι ((u⁻¹ : Rˣ) : R), ?_, ?_⟩
  · exact O.mul_mem (O.sub_mem (hιO _) (O.mul_mem hLO (O.sub_mem (hιO _) (O.mul_mem (hιO _) hΘO)))) (hιO _)
  · rw [hsL, ← hc, ← mul_assoc, hcc, ← hu, ← map_mul, Units.mul_inv, map_one]

end Formalism.L2.SG.Pf.NcS.IntWittPf
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter
  Formalism.L2.SG.Pf.NcS.KfOrbPf
open scoped TensorProduct

theorem lamAE : LamAE := by
  intro F E _ _ _ _ _ σ hCM δ hδ hδ0
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hσ : ∀ z, σ (σ z) = z := PI.VolStabS.sigma_invol σ hCM.2.2.2
  obtain ⟨x, hx⟩ : ∃ x : E, σ x ≠ x := by
    by_contra H
    push Not at H
    let w : InfinitePlace E := Classical.arbitrary _
    have hreal : ComplexEmbedding.IsReal w.embedding := by
      rw [ComplexEmbedding.isReal_iff]
      ext z
      rw [ComplexEmbedding.conjugate_coe_eq, ← Complex.star_def, ← hCM.2.2.2, H z]
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (hCM.2.1.isComplex w)) (InfinitePlace.isReal_iff.2 hreal)
  set θ : E := x - σ x with hθdef
  have hσθ : σ θ = -θ := by rw [hθdef, map_sub, hσ]; ring
  have hθ0 : θ ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hind : ∀ p q : F, algebraMap F E p + algebraMap F E q * θ = 0 → p = 0 ∧ q = 0 := by
    intro p q h
    have h' := congrArg σ h
    rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσθ, map_zero] at h'
    have hq : (2 : E) * (algebraMap F E q * θ) = 0 := by linear_combination h - h'
    have hq0 : q = 0 := by
      rcases mul_eq_zero.1 ((mul_eq_zero.1 hq).resolve_left two_ne_zero) with h1 | h1
      · exact (algebraMap F E).injective (by rw [h1, map_zero])
      · exact absurd h1 hθ0
    subst hq0
    rw [map_zero, zero_mul, add_zero] at h
    exact ⟨(algebraMap F E).injective (by rw [h, map_zero]), rfl⟩
  let v2 : Fin 2 → E := ![1, θ]
  have hli : LinearIndependent F v2 := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_two] at hg
    have e : algebraMap F E (g 0) + algebraMap F E (g 1) * θ = 0 := by
      rw [← hg]; simp [v2, Algebra.smul_def]
    obtain ⟨h0, h1⟩ := hind _ _ e
    intro i
    fin_cases i
    · exact h0
    · exact h1
  let b2 : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hCM.2.2.1])
  have hb2 : ∀ i, b2 i = v2 i := fun i => by
    simp only [b2, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hdec : ∀ e : E, e = algebraMap F E (b2.repr e 0) + algebraMap F E (b2.repr e 1) * θ := by
    intro e
    conv_lhs => rw [← b2.sum_repr e]
    rw [Fin.sum_univ_two, hb2, hb2]
    simp [v2, Algebra.smul_def]

  have hfixF : ∀ e : E, σ e = e → e = algebraMap F E (b2.repr e 0) := by
    intro e he
    have h1 := hdec e
    have h2 := congrArg σ h1
    rw [he, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσθ] at h2
    have h3 : algebraMap F E 0 + algebraMap F E (2 * b2.repr e 1) * θ = 0 := by
      rw [map_zero, map_mul, map_ofNat]; linear_combination h2 - h1
    have hq := (hind _ _ h3).2
    have hq' : b2.repr e 1 = 0 := (mul_eq_zero.1 hq).resolve_left two_ne_zero
    rw [hq', map_zero (algebraMap F E), zero_mul, add_zero] at h1
    exact h1
  have hθ2σ : σ (θ ^ 2) = θ ^ 2 := by rw [map_pow, hσθ, neg_sq]
  set d := b2.repr (θ ^ 2) 0 with hd_def
  have hd : θ ^ 2 = algebraMap F E d := hfixF _ hθ2σ
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, map_zero] at hd
    exact hθ0 ((pow_eq_zero_iff two_ne_zero).1 hd)
  have hd1 : d ≠ 1 := by
    intro h
    rw [h, map_one] at hd
    have h1 : (θ - 1) * (θ + 1) = 0 := by linear_combination hd
    rcases mul_eq_zero.1 h1 with h | h
    · have e : θ = 1 := sub_eq_zero.1 h
      rw [e, map_one] at hσθ
      exact two_ne_zero (by linear_combination hσθ : (2 : E) = 0)
    · have e : θ = -1 := eq_neg_of_add_eq_zero_left h
      rw [e, map_neg, map_one] at hσθ
      exact two_ne_zero (by linear_combination -hσθ : (2 : E) = 0)
  set β0 := b2.repr δ 0 with hβ0_def
  have hδF : δ = algebraMap F E β0 := hfixF δ hδ
  have hβ0 : β0 ≠ 0 := by
    intro h
    rw [h, map_zero] at hδF
    exact hδ0 hδF
  have h1d : (1 - d) ≠ 0 := sub_ne_zero.2 (Ne.symm hd1)
  set Pc : F := (1 + d) / (1 - d) with hPc
  set Qc : F := 2 / (1 - d) with hQc_def
  have hQc : Qc ≠ 0 := div_ne_zero two_ne_zero h1d
  have hpq : Pc ^ 2 - d * Qc ^ 2 = 1 := by
    rw [hPc, hQc_def]
    field_simp
    ring
  filter_upwards [ev_int (F := F) d, ev_int (F := F) β0, ev_int (F := F) β0⁻¹, ev_int (F := F) Pc,
    ev_int (F := F) Qc, ev_int (F := F) (Qc * d)⁻¹, ev_int (F := F) (4 : F)⁻¹, ev_oev (F := F) θ, ev_crd_oev b2]
    with v hdv hβv hβiv hPv hQv hKv h4v hθv hcrd
  intro t ht
  let ι : v.adicCompletionIntegers F →+* Fv F v ⊗[F] E :=
    (algebraMap (Fv F v) (Fv F v ⊗[F] E)).comp (v.adicCompletionIntegers F).subtype
  have hιF : ∀ (y : F) (hy : algebraMap F (Fv F v) y ∈ v.adicCompletionIntegers F),
      ι ⟨_, hy⟩ = algebraMap F (Fv F v ⊗[F] E) y := by
    intro y hy
    show algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) y) = _
    rw [← IsScalarTower.algebraMap_apply]
  have hιO : ∀ r, ι r ∈ oevRing (E := E) v := by
    intro r
    show algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) ∈ OEv (E := E) v
    rw [Algebra.algebraMap_eq_smul_one]
    exact oev_smul' v r.2 (oev_one v)
  have hsι : ∀ r, sigR (Fv F v) σ (ι r) = ι r := by
    intro r
    show sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v)) = _
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have hincl : ∀ y : F, inclR (F := F) (Fv F v) (algebraMap F E y) = algebraMap F (Fv F v ⊗[F] E) y :=
    fun y => (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E).commutes y
  have hΘ : (inclR (F := F) (Fv F v) θ) ^ 2 = ι ⟨_, hdv⟩ := by
    rw [hιF, ← map_pow, hd, hincl]
  have hsΘ : sigR (Fv F v) σ (inclR (F := F) (Fv F v) θ) = -inclR (F := F) (Fv F v) θ := by
    simp [sigR, inclR, hσθ, TensorProduct.tmul_neg]
  have hcrd' := hcrd t ht
  have htd : t = ι ⟨_, hcrd' 0⟩ + ι ⟨_, hcrd' 1⟩ * inclR (F := F) (Fv F v) θ := by
    conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b2).sum_repr t]
    rw [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply, hb2, hb2]
    show _ = algebraMap (Fv F v) (Fv F v ⊗[F] E) (PI.VolStabS.PositiveNearLattice.crd b2 (Fv F v) t 0) +
      algebraMap (Fv F v) (Fv F v ⊗[F] E) (PI.VolStabS.PositiveNearLattice.crd b2 (Fv F v) t 1) * inclR (F := F) (Fv F v) θ
    simp only [PI.VolStabS.PositiveNearLattice.crd, Algebra.smul_def, v2, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp [inclR]
  have hPQ : (⟨_, hPv⟩ : v.adicCompletionIntegers F) ^ 2 - ⟨_, hdv⟩ * ⟨_, hQv⟩ ^ 2 = 1 := by
    apply Subtype.ext
    show (algebraMap F (Fv F v) Pc) ^ 2 - algebraMap F (Fv F v) d * (algebraMap F (Fv F v) Qc) ^ 2 = 1
    rw [← map_pow, ← map_pow, ← map_mul, ← map_sub, hpq, map_one]
  have hB : (⟨_, hβv⟩ : v.adicCompletionIntegers F) * ⟨_, hβiv⟩ = 1 := by
    apply Subtype.ext
    show algebraMap F (Fv F v) β0 * algebraMap F (Fv F v) β0⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hβ0, map_one]
  have hK : (⟨_, hQv⟩ : v.adicCompletionIntegers F) * ⟨_, hdv⟩ * ⟨_, hKv⟩ = 1 := by
    apply Subtype.ext
    show algebraMap F (Fv F v) Qc * algebraMap F (Fv F v) d * algebraMap F (Fv F v) (Qc * d)⁻¹ = 1
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (mul_ne_zero hQc hd0), map_one]
  have h4 : (4 : v.adicCompletionIntegers F) * ⟨_, h4v⟩ = 1 := by
    apply Subtype.ext
    show ((4 : v.adicCompletionIntegers F) : Fv F v) * algebraMap F (Fv F v) (4 : F)⁻¹ = 1
    have e4 : ((4 : v.adicCompletionIntegers F) : Fv F v) = algebraMap F (Fv F v) 4 := by
      rw [map_ofNat]; rfl
    rw [e4, ← map_mul, mul_inv_cancel₀ (by norm_num), map_one]
  obtain ⟨lam, hlamO, hlam, c', hc'O, hc'⟩ := core_loc ι (sigR (Fv F v) σ) (oevRing (E := E) v) hιO
    (inclR (F := F) (Fv F v) θ) hθv ⟨_, hdv⟩ ⟨_, hβv⟩ ⟨_, hPv⟩ ⟨_, hQv⟩ ⟨_, hcrd' 0⟩ ⟨_, hcrd' 1⟩
    hΘ hsΘ hsι hPQ ⟨_, hβiv⟩ ⟨_, hKv⟩ ⟨_, h4v⟩ hB hK h4
  refine ⟨lam, hlamO, hlam, c', hc'O, ?_⟩
  have hδι : inclR (F := F) (Fv F v) δ = ι ⟨_, hβv⟩ := by rw [hιF, hδF, hincl]
  rw [hδι]
  conv_lhs => rw [htd]
  exact hc'

end Formalism.L2.SG.Pf.NcS.IntWittPf
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter
  Matrix Formalism.L2.SG.Pf.NcS.KfOrbPf Formalism.L2.SG.Pf.NcS.IntWittAlg
open scoped TensorProduct

section Main

theorem sigR_inclR' {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem hform_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Formalism.UG.hform (sigR R σ) (JR R J) (fun i => inclR R (x i)) (fun i => inclR R (y i)) =
      inclR R (Formalism.UG.hform (σ : E →+* E) J x y) := by
  simp only [Formalism.UG.hform, map_sum, map_mul, JR, Matrix.map_apply, sigR_inclR']
  rfl

theorem intWittAE_of (hA : AlgWitt) (hD : HermDiag) (hL : LamAE) : LocSBPf.IntWittAE := by
  intro F E _ _ _ _ _ σ n J a X0 Λ hCM hJ hT hLat d b
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨L, hLL, rfl⟩ := hLat
  have hσ : ∀ z, σ (σ z) = z := PI.VolStabS.sigma_invol σ hCM.2.2.2
  have hJh : Formalism.UG.IsHerm (σ : E →+* E) J := by
    unfold Formalism.UG.IsHerm Formalism.UG.cT
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    exact hJ.1 i j
  obtain ⟨P, Q, hQP, hPo, hPd⟩ := hD E (σ : E →+* E) hσ two_ne_zero n J hJh a X0 hT
  set Z0 : Fin a → Fin n → E := fun i => ∑ l, P i l • X0 l with hZ0
  have hZ0e : ∀ i, Z0 i = ∑ l, P i l • X0 l := fun i => rfl
  have hX0e : ∀ c, X0 c = ∑ l, Q c l • Z0 l := fun c => by
    funext k
    simp only [hZ0, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hm : ∀ m, ∑ l, Q c l * (P l m * X0 m k) = (if c = m then 1 else 0) * X0 m k := by
      intro m
      simp_rw [← mul_assoc, ← Finset.sum_mul]
      rw [← Matrix.mul_apply, hQP, Matrix.one_apply]
    simp_rw [hm]
    simp
  let δ : Fin a → E := fun i => Formalism.UG.hform (σ : E →+* E) J (Z0 i) (Z0 i)
  have hδσ : ∀ i, σ (δ i) = δ i := fun i => hform_conj (σ : E →+* E) J hσ hJh _ _
  have hJi : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J (isUnit_iff_ne_zero.2 hJ.2)
  filter_upwards [ev_latLoc_std L hLL,
    eventually_all.2 fun k => ev_oev (F := F) (b k),
    eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (J i j),
    eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (J⁻¹ i j),
    eventually_all.2 fun i => ev_oev (F := F) (δ i),
    eventually_all.2 fun i => ev_oev (F := F) (δ i)⁻¹,
    eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (P i j),
    eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (Z0 i j),
    eventually_all.2 fun i => hL F E σ hCM (δ i) (hδσ i) (hPd i)]
    with v hstd hbv hJv hJiv hδv hδiv hPv hZv hlam
  intro X hX hgram
  let O := oevRing (E := E) v
  have hXO : ∀ c k, X c k ∈ O := by
    intro c k
    show X c k ∈ OEv (E := E) v
    rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr (X c k)]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
    exact oev_smul' v (hX c k l) (hbv l)
  let s := sigR (Fv F v) σ
  have hs : ∀ z, s (s z) = z := PI.VolStabS.sigR_invol (Fv F v) σ hσ
  have hsO : ∀ z ∈ O, s z ∈ O := by
    intro z hz
    exact oev_sigR v σ hz
  let Jv := JR (F := F) (Fv F v) J
  let Jv' := JR (F := F) (Fv F v) J⁻¹
  have hJJ : Jv' * Jv = 1 := by
    show J⁻¹.map (inclR (F := F) (Fv F v)) * J.map (inclR (F := F) (Fv F v)) = 1
    rw [← Matrix.map_mul, hJi, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJvh : Formalism.UG.IsHerm s Jv := by
    unfold Formalism.UG.IsHerm Formalism.UG.cT
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Jv, JR, s, sigR_inclR']
    rw [hJ.1 i j]
  let y : Fin a → Fin n → Fv F v ⊗[F] E := fun i k => inclR (F := F) (Fv F v) (Z0 i k)
  let x : Fin a → Fin n → Fv F v ⊗[F] E := fun i => ∑ l, inclR (F := F) (Fv F v) (P i l) • X l
  have hxO : ∀ i k, x i k ∈ O := by
    intro i k
    simp only [x, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact O.sum_mem fun l _ => O.mul_mem (hPv i l) (hXO l k)
  have hyy : ∀ i j, Formalism.UG.hform s Jv (y i) (y j) = if i = j then inclR (F := F) (Fv F v) (δ i) else 0 := by
    intro i j
    rw [show Formalism.UG.hform s Jv (y i) (y j) = inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (Z0 i) (Z0 j)) from
      hform_inclR _ σ J _ _]
    split_ifs with h
    · subst h; rfl
    · rw [hPo i j h, map_zero]
  have hXX : ∀ l m, Formalism.UG.hform s Jv (X l) (X m) =
      inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (X0 l) (X0 m)) := by
    intro l m
    exact congrFun (congrFun hgram l) m
  have hxx : ∀ i j, Formalism.UG.hform s Jv (x i) (x j) = if i = j then inclR (F := F) (Fv F v) (δ i) else 0 := by
    intro i j
    have e1 : Formalism.UG.hform s Jv (x i) (x j) = inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (Z0 i) (Z0 j)) := by
      calc Formalism.UG.hform s Jv (x i) (x j)
          = ∑ l, inclR (F := F) (Fv F v) (σ (P i l)) * ∑ m, inclR (F := F) (Fv F v) (P j m) *
              inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (X0 l) (X0 m)) := by
            simp only [x]
            rw [hform_sum_left]
            simp_rw [hform_sum_right, hXX, s, sigR_inclR']
        _ = _ := by
            rw [hZ0e i, hZ0e j, hform_sum_left]
            simp_rw [hform_sum_right]
            simp only [map_sum, map_mul]
            rfl
    rw [e1]
    split_ifs with h
    · subst h; rfl
    · rw [hPo i j h, map_zero]
  obtain ⟨g, hg, hgO, hgiO, hgy⟩ := hA (Fv F v ⊗[F] E) s O hs hsO n Jv Jv' hJvh hJJ hJv hJiv a
    (fun i => inclR (F := F) (Fv F v) (δ i)) (fun i => inclR (F := F) (Fv F v) (δ i)⁻¹) hδv hδiv
    (fun i => by rw [← map_mul, mul_inv_cancel₀ (hPd i), map_one])
    hlam x y hxO hZv hxx hyy
  refine ⟨(⟨g, hg⟩ : HR (Fv F v) σ J), ?_, ?_⟩
  · show ∀ w, w ∈ latLoc (E := E) v (L : Set (Fin n → E)) ↔
      (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ w ∈ latLoc (E := E) v (L : Set (Fin n → E))
    rw [hstd]
    intro w
    constructor
    · intro hw
      exact mem_std_of_oev v _ fun i => mulVec_mem O _ hgO w (fun k => mem_oev_of_std v w hw k) i
    · intro hw
      have e : w = ((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ
          ((g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ w) := by
        rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
      rw [e]
      exact mem_std_of_oev v _ fun i => mulVec_mem O _ hgiO _ (fun k => mem_oev_of_std v _ hw k) i
  · funext c
    show (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ ratTup (F := F) (Fv F v) X0 c = X c
    have e1 : ratTup (F := F) (Fv F v) X0 c = ∑ l, inclR (F := F) (Fv F v) (Q c l) • y l := by
      funext k
      simp only [ratTup, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, y]
      rw [hX0e c]
      simp [Finset.sum_apply, map_sum, map_mul]
    rw [e1, mulVec_sum]
    simp_rw [mulVec_smul, hgy]
    funext k
    simp only [x, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hm : ∀ m, ∑ l, inclR (F := F) (Fv F v) (Q c l) * (inclR (F := F) (Fv F v) (P l m) * X m k) =
        (if c = m then 1 else 0) * X m k := by
      intro m
      simp_rw [← mul_assoc, ← Finset.sum_mul, ← map_mul, ← map_sum]
      rw [← Matrix.mul_apply, hQP, Matrix.one_apply]
      split_ifs <;> simp
    simp_rw [hm]
    simp

end Main

theorem integral_witt_almost_everywhere : Formalism.L2.SG.Pf.NcS.LocSBPf.IntWittAE :=
  intWittAE_of IntWittAlg.algWitt IntWittAlg.hermDiag lamAE

end Formalism.L2.SG.Pf.NcS.IntWittPf
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.NcAllS

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.LocVol
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

set_option maxHeartbeats 4000000 in
variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem ncTieAllS_of (hSplit : Formalism.L2.SG.Pf.NcSplitS.SplitOm) (hRB : Formalism.L2.SG.Pf.NcReal.RealBracket)
    (hHyp : HypX X hb FdN FdN' u u') (hMC : MeasCompatψ X ψ) (hStd : StdHyp X.B.I.cm.sig X.B.I.J ψ)
    (hLat : ∃ L : Submodule (NumberField.RingOfIntegers X.B.I.E) (Fin X.B.I.n → X.B.I.E),
      Submodule.IsLattice X.B.I.E L ∧ (L : Set (Fin X.B.I.n → X.B.I.E)) = (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
    (hdet : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0)
    (hSW1 : Formalism.MainNotions.UnusedSlot34.SWa1 X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J)
    (hSW2 : Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J)
    (hP : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos)
    (hM : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMass)
    (hMs : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMasses)
    (hL : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InLevelS)
    (hO : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InOrdinary)
    (hTy : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InTyped)
    (hV : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InVolumes)
    (hVG : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG)
    (hcong : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hRR : IsRowReps D F0 what₂)
    (hVo : Formalism.L2.SG.Pf.NcVal.VolOrdV X u u' ψ) (hVt : Formalism.L2.SG.Pf.NcVal.VolTypV X u u' ψ)
    (hIx : Formalism.L2.SG.Pf.NcIdx.IndexTypC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hOm : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ) (hFD : Formalism.L2.SG.Pf.NcVal.FieldDict X u u')
    (hPC : ProdConv X u u' ψ) :
    NcTieC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂) := by
  obtain ⟨⟨hT1, νH, hOmT, hCT⟩, -⟩ := hMC.1 u'
  have hn : X.B.I.n = D.R.r := hFD.2.2.2.2.2.2.1
  have hk5 : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hm := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hn2 : 2 * (D.R.rS + 1 + D.R.rS) < X.B.I.n := by rw [hn]; omega

  have hp := hP.1
  have hKo := hP.2.1
  have hprod : 0 < ∏ p : TypX X, (X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _) p.1)).toReal :=
    Finset.prod_pos fun p _ => (hp p).2.2.2.2.2.1
  have hKf : 0 < (X.measG.μGf (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _))).toReal := by
    have h := hKo
    change 0 < (X.measG.μGf (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _))).toReal / _ at h
    exact (div_pos_iff_of_pos_right hprod).1 h
  obtain ⟨hK0, hKtop⟩ := ENNReal.toReal_pos_iff.1 hKf
  obtain ⟨a', ha, hinf, hfin⟩ := hSplit X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ψ D.R.rS (frameOf X u')
    X.measG (X.measW u') hT1 νH (X.B.I.L : Set _) hStd hLat hdet hn2 hSW1 hSW2 X.measG_norm (X.measW_norm u')
    hOmT hCT (by exact hK0) (by exact hKtop)
  have hR0 := hRB X hb FdN FdN' u u' ψ hHyp hMC hStd.2.2.2 hT1 a' ha hinf
  have e1 : Formalism.L2.SG.Pf.NcReal.eDF D.R.k D.R.rS =
      -(8 * (D.R.rS : ℝ) ^ 3 + 6 * (D.R.rS : ℝ) ^ 2 + 6 * D.R.k * (D.R.rS : ℝ) ^ 2 + D.R.rS) / 3 := by
    unfold Formalism.L2.SG.Pf.NcReal.eDF; ring
  rw [e1] at hR0
  have hR : Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN' =
      a' * 2 ^ (D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F)) *
        (Real.pi ^ D.R.k / (Nat.factorial (D.R.k - 1) : ℝ)) ^ Fintype.card (NumberField.InfinitePlace X.B.I.F) *
        ((Tw u : ℕ) : ℝ) ^ (-((D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F) : ℕ) : ℤ)) *
        |(NumberField.discr X.B.I.F : ℝ)| ^
          (-(8 * (D.R.rS : ℝ) ^ 3 + 6 * (D.R.rS : ℝ) ^ 2 + 6 * D.R.k * (D.R.rS : ℝ) ^ 2 + D.R.rS) / 3) := hR0
  have hμK : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK =
      (X.measG.μGf (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _))).toReal := by
    show (X.measG.μGf (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _))).toReal /
        (∏ p : TypX X, (X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _) p.1)).toReal) *
        ∏ p : TypX X, (X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _) p.1)).toReal = _
    rw [div_mul_cancel₀ _ hprod.ne']
  have hS : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK * a' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' *
        ∏' v : PlX X,
          (omAt X.B.I.cm.sig X.B.I.J ψ v
            ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
            {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
              Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal := by
    rw [hμK]
    exact hfin
  exact Formalism.L2.SG.Pf.NcLeaves.ncTieC_of_leaves X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq a' ha
    hP hM hMs hL hO hTy hV hVG hStd.2.2.1 hStd.2.2.2 hcong hRR hS hR hVo hVt hIx hOm hFD hPC

set_option maxHeartbeats 4000000 in
variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem ncTie0All_of (hRB : Formalism.L2.SG.Pf.NcReal.RealBracket) (hSW : PI.VolStabS.MassDataS.SWXS)
    (hHyp : HypX X hb FdN FdN' u u') (hMC : MeasCompatψ X ψ) (hStd : StdHyp X.B.I.cm.sig X.B.I.J ψ)
    (hLat : ∃ L : Submodule (NumberField.RingOfIntegers X.B.I.E) (Fin X.B.I.n → X.B.I.E),
      Submodule.IsLattice X.B.I.E L ∧ (L : Set (Fin X.B.I.n → X.B.I.E)) = (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
    (hdet' : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0)
    (hdet : (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0) (hPC : ProdConv X u u' ψ)
    (hL : LocTieX X ψ u) (hL' : LocTieX X ψ u') (hTF : TypFacts X u u')
    (hQ : Formalism.L2.SG.Pf.MassDataPos.QuotVolPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hsd : 0 ≤ sd) (hC0 : 0 ≤ C) (hTh : 0 < Th)
    (hcong : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hRR : IsRowReps D F0 what₂) :
    NcTieC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂) :=
  ncTieAllS_of X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq
    (Formalism.L2.SG.Pf.NcS.SplitPf.splitOm_of_intWitt Formalism.L2.SG.Pf.NcS.IntWittPf.integral_witt_almost_everywhere) hRB hHyp hMC hStd hLat
    hdet' (hSW X).1 (hSW X).2
    (Formalism.L2.SG.Pf.MassDataX.pos_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hSW hHyp hPC hStd.2.2.1 hMC
      hdet hQ hsd hC0 hTh)
    (Formalism.L2.SG.Pf.MassDataX.inMass_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (Formalism.L2.SG.Pf.MassDataX.inMasses_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hHyp)
    (Formalism.L2.SG.Pf.MassDataX.inLevelS_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hHyp)
    (Formalism.L2.SG.MassDataConc.inOrdinary_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hPC)
    (Formalism.L2.SG.Pf.MassDataX.inTyped_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hHyp hPC hL hL' hTF
      hStd.2.2.1 hStd.2.2.2)
    (Formalism.L2.SG.Pf.MassDataX.inVolumes_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hSW hHyp hStd.2.2.1
      hStd.2.2.2 hMC hdet)
    (Formalism.L2.SG.Pf.MassDataX.volHa'_eq X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hSW hStd.2.2.1 hMC)
    hcong hRR (Formalism.L2.SG.Pf.NcVal.volOrdV_holds X u u' ψ) (Formalism.L2.SG.Pf.NcVal.volTypV_holds X u u' ψ)
    (Formalism.L2.SG.Pf.AlTieIdx.indexTypC_holds X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ.omV_holdsX X u' ψ) (Formalism.L2.SG.Pf.AlTieLG.fieldDict_holds X u u') hPC

end Formalism.L2.SG.Pf.NcAllS
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.NcAllC

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.LocVol
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

set_option maxHeartbeats 4000000 in
variable [Fact PI.AprimeInfW.GaugeVolUD] [Fact Formalism.L2.SG.Pf.WB.RhsWLim] [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem ncTieC_of_closed (hCov : Formalism.L2.SG.Pf.NcReal.JX.CovolRef) (hSW : PI.VolStabS.MassDataS.SWXS)
    (hHyp : HypX X hb FdN FdN' u u') (hMC : MeasCompatψ X ψ) (hStd : StdHyp X.B.I.cm.sig X.B.I.J ψ)
    (hLat : ∃ L : Submodule (NumberField.RingOfIntegers X.B.I.E) (Fin X.B.I.n → X.B.I.E),
      Submodule.IsLattice X.B.I.E L ∧ (L : Set (Fin X.B.I.n → X.B.I.E)) = (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
    (hdet' : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0)
    (hdet : (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0) (hPC : ProdConv X u u' ψ)
    (hL : LocTieX X ψ u) (hL' : LocTieX X ψ u') (hTF : TypFacts X u u')
    (hQ : Formalism.L2.SG.Pf.MassDataPos.QuotVolPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hsd : 0 ≤ sd) (hC0 : 0 ≤ C) (hTh : 0 < Th)
    (hcong : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hRR : IsRowReps D F0 what₂) :
    NcTieC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂) :=
  Formalism.L2.SG.Pf.NcAllS.ncTie0All_of X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq
    (Formalism.L2.SG.Closed.RealBracket_holds hCov) hSW hHyp hMC hStd hLat hdet' hdet hPC hL hL' hTF hQ hsd hC0 hTh hcong hRR

end Formalism.L2.SG.Pf.NcAllC
end
end
