import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowDvdOfHermMatEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumQuotientTransportStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightInvariantEqSumOpenSubgroupCosetsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedZetaSumGLCosets
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalSectionGraphSplitPlace

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LocValSplit
open GlobalTheory.LFun (LvTw_eq eulerFac_eq_prod etaU locL etaFam_of_unram eulerFac_singleton mem_aboveF)

theorem LvTw_div_dv_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (v : HeightOneSpectrum (𝓞 F)) (w w' : HeightOneSpectrum (𝓞 E)) (r b : ℕ) (s : ℂ), IsSplit (E := E) v → Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v → w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = w ∨ u = w') → Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal → Ideal.absNorm w'.asIdeal = Ideal.absNorm v.asIdeal → B w' = (B w).map (·⁻¹) → m w * m w' = 1 → LvTw B m v (s + 1 / 2) / dv E r b v s = eulerFac ((B w).map ((m w)⁻¹ * ·)) (GlobalTheory.LFun.npow w (-(s + 1 / 2))) * eulerFac ((B w).map fun β => ((m w)⁻¹ * β)⁻¹) (GlobalTheory.LFun.npow w (-(s + 1 / 2))) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ (-(2 * s + r - i))) := by
  intro F E _ _ _ _ _ B m v w w' r b s hsplit hunr hne hv hqw hqw' hB' hm1
  classical
  set X : ℂ := GlobalTheory.LFun.npow w (-(s + 1 / 2)) with hXdef
  set μ : ℂ := (m w : ℂ) with hμ
  have hX' : GlobalTheory.LFun.npow w' (-(s + 1 / 2)) = X := by rw [hXdef, GlobalTheory.LFun.npow, GlobalTheory.LFun.npow, hqw, hqw']
  have hinv : ((m w' : ℂ))⁻¹ = μ := inv_eq_of_mul_eq_one_left (by rw [hμ, ← Units.val_mul, hm1, Units.val_one])
  have e : Formalism.L2.Host.aboveF (L := E) F v = {w, w'} := by ext u; simp [mem_aboveF, hv]
  have hL : LvTw B m v (s + 1 / 2) = ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod *
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [LvTw_eq, e, Finset.prod_pair hne, hB', Multiset.map_map, hX', hinv]
    simp only [Function.comp_def, Units.val_inv_eq_inv_val]
    rfl
  have hr1 : eulerFac ((B w).map ((m w)⁻¹ * ·)) X = ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod := by
    rw [eulerFac_eq_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
    simp only [Function.comp_apply, Units.val_mul, Units.val_inv_eq_inv_val, hμ]
    ring
  have hr2 : eulerFac ((B w).map fun β => ((m w)⁻¹ * β)⁻¹) X =
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [eulerFac_eq_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
    simp only [Function.comp_apply, Units.val_inv_eq_inv_val, Units.val_mul, mul_inv, inv_inv, hμ]
    ring
  have hd : dv E r b v s = (∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ (-(2 * s + r - i))))⁻¹ := by
    rw [← Finset.prod_inv_distrib, dv]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hu : etaU E v = 1 := by unfold etaU; rw [if_pos hsplit]
    rw [locL, etaFam_of_unram hunr, hu, one_pow, eulerFac_singleton, Units.val_one, one_mul, GlobalTheory.LFun.npow, qV, hqw]
  rw [hd, div_inv_eq_mul, hL, hr1, hr2]

end GlobalTheory.LocValSplit
end

section
noncomputable section

namespace GlobalTheory.Core.Rk.BdSplit

section Abstract

open Formalism.UG GlobalTheory.LFun

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}

open Classical in

def cosetInd (S : Finset (G ⧸ K)) : G → ℂ := fun g => if (g : G ⧸ K) ∈ S then 1 else 0

theorem cosetInd_mem {S : Finset (G ⧸ K)} (hS : ∀ x ∈ K, ∀ c ∈ S, x • c ∈ S) : cosetInd S ∈ Hecke ℂ K := by
  classical
  refine ⟨fun a b g => ?_, S.image Quotient.out, fun g hg => ?_⟩
  · have e : ((a * g * b : G) : G ⧸ K) = (a : G) • (g : G ⧸ K) := QuotientGroup.mk_mul_of_mem _ b.2
    have : (a : G) • (g : G ⧸ K) ∈ S ↔ (g : G ⧸ K) ∈ S :=
      ⟨fun h => by simpa using hS _ (inv_mem a.2) _ h, hS _ a.2 _⟩
    simp only [cosetInd, e, this]
  · have h : (g : G ⧸ K) ∈ S := by
      by_contra h
      exact hg (if_neg h)
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    exact ⟨_, Finset.mem_image_of_mem _ h, 1, k⁻¹, by rw [hk]; simp⟩

theorem heckeVec_cosetInd (ρ : Representation ℂ G V) (S : Finset (G ⧸ K)) (x : V) :
    heckeVec ρ K (cosetInd S) x = ∑ c ∈ S, ρ c.out x := by
  rw [heckeVec, finsum_eq_sum_of_support_subset (s := S)]
  · exact Finset.sum_congr rfl fun c hc => by simp [cosetInd, hc]
  · intro c hc
    by_contra h
    exact hc (by simp [cosetInd, show c ∉ S from h])

theorem norm_le_card {ι : Type} (ρ : Representation ℂ G V) {x : V} (l : V →ₗ[ℂ] ℂ) {C : ℝ}
    (hC : ∀ y, ‖l (ρ y x)‖ ≤ C) (h1 : l (ρ 1 x) ≠ 0) (S : Finset ι) (g : ι → G) (a : ℂ)
    (h : ∑ c ∈ S, ρ (g c) x = a • x) : ‖a‖ ≤ S.card := by
  have hb : BddAbove (Set.range fun y => ‖l (ρ y x)‖) := ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩
  set M := ⨆ y, ‖l (ρ y x)‖
  have hM : ∀ y, ‖l (ρ y x)‖ ≤ M := fun y => le_ciSup hb y
  have hM0 : 0 < M := (norm_pos_iff.2 h1).trans_le (hM 1)
  have key : ∀ y, ‖a‖ * ‖l (ρ y x)‖ ≤ S.card * M := fun y => by
    rw [← norm_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← h, map_sum, map_sum]
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun c _ => ?_
    rw [← Module.End.mul_apply, ← map_mul]
    exact hM _
  rcases (norm_nonneg a).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · have : M ≤ S.card * M / ‖a‖ := ciSup_le fun y => by rw [le_div_iff₀' h0]; exact key y
    rw [le_div_iff₀' h0] at this
    exact le_of_mul_le_mul_right this hM0

end Abstract

section Linear

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SatakeBound

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem norm_le_of_isSatVecGL {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {x : V} {B : Multiset ℂˣ}
    (hx : IsSatVecGL w ρ x B) (l : V →ₗ[ℂ] ℂ) {C : ℝ} (hC : ∀ y, ‖l (ρ y x)‖ ≤ C) (h1 : l (ρ 1 x) ≠ 0) :
    ∀ β ∈ B, ‖(β : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  obtain ⟨α, rfl⟩ : ∃ α : Fin n → ℂˣ, Finset.univ.val.map α = B := by
    obtain ⟨l, rfl⟩ := Quot.exists_rep B
    obtain rfl : l.length = n := hx.2.2.1
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  obtain ⟨φ, hφ, hφ1, -⟩ := Final.SphericalExists E w n (fun i => (α i : ℂ)) fun i => (α i).ne_zero
  have hφ0 : φ ≠ 0 := fun e => by simp [e] at hφ1
  have hy := isSatVecGL_of_isSpherical hφ hφ0
  have hKO : KO (w.adicCompletion E) (Fin n) = KGL w n := SphCompletion.KO_completion w n
  have hb : HasBoundedSums (w.adicCompletion E) φ := by
    intro S hS
    have H := SatCompare.exists_eigenvalue_GL hx hy
    rw [← hKO] at H
    obtain ⟨c, e1, e2⟩ := H _ (cosetInd_mem hS)
    rw [heckeVec_cosetInd] at e1 e2
    have e3 : ∑ c ∈ S, φ c.out = c := by
      have := congrFun e2 1
      rw [Finset.sum_apply, Pi.smul_apply, hφ1, smul_eq_mul, mul_one] at this
      rw [← this]
      exact Finset.sum_congr rfl fun c _ => congrArg φ (one_mul _).symm
    rw [e3]
    exact norm_le_card ρ l hC h1 S _ c e1
  have hs : IsBorelSph (w.adicCompletion E) (fun i : Fin n => (α i : ℂ) *
      (((resCard (w.adicCompletion E) : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) φ := by
    refine ⟨fun g k hk => congrFun (GlobalTheory.LGrp.mem_fixed.1 hy.2.1 k (hKO ▸ hk)) g, fun b hb' t ht => ?_⟩
    obtain ⟨y, -, rfl⟩ := (SphCompletion.isSpherical_iff E w n α φ).1 hφ
    have h := GlobalTheory.SatakeBound.Rep.law α y b hb' t ht 1
    rwa [hφ1, mul_one, mul_one] at h
  intro β hβ
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hβ
  have hq : (0 : ℝ) < resCard (w.adicCompletion E) := by
    exact_mod_cast (GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard (w.adicCompletion E)).le
  have h2 := norm_le_pow hs hb i
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hq.le _), ← Real.rpow_natCast] at h2
  rw [← le_div_iff₀ (Real.rpow_pos_of_pos hq _), ← Real.rpow_sub hq] at h2
  rw [← GlobalTheory.LFun.SatBoundGL.resCard_completion w]
  exact h2.trans_eq (congrArg _ (by ring))

end Linear

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem paramBound_split : ∀ D : D7, ParamBoundOn D fun v => Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  rintro D A L - v hv par c ⟨⟨C, hC⟩, V, _, _, ρ, x, l, hx, -, hc⟩ h1 w h
  refine ⟨(hx w h).card, fun β hβ => ?_⟩
  rcases hx w h with ⟨-, e, -, hx⟩ | ⟨hw, -⟩
  · have hb := norm_le_of_isSatVecGL hx l (C := C) (fun y => (hc (e.symm y)) ▸ hC (e.symm y))
      (by rw [hc] at h1; rwa [map_one, ← map_one ρ]) β hβ
    refine hb.trans (Real.rpow_le_rpow_of_exponent_le ?_ (by linarith))
    exact_mod_cast (GlobalTheory.LFun.one_lt_absNorm w).le
  · exact absurd hv (GlobalTheory.LFun.not_isSplit_of_isInertAt hw)

end GlobalTheory.Core.Rk.BdSplit

end
end

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalParameterBound_split_place : ∀ D : D7, ParamBoundOn D fun v => Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.Core.Rk.BdSplit.paramBound_split | exact GlobalTheory.Core.Rk.BdSplit.paramBound_split | (intros; apply GlobalTheory.Core.Rk.BdSplit.paramBound_split <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.ZetaGL

theorem zeta_sum_GL_complex : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (s : ℂ), (r : ℝ) / 2 < s.re → ∀ (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), ‖(z : ℂ)‖ = 1 → (∀ ϖ, IsUnifV E w ϖ → ∀ (d : Fin r → ℤ) (t : GL (Fin r) (w.adicCompletion E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w r, ∀ k₂ ∈ KGL w r, φ (k₁ * t * k₂) = (z : ℂ) ^ (∑ i, d i) * (qV E w : ℂ) ^ (-((r : ℂ) / 2 + s) * ((∑ i, |d i| : ℤ) : ℂ))) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), IsSatVecGL w ρ x B → ∀ ℓ : V →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) → (ℓ x ≠ 0 → ∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ ((r : ℝ) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ ((r : ℝ) / 2)) → HasSum (fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r => φ a.out * ℓ (ρ a.out x)) (eulerFac (B.map (z * ·)) (GlobalTheory.LFun.npow w (-(s + 1 / 2))) * eulerFac (B.map fun β => (z * β)⁻¹) (GlobalTheory.LFun.npow w (-(s + 1 / 2))) * (∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ (-(2 * s + r - i)))) * ℓ x) := by
  intro H E _ _ w r s hs z φ hz hφ V _ _ ρ x B hx ℓ hℓ hB
  obtain ⟨Cℓ, hC⟩ := hℓ
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  have h0 : ϖ ≠ 0 := GlobalTheory.LFun.SatCompare.ne_zero_of_isUnifV hϖ
  let T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E) := fun d => GlobalTheory.WeylGL.tor h0 d
  have hTv : ∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i := fun d => rfl
  have hK : Formalism.UG.IsCommensurated (KGL w r) := Formalism.UG.Final.GLintComm E w r
  have hmem : ∀ g, Formalism.UG.dosetInd ℂ (KGL w r) g ∈ Hecke ℂ (KGL w r) := fun g => Formalism.UG.Final.DosetIndMem _ _ ℂ g
  choose c hc using fun d => GlobalTheory.LFun.SatCompare.exists_eigenvalue_GL hx hx _ (hmem (T d))
  let S : (Fin r → ℤ) → Set (GL (Fin r) (w.adicCompletion E) ⧸ KGL w r) := fun d =>
    {a | a.out ∈ DoubleCoset.doubleCoset (T d) (KGL w r : Set (GL (Fin r) (w.adicCompletion E))) (KGL w r)}
  have hSfin : ∀ d, (S d).Finite := fun d =>
    (Formalism.UG.P.finite_support_cosets hK (hmem (T d)).2).subset fun a ha => by
      simp only [Set.mem_setOf_eq, Formalism.UG.dosetInd]; rw [Set.indicator_of_mem (s := DoubleCoset.doubleCoset _ _ _) ha]; exact one_ne_zero
  have hsumS : ∀ d, ∑ᶠ a ∈ S d, ρ a.out x = c d • x := fun d => by
    rw [← (hc d).1, GlobalTheory.LFun.heckeVec, finsum_mem_def]
    refine finsum_congr fun a => ?_
    by_cases ha : a ∈ S d
    · rw [Set.indicator_of_mem ha, Formalism.UG.dosetInd, Set.indicator_of_mem (s := DoubleCoset.doubleCoset _ _ _) ha]; simp
    · rw [Set.indicator_of_notMem ha, Formalism.UG.dosetInd, Set.indicator_of_notMem (s := DoubleCoset.doubleCoset _ _ _) ha]; simp
  have hU := fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r => GlobalTheory.ZetaGL.cartan_existsUnique E w r hϖ T hTv a.out
  choose D hD using fun a => (hU a).exists
  have hDu : ∀ (d : {d : Fin r → ℤ // Antitone d}) (a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r), a ∈ S d.1 → D a = d :=
    fun d a ha => (hU a).unique (hD a) ha
  let e : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r ≃ Σ d : {d : Fin r → ℤ // Antitone d}, S d.1 :=
    { toFun := fun a => ⟨D a, a, hD a⟩
      invFun := fun p => p.2.1
      left_inv := fun a => rfl
      right_inv := fun ⟨d, a, ha⟩ => by
        have h1 : D a = d := hDu d a ha
        subst h1
        rfl }
  haveI : ∀ d, Fintype (S d) := fun d => (hSfin d).fintype
  have hsumF : ∀ d, ∑ a : S d, ρ (a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r).out x = c d • x := fun d => by
    rw [← hsumS d, ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  set q : ℝ := (qV E w : ℝ) with hqdef
  have hq1 : (1 : ℝ) < q := by
    show (1 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ); exact_mod_cast GlobalTheory.LFun.one_lt_absNorm w
  have hq0 : (0 : ℝ) < q := by linarith
  have hqC : (qV E w : ℂ) ≠ 0 := by exact_mod_cast GlobalTheory.LFun.qV_ne_zero w
  set M : ℝ := q ^ ((r : ℝ) / 2) with hM
  set M₁ : ℝ := q ^ (((r : ℝ) - 1) / 2) with hM₁
  set ρ₀ : ℝ := q ^ (-((r : ℝ) - 1 / 2)) with hρ₀
  have hM0 : 0 < M := Real.rpow_pos_of_pos hq0 _
  have hM₁0 : 0 < M₁ := Real.rpow_pos_of_pos hq0 _
  have hM₁M : M₁ ≤ M := Real.rpow_le_rpow_of_exponent_le hq1.le (by linarith)
  have hMM : M * M₁ * ρ₀ = 1 := by
    rw [hM, hM₁, hρ₀, ← Real.rpow_add hq0, ← Real.rpow_add hq0,
      show (r : ℝ) / 2 + ((r : ℝ) - 1) / 2 + -((r : ℝ) - 1 / 2) = 0 by ring, Real.rpow_zero]
  set cq : ℂ := (qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) with hcq
  have hcqn : ‖cq‖ = M₁ := by
    rw [hcq, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero w))]
    congr 1; simp
  have hsmall : ∀ β : ℂ, ‖β‖ ≤ M → ∀ X : ℂ, ‖X‖ < ρ₀ → ‖β * (cq * X)‖ < 1 := fun β hβ X hX => by
    rw [norm_mul, norm_mul, hcqn]
    calc ‖β‖ * (M₁ * ‖X‖) ≤ M * (M₁ * ‖X‖) := mul_le_mul_of_nonneg_right hβ (by positivity)
      _ < M * (M₁ * ρ₀) := by gcongr
      _ = 1 := by rw [← mul_assoc, hMM]
  set X₀ : ℂ := (qV E w : ℂ) ^ (-((r : ℂ) / 2 + s)) with hX₀
  have hX₀n : ‖X₀‖ = q ^ (-((r : ℝ) / 2 + s.re)) := by
    rw [hX₀, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero w))]
    congr 1; simp
  have hX₀ρ : ‖X₀‖ < ρ₀ := by
    rw [hX₀n]; exact Real.rpow_lt_rpow_of_exponent_lt hq1 (by linarith)
  let deg : {d : Fin r → ℤ // Antitone d} → ℕ := fun d => (∑ i, |d.1 i|).toNat
  have hdeg : ∀ k, {d | deg d = k}.Finite := fun k => by
    have hfin : (Set.pi Set.univ fun _ : Fin r => Set.Icc (-(k : ℤ)) k).Finite :=
      Set.Finite.pi fun _ => Set.finite_Icc _ _
    refine (hfin.preimage Subtype.val_injective.injOn).subset fun d hd => ?_
    simp only [Set.mem_setOf_eq, deg] at hd
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
    intro i
    have h1 : |d.1 i| ≤ ∑ j, |d.1 j| := Finset.single_le_sum (fun j _ => abs_nonneg (d.1 j)) (Finset.mem_univ i)
    have h2 : ∑ j, |d.1 j| = k := by rw [← hd, Int.toNat_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)]
    constructor
    · linarith [neg_abs_le (d.1 i)]
    · linarith [le_abs_self (d.1 i)]
  obtain ⟨δ₁, hδ₁, hs₁⟩ := GlobalTheory.T.satake_vector_hecke_eigenvalue H E w r V ρ x B hx z ϖ hϖ T hTv c (fun d => (hc d).1)
  obtain ⟨B₀, hB₀, δ₂, hδ₂, hs₂⟩ := GlobalTheory.T.hasSum_card_cosets_diagonalDoubleCoset_GL H E w r ϖ hϖ T hTv
  let a : {d : Fin r → ℤ // Antitone d} → ℂ := fun d => (z : ℂ) ^ (∑ i, d.1 i) * c d.1 * ℓ x
  let b : {d : Fin r → ℤ // Antitone d} → ℝ := fun d => (Nat.card (S d.1) : ℝ)
  let P : ℂ → ℂ := fun X => eulerFac (B.map (z * ·)) (cq * X) * eulerFac (B.map fun β => (z * β)⁻¹) (cq * X) *
    (∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * X ^ 2)) * ℓ x
  let P' : ℂ → ℂ := fun X => eulerFac B₀ (cq * X) * eulerFac (B₀.map (·⁻¹)) (cq * X) *
    ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * X ^ 2)
  have hC0 : 0 ≤ Cℓ := (norm_nonneg _).trans (hC 1)
  have hab : ∀ d, ‖a d‖ ≤ Cℓ * b d := fun d => by
    have e1 : c d.1 * ℓ x = ∑ y : S d.1, ℓ (ρ (y : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r).out x) := by
      rw [← map_sum, hsumF, map_smul, smul_eq_mul]
    have hz' : ‖(z : ℂ) ^ (∑ i, d.1 i)‖ = 1 := by rw [norm_zpow, hz, _root_.one_zpow]
    simp only [a, b]
    rw [mul_assoc, norm_mul, hz', one_mul, e1]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun y _ => hC _).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card, mul_comm]
  have hbnd₀ : ∀ β ∈ B₀, ‖(β : ℂ)‖ ≤ M := fun β hβ => (hB₀ β hβ).1.trans hM₁M
  have hbnd₀' : ∀ β ∈ B₀.map (·⁻¹), ‖(β : ℂ)‖ ≤ M := by
    intro β hβ
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hβ
    exact (hB₀ b hb).2.trans hM₁M
  have hpoly : Differentiable ℂ fun X : ℂ => ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * X ^ 2) := by fun_prop
  have hE3 := GlobalTheory.ZetaGL.differentiableOn_eulerFac _ cq ρ₀ fun β hβ X hX => hsmall _ (hbnd₀ β hβ) X hX
  have hE4 := GlobalTheory.ZetaGL.differentiableOn_eulerFac _ cq ρ₀ fun β hβ X hX => hsmall _ (hbnd₀' β hβ) X hX
  have hP : DifferentiableOn ℂ P (Metric.ball 0 ρ₀) := by
    by_cases hl : ℓ x = 0
    · have hP0 : P = fun _ => 0 := funext fun X => by simp only [P, hl, mul_zero]
      rw [hP0]; exact differentiableOn_const 0
    · have hbnd : ∀ β ∈ B.map (z * ·), ‖(β : ℂ)‖ ≤ M := by
        intro β hβ
        obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hβ
        simpa [norm_mul, hz] using (hB hl b hb).1
      have hbnd' : ∀ β ∈ B.map fun β => (z * β)⁻¹, ‖(β : ℂ)‖ ≤ M := by
        intro β hβ
        obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hβ
        simpa [norm_mul, hz, Units.val_inv_eq_inv_val] using (hB hl b hb).2
      have hE1 := GlobalTheory.ZetaGL.differentiableOn_eulerFac _ cq ρ₀ fun β hβ X hX => hsmall _ (hbnd β hβ) X hX
      have hE2 := GlobalTheory.ZetaGL.differentiableOn_eulerFac _ cq ρ₀ fun β hβ X hX => hsmall _ (hbnd' β hβ) X hX
      exact (((hE1.mul hE2).mul hpoly.differentiableOn).mul_const (ℓ x)).congr fun X _ => by simp only [P, Pi.mul_apply]
  have hP' : DifferentiableOn ℂ P' (Metric.ball 0 ρ₀) :=
    ((hE3.mul hE4).mul hpoly.differentiableOn).congr fun X _ => rfl
  have hser : ∀ X : ℝ, 0 < X → X < min δ₁ δ₂ → HasSum (fun d => a d * (X : ℂ) ^ deg d) (P X) ∧
      HasSum (fun d => (b d : ℂ) * (X : ℂ) ^ deg d) (P' X) := fun X hX h =>
    ⟨by
      have h1 := (hs₁ X hX (lt_of_lt_of_le h (min_le_left _ _))).mul_right (ℓ x)
      rw [show (fun d => a d * (X : ℂ) ^ deg d) = fun d : {d : Fin r → ℤ // Antitone d} =>
        (z : ℂ) ^ (∑ i, d.1 i) * c d.1 * (X : ℂ) ^ (∑ i, |d.1 i|).toNat * ℓ x from funext fun d => by
          simp only [a, deg]; ring]
      exact h1,
    hs₂ X hX (lt_of_lt_of_le h (min_le_right _ _))⟩
  obtain ⟨hA, hBs⟩ := GlobalTheory.T.hasSum_and_summable_on_ball_of_hasSum_on_interval deg hdeg a b Cℓ (min δ₁ δ₂) ρ₀ P P' (lt_min hδ₁ hδ₂) (fun d => Nat.cast_nonneg _)
    hab hP hP' hser X₀ hX₀ρ
  have hφv : ∀ a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r,
      φ a.out = (z : ℂ) ^ (∑ i, (D a).1 i) * X₀ ^ deg (D a) := fun a => by
    obtain ⟨k₁, hk₁, k₂, hk₂, e1⟩ := DoubleCoset.mem_doubleCoset.1 (hD a)
    rw [e1, hφ ϖ hϖ (D a).1 (T (D a).1) (hTv _) k₁ hk₁ k₂ hk₂]
    congr 1
    have hn : ((∑ i, |(D a).1 i| : ℤ) : ℂ) = ((deg (D a) : ℕ) : ℂ) := by
      simp only [deg]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)]
    rw [hn, hX₀, ← Complex.cpow_nat_mul, mul_comm]
  let f : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r → ℂ := fun a => φ a.out * ℓ (ρ a.out x)
  let u : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r → ℝ := fun a => Cℓ * ‖X₀‖ ^ deg (D a)
  have hfu : ∀ a, ‖f a‖ ≤ u a := fun a => by
    simp only [f, u]
    rw [hφv, norm_mul, norm_mul, norm_zpow, hz, _root_.one_zpow, one_mul, norm_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (pow_nonneg (norm_nonneg _) _)
  have hu : Summable u := by
    rw [← e.symm.summable_iff]
    refine (summable_sigma_of_nonneg fun p => mul_nonneg hC0 (pow_nonneg (norm_nonneg _) _)).2
      ⟨fun d => Summable.of_finite, ?_⟩
    have h1 : ∀ d : {d : Fin r → ℤ // Antitone d},
        Cℓ * (b d * ‖X₀‖ ^ deg d) = ∑' y : S d.1, (u ∘ e.symm) ⟨d, y⟩ := fun d => by
      have h2 : ∀ y : S d.1, (u ∘ e.symm) ⟨d, y⟩ = Cℓ * ‖X₀‖ ^ deg d := fun y => by
        show Cℓ * ‖X₀‖ ^ deg (D y.1) = _
        rw [hDu d y.1 y.2]
      simp_rw [h2]
      rw [tsum_const, nsmul_eq_mul]
      simp only [b]
      ring
    exact (hBs.mul_left Cℓ).congr h1
  have hf : Summable f := Summable.of_norm_bounded hu hfu
  have hfib : ∀ d : {d : Fin r → ℤ // Antitone d},
      HasSum (fun y : S d.1 => (f ∘ e.symm) ⟨d, y⟩) (a d * X₀ ^ deg d) := fun d => by
    have h2 : ∀ y : S d.1, (f ∘ e.symm) ⟨d, y⟩ =
        (z : ℂ) ^ (∑ i, d.1 i) * X₀ ^ deg d * ℓ (ρ (y : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r).out x) :=
      fun y => by
        show φ (y : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r).out * _ = _
        rw [hφv, hDu d y.1 y.2]
        rfl
    have h3 : ∑ y : S d.1, (f ∘ e.symm) ⟨d, y⟩ = a d * X₀ ^ deg d := by
      rw [Finset.sum_congr rfl fun y _ => h2 y, ← Finset.mul_sum, ← map_sum, hsumF, map_smul, smul_eq_mul]
      simp only [a]
      ring
    exact h3 ▸ hasSum_fintype _
  have heq : ∑' a, f a = P X₀ := (((e.symm.hasSum_iff).2 hf.hasSum).sigma hfib).unique hA
  have hfin := hf.hasSum
  rw [heq] at hfin
  have hcX : cq * X₀ = GlobalTheory.LFun.npow w (-(s + 1 / 2)) := by
    rw [hcq, hX₀, ← Complex.cpow_add _ _ hqC]
    show ((qV E w : ℕ) : ℂ) ^ _ = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ _
    congr 1
    ring
  have hprod : ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * X₀ ^ 2) =
      ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ (-(2 * s + r - i))) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hX₀, ← Complex.cpow_nat_mul, ← Complex.cpow_natCast (qV E w : ℂ) i, ← Complex.cpow_add _ _ hqC]
    congr 2
    push_cast
    ring
  have hval : P X₀ = eulerFac (B.map (z * ·)) (GlobalTheory.LFun.npow w (-(s + 1 / 2))) *
      eulerFac (B.map fun β => (z * β)⁻¹) (GlobalTheory.LFun.npow w (-(s + 1 / 2))) *
      (∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ (-(2 * s + r - i)))) * ℓ x := by
    simp only [P]
    rw [hcX, hprod]
  rw [hval] at hfin
  exact hfin

end GlobalTheory.ZetaGL
end

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open GlobalTheory.LFun (locChar IsSplitChart IsInertChart KGL UnrAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalSection_graph_splitPlace : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (χ : (AE D)ˣ →* Circle) (b : ℕ), ResEta D χ b → ∀ v : FinPl D, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → UnrAt χ w) → ∀ (s : ℂ) (φ : Gv (dblSp A) v → ℂ), IsSphSecAt A L v χ⁻¹ s φ → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (e : Gv A v ≃* GL (Fin A.rank) (w.adicCompletion D.host.E)), IsSplitChart D.sp.cm.sig A.gram L h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin A.rank → ℤ) (t : GL (Fin A.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w A.rank, ∀ k₂ ∈ KGL w A.rank, φ (ioAt A v (e.symm (k₁ * t * k₂))) = (((GlobalTheory.LFun.val χ w)⁻¹ : ℂˣ) : ℂ) ^ (∑ i, d i) * (qV D.host.E w : ℂ) ^ (-((A.rank : ℂ) / 2 + s) * ((∑ i, |d i| : ℤ) : ℂ)) := by
  first | exact @GlobalTheory.Core.Rk.KerSplit.sphSec_split | exact GlobalTheory.Core.Rk.KerSplit.sphSec_split | (intros; apply GlobalTheory.Core.Rk.KerSplit.sphSec_split <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

open Formalism.UG (IsUnifV qV)
open GlobalTheory.LFun (KGL IsSatVecGL eulerFac UnrAt LvTw)
open GlobalTheory.LFun (locChar IsSplitChart IsInertChart KGL UnrAt toCompl locMat IsFrameAt IsSatVecU eulerFac LvTw dv Fam)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.Doubling (ioH_mem_KFin)

namespace GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 2000000 in

theorem localZetaOn_split : GlobalTheory.Published.UnramifiedDoublingGL →
    ∀ D : D7, LocalZetaOn D fun v => Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  intro hP D A L hL χ b hχ hb v hv hU μ hμH hK s hs φ hφ par c hc
  classical
  have hcm := isCMExt_host D
  have h2 : Module.finrank D.host.F D.host.E = 2 := hcm.2.2.1
  have hJ : IsHermND D.sp.cm.sig A.gram := GlobalTheory.Doubling.isHermND_gram A
  have hd : IsSelfDualAt D.sp.cm.sig A.gram L v :=
    (SelfDual.forall_isSelfDualAt_iff (σ := D.sp.cm.sig) (GlobalTheory.Doubling.isHermND_gram A).2 hL.1).2
      (fun y => hL.2 y) v
  obtain ⟨w, h⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hc' := hc
  obtain ⟨⟨C, hC⟩, V, _, _, ρ, x, ℓ, hpar, -, hcx⟩ := hc
  obtain ⟨w', hne, hall, hN, hN', -⟩ := GlobalTheory.LFun.SplitChart.exists_conj_place hcm h hv
  have h' : w'.under (𝓞 D.host.F) = v := (hall w').2 (Or.inr rfl)
  obtain ⟨e, he, hsat⟩ : ∃ e, IsSplitChart D.sp.cm.sig A.gram L h e ∧
      IsSatVecGL w (ρ.comp e.symm.toMonoidHom) x (par w) := by
    rcases hpar w h with ⟨-, e, he, hsat⟩ | ⟨hw, -⟩
    · exact ⟨e, he, hsat⟩
    · exact absurd hv (GlobalTheory.LFun.not_isSplit_of_isInertAt hw)
  have hB' : par w' = (par w).map (·⁻¹) :=
    GlobalTheory.LFun.ConjPlace.eq_map_inv_of_isParamVec hcm hJ hd hne (hpar w h) (hpar w' h')
  have hm : GlobalTheory.LFun.val χ w * GlobalTheory.LFun.val χ w' = 1 :=
    GlobalTheory.LFun.ResEta.val_mul_val h2 ((GlobalTheory.LFun.resEta_iff χ _).1 hb) hne h h' (hU w h) (hU w' h')
  have hfix : ∀ k ∈ stabLoc D.sp.cm.sig A.gram L v, ρ k x = x :=
    GlobalTheory.LGrp.mem_fixed.1 (hpar w h).mem_fixed
  have hz1 : ‖(((GlobalTheory.LFun.val χ w)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, GlobalTheory.LFun.norm_val, inv_one]
  have hker := GlobalTheory.T.sphericalSection_graph_splitPlace D A L hL χ b hb v hv hU s φ hφ w h e he
  have hbd : ℓ x ≠ 0 → ∀ β ∈ par w, ‖(β : ℂ)‖ ≤ (qV D.host.E w : ℝ) ^ ((A.rank : ℝ) / 2) ∧
      ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV D.host.E w : ℝ) ^ ((A.rank : ℝ) / 2) := by
    intro h0 β hβ
    have hc1 : c 1 ≠ 0 := by rw [hcx, map_one, Module.End.one_apply]; exact h0
    have Hb := GlobalTheory.T.sphericalParameterBound_split_place D A L hL v hv par c hc' hc1
    refine ⟨(Hb w h).2 β hβ, ?_⟩
    have H2 := (Hb w' h').2 β⁻¹ (hB' ▸ Multiset.mem_map_of_mem _ hβ)
    have e2 : ((Ideal.absNorm w'.asIdeal : ℕ) : ℝ) = (qV D.host.E w : ℝ) := by
      rw [hN', ← hN]; rfl
    rwa [e2] at H2
  have hsum := GlobalTheory.ZetaGL.zeta_sum_GL_complex hP D.host.E w A.rank s (by have : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _; linarith)
    (GlobalTheory.LFun.val χ w)⁻¹ (fun g => φ (ioAt A v (e.symm g))) hz1 hker V (ρ.comp e.symm.toMonoidHom) x (par w) hsat ℓ
    ⟨C, fun g => by have := hC (e.symm g); rwa [hcx] at this⟩ hbd
  have hval := GlobalTheory.LocValSplit.LvTw_div_dv_split D.host.F D.host.E par (GlobalTheory.LFun.val χ) v w w' A.rank b s hv
    (GlobalTheory.LFun.isUnram_of_isSplit h2 hv) hne hall hN hN' hB' hm
  have hinv : ∀ y, ∀ k ∈ stabLoc D.sp.cm.sig A.gram L v,
      φ (ioAt A v (y * k)) * c (y * k) = φ (ioAt A v y) * c y := by
    intro y k hk
    have e1 : ioAt A v (y * k) = ioAt A v y * ioAt A v k := by
      unfold ioAt
      rw [← map_mul]
      simp
    have hk' : ioAt A v k ∈ KFin D.sp.cm.sig (dblSp A).gram L v :=
      (ioH_mem_KFin (gram_hdbl A)).2 ⟨hk, one_mem _⟩
    rw [e1, hφ.2.1 _ hk', hcx, hcx, map_mul, Module.End.mul_apply, hfix k hk]
  have hsum' := GlobalTheory.T.hasSum_quotient_of_hasSum_mulEquiv_quotient _ _ e (stabLoc D.sp.cm.sig A.gram L v) (KGL w A.rank) he.2
    (fun y => φ (ioAt A v y) * c y) hinv _ (by
      refine hsum.congr_fun ?_
      intro a
      simp [hcx])
  haveI : Submodule.IsLattice D.host.E L := hL.1
  obtain ⟨hI, hE⟩ := GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets (Gv A v) μ (stabLoc D.sp.cm.sig A.gram L v)
    (GlobalTheory.AdelicU.isOpen_stabLoc _ _ _ v) hK (fun y => φ (ioAt A v y) * c y) _ hinv hsum'
  refine ⟨hI, ?_⟩
  rw [hE, hval, hcx, map_one, Module.End.one_apply]

end GlobalTheory.Core.Rk.IP
end
