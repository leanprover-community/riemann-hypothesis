import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLsB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergTranslateFixesThetaDeepLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFinitePointReadsClassicalTranslation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualImageOrthonormalFrameLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDifferentLatticeProductHermitianIsSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeOIffScaleMulFinitePartMemIdealLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePointSignEqThetaLawSemicharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartRationalTensorZeroAtPrimeIffPlaceIdemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotentStatement

section
section
open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SplitPhase

open scoped TensorProduct

theorem phase_eq : ∀ D : D7, ∃ w : 𝓞 D.host.E, w + GlobalTheory.FinWeil.sgO D w = 1 ∧
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E),
  Setup ψ θ S T cc δ r → ∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
  ψ (-symplOH S T (GlobalTheory.FinWeilO.intA D w • finPt (S := S) (T := T) rfl rfl r z) (finPt (S := S) (T := T) rfl rfl r z)) =
    Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) := by
  intro D
  have hsq := D.host.sqd_sq
  let b : 𝓞 D.host.E := ⟨(1 + D.host.sqrtMinusD) / 2,
    GlobalTheory.NormSum.isIntegral_half_one_add D.host.d D.host.hyp.2.2.2.1 _ hsq⟩
  have hbv : (b : D.host.E) = (1 + D.host.sqrtMinusD) / 2 := rfl
  have h2s : star (2 : D.host.E) = 2 := by
    have := star_natCast (R := D.host.E) 2
    exact_mod_cast this
  have hbs : star (b : D.host.E) = 1 - (b : D.host.E) := by
    rw [hbv, star_div₀, star_add, star_one, h2s, GlobalTheory.FockCompare.RealChart.star_sqrtMinusD]
    ring
  refine ⟨b, ?_, ?_⟩
  · apply NumberField.RingOfIntegers.ext
    show (b : D.host.E) + ((GlobalTheory.FinWeil.sgO D b : 𝓞 D.host.E) : D.host.E) = 1
    have hc : ((GlobalTheory.FinWeil.sgO D b : 𝓞 D.host.E) : D.host.E) = star (b : D.host.E) := by
      have e1 : ((GlobalTheory.FinWeil.sgO D b : 𝓞 D.host.E) : D.host.E) = D.host.conj (b : D.host.E) := rfl
      rw [e1]
      exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
    rw [hc, hbs]; ring
  · intro ψ θ S T cc δ r hset z
    have hr : r ≠ 0 := GlobalTheory.NormExact.IsScale.ne_zero hset.crv.1.1 hset.scale
    set X : Matrix (Fin T.rank) (Fin S.rank) D.host.E := Matrix.of fun i j => -(r⁻¹ * z i j) with hX
    have hfin : finPt (S := S) (T := T) rfl rfl r z = GlobalTheory.LatVac.finTens 1 X := by
      funext i j; rfl
    have hmap : GlobalTheory.FinWeilO.intA D b • GlobalTheory.LatVac.finTens 1 X =
        GlobalTheory.LatVac.finTens 1 (Matrix.of fun i j => (b : D.host.E) * X i j) := by
      funext i j
      show ((1 : AF D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (X i j)) =
        pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((b : D.host.E) * X i j)
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    set n : D.host.E := ∑ c, ∑ a, star (X c a) * X c a with hn
    have hns : star n = n := by
      rw [hn, star_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [star_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [star_mul', star_star, mul_comm]
    have hR : GlobalTheory.LatVac.hRat S T X X = n := by
      rw [GlobalTheory.LatVac.hRat, hset.gS, hset.gT, inv_one]
      simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have e : ∀ x, (∑ x_1, ∑ x_2, if x = x_1 then star (X x_2 x_1) * X x_2 x else 0) =
          ∑ x_2, star (X x_2 x) * X x_2 x := fun x => by
        rw [Finset.sum_comm]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_comm]
    have hs : symplOH S T (GlobalTheory.FinWeilO.intA D b • finPt (S := S) (T := T) rfl rfl r z)
        (finPt (S := S) (T := T) rfl rfl r z) = pairA D.host.F 0
        (algebraMap D.host.F (Af D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((b : D.host.E) * n)))) := by
      rw [hfin, hmap, symplOH, GlobalTheory.LatVac.symplO_finTens, GlobalTheory.ThetaSignLat.hRat_smul_left, hR]
      refine Prod.ext (mul_zero _) ?_
      show algebraMap D.host.F (Af D.host.F) (1 / 2) * (1 * 1 * _) = _
      rw [one_mul, one_mul, ← RingHom.map_mul]
      rfl
    have hq := GlobalTheory.ThetaSignLat.trace_val n (b : D.host.E) hns hbv
    set q : D.host.F := 1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((b : D.host.E) * n)) with hqdef
    have hneg : -(pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) q)) =
        pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (-q)) := by
      refine Prod.ext ?_ ?_
      · show -(0 : Ainf D.host.F) = 0
        exact neg_zero
      · show -(algebraMap D.host.F (Af D.host.F) q) = _
        rw [map_neg]
        rfl
    rw [hs, hneg, GlobalTheory.PsiFinRat.psi_pairA_zero_algebraMap ψ hset.std]
    obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ∑ τ, tauE D τ n := ⟨_, rfl⟩
    obtain ⟨hxi, hN1, hd1⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
    have hNR : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0 := by linarith
    have hNC : (Ideal.absNorm D.host.ccK : ℂ) ≠ 0 := by exact_mod_cast hNR
    have hdR : Real.sqrt D.host.d ≠ 0 := by linarith
    have hsumq : ∑ τ, tauE D τ ((-q : D.host.F) : D.host.E) = c / (2 * (Ideal.absNorm D.host.ccK : ℂ)) := by
      have e : ∀ τ, tauE D τ ((-q : D.host.F) : D.host.E) = tauE D τ n / (2 * (Ideal.absNorm D.host.ccK : ℂ)) :=
        fun τ => by
          rw [show ((-q : D.host.F) : D.host.E) = -((q : D.host.F) : D.host.E) from rfl, hq, neg_div, neg_neg,
            map_div₀, map_mul, map_natCast, map_ofNat]
      rw [Finset.sum_congr rfl fun τ _ => e τ, ← Finset.sum_div, hc]
    have hcre : ((c.re : ℝ) : ℂ) = c := by
      have : starRingEnd ℂ c = c := by
        rw [hc, map_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [← GlobalTheory.FockCompare.tauE_star, hns]
      exact Complex.conj_eq_iff_re.1 this
    set Z : VC D S.rank T.rank := fun τ i j => -(embT D τ (X i j)) with hZ
    have hpt : pt D (tor0 D cc δ) δ z = fun τ i j => δ * embT D τ r * Z τ i j := by
      funext τ i j
      have ez : z i j = r * -(X i j) := by
        rw [hX, Matrix.of_apply]
        field_simp
      show δ * embT D τ (z i j) = δ * embT D τ r * -(embT D τ (X i j))
      rw [ez, map_mul, map_neg]
      ring
    have hsum : ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Z τ i j) = c := by
      rw [hc]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [hn, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, GlobalTheory.FockCompare.tauE_star, hZ]
      show -(tauE D τ (X i j)) * starRingEnd ℂ (-(tauE D τ (X i j))) = _
      rw [map_neg]
      ring
    rw [Formalism.MainNotions.StandardLatticesGL3.wdPh, Formalism.MainNotions.TaylorLogMetric.qH, hpt, GlobalTheory.NormExact.Hf_scale hset.crv hset.scale, hsum, Formalism.MainNotions.StandardLatticesGL3.ee,
      hsumq]
    have hre : Real.sqrt D.host.d / 2 * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c).re / 2 =
        c.re / (2 * Ideal.absNorm D.host.ccK) := by
      rw [show (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c) = ((2 * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c by push_cast; ring,
        Complex.re_ofReal_mul, hxi]
      field_simp
    rw [hre]
    congr 1
    push_cast
    rw [hcre]
end GlobalTheory.SplitPhase
end
end

open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePartQuadraticPhase_eq_cmTheta_exp : ∀ D : D7, ∃ w : 𝓞 D.host.E, w + GlobalTheory.FinWeil.sgO D w = 1 ∧
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E),
  Setup ψ θ S T cc δ r → ∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
  ψ (-symplOH S T (GlobalTheory.FinWeilO.intA D w • finPt (S := S) (T := T) rfl rfl r z) (finPt (S := S) (T := T) rfl rfl r z)) =
    Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) := by
  atlas_forward_decl GlobalTheory.SplitPhase.phase_eq
end

section
open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open Formalism.MainNotions.StandardLattice Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO

namespace GlobalTheory.SplitProj

open Filter Topology GlobalTheory.IdemSupport

variable {D : D7}

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun y : D.host.E => a ⊗ₜ[D.host.F] y) (star_star x)
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb]

def spl (ε : AE D) : AE D := ε + cA D ε

variable {ε : AE D}

theorem spl_idem (hε : GlobalTheory.RatAut.IsHalfIdem D ε) : spl ε * spl ε = spl ε := by
  obtain ⟨h1, h2, -, -, -⟩ := hε
  have h3 : cA D ε * cA D ε = cA D ε := by rw [← RingHom.map_mul, h1]
  unfold spl
  linear_combination h1 + h3 + 2 * h2

theorem cA_spl (ε : AE D) : cA D (spl ε) = spl ε := by
  unfold spl; rw [RingHom.map_add, cA_cA, add_comm]

theorem infPart_spl (hε : GlobalTheory.RatAut.IsHalfIdem D ε) : infPart D (spl ε) = 0 := by
  unfold spl
  rw [RingHom.map_add, (GlobalTheory.IdemSupport.parts_cA ε).1, hε.2.2.1, RingHom.map_zero, add_zero]

theorem spl_mul_split (hε : GlobalTheory.RatAut.IsHalfIdem D ε) {e : AE D} (he : IsSplitIdem D e) :
    spl ε * (e + cA D e) = e + cA D e := by
  have k1 : ∀ x y : AE D, x * y = 0 → cA D x * cA D y = 0 := fun x y h => by
    rw [← RingHom.map_mul, h, RingHom.map_zero]
  have k2 : ∀ x y : AE D, x * y = y → cA D x * cA D y = cA D y := fun x y h => by
    rw [← RingHom.map_mul, h]
  unfold spl
  rcases hε.2.2.2.1 e he with ⟨a, b⟩ | ⟨a, b⟩
  · have c1 := k2 _ _ a
    have c2 := k1 _ _ b
    rw [cA_cA] at c2
    linear_combination a + b + c1 + c2
  · have c1 := k1 _ _ a
    have c2 := k2 _ _ b
    rw [cA_cA] at c2
    linear_combination a + b + c1 + c2

theorem spl_mul_nonSplit (hε : GlobalTheory.RatAut.IsHalfIdem D ε) {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F}
    (hv : NonSplitAt D v η) : spl ε * algebraMap (AF D.host.F) (AE D) η = 0 := by
  have h := hε.2.2.2.2 v η hv
  have h' : algebraMap (AF D.host.F) (AE D) η * cA D ε = 0 := by
    rw [← GlobalTheory.IdemSupport.cA_algebraMap η, ← RingHom.map_mul, h, RingHom.map_zero]
  unfold spl
  linear_combination h + h'

def pc (hε : GlobalTheory.RatAut.IsHalfIdem D ε) (V : HSp D) (g : GA D V) : GA D V :=
  ⟨piece (spl_idem hε) g.1, piece_mem _ _ (spl_idem hε) (cA_spl ε) g.2⟩

theorem mt_pc (hε : GlobalTheory.RatAut.IsHalfIdem D ε) (V : HSp D) (g : GA D V) :
    mt V (pc hε V g) = spl ε • mt V g + (1 - spl ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := rfl

def proj (hε : GlobalTheory.RatAut.IsHalfIdem D ε) (V : HSp D) : GA D V →* GA D V :=
  MonoidHom.mk' (pc hε V) fun g h => mt_inj V (by
    simp only [mt_pc, GlobalTheory.IdemSupport.mt_mul]
    rw [mix_mul (spl_idem hε), one_mul])

variable (hε : GlobalTheory.RatAut.IsHalfIdem D ε) {V : HSp D}
include hε

theorem mt_proj (g : GA D V) :
    mt V (proj hε V g) = spl ε • mt V g + (1 - spl ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := mt_pc hε V g

theorem proj_eq_self {g : GA D V} (hg : ∀ i j, spl ε * (mt V g - 1) i j = (mt V g - 1) i j) : proj hε V g = g :=
  mt_inj V (by
    rw [mt_proj]
    ext i j
    have := hg i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at this ⊢
    linear_combination this)

theorem proj_eq_one {g : GA D V} (hg : ∀ i j, spl ε * (mt V g - 1) i j = 0) : proj hε V g = 1 :=
  mt_inj V (by
    rw [mt_proj, GlobalTheory.IdemSupport.mt_one]
    ext i j
    have := hg i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at this ⊢
    linear_combination this)

theorem proj_mem_GfC (g : GA D V) : proj hε V g ∈ GfC V :=
  mem_GfC_of_suppF V (infPart_spl hε) ((suppF_iff V _ _).2 (smul_mix (spl_idem hε) (mt_proj hε g)))

theorem proj_of_suppAt {g : GA D V} (hg : SuppAt ε V g) : proj hε V g = g := proj_eq_self hε hg

theorem proj_of_split {e : AE D} (he : IsSplitIdem D e) {g : GA D V} (hg : SuppAt e V g) : proj hε V g = g :=
  proj_eq_self hε fun i j => by rw [← hg i j, ← mul_assoc, spl_mul_split hε he]

theorem proj_of_nonSplit {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F} (hv : NonSplitAt D v η) {g : GA D V}
    (hg : SuppPl η V g) : proj hε V g = 1 :=
  proj_eq_one hε fun i j => by rw [← hg i j, ← mul_assoc, spl_mul_nonSplit hε hv, zero_mul]

theorem proj_of_real {g : GA D V} (hg : g ∈ GinfC V) : proj hε V g = 1 := by
  refine proj_eq_one hε fun i j => GlobalTheory.PlaceIdem.parts_inj D _ _ (by rw [RingHom.map_mul, infPart_spl hε, zero_mul, RingHom.map_zero]) ?_
  have h1 : (finPart D).mapMatrix (Formalism.L2.Theta.mt V g) = 1 := congrArg Units.val hg
  have h2 : (finPart D).mapMatrix (Formalism.L2.Theta.mt V g - 1) = 0 := by
    rw [RingHom.map_sub, h1, RingHom.map_one, sub_self]
  have h3 : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := congrFun (congrFun h2 i) j
  rw [RingHom.map_mul, h3, mul_zero, RingHom.map_zero]

omit hε in
theorem continuous_mt (V : HSp D) : Continuous fun g : GA D V => mt V g :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_proj : Continuous (proj hε V) := by
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  have c1 : Continuous fun g => mt V (proj hε V g) := by
    simp only [mt_proj]
    exact ((continuous_mt V).const_smul (spl ε)).add continuous_const
  have c2 : Continuous fun g => mt V (proj hε V g)⁻¹ := by
    simp only [← map_inv]
    exact c1.comp continuous_inv
  exact continuous_iff_continuousAt.2 fun g =>
    GlobalTheory.LocalGlobalChar.tendsto_HA _ _ _ (c1.tendsto g) (c2.tendsto g)

end GlobalTheory.SplitProj
end
end

section
section
open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open Formalism.MainNotions.StandardLattice Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.SplitProj

namespace GlobalTheory.SplitWeilDict

theorem lemB : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (w : 𝓞 D.host.E) (lam : ℕ →* ℂ) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)),
    GlobalTheory.FinWeilO.IsLatRep hψ.1 ΛS ΛT w lam Om → GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam →
    ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∃ c : ℂ, ‖c‖ = 1 ∧
      ∀ f (hf : IsThetaFunO ψ S T f), om (g, h) f = c • (Om (g, h) ⟨f, hf⟩ : WO S T → ℂ) := by
  intro D ψ hψ S T χS χT om hW ΛS ΛT w lam Om hL hlam g hg h hh
  obtain ⟨o, ho⟩ := exists_extend (thetaSub ψ S T) Om
  have ho' : ∀ p f (hf : IsThetaFunO ψ S T f), o p f = (Om p ⟨f, hf⟩ : WO S T → ℂ) := fun p f hf => ho p ⟨f, hf⟩
  have hpres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (o p f) := fun p f hf => by
    rw [ho' p f hf]
    exact (Om p ⟨f, hf⟩).2
  have hheis : ∀ (g' : GA D S) (k' : GA D T), g' ∈ GfC S → k' ∈ GfC T → ∀ u f, IsThetaFunO ψ S T f →
      o (g', k') (heisO ψ S T u f) = heisO ψ S T (actO S T g' k' u) (o (g', k') f) := by
    intro g' k' hg' hk' u f hf
    obtain ⟨f', h1, h2⟩ := hL.Heisenberg₂ hψ hg' hk' u ⟨f, hf⟩
    rw [ho' _ f hf, ← h2, ← h1]
    exact ho _ f'
  obtain ⟨c, hc, H⟩ := GlobalTheory.ThetaSchur.schur D ψ hψ S T (om (g, h) * o (g⁻¹, h⁻¹))
    (fun f hf => hW.om_pres _ _ (hpres _ _ hf))
    (fun u f hf => by
      rw [Module.End.mul_apply, Module.End.mul_apply, hheis _ _ (inv_mem hg) (inv_mem hh) u f hf,
        hW.om_heis _ _ _ _ (hpres _ _ hf), GlobalTheory.FinWeilForm.actO_actO_inv])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, hW.om_unit μ 𝓕 hμ h𝓕 _ _ (hpres _ _ hf), ho' _ f hf,
        hL.unit hlam μ 𝓕 hμ h𝓕 _ ⟨f, hf⟩])
  refine ⟨c, hc, fun f hf => ?_⟩
  have h1 := H _ (hpres (g, h) f hf)
  rw [Module.End.mul_apply, ← Module.End.mul_apply (o _), ← map_mul,
    show ((g⁻¹, h⁻¹) * (g, h) : GA D S × GA D T) = 1 from inv_mul_cancel (g, h), map_one,
    Module.End.one_apply] at h1
  rw [h1, ho' _ f hf]

theorem lemC : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (w : 𝓞 D.host.E) (lam : ℕ →* ℂ) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)),
    GlobalTheory.FinWeilO.IsLatRep hψ.1 ΛS ΛT w lam Om →
    (∀ g ∈ GfC S, ∀ h ∈ GfC T, ∃ c : ℂ, ‖c‖ = 1 ∧
      ∀ f (hf : IsThetaFunO ψ S T f), om (g, h) f = c • (Om (g, h) ⟨f, hf⟩ : WO S T → ℂ)) →
    ∀ (ε : AE D) (hε : GlobalTheory.RatAut.IsHalfIdem D ε), ∃ ν : GA D S × GA D T →* Circle, Continuous ν ∧
      ∀ (p : GA D S × GA D T) f (hf : IsThetaFunO ψ S T f),
        om (GlobalTheory.SplitProj.proj hε S p.1, GlobalTheory.SplitProj.proj hε T p.2) f =
          (ν p : ℂ) • (Om (GlobalTheory.SplitProj.proj hε S p.1, GlobalTheory.SplitProj.proj hε T p.2) ⟨f, hf⟩ : WO S T → ℂ) := by
  intro D ψ hψ S T χS χT om hW ΛS ΛT hS hT w lam Om hL hB ε hε
  let P : GA D S × GA D T →* GA D S × GA D T := (proj hε S).prodMap (proj hε T)
  have hPc : Continuous P := (continuous_proj hε).prodMap (continuous_proj hε)
  have hs : ∀ p : GA D S × GA D T, ∃ c : ℂ, ‖c‖ = 1 ∧
      ∀ f (hf : IsThetaFunO ψ S T f), om (P p) f = c • (Om (P p) ⟨f, hf⟩ : WO S T → ℂ) :=
    fun p => hB _ (proj_mem_GfC hε p.1) _ (proj_mem_GfC hε p.2)
  choose c hc h using hs
  obtain ⟨f, f0, hf⟩ := GlobalTheory.FinWeilForm.exists_theta hψ S T
  have hne : ∀ p, (Om p ⟨f, hf⟩ : WO S T → ℂ) ≠ 0 := fun p h0 => f0 (by
    have h1 : Om p ⟨f, hf⟩ = 0 := Subtype.ext h0
    have h2 := congrArg (Om p⁻¹) h1
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at h2
    exact congrArg Subtype.val h2)
  refine ⟨MonoidHom.mk' (fun p => ⟨c p, mem_sphere_zero_iff_norm.2 (hc p)⟩) fun p q => Circle.ext ?_, ?_,
    fun p f hf => h p f hf⟩
  · show c (p * q) = c p * c q
    refine smul_left_injective ℂ (hne (P (p * q))) ?_
    show c (p * q) • (Om (P (p * q)) ⟨f, hf⟩ : WO S T → ℂ) = (c p * c q) • (Om (P (p * q)) ⟨f, hf⟩ : WO S T → ℂ)
    rw [← h _ f hf, map_mul P, map_mul om, Module.End.mul_apply, h q f hf, map_smul, h p _ (Om (P q) ⟨f, hf⟩).2,
      smul_smul, map_mul Om, Module.End.mul_apply, mul_comm (c q)]
  · refine Continuous.subtype_mk (continuous_iff_continuousAt.2 fun q => ?_) _
    obtain ⟨u, hu⟩ := Function.ne_iff.1 (hne (P q))
    have a1 : Continuous fun p => om (P p) f u := (hW.om_cont f hf u).comp hPc
    have a2 : Continuous fun p => (Om (P p) ⟨f, hf⟩ : WO S T → ℂ) u := (hL.cont hS hT ⟨f, hf⟩ u).comp hPc
    refine ((a1.continuousAt).div a2.continuousAt hu).congr ?_
    filter_upwards [a2.continuousAt.eventually_ne hu] with p hp
    show om (P p) f u / (Om (P p) ⟨f, hf⟩ : WO S T → ℂ) u = c p
    rw [h p f hf, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hp]

theorem lemD : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (w : 𝓞 D.host.E) (lam : ℕ →* ℂ) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)),
    GlobalTheory.FinWeilO.IsLatRep hψ.1 ΛS ΛT w lam Om →
    (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) →
    ∀ e, IsSplitIdem D e → ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h →
    ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ∀ c : ℂ, ‖c‖ = 1 →
    (∀ f (hf : IsThetaFunO ψ S T f), om (g, h) f = c • (Om (g, h) ⟨f, hf⟩ : WO S T → ℂ)) →
    c = (splitFacO χS χT x y : ℂ) := by
  intro D ψ hψ S T χS χT om hW ΛS ΛT w lam Om hL hsq e he g h hg hh x y hx hy c hc H
  obtain ⟨r, hr, a⟩ := hW.om_split e he g h hg hh x y hx hy
  obtain ⟨r', hr', b⟩ := hL.split hsq he hg hh
  obtain ⟨ℓ, hℓ, f₁, hf₁, h0⟩ := GlobalTheory.HalfCoinv.exists_invariant_form D ψ hψ S T e he
  have k := a ℓ hℓ f₁ hf₁
  rw [H f₁ hf₁, map_smul, b ℓ hℓ ⟨f₁, hf₁⟩, smul_eq_mul] at k
  have k1 : (c * (r' : ℂ)) * ℓ f₁ = ((r : ℂ) * (splitFacO χS χT x y : ℂ)) * ℓ f₁ := by
    rw [mul_assoc]; exact k
  have k2 := mul_right_cancel₀ h0 k1
  have k3 := congrArg norm k2
  rw [norm_mul, norm_mul, hc, Circle.norm_coe, one_mul, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hr.le, Real.norm_of_nonneg hr'.le] at k3
  rw [k3, mul_comm] at k2
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hr.ne') k2

theorem splitWeil_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
  (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
  IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ lam : ℕ →* ℂ, GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam →
  (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) →
  ∀ (w : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)),
  GlobalTheory.FinWeilO.IsLatRep hψ.1 ΛS ΛT w lam Om → ∀ ε : AE D, GlobalTheory.RatAut.IsHalfIdem D ε →
  ∀ (g : GA D S) (h : GA D T), SuppAt ε S g → SuppAt ε T h → ∀ x y : (AE D)ˣ, IsDetAt ε S g x → IsDetAt ε T h y →
  ∀ f : GlobalTheory.FinWeilO.thetaSub ψ S T,
    om (g, h) f = ((splitFacO χS χT x y : Circle) : ℂ) • (Om (g, h) f : WO S T → ℂ) := by
  intro D ψ hψ S T χS χT om hW ΛS ΛT hS hT lam hlam hsq w Om hL ε hε g₀ h₀ hg₀ hh₀ x₀ y₀ hx₀ hy₀ f₀
  have hB := lemB D ψ hψ S T χS χT om hW ΛS ΛT w lam Om hL hlam
  obtain ⟨ν, hνc, hν⟩ := lemC D ψ hψ S T χS χT om hW ΛS ΛT hS hT w lam Om hL hB ε hε
  obtain ⟨c, c1, c2, c3, c4, c5⟩ := GlobalTheory.FinWeilForm.exists_half_character hε S χT _ hW.hecT hW.resT
  obtain ⟨d, d1, d2, d3, d4, d5⟩ := GlobalTheory.FinWeilForm.exists_half_character hε T χS _ hW.hecS hW.resS
  obtain ⟨f₁, f1, hf₁⟩ := GlobalTheory.FinWeilForm.exists_theta hψ S T
  have hone : ∀ p : GA D S × GA D T, proj hε S p.1 = 1 → proj hε T p.2 = 1 → ν p = 1 := fun p a b => by
    have e := hν p f₁ hf₁
    rw [a, b, show ((1 : GA D S), (1 : GA D T)) = 1 from rfl, map_one, map_one, Module.End.one_apply,
      Module.End.one_apply] at e
    exact Circle.ext (smul_left_injective ℂ f1 (e.symm.trans (one_smul ℂ f₁).symm))
  have hsp : ∀ e, IsSplitIdem D e → ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h →
      ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ν (g, h) = splitFacO χS χT x y :=
    fun e he g h hg hh x y hx hy => by
      have e1 : ∀ f (hf : IsThetaFunO ψ S T f), om (g, h) f = (ν (g, h) : ℂ) • (Om (g, h) ⟨f, hf⟩ : WO S T → ℂ) :=
        fun f hf => by
          have := hν (g, h) f hf
          dsimp only at this
          rwa [proj_of_split hε he hg, proj_of_split hε he hh] at this
      exact Circle.ext (lemD D ψ hψ S T χS χT om hW ΛS ΛT w lam Om hL hsq e he g h hg hh x y hx hy _
        (Circle.norm_coe _) e1)
  have s1 : ∀ (V : HSp D) (a : AE D) i j, a * (Formalism.L2.Theta.mt V 1 - 1) i j = (Formalism.L2.Theta.mt V 1 - 1) i j :=
    fun V a i j => by rw [GlobalTheory.IdemSupport.mt_one, sub_self, Matrix.zero_apply, mul_zero]
  have d1' : ∀ (V : HSp D) (e : AE D), IsDetAt e V 1 1 := fun V e => by
    show ((1 : (AE D)ˣ) : AE D) = e * (Formalism.L2.Theta.mt V 1).det + (1 - e)
    rw [GlobalTheory.IdemSupport.mt_one, Matrix.det_one, Units.val_one]
    ring
  let μ : GA D S × GA D T →* Circle := ν * (c.comp (MonoidHom.fst _ _)) * (d.comp (MonoidHom.snd _ _))⁻¹
  have hμ : ∀ p, μ p = ν p * c p.1 * (d p.2)⁻¹ := fun p => rfl
  have hμc : Continuous μ := by
    show Continuous fun p : GA D S × GA D T => ν p * c p.1 * (d p.2)⁻¹
    exact (hνc.mul (c1.comp continuous_fst)).mul (d1.comp continuous_snd).inv
  have hl := GlobalTheory.LocalGlobalChar.eq_one_of_local D S (μ.comp (MonoidHom.inl _ _)) (hμc.comp (Continuous.prodMk_left 1))
    (fun g hg => by
      show μ (g, 1) = 1
      rw [hμ, hone (g, 1) (proj_of_real hε hg) (map_one _), c2 g hg]
      simp)
    (fun e he g hg => by
      show μ (g, 1) = 1
      obtain ⟨x, hx⟩ := GlobalTheory.FinWeilForm.exists_isDetAt he S g
      rw [hμ, hsp e he g 1 hg (s1 T _) x 1 hx (d1' T e), c4 e he g hg x hx, splitFacO]
      simp)
    (fun v η hv g hg => by
      show μ (g, 1) = 1
      rw [hμ, hone (g, 1) (proj_of_nonSplit hε hv hg) (map_one _), c3 v η hv g hg]
      simp)
  have hr := GlobalTheory.LocalGlobalChar.eq_one_of_local D T (μ.comp (MonoidHom.inr _ _)) (hμc.comp (Continuous.prodMk_right 1))
    (fun h hh => by
      show μ (1, h) = 1
      rw [hμ, hone (1, h) (map_one _) (proj_of_real hε hh), d2 h hh]
      simp)
    (fun e he h hh => by
      show μ (1, h) = 1
      obtain ⟨y, hy⟩ := GlobalTheory.FinWeilForm.exists_isDetAt he T h
      rw [hμ, hsp e he 1 h (s1 S _) hh 1 y (d1' S e) hy, d4 e he h hh y hy, splitFacO]
      simp)
    (fun v η hv h hh => by
      show μ (1, h) = 1
      rw [hμ, hone (1, h) (map_one _) (proj_of_nonSplit hε hv hh), d3 v η hv h hh]
      simp)
  have hall : ∀ p, μ p = 1 := fun p => by
    have : p = (p.1, 1) * (1, p.2) := Prod.ext (mul_one _).symm (one_mul _).symm
    rw [this, map_mul, show μ (p.1, 1) = 1 from hl p.1, show μ (1, p.2) = 1 from hr p.2, mul_one]
  have hνp : ν (g₀, h₀) = splitFacO χS χT x₀ y₀ := by
    have h1 := hall (g₀, h₀)
    rw [hμ, mul_inv_eq_one] at h1
    rw [splitFacO, ← c5 g₀ x₀ hx₀, ← d5 h₀ y₀ hy₀, ← h1]
    show ν (g₀, h₀) = (c g₀)⁻¹ * (ν (g₀, h₀) * c g₀)
    rw [mul_comm, mul_inv_cancel_right]
  have e := hν (g₀, h₀) f₀.1 f₀.2
  dsimp only at e
  rw [proj_of_suppAt hε hg₀, proj_of_suppAt hε hh₀, hνp] at e
  exact e

end GlobalTheory.SplitWeilDict
end
end

open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_splitSupported_eq_intertwiner_mul_halfDetChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
  (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
  IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ lam : ℕ →* ℂ, GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam →
  (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) →
  ∀ (w : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)),
  GlobalTheory.FinWeilO.IsLatRep hψ.1 ΛS ΛT w lam Om → ∀ ε : AE D, GlobalTheory.RatAut.IsHalfIdem D ε →
  ∀ (g : GA D S) (h : GA D T), SuppAt ε S g → SuppAt ε T h → ∀ x y : (AE D)ˣ, IsDetAt ε S g x → IsDetAt ε T h y →
  ∀ f : GlobalTheory.FinWeilO.thetaSub ψ S T,
    om (g, h) f = ((splitFacO χS χT x y : Circle) : ℂ) • (Om (g, h) f : WO S T → ℂ) := by
  atlas_forward_decl GlobalTheory.SplitWeilDict.splitWeil_eq
end

section
open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitVacMove

open GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.BotClassDict GlobalTheory.SplitScalar

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}

theorem exists_isLatRep_of {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) {lam : ℕ →* ℂ} (hlam : GoodNorm (sgO D) lam) {w : 𝓞 D.host.E} (hw : w + sgO D w = 1) :
    ∃ Om, IsLatRep hψ.1 ΛS ΛT w lam Om := by
  have H := isHeis_opF hψ.1 S T hw
  have hA := selfDual_latF (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1
  obtain ⟨hlev, hmov⟩ := GlobalTheory.T.completedHomLattice_multiple_mem_open_level D S T ΛS ΛT hS hT (GlobalTheory.T.completedHomLattice_finitelyGenerated D S T ΛS ΛT hS hT)
  have hspan := GlobalTheory.T.span_heisenberg_translates_of_lattice_vacua_eq_top H _ hA (smooth_theta hψ.1 hS hT hw hA hlev)
  have hidx : ∀ p, idx (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T p)) ≠ 0 := fun p => by
    obtain ⟨N, hN, h⟩ := hmov p.1 p.2
    refine idx_latF_ne_zero hS hT _ hN ?_
    rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  obtain ⟨Om, h1, h2⟩ := GlobalTheory.T.exists_weil_representation_of_lattice_vacua H lam hlam _ hA hspan (rhoF S T) gamF_rhoF hidx
  exact ⟨Om, hw, hA, hspan, hidx, h1, fun p => (h2 p).1, fun p => (h2 p).2⟩

theorem ext_finQ {a b : AE D} (h1 : infPart D a = infPart D b) (h2 : finQ D a = finQ D b) : a = b :=
  adele_ext h1 (by
    have := congrArg (GlobalTheory.BotFormula.toAfE D) h2
    rwa [toAfE_finQ, toAfE_finQ] at this)

theorem finPart_surjective (D : D7) : Function.Surjective (finPart D) := by
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, (finPart D).map_zero⟩
  | tmul a x => exact ⟨TensorProduct.tmul D.host.F (pairA D.host.F 0 a) x, rfl⟩
  | add y z hy hz =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    exact ⟨a + b, (finPart D).map_add a b⟩

theorem exists_finQ (q : Formalism.MainNotions.StandardLatticesGL3.AE D) : ∃ a : AE D, infPart D a = 0 ∧ finQ D a = q := by
  obtain ⟨a, ha⟩ := finPart_surjective D (GlobalTheory.BotFormula.toAfE D q)
  refine ⟨(1 - realIdem D) * a, ?_, ?_⟩
  · rw [RingHom.map_mul, RingHom.map_sub, infPart_realIdem, RingHom.map_one, sub_self, zero_mul]
  · apply (GlobalTheory.BotFormula.toAfE D).injective
    rw [toAfE_finQ]
    show finPart D _ = _
    rw [RingHom.map_mul, RingHom.map_sub, finPart_realIdem, RingHom.map_one, sub_zero, one_mul, ha]

def back (S T : HSp D) (r : D.host.E) : XF S T →+ XA D S.rank T.rank where
  toFun x := (-Formalism.MainNotions.StandardLatticesGL3.inc D r) • (x : WO S T).map (finQ D)
  map_zero' := by rw [XF.coe_zero, Matrix.map_zero _ (map_zero _), smul_zero]
  map_add' x y := by rw [XF.coe_add, Matrix.map_add _ (map_add (finQ D)), smul_add]

theorem back_apply (r : D.host.E) (x : XF S T) (i : Fin T.rank) (j : Fin S.rank) :
    back S T r x i j = -(Formalism.MainNotions.StandardLatticesGL3.inc D r * finQ D ((x : WO S T) i j)) := neg_mul _ _

theorem inc_mul_inv {r : D.host.E} (hr : r ≠ 0) : Formalism.MainNotions.StandardLatticesGL3.inc D r * Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ hr, map_one]

theorem back_injective {r : D.host.E} (hr : r ≠ 0) : Function.Injective (back S T r) := fun x y h => by
  refine XF.ext (Matrix.ext fun i j => ext_finQ ?_ ?_)
  · exact (congrFun (congrFun x.fin i) j).trans (congrFun (congrFun y.fin i) j).symm
  · have h1 := congrFun (congrFun h i) j
    rw [back_apply, back_apply] at h1
    linear_combination (-Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹) * h1 -
      (finQ D ((x : WO S T) i j) - finQ D ((y : WO S T) i j)) * inc_mul_inv (D := D) hr

theorem back_surjective {r : D.host.E} (hr : r ≠ 0) : Function.Surjective (back S T r) := fun ζ => by
  choose a h1 h2 using fun i j => exists_finQ (D := D) (-(Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * ζ i j))
  refine ⟨XF.mk (Matrix.of a) (Matrix.ext h1), Matrix.ext fun i j => ?_⟩
  rw [back_apply, XF.coe_mk, Matrix.of_apply, h2]
  linear_combination ζ i j * inc_mul_inv (D := D) hr

def ratX (S T : HSp D) (r : D.host.E) (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : XF S T :=
  XF.mk (finPt (S := S) (T := T) rfl rfl r z) (GlobalTheory.VacUnique.finRat_inf S T _)

theorem back_ratX {r : D.host.E} (hr : r ≠ 0) (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    back S T r (ratX S T r z) = z.map (Formalism.MainNotions.StandardLatticesGL3.inc D) := by
  show (-Formalism.MainNotions.StandardLatticesGL3.inc D r) • (finPt (S := S) (T := T) rfl rfl r z).map (finQ D) = _
  rw [GlobalTheory.LevelTr.finQ_finPt, neg_smul, smul_neg, neg_neg, smul_smul, inc_mul_inv hr, one_smul]

theorem back_rhoF (gS : S.gram = 1) (gT : T.gram = 1) (r : D.host.E) {x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank}
    {y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank} {g : GA D S} {h : GA D T} (hg : IsFinPt S g x) (hh : IsFinPt T h y) (u : XF S T) :
    back S T r (rhoF S T (g, h) u) = actA D S.rank T.rank (x, y) (back S T r u) := by
  show (-Formalism.MainNotions.StandardLatticesGL3.inc D r) • (actO S T g h u).map (finQ D) = _
  rw [actA_apply, actO, Matrix.map_mul, Matrix.map_mul, GlobalTheory.LevelTr.finQ_mt_of_isFinPt T gT hh,
    GlobalTheory.LevelTr.finQ_mt_inv_of_isFinPt S gS hg]
  show _ = _ * ((-Formalism.MainNotions.StandardLatticesGL3.inc D r) • (u : WO S T).map (finQ D)) * _
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem back_mem_iff (gS : S.gram = 1) {cc : Ideal (𝓞 D.host.K)} {r : D.host.E} (hc : cc ≠ ⊥) (hr : IsScale D cc r)
    (u : XF S T) : back S T r u ∈ latA D cc S.rank T.rank ↔
      u ∈ latF S T (GlobalTheory.VacRead.lsB D cc r S.rank) (stdL D T.rank) := by
  rw [mem_latF, GlobalTheory.T.mem_latticeO_iff_scale_mul_finitePart_mem_idealLattice D S T gS cc r hc hr _ u.fin, mem_latA]
  simp only [back_apply, neg_mem_iff]

theorem exists_deep {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hψ : IsCharAF D.host.F ψ) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) {w : 𝓞 D.host.E} (hw : w + sgO D w = 1) (hA : SelfDual (gamF ψ S T) (latF S T ΛS ΛT))
    (x : XF S T) (f : thetaSub ψ S T) :
    ∃ m : ℕ, 0 < m ∧ ∀ l ∈ latF S T ΛS ΛT, opF hψ S T w (x + m • l) f = opF hψ S T w x f := by
  have H := isHeis_opF hψ S T hw
  obtain ⟨hlev, -⟩ := GlobalTheory.T.completedHomLattice_multiple_mem_open_level D S T ΛS ΛT hS hT (GlobalTheory.T.completedHomLattice_finitelyGenerated D S T ΛS ΛT hS hT)
  obtain ⟨V, hV, hf⟩ := f.2.level
  obtain ⟨N, hN, hNU⟩ := hlev V hV
  obtain ⟨M, hM, hMU⟩ := hlev _ (GlobalTheory.FinTranslate.isOpen_annSub hψ (XF.fin (w • x)))
  refine ⟨2 * (N * M), by positivity, fun l hl => ?_⟩
  have e1 : opF hψ S T w ((2 * (N * M)) • l) f = f := by
    apply Subtype.ext
    rw [coe_opF, hf _ (by
      rw [XF.coe_nsmul, show 2 * (N * M) = N * (2 * M) by ring, mul_smul]
      exact hNU _ (nsmul_mem hl _)) (XF.fin _), mul_smul, phase_two hA w (nsmul_mem hl _), one_smul]
  have e2 : gamF ψ S T (w • x) ((2 * (N * M)) • l) = 1 := by
    have e3 : ψ (symplOH S T (w • x : XF S T) (M • ((2 * N) • (l : WO S T)))) = 1 := (hMU _ (nsmul_mem hl _)).2
    rw [← mul_smul, show M * (2 * N) = 2 * (N * M) by ring] at e3
    rw [gamF, ← symplOH_add_self, AddChar.map_add_eq_mul, XF.coe_nsmul, e3, one_mul]
  have e4 := H.comp x ((2 * (N * M)) • l) f
  rw [e1, e2, one_smul] at e4
  exact e4.symm

variable {θ : InfFam D} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E}

theorem reads_sum {ι : Type} (s : Finset ι) {G : ι → VC D S.rank T.rank → ℂ} {f : ι → WO S T → ℂ}
    (h : ∀ i, Reads ψ θ rfl rfl cc δ r (G i) (f i)) :
    Reads ψ θ (S := S) (T := T) rfl rfl cc δ r (∑ i ∈ s, G i) (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => exact ⟨(thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons]; exact (h a).add ih

theorem reads_opF (hset : Setup ψ θ S T cc δ r) {w w' : 𝓞 D.host.E} (hw : w + sgO D w = 1)
    (hph : ∀ z, phase ψ w (ratX S T r z) = Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z))
    (hS : IsSelfDualC S (GlobalTheory.VacRead.lsB D cc r S.rank)) (hT : IsSelfDualC T (stdL D T.rank))
    (hA : SelfDual (gamF ψ S T) (latF S T (GlobalTheory.VacRead.lsB D cc r S.rank) (stdL D T.rank)))
    {γ : XA D S.rank T.rank → XA D S.rank T.rank → ℂ}
    {WA : XA D S.rank T.rank → TTs D (tor0 D cc δ) S.rank T.rank →ₗ[ℂ] TTs D (tor0 D cc δ) S.rank T.rank}
    (hM : IsModel D cc δ S.rank T.rank w' γ WA) (F : TTs D (tor0 D cc δ) S.rank T.rank) (f : thetaSub ψ S T)
    (h : Reads ψ θ (S := S) (T := T) rfl rfl cc δ r F f) (x : XF S T) :
    Reads ψ θ (S := S) (T := T) rfl rfl cc δ r (WA (back S T r x) F) (opF hset.std.1 S T w x f) := by
  have hr : r ≠ 0 := IsScale.ne_zero hset.crv.1.1 hset.scale
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hset.crv S.rank T.rank
  obtain ⟨m, hm, hmx⟩ := exists_deep hset.std.1 hS hT hw hA x f
  obtain ⟨n, hn, hnx⟩ := hM.2.2.2.2 (back S T r x) F
  obtain ⟨z, a, ha, hz⟩ := h3 (back S T r x) (m * n) (Nat.mul_pos hm hn)
  obtain ⟨l, rfl⟩ := back_surjective (S := S) (T := T) hr a
  have hl := (back_mem_iff hset.gS hset.crv.1.1 hset.scale l).1 ha
  have e : ratX S T r z = x + m • n • l := back_injective hr (by
    rw [back_ratX hr, hz, map_add, map_nsmul, map_nsmul, mul_smul])
  have e1 : WA (back S T r x) F = WA (z.map (Formalism.MainNotions.StandardLatticesGL3.inc D)) F := by
    rw [hz, mul_comm, mul_smul, hnx _ (nsmul_mem ha m)]
  rw [e1, ← hmx _ (nsmul_mem hl n), ← e, hM.2.2.2.1, coe_opF, hph]
  exact (heisO_finPt_reads ψ θ S T rfl rfl cc δ r hset _ _ h z).smul _

theorem reads_latRep (hset : Setup ψ θ S T cc δ r) {w : 𝓞 D.host.E}
    (hph : ∀ z, phase ψ w (ratX S T r z) = Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z))
    (hS : IsSelfDualC S (GlobalTheory.VacRead.lsB D cc r S.rank)) (hT : IsSelfDualC T (stdL D T.rank)) {lam : ℕ →* ℂ}
    (hsq : ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ))
    {Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)}
    (hL : IsLatRep hset.std.1 (GlobalTheory.VacRead.lsB D cc r S.rank) (stdL D T.rank) w lam Om)
    {e0 : VC D S.rank T.rank → ℂ} (he : e0 ∈ Th D (tor0 D cc δ) (stdL D S.rank) (stdL D T.rank)) (h0 : e0 ≠ 0)
    (f : thetaSub ψ S T) (hf : Reads ψ θ (S := S) (T := T) rfl rfl cc δ r e0 f)
    {x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank} {y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank} {g : GA D S} {h : GA D T} (hg : IsFinPt S g x)
    (hh : IsFinPt T h y) (sx : Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (x : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)))
    (sy : Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (y : GL (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))) {L₁ L₁'}
    (h1 : Formalism.MainNotions.StandardLatticesGL3.Moves D (x : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) L₁)
    (h1' : Formalism.MainNotions.StandardLatticesGL3.Moves D (y : GL (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) L₁') :
    Reads ψ θ (S := S) (T := T) rfl rfl cc δ r (Formalism.MainNotions.TaylorLogMetric.Iop D (tor0 D cc δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D cc δ) S.rank T.rank)
      (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L₁ L₁') e0) (Om (g, h) f) := by
  have hG := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  have hr : r ≠ 0 := IsScale.ne_zero hset.crv.1.1 hset.scale
  have hmem := back_mem_iff (T := T) hset.gS hset.crv.1.1 hset.scale
  obtain ⟨w', γ, WA, hM⟩ := GlobalTheory.T.exists_adelicWeilRepresentationModel D hG cc δ hset.crv S.rank T.rank
  obtain ⟨hTT, hfix, -⟩ := GlobalTheory.T.adelicWeil_vacuum_fixed_and_translates_span D hG cc δ hset.crv S.rank T.rank w' γ WA hM e0 he h0
  have hread := reads_opF hset hL.hw hph hS hT hL.sd hM ⟨e0, hTT⟩ f hf
  have hfixF : Fixes (opF hset.std.1 S T w) (latF S T (GlobalTheory.VacRead.lsB D cc r S.rank) (stdL D T.rank)) f := fun a ha => by
    have := hread a
    rw [hfix _ ((hmem a).2 ha)] at this
    exact Subtype.ext (this.unique hf)
  have hmem' : ∀ u, back S T r u ∈ (latA D cc S.rank T.rank).map (actA D S.rank T.rank (x, y)) ↔
      u ∈ (latF S T (GlobalTheory.VacRead.lsB D cc r S.rank) (stdL D T.rank)).map (rhoF S T (g, h)) := fun u => by
    constructor
    · rintro ⟨a, ha, e⟩
      obtain ⟨l, rfl⟩ := back_surjective (S := S) (T := T) hr a
      exact ⟨l, (hmem l).1 ha, back_injective hr (by rw [back_rhoF hset.gS hset.gT r hg hh, e])⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨_, (hmem l).2 hl, (back_rhoF hset.gS hset.gT r hg hh l).symm⟩
  have hSD : SelfDual γ ((latA D cc S.rank T.rank).map (actA D S.rank T.rank (x, y))) := fun ζ => by
    rw [IopSum.mem_map_act, hM.2.1]
    constructor
    · rintro h2 _ ⟨a, ha, rfl⟩
      rw [← h2 a ha, ← hM.2.2.1 (x, y) (actA D S.rank T.rank (x, y)⁻¹ ζ), IopSum.act_act_inv]
    · intro h2 a ha
      rw [← hM.2.2.1 (x, y), IopSum.act_act_inv]
      exact h2 _ ⟨a, ha, rfl⟩
  have H := isHeis_opF hset.std.1 S T hL.hw
  obtain ⟨n, t, ht, hu⟩ := ((sumOp_transversal H _ _ (hL.sd' (g, h))).2.1 (hL.fin (g, h))).1
  obtain ⟨s1, i1⟩ := (sumOp_transversal H _ _ (hL.sd' (g, h))).1 f hfixF _ t ht hu
  obtain ⟨s2, i2⟩ := (sumOp_transversal hM.1 _ _ hSD).1 _ hfix _ (fun i => back S T r (t i))
    (fun i => (hmem' _).2 (ht i)) (fun b hb => by
      obtain ⟨l, rfl⟩ := back_surjective (S := S) (T := T) hr b
      simp only [← map_sub, hmem]
      exact hu l ((hmem' l).1 hb))
  have hidx := GlobalTheory.T.heisenbergRelativeIndex_translate_completed_lattice D hG cc δ hset.crv S.rank T.rank x y
  have hl := hsq _ hidx.1 fun q hq hi => hidx.2.1 q hq (sx q hq hi) (sy q hq hi)
  have hI := iop_eq_sumOp D hG cc δ hset.crv S.rank T.rank w' γ WA hM x y L₁ L₁' h1 h1' hSD ⟨e0, hTT⟩ hfix
  rw [show Formalism.MainNotions.TaylorLogMetric.Iop D (tor0 D cc δ) _ _ e0 = _ from hI, hL.vac _ f hfixF, normOp, s1, s2, i1, ← i2, hl,
    Submodule.coe_smul, Submodule.coe_sum, Submodule.coe_sum]
  exact (reads_sum _ fun i => hread (t i)).smul _

theorem exists_prime_mem {R : Type} [CommRing R] {P : Ideal R} (hP : P.IsPrime) :
    ∀ n : ℕ, n ≠ 0 → (n : R) ∈ P → ∃ q : ℕ, q.Prime ∧ (q : R) ∈ P := by
  intro n
  induction n using induction_on_primes with
  | zero => exact fun h => absurd rfl h
  | one => exact fun _ h => absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) hP.ne_top
  | prime_mul p a hp ih =>
    intro h0 h
    rw [Nat.cast_mul] at h
    exact (hP.mem_or_mem h).elim (fun h => ⟨p, hp, h⟩) (ih (right_ne_zero_of_mul h0))

theorem cA_cA' (a : AE D) : cA D (cA D a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul x e =>
    show TensorProduct.tmul D.host.F x (star (star e)) = _
    rw [star_star]
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb]

theorem zeroAt_half {ε : AE D} (hε : GlobalTheory.RatAut.IsHalfIdem D ε) {q : ℕ} (hq : q.Prime) (hi : Formalism.MainNotions.StandardLatticesGL3.InertQ D q)
    (b : AE D) : Formalism.MainNotions.StandardLatticesGL3.ZeroAt D q (finQ D (ε * b)) :=
  (GlobalTheory.T.finitePartRationalTensor_zeroAtPrime_iff_placeIdem D q hq _).2 fun v η hv hqv => by
    rw [← mul_assoc, hε.2.2.2.2 v η ((GlobalTheory.T.inertPrime_iff_nonSplitPlaceIdempotent D q hq v η hv hqv).1 hi), zero_mul]

theorem half_supp {ε : AE D} (hε : GlobalTheory.RatAut.IsHalfIdem D ε) {a : AE D} (h0 : infPart D a = 0)
    (ha : ∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → Formalism.MainNotions.StandardLatticesGL3.ZeroAt D q (finQ D a)) : (ε + cA D ε) * a = a := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  refine hΦ.ext' (by rw [RingHom.map_mul, h0, mul_zero]) fun Q => ?_
  obtain ⟨η, hη⟩ := GlobalTheory.IdemSupport.exists_placeIdem (D := D) (Q.under (𝓞 D.host.F))
  have key : algebraMap (AF D.host.F) (AE D) η * ((ε + cA D ε) * a) = algebraMap (AF D.host.F) (AE D) η * a := by
    by_cases hn : GlobalTheory.WeilParts.NonSplitAt D (Q.under (𝓞 D.host.F)) η
    · obtain ⟨q, hq, hqv⟩ := exists_prime_mem (Q.under (𝓞 D.host.F)).isPrime _
        (Ideal.absNorm_eq_zero_iff.not.2 (Q.under (𝓞 D.host.F)).ne_bot) (Ideal.absNorm_mem _)
      have := (GlobalTheory.T.finitePartRationalTensor_zeroAtPrime_iff_placeIdem D q hq a).1 (ha q hq ((GlobalTheory.T.inertPrime_iff_nonSplitPlaceIdempotent D q hq _ η hη hqv).2 hn)) _ η hη hqv
      rw [mul_left_comm, this, mul_zero]
    · obtain ⟨e, he, hs⟩ : ∃ e : AE D, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) η := by
        by_contra h
        exact hn ⟨hη, h⟩
      rw [← hs]
      rcases hε.2.2.2.1 e he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h3 := congrArg (cA D) h1
        have h4 := congrArg (cA D) h2
        rw [RingHom.map_mul] at h3
        rw [RingHom.map_mul, cA_cA', RingHom.map_zero] at h4
        linear_combination a * (h1 + h2 + h3 + h4)
      · have h3 := congrArg (cA D) h1
        have h4 := congrArg (cA D) h2
        rw [RingHom.map_mul, RingHom.map_zero] at h3
        rw [RingHom.map_mul, cA_cA'] at h4
        linear_combination a * (h1 + h2 + h3 + h4)
  have h1 := congrArg (fun z => Φ z Q) key
  simp only [GlobalTheory.IdemSupport.ev_mul (Φ := Φ) (algebraMap (AF D.host.F) (AE D) η),
    (GlobalTheory.IdemSupport.place_comp hΦ hη).2.1 Q rfl, one_mul] at h1
  exact h1

theorem cut_sub_one {R : Type} [CommRing R] {e z u : R} (h : u = e * z + (1 - e)) : e * (z - 1) = u - 1 := by
  rw [h]; ring

theorem cut_conj {R : Type} [CommRing R] {e e' z z' : R} (h : (1 - (e + e')) * z = 1 - (e + e')) (h' : z' * z = 1) :
    e * z + (1 - e) = z * (e' * z' + (1 - e')) := by
  linear_combination -h - e' * h'

set_option maxHeartbeats 1000000 in

theorem exists_half_det {ε : AE D} (hε : GlobalTheory.RatAut.IsHalfIdem D ε) (V : HSp D) (gV : V.gram = 1) {g : GA D V}
    {x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank} (hg : IsFinPt V g x) (sx : Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))) :
    SuppAt ε V g ∧ ∃ (u : (AE D)ˣ) (x₀ : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ), IsDetAt ε V g u ∧ IsFinIdl u x₀ ∧
      (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → Formalism.MainNotions.StandardLatticesGL3.ZeroAt D q ((x₀ : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1)) ∧
      x₀ = Matrix.GeneralLinearGroup.det (x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * Formalism.MainNotions.StandardLatticesGL3.sgU D x₀ := by
  have hfin := GlobalTheory.LevelTr.finQ_mt_of_isFinPt V gV hg
  have hinf := GlobalTheory.LevelTr.infPart_mt_of_mem_GfC V hg.1
  have hs : SuppAt ε V g := fun i j => half_supp hε (by
      rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]
      refine (congrFun (congrFun hinf i) j).trans ?_
      rw [← Matrix.map_one (infPart D) (infPart D).map_zero (infPart D).map_one]
      rfl) fun q hq hi => by
    have e1 : finQ D (Formalism.L2.Theta.mt V g i j) = _ := congrFun (congrFun hfin i) j
    have e2 : finQ D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j := by
      rw [← Matrix.map_one (finQ D) (finQ D).map_zero (finQ D).map_one]
      rfl
    rw [Matrix.sub_apply, RingHom.map_sub, e1, e2]
    exact sx q hq hi i j
  let u := GlobalTheory.SplitDetChar.cut ε hε.1 (Matrix.GeneralLinearGroup.det (matHom V g))
  have hu : (u : AE D) = ε * (Formalism.L2.Theta.mt V g).det + (1 - ε) := rfl
  clear_value u
  have hout := GlobalTheory.SplitDetChar.mul_det (1 - (ε + cA D ε)) (Formalism.L2.Theta.mt V g) fun i j => by
    rw [sub_mul, one_mul, hs i j, sub_self]
  have hun := det_conj_mul V g
  have hdet : finQ D (Formalism.L2.Theta.mt V g).det =
      ((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)).det := by
    rw [RingHom.map_det, ← hfin]
    rfl
  refine ⟨hs, u, Units.map (finQ D).toMonoidHom u, hu, ⟨?_, ?_⟩, fun q hq hi => ?_, Units.ext ?_⟩
  · rw [hu, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, hε.2.2.1, RingHom.map_one, zero_mul, sub_zero, zero_add]
  · show _ = GlobalTheory.BotFormula.toFinE D (finQ D u)
    rw [← finAdEquiv_toAfE, toAfE_finQ]
    rfl
  · have := zeroAt_half hε hq hi ((Formalism.L2.Theta.mt V g).det - 1)
    rw [show ε * ((Formalism.L2.Theta.mt V g).det - 1) = u - 1 from cut_sub_one hu, RingHom.map_sub, RingHom.map_one] at this
    exact this
  · have e1 : (u : AE D) = (Formalism.L2.Theta.mt V g).det * cA D (u : AE D) := by
      rw [hu, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
      exact cut_conj hout hun
    have e2 := congrArg (finQ D) e1
    have e5 : finQ D (cA D (u : AE D)) = Formalism.MainNotions.StandardLatticesGL3.sgA D (finQ D u) := finQ_sigR (u : AE D)
    replace e2 := e2.trans ((finQ D).map_mul _ _)
    rw [hdet, e5] at e2
    have e3 : ∀ z : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ, (Formalism.MainNotions.StandardLatticesGL3.sgU D z : Formalism.MainNotions.StandardLatticesGL3.AE D) = Formalism.MainNotions.StandardLatticesGL3.sgA D z := fun _ => rfl
    have e4 : ((Units.map (finQ D).toMonoidHom u : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) = finQ D u := rfl
    rw [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, e3, e4]
    exact e2

theorem isSelfDualC_of_sd (V : HSp D) (gV : V.gram = 1) {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hL : Formalism.MainNotions.StandardLatticesGL3.SD D L) : IsSelfDualC V L := by
  obtain ⟨Λ, h1, h2⟩ := GlobalTheory.MovedDict.isSelfDualC_inV V 1 (by rw [gV]; simp [Formalism.UG.cT]) L hL
  have : Λ = L := SetLike.coe_injective (by rw [h1]; simp [GlobalTheory.MovedDict.inV])
  exact this ▸ h2

theorem reads_om_split : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hset e0 W χS χT om hom _ t0 _ _ hodd cS cT f₀ hf x y g h hg hh sx sy
  subst hS hT
  obtain ⟨w, hw, hph⟩ := GlobalTheory.T.finitePartQuadraticPhase_eq_cmTheta_exp D
  obtain ⟨lam, hlam, hsq⟩ := exists_goodNorm D
  obtain ⟨ε, hε⟩ := GlobalTheory.RatAut.exists_isHalfIdem D
  have dS := isSelfDualC_of_sd S hset.gS (GlobalTheory.T.invDifferentLatticeProductHermitian_isSelfDual D cc r S.rank hset.crv.1.1 hset.scale)
  have dT := isSelfDualC_of_sd T hset.gT (GlobalTheory.MovedVacuum.sd_stdL D T.rank)
  obtain ⟨Om, hL⟩ := exists_isLatRep_of hset.std dS dT hlam hw
  obtain ⟨sg, u, x₀, hu, iu, zx, dx⟩ := exists_half_det hε S hset.gS hg sx
  obtain ⟨sh, v, y₀, hv, iv, zy, dy⟩ := exists_half_det hε T hset.gT hh sy
  obtain ⟨Lt, hLt, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D S.rank
  obtain ⟨Lt', hLt', -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D T.rank
  have h1 := reads_latRep hset (hph ψ θ S T cc δ r hset) dS dT hsq hL hodd.1 W.nz ⟨f₀, hf.1⟩ hf hg hh sx sy
    (hLt x).1 (hLt' y).1
  have h2 := GlobalTheory.T.weilDatum_splitSupported_eq_intertwiner_mul_halfDetChar D ψ hset.std S T χS χT om hom _ _ dS dT lam hlam hsq w Om hL ε hε g h sg sh u v hu hv ⟨f₀, hf.1⟩
  have h3 := W.split x y x₀ y₀ _ _ sx sy (fun q hq hi => ⟨zx q hq hi, zy q hq hi⟩) dx dy (hLt x).1 (hLt' y).1
  have h4 : ((splitFacO χS χT u v : Circle) : ℂ) = ((W.chV.f y₀ ^ W.ep * W.chV'.f x₀ ^ W.ep' : ℂˣ) : ℂ) := by
    rw [splitFacO, Circle.coe_mul, Circle.coe_inv, cS v y₀ iv, cT u x₀ iu, zpow_neg, Units.val_inv_eq_inv_val, inv_inv,
      Units.val_mul, mul_comm]
  rw [h3, show om (g, h) f₀ = _ from h2, h4]
  exact h1.smul _

end GlobalTheory.SplitVacMove
end
end
