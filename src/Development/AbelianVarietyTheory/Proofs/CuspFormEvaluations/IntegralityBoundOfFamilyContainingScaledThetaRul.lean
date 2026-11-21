import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DeterminantBlockProductRenameTorusPolynomial
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SumLeFinsumOfSurjectsOntoFinsetStatement

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem exists_ortho_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : FD.Data E r), ∀ x ∈ X.dom, ∃ b ∈ FD.Bor X.Ψ r, FD.rmul x b ∈ X.dom ∧ X.IsOrtho (FD.rmul x b) ∧ (∀ τ i, ‖FD.dmin X.Gm (FD.rmul x b) τ i‖ = 1) ∧ (∀ th, I2.phiFD X th (FD.rmul x b) = I2.phiFD X th x) ∧ ∀ (la : FD.Wt X.Ψ r) (P : FD.Frame X.Ψ r → ℂ), X.IsSec la P → X.pnorm la P x = ‖P (FD.rmul x b)‖ := by
  intro E _ _ _ r X x hx
  have hb := FD.FrameDegreeData.bOf_mem X hx
  have ho := FD.FrameDegreeData.ortho_bOf X hx
  have hd : ∀ τ i, ‖FD.dmin X.Gm (FD.rmul x (FD.FrameDegreeData.bOf X x)) τ i‖ = 1 := by
    intro τ i
    unfold FD.dmin
    rw [ho τ, FD.FrameDegreeData.lminor_diagonal, norm_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [Complex.norm_real]
    rcases FD.FrameDegreeData.sgn_sq X.p0 (Fin.castLE (Nat.le_of_lt_succ i.isLt) j : Fin r) with h | h <;>
      rw [h] <;> simp
  have hl : X.la1 (FD.rmul x (FD.FrameDegreeData.bOf X x)) = X.la1 x := by
    unfold FD.Data.la1
    rw [ReciprocityTheory.ChartRestriction.G.AR.Inst.firstMinimumSq_rightBorel X hx hb]
  refine ⟨_, hb, FD.OrthogonalFrameDomain.rmul_mem_dom X hx hb, ho, hd, fun th => ?_, fun la P hP => ?_⟩
  · unfold I2.phiFD
    rw [hl]
  · rw [← FD.FrameDegreeData.pnorm_rmul X la P hP.2.1 x hx _ hb]
    unfold FD.Data.pnorm
    simp only [norm_div, hd, div_one, Real.one_rpow, Finset.prod_const_one, _root_.mul_one]

end GlobalTheory.AnVal
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinantBlockProduct_rename_torusPolynomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (K : Type) [Field K] (σ : K →+* ℂ) (P : MvPolynomial (LtN Dw n) K), IsBlockProd P → ∀ (dim : (E →+* ℂ) → ℕ) (rl : (E →+* ℂ) → (E →+* ℂ)) (hd : ∀ τ, Dw.mult τ ≤ dim (rl τ)), Function.Injective rl → P ≠ 0 ∧ P.IsHomogeneous P.totalDegree ∧ ∃ (nb : ℕ) (bs : Fin nb → I2.Block E n dim), I2.Disj bs ∧ I2.DF bs = P.totalDegree ∧ ∀ (t : ℂ) (F : (Fin n → I2.Vsp dim) → ℂ), Differentiable ℂ F → I2.polyDeriv (MvPolynomial.map σ P) (fun ℓ => t • I2.dir ((ℓ.2.2, ⟨rl ℓ.1, Fin.castLE (hd ℓ.1) ℓ.2.1⟩) : I2.Letter n dim)) F 0 = t ^ P.totalDegree * I2.polyDeriv (I2.P1 bs) I2.dir F 0 := by
  first | exact @GlobalTheory.BlockRen.blockProd_rename | exact GlobalTheory.BlockRen.blockProd_rename | (intros; apply GlobalTheory.BlockRen.blockProd_rename <;> assumption)
end

section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem neg_log_sqrt_le_of_jbound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : I2.PT E) (dg n : ℕ) (P : I2.Par X dg) (S tableLineDegreeFive cc : ℝ), (Real.pi⁻¹) ^ dg * P.Jbound n ≤ S → p14 E X.r n P.m ≤ tableLineDegreeFive → 8100 * Real.pi * n * (P.m : ℝ) ^ 4 * (I2.dstar (E := E) P.m : ℝ) ^ 4 * I2.RR (E := E) / P.q ≤ cc → -Real.log (Real.sqrt S) ≤ tableLineDegreeFive * dg + cc * P.ph := by
  intro E _ _ _ X dg n P S tableLineDegreeFive cc hS hP14 hcc
  have hf : 0 < I2.PT.f E := by
    have h1 := P.hfr
    rcases Nat.eq_zero_or_pos (I2.PT.f E) with h | h
    · rw [h] at h1; simp at h1
    · exact h
  have hdp : 0 < I2.dstar (E := E) P.m := Nat.mul_pos (Nat.mul_pos two_pos hf) P.hm1
  have hd0 : (1 : ℝ) ≤ (I2.dstar (E := E) P.m : ℝ) := by exact_mod_cast hdp
  have hd : (0 : ℝ) < 2 * (I2.dstar (E := E) P.m : ℝ) := by linarith
  have hB := Real.rpow_pos_of_pos hd ((I2.dstar (E := E) P.m : ℝ) / 2)
  have h6 : (0 : ℝ) < 6 * (2 * (I2.dstar (E := E) P.m : ℝ)) ^ ((I2.dstar (E := E) P.m : ℝ) / 2) :=
    mul_pos (by norm_num) hB
  have hph : 0 ≤ P.ph := by
    unfold I2.Par.ph I2.PT.ph
    split_ifs <;> positivity
  have hA : (4 : ℝ)⁻¹ ^ n ≠ 0 := by positivity
  have hBn : (6 * (2 * (I2.dstar (E := E) P.m : ℝ)) ^ ((I2.dstar (E := E) P.m : ℝ) / 2))⁻¹ ^ n ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero h6.ne')
  have hC : (2 : ℝ)⁻¹ ^ ((X.r + 2) * dg) ≠ 0 := by positivity
  have hJpos : 0 < P.Jbound n := by
    unfold I2.Par.Jbound
    exact mul_pos (mul_pos (mul_pos (pow_pos (by norm_num) _) (pow_pos (inv_pos.2 h6) _))
      (pow_pos (by norm_num) _)) (Real.exp_pos _)
  have hJ : Real.log (P.Jbound n) = -(n * Real.log 4) -
      n * (Real.log 6 + (I2.dstar (E := E) P.m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) P.m : ℝ))) -
      (((X.r + 2) * dg : ℕ) : ℝ) * Real.log 2 -
      2 * (8100 * Real.pi * n * (P.m : ℝ) ^ 4 * (I2.dstar (E := E) P.m : ℝ) ^ 4 * I2.RR (E := E) / P.q * P.ph) := by
    unfold I2.Par.Jbound
    rw [Real.log_mul (mul_ne_zero (mul_ne_zero hA hBn) hC) (Real.exp_pos _).ne',
      Real.log_mul (mul_ne_zero hA hBn) hC, Real.log_mul hA hBn, Real.log_exp, Real.log_pow,
      Real.log_pow, Real.log_pow, Real.log_inv, Real.log_inv, Real.log_inv,
      Real.log_mul (by norm_num) hB.ne', Real.log_rpow hd]
    unfold I2.Cchi
    ring
  have hdg : (1 : ℝ) ≤ dg := by exact_mod_cast P.hDF
  have h24 : Real.log 24 = Real.log 4 + Real.log 6 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hl2d : 0 ≤ Real.log (2 * (I2.dstar (E := E) P.m : ℝ)) := Real.log_nonneg (by linarith)
  have hT : 0 ≤ Real.log 24 + (I2.dstar (E := E) P.m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) P.m : ℝ)) := by
    have : 0 < Real.log 24 := Real.log_pos (by norm_num)
    have : 0 ≤ (I2.dstar (E := E) P.m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) P.m : ℝ)) := by positivity
    linarith
  have hpi : (0 : ℝ) < (Real.pi⁻¹) ^ dg := pow_pos (inv_pos.2 Real.pi_pos) _
  have hpos : 0 < (Real.pi⁻¹) ^ dg * P.Jbound n := mul_pos hpi hJpos
  have hlS := Real.log_le_log hpos hS
  rw [Real.log_mul hpi.ne' hJpos.ne', Real.log_pow, Real.log_inv, hJ] at hlS
  rw [Real.log_sqrt (hpos.le.trans hS)]
  have e2 := mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hT) (sub_nonneg.2 hdg)
  have e3 := mul_le_mul_of_nonneg_right hcc hph
  have e4 := mul_le_mul_of_nonneg_right hP14 (by linarith : (0 : ℝ) ≤ dg)
  unfold p14 at e4
  push_cast at hlS
  rw [h24] at e2 e4
  linarith [e2, e3, e4]

end GlobalTheory.AnVal
end

section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem totalDegree_eq_sum_rows {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ harmA c a n) (h0 : P ≠ 0) (hh : P.IsHomogeneous P.totalDegree) :
    P.totalDegree = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i) := by
  classical
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.2 h0
  have hr := hP.1.2.2 m hm
  have h1 := hh (MvPolynomial.mem_support_iff.1 hm)
  have h2 : m.degree = P.totalDegree := by rw [Finsupp.degree_eq_weight_one]; exact h1
  rw [← h2, Finsupp.degree_eq_sum]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => hr τ i

theorem lieFac_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (x : ℝ) (hx : 0 < x)
    (a : (E →+* ℂ) × ℕ → ℕ) (d : ℕ) (hd : d = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)) :
    lieFac Dw x a ^ 2 = ((2 * Real.pi * x)⁻¹) ^ d := by
  have hp : 0 < 2 * Real.pi * x := by positivity
  have hd' : (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) = d := by rw [hd]; push_cast; rfl
  unfold lieFac
  rw [hd', ← Real.exp_nat_mul, ← Real.exp_log (inv_pos.2 hp), ← Real.exp_nat_mul, Real.log_inv]
  congr 1
  push_cast
  ring

theorem i2iAt_of_containsTh : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (xR : ℝ) (nab : NabV Xo c), IsNab Xo c nab → (∀ σ, GoodEmb c σ → IsUnf (U σ) ∧ (∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un k x)) ∧ ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xR) → ∀ α : 𝓞 E, α * H.bar α = (l.M : 𝓞 E) → l.Mb = Ideal.span {H.bar α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P₁ : MvPolynomial (LtN Dw n) c.F), Dom a n → P₁ ∈ harmA c a n → IsBlockProd P₁ → ∀ s : c.F, (∀ σ : c.F →+* ℂ, (l.M : ℝ) ^ P₁.totalDegree ≤ ‖σ s‖ ^ 2) → ∀ (N : ℕ) (wR : Fin (N + 1) → Rul Xo c), (∀ i, wR i ∈ sec Xo c a n) → ContainsTh Xo c nab s P₁ wR → ∀ (R0 : ℝ) (m : ℕ), RunOK E r P₁.totalDegree l.M R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∀ tableLineDegreeFive cc : ℝ, p14 E r n m ≤ tableLineDegreeFive → 8100 * Real.pi * n * (m : ℝ) ^ 4 * (I2.dstar (E := E) m : ℝ) ^ 4 * I2.RR (E := E) / l.M ≤ cc → I2AtFramePoints U xR wR (a, n) (I2.th (E := E) l.M R0) tableLineDegreeFive P₁.totalDegree cc := by
  intro hCI E _ _ _ H Dw l Xo c _ r U xR nab hnab hU α hα hMb a n P₁ hdom hP hbp s hs N wR hw hct R0 m hrun hm
    tableLineDegreeFive cc hP14 hcc σ hσ k x hx
  classical
  obtain ⟨hUn, hFT, hxi⟩ := hU σ hσ
  obtain ⟨b, -, hbd, hbo, -, hphi, hpn⟩ := exists_ortho_frame E r ((U σ).X k) x hx
  obtain ⟨T, Pr, hTr, hq, hPm, hph, hbound⟩ := GlobalTheory.T.unfoldedThetaRule_archimedeanValue_bound hCI E H Dw l Xo c σ r (U σ) k ⟨_, hbd⟩ xR nab hnab hσ hUn
    (hFT k _) hbo (hxi k) α hα hMb a n P₁ hP hbp R0 m hrun hm
  obtain ⟨h0, hh, -⟩ := GlobalTheory.T.determinantBlockProduct_rename_torusPolynomial E H Dw n c.F σ P₁ hbp Dw.mult id (fun _ => le_rfl) Function.injective_id
  have hdeg := totalDegree_eq_sum_rows c a n P₁ hP h0 hh
  have hxR : 0 < xR := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← hxi k τ]
    exact norm_pos_iff.2 ((map_ne_zero τ).2 ((U σ).X k).ξ0_ne)
  have hM : (0 : ℝ) < l.M := by
    have := Pr.hq
    rw [hq] at this
    exact_mod_cast this
  obtain ⟨jb, hjb, hf⟩ := hct
  choose f hf1 hf2 using hf
  haveI : Finite (LevQ Dw l) := (GlobalTheory.card_levQ E H Dw l).1
  haveI : Fintype (Fin n → LevQ Dw l) := Fintype.ofFinite _
  have hb := hbound f hf1
  rw [finsum_eq_sum_of_fintype] at hb
  have hrec : ∀ j, recNrm (U σ) xR a n (wR j) k x =
      lieFac Dw xR a * ‖rdU (U σ) (wR j) k (FD.rmul x b)‖ := fun j => by
    unfold recNrm
    rw [hpn _ _ (hUn.2.2.2.2.1 a n hdom (wR j) (hw j) k)]
  have hval : ∀ q, rdU (U σ) (wR (jb q)) k (FD.rmul x b) =
      σ s * toC (evR Xo c (f q) ((U σ).un k ⟨_, hbd⟩)) := fun q => by
    have e : wR (jb q) = s • f q := by
      funext p y
      rw [hf2 q p y]
      exact (Algebra.smul_def s (f q p y)).symm
    rw [e, map_smulₛₗ]
    show σ s * rdU (U σ) (f q) k (FD.rmul x b) = _
    congr 1
    exact dif_pos hbd
  have hkey : (Real.pi⁻¹) ^ P₁.totalDegree * Pr.Jbound n ≤ ∑ j, recNrm (U σ) xR a n (wR j) k x ^ 2 := by
    have hl := lieFac_sq Dw xR hxR a _ hdeg
    have hL : (0 : ℝ) ≤ ((2 * Real.pi * xR)⁻¹) ^ P₁.totalDegree := by positivity
    calc (Real.pi⁻¹) ^ P₁.totalDegree * Pr.Jbound n
        = ((2 * Real.pi * xR)⁻¹) ^ P₁.totalDegree * ((l.M : ℝ) ^ P₁.totalDegree *
            ((2 * xR / l.M) ^ P₁.totalDegree * Pr.Jbound n)) := by
          rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← mul_pow, ← mul_pow]
          congr 2
          field_simp
      _ ≤ ((2 * Real.pi * xR)⁻¹) ^ P₁.totalDegree * ((l.M : ℝ) ^ P₁.totalDegree *
            ∑ q, ‖toC (evR Xo c (f q) ((U σ).un k ⟨_, hbd⟩))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (by positivity)) hL
      _ ≤ ((2 * Real.pi * xR)⁻¹) ^ P₁.totalDegree * (‖σ s‖ ^ 2 *
            ∑ q, ‖toC (evR Xo c (f q) ((U σ).un k ⟨_, hbd⟩))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hs σ)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)) hL
      _ = ∑ q, recNrm (U σ) xR a n (wR (jb q)) k x ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [hrec, hval, mul_pow, hl, norm_mul, mul_pow]
      _ = ∑ j ∈ Finset.univ.image jb, recNrm (U σ) xR a n (wR j) k x ^ 2 :=
          (Finset.sum_image (f := fun j => recNrm (U σ) xR a n (wR j) k x ^ 2) fun _ _ _ _ h => hjb h).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  have hfin := neg_log_sqrt_le_of_jbound E T P₁.totalDegree n Pr _ tableLineDegreeFive cc hkey (by rw [hTr, hPm]; exact hP14)
    (by rw [hPm, hq]; exact hcc)
  rw [hph] at hfin
  rw [← hphi]
  exact hfin

end GlobalTheory.AnVal
end
