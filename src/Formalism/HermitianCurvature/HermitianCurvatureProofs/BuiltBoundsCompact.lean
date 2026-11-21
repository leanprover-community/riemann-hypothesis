import Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfLeaves
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDiffForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramLocSetCApp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UniformDecayOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormsJointContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondDefectNonneg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LenEqLenI
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LoeZeroOfPsd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SizeAtMinusW
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopRatio
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DegreeTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGDegLift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbHeadTopOfMkTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkTop

section
namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

open Formalism.FourierDecayAlt NumberField MeasureTheory Filter Topology Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBD Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate

noncomputable section

theorem thr_plus3 (c0 Cc R X N A : ℝ) (hc : max (4 * c0) 0 ≤ Cc) (hR : 0 ≤ R) (hX : 1 ≤ X) (hN : 0 ≤ N)
    (hA : Cc * R * (N * X ^ 2 + X ^ 3) ≤ A) : c0 * R * ((N + 3) * X ^ 2 + X ^ 3) ≤ A := by
  have hX2 : X ^ 2 ≤ X ^ 3 := by nlinarith
  have hY : 0 ≤ N * X ^ 2 + X ^ 3 := by positivity
  have hle : (N + 3) * X ^ 2 + X ^ 3 ≤ 4 * (N * X ^ 2 + X ^ 3) := by nlinarith
  have hY' : 0 ≤ (N + 3) * X ^ 2 + X ^ 3 := by positivity
  have h0 : 0 ≤ Cc := le_trans (le_max_right _ _) hc
  have h4 : 4 * c0 ≤ Cc := le_trans (le_max_left _ _) hc
  refine le_trans ?_ hA
  rcases le_or_gt c0 0 with hc0 | hc0
  · have : c0 * R * ((N + 3) * X ^ 2 + X ^ 3) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc0 hR) hY'
    exact le_trans this (by positivity)
  · calc c0 * R * ((N + 3) * X ^ 2 + X ^ 3) ≤ c0 * R * (4 * (N * X ^ 2 + X ^ 3)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (4 * c0) * R * (N * X ^ 2 + X ^ 3) := by ring
      _ ≤ Cc * R * (N * X ^ 2 + X ^ 3) := by gcongr

theorem bound_absorb (K C M y a b : ℝ) (_hM : 0 ≤ M) (hy : 0 ≤ y) (_hb : 0 ≤ b) (hK : 0 ≤ K)
    (ha : a ≤ C * y) (hyM : y ≤ M * b) : K * a ≤ (K * |C| * M) * b := by
  have h1 : C * y ≤ |C| * (M * b) := le_trans (mul_le_mul_of_nonneg_right (le_abs_self C) hy)
    (mul_le_mul_of_nonneg_left hyM (abs_nonneg C))
  calc K * a ≤ K * (|C| * (M * b)) := mul_le_mul_of_nonneg_left (le_trans ha h1) hK
    _ = (K * |C| * M) * b := by ring

def DecayUnifOfPlace : Prop :=
  P5.ThmPActualCpt → KB.RadHead → KB.HeadTop → Formalism.FourierDecayAlt.P.PBO.DecayUnif → Formalism.FourierDecayAlt.P.PBASM.DecayUnif

theorem decayUnif_of_place (hP : P5.ThmPActualCpt) (hRH : KB.RadHead) (hHT : KB.HeadTop)
    (hD : Formalism.FourierDecayAlt.P.PBO.DecayUnif) : Formalism.FourierDecayAlt.P.PBASM.DecayUnif := by
  have hPS : PStdC := pStdC_of hP hRH hHT
  intro Cb
  obtain ⟨c0, hc0⟩ := hD hP Cb
  obtain ⟨c1, hc1⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  refine ⟨max (max (4 * c0) 0) c1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB v ε hε i hi1 hir a ha h h' hsz hsz'
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hj : j ≤ S.G.r := by omega
  simp only [Nat.add_sub_cancel] at hsz hsz'
  have hgpos := g_pos_of_built hB
  have hB' := hB
  obtain ⟨-, -, -, hcut, -, -, -, -, -, -, hGo, -, -, -, hA, hv⟩ := hB'
  obtain ⟨hl0, hInD, -, hCk, hCC⟩ := hv v
  have hCI : KB.CutInside S := Formalism.FourierDecayAlt.P.PBCut.cutInside_of_built hB
  obtain ⟨w, rfl⟩ := ha
  have hw : KB.CutWord (D.parOf S v) (S.l + 1) (w.1 v) := cutWord_of_adm S hGo hCI w v
  have hlen : (w.1 v).length ≤ S.Ntop := le_trans (Formalism.FourierDecayAlt.P.PBB.len_le_cnt S w v) w.2.2
  have hR : (0 : ℝ) ≤ ((S.G.r : ℝ) + 1) ^ 4 := by positivity
  have hX : (1 : ℝ) ≤ 2 * (S.G.r : ℝ) + S.G.k + 1 := by
    have : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ S.G.k := Nat.cast_nonneg _
    linarith
  have hNn : (0 : ℝ) ≤ S.Ntop := Nat.cast_nonneg _

  have hcpt : ∀ n, KB.CptCoef (p v).T.base (Formalism.FourierDecayAlt.P.PBASM.cutSeq S p f χ n v ε) := by
    intro n
    refine ((hc1 (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (f v) χ ε A₀ S.Ntop Formalism.FourierDecayAlt.P.PBASM.cutN
      (by rw [hl0]; exact hInD) hcut hε hCk hCC (le_trans ?_ hA) (fun n g => rfl)).1 n)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hR) (by positivity)
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · have hH : D.IsLocPt (stdS S h) j := (isLocPt_toStd_iff _ _ hgpos h 1 j).2 hloc.1
    have hH' : D.IsLocPt (stdS S h') j := (isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hloc.2
    have hroom : 10 * ((S.Ntop : ℝ) + 3 * (2 * (S.G.r : ℝ) + 1) + 1) ≤ S.cutHi v - S.cutLo v := by
      have hN : (S.Ntop : ℝ) = 20 * ((S.G.r : ℝ) + 1) := by
        unfold C.HidaSetting.Ntop C.Kst; push_cast; ring
      have h6 := (hGo v).1
      have hr : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
      have hN20 : (20 : ℝ) ≤ S.Ntop := by rw [hN]; linarith
      have hsq : (400 : ℝ) ≤ (S.Ntop : ℝ) ^ 2 := by nlinarith
      have hN3 : (400 : ℝ) * S.Ntop ≤ (S.Ntop : ℝ) ^ 3 := by
        calc (400 : ℝ) * S.Ntop ≤ (S.Ntop : ℝ) ^ 2 * S.Ntop := mul_le_mul_of_nonneg_right hsq hNn
          _ = (S.Ntop : ℝ) ^ 3 := by ring
      nlinarith
    obtain ⟨C, hC⟩ := hc0 (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (f v) χ ε A₀ S.Ntop
      Formalism.FourierDecayAlt.P.PBASM.cutN (S.cutLo v) (S.cutHi v) (by rw [hl0]; exact hInD) hcut hε hCk hCC
      (by
        have := thr_plus3 c0 (max (max (4 * c0) 0) c1) (((S.G.r : ℝ) + 1) ^ 4) (2 * (S.G.r : ℝ) + S.G.k + 1)
          S.Ntop A₀ (le_max_left _ _) hR hX hNn (by simpa [mul_assoc] using hA)
        push_cast
        linarith [this])
      (fun n g => rfl) (fun Y h1 h2 => by rw [hl0]; exact hCI v Y ⟨h1, h2⟩) (by push_cast; linarith [hroom])
      j hj (w.1 v) (by rw [hl0]; exact hw) hlen (stdS S h) (stdS S h') hH hH'
    set lam := lamS S j with hlam
    have hlam_pos : 0 < lam := lamS_pos S hgpos j
    set tw : ℝ := 2 * Real.pi / ((S.g : ℝ) * lam) with htw
    have htw_pos : 0 < tw := by rw [htw]; positivity
    have hsW : ∀ l : ℂ, ‖sW S j l‖ = tw * ‖l‖ := by
      intro l
      unfold sW
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg htw_pos.le, one_mul]
    set K1 : ℝ := |Kg S j h h'| with hK1
    set K2 : ℝ := abs (Kg S j h h' * |(lamS S j ^ 2)⁻¹|) with hK2
    refine ⟨K1 * |C| * (max 1 lam⁻¹) ^ 3 + K2 * |C| * (max 1 tw⁻¹) ^ 3, fun n => ⟨fun c hc => ?_, fun l => ?_⟩⟩
    · have hb : 0 ≤ ((1 + ‖c‖) ^ 3)⁻¹ := by positivity
      have hlc : (lam : ℂ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast hlam_pos.ne') hc
      have hb1 := (hC n).1 _ hlc
      rw [gramLoc_setC_app hB _ v ε j hj (w.1 v) h h' hsz hsz' c hc, mul_assoc, norm_mul, Complex.norm_real,
        Real.norm_eq_abs]
      have hnl : ‖(lam : ℂ) * c‖ = lam * ‖c‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam_pos.le]
      rw [hnl] at hb1
      have := bound_absorb K1 C ((max 1 lam⁻¹) ^ 3) (((1 + lam * ‖c‖) ^ 3)⁻¹) _ _ (by positivity) (by positivity)
        hb (abs_nonneg _) hb1 (decay_scale lam ‖c‖ hlam_pos (norm_nonneg _))
      have h2 : 0 ≤ K2 * |C| * (max 1 tw⁻¹) ^ 3 * ((1 + ‖c‖) ^ 3)⁻¹ := by positivity
      calc K1 * _ ≤ (K1 * |C| * (max 1 lam⁻¹) ^ 3) * ((1 + ‖c‖) ^ 3)⁻¹ := this
        _ ≤ _ := by nlinarith
    · have hb : 0 ≤ ((1 + ‖l‖) ^ 3)⁻¹ := by positivity
      have hb1 := (hC n).2 (sW S j l)
      rw [hsW l] at hb1
      rw [int_gramLoc_setC hPS hB _ v ε (hcpt n) j hj (w.1 v) hw l h h' hloc.1 hloc.2, norm_mul,
        Complex.norm_real, Real.norm_eq_abs]
      have := bound_absorb K2 C ((max 1 tw⁻¹) ^ 3) (((1 + tw * ‖l‖) ^ 3)⁻¹) _ _ (by positivity) (by positivity)
        hb (abs_nonneg _) hb1 (decay_scale tw ‖l‖ htw_pos (norm_nonneg _))
      have h2 : 0 ≤ K1 * |C| * (max 1 lam⁻¹) ^ 3 * ((1 + ‖l‖) ^ 3)⁻¹ := by positivity
      calc K2 * _ ≤ (K2 * |C| * (max 1 tw⁻¹) ^ 3) * ((1 + ‖l‖) ^ 3)⁻¹ := this
        _ ≤ _ := by nlinarith
  · have hz : ∀ (n : ℕ) (c : ℂ), (setC S p (Formalism.FourierDecayAlt.P.PBASM.cutSeq S p f χ n)).gramLoc v ε (j + 1) (w.1 v)
        (h ++ [(1, c)]) (h' ++ [(1, c)]) = 0 := by
      intro n c
      rw [gramLoc_setC hB, rr_zero_of_not, mul_zero]
      unfold stdS
      rw [isLocPt_toStd_iff _ _ hgpos, isLocPt_toStd_iff _ _ hgpos]
      rintro ⟨h1, h2⟩
      exact hloc ⟨⟨fun b hb => h1.1 b (List.mem_append_left _ hb), hsz⟩,
        ⟨fun b hb => h2.1 b (List.mem_append_left _ hb), hsz'⟩⟩
    refine ⟨0, fun n => ⟨fun c _ => ?_, fun l => ?_⟩⟩
    · rw [hz n c]; simp
    · simp [hz n]

end

end Formalism.FourierDecayAlt.P.StandardPairingDecay

theorem Formalism.FourierDecayAlt.P.uniform_decay_of_place : Formalism.FourierDecayAlt.P.StandardPairingDecay.DecayUnifOfPlace :=
  fun hP hRH hHT hD => Formalism.FourierDecayAlt.P.StandardPairingDecay.decayUnif_of_place hP hRH hHT hD
end

section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section wts

variable {P : M.Par} (l0 : ℕ) (a : List C.Letter) (e : Wd.Ix (Fin a.length)) (ρ : M.Ty P) (Pv : ℝ → ℝ) (C : ℝ)

def RHyp : List ℝ → Prop
  | [] => True
  | y :: ys => (0 < (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re ∧
      (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).im = 0 ∧
      |Pv y| ≤ C * (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re) ∧ RHyp ys

theorem prodR_props (hC : 0 ≤ C) : ∀ ys : List ℝ, RHyp l0 a e ρ Pv C ys →
    (topRprod l0 a e ρ ys).im = 0 ∧ 0 < (topRprod l0 a e ρ ys).re ∧
      (ys.map fun y => |Pv y|).prod ≤ C ^ ys.length * (topRprod l0 a e ρ ys).re
  | [], _ => by simp [topRprod]
  | y :: ys, ⟨⟨h1, h2, h3⟩, hr⟩ => by
    obtain ⟨i1, i2, i3⟩ := prodR_props hC ys hr
    simp only [topRprod, Complex.mul_im, Complex.mul_re, List.map_cons, List.prod_cons, List.length_cons]
    refine ⟨by rw [i1, h2]; ring, by rw [i1, h2]; simp only [mul_zero, zero_mul, sub_zero]; positivity, ?_⟩
    rw [i1, h2]
    simp only [mul_zero, sub_zero]
    have hp : 0 ≤ (ys.map fun y => |Pv y|).prod := List.prod_nonneg fun x hx => by
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _
    calc |Pv y| * (ys.map fun y => |Pv y|).prod ≤ (C * (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re) *
          (C ^ ys.length * (topRprod l0 a e ρ ys).re) := mul_le_mul h3 i3 hp (by positivity)
      _ = C ^ (ys.length + 1) * ((topRprod l0 a e ρ ys).re * (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re) := by
          ring

end wts

section wts2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem second_defect_plus_word_le (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f)
    (a : List C.Letter) (e : Wd.Ix (Fin a.length)) (ρ : M.Ty (D.parOf S v)) (C : ℝ) (hC : 0 ≤ C) (ys : List ℝ)
    (hR : RHyp (p v).l0 a e ρ (S.P v) C ys) :
    del2 S p v a e ρ * (ys.map fun y => |S.P v y|).prod ≤
      C ^ ys.length * del2 S p v (KB.plusW ys a) (KB.firstSt ys e) ρ := by
  obtain ⟨i1, i2, i3⟩ := prodR_props (p v).l0 a e ρ (S.P v) C hC ys hR
  have hd : del2 S p v (KB.plusW ys a) (KB.firstSt ys e) ρ = del2 S p v a e ρ * (topRprod (p v).l0 a e ρ ys).re := by
    unfold del2
    rw [cW_plusW, Complex.mul_re, i1, mul_zero, sub_zero, Real.sqrt_mul' _ i2.le]
    rw [show √(Top.cW (D.parOf S v) (p v).l0 a e ρ).re * √(topRprod (p v).l0 a e ρ ys).re *
        (√(Top.cW (D.parOf S v) (p v).l0 a e ρ).re * √(topRprod (p v).l0 a e ρ ys).re) =
        √(Top.cW (D.parOf S v) (p v).l0 a e ρ).re * √(Top.cW (D.parOf S v) (p v).l0 a e ρ).re *
          (√(topRprod (p v).l0 a e ρ ys).re * √(topRprod (p v).l0 a e ρ ys).re) by ring,
      Real.mul_self_sqrt i2.le]
  rw [hd]
  have h0 := second_defect_nonneg S p v a e ρ
  calc del2 S p v a e ρ * (ys.map fun y => |S.P v y|).prod ≤
        del2 S p v a e ρ * (C ^ ys.length * (topRprod (p v).l0 a e ρ ys).re) := mul_le_mul_of_nonneg_left i3 h0
    _ = _ := by ring

end wts2

end

end Formalism.FourierDecayAlt.P.PBL
end

section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section helpers

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem mix_pushT (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (i : ℕ) {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ)
    (mk : List ℝ → List C.Letter) (P Q : C.LPt) :
    KB.mix S v ε i (PBD.pushU grid mk) (PBD.pushTh grid mk) P Q =
      ∑ n : Fin K → Fin (d + 1), ((F7.thGrid grid n : ℝ) : ℂ) * KB.gN S v ε i (mk (List.ofFn fun b => grid b (n b))) P Q := by
  unfold KB.mix PBD.pushTh
  simp only [Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hmem : mk (List.ofFn fun b => grid b (n b)) ∈ PBD.pushU grid mk :=
    Finset.mem_image_of_mem _ (Finset.mem_univ n)
  simp only [apply_ite, Complex.ofReal_zero, zero_mul, ite_mul]
  rw [Finset.sum_ite_eq, if_pos hmem]

end helpers

section lists

theorem ofFn_split {K : ℕ} (f : Fin K → ℝ) (ys₁ : List ℝ) (y : ℝ) (ys₂ : List ℝ)
    (h : List.ofFn f = ys₁ ++ y :: ys₂) :
    ∃ b₀ : Fin K, b₀.val = ys₁.length ∧ y = f b₀ ∧ ys₁.length + 1 + ys₂.length = K ∧
      ∀ y' ∈ ys₂, ∃ b' : Fin K, b₀ < b' ∧ y' = f b' := by
  have hlen : K = ys₁.length + 1 + ys₂.length := by
    have := congrArg List.length h
    simp only [List.length_ofFn, List.length_append, List.length_cons] at this
    omega
  have hb : ys₁.length < K := by omega
  refine ⟨⟨ys₁.length, hb⟩, rfl, ?_, hlen.symm, ?_⟩
  · have h1 : (List.ofFn f)[ys₁.length]'(by simp; omega) = (ys₁ ++ y :: ys₂)[ys₁.length]'(by simp) := by
      simp only [h]
    rw [List.getElem_ofFn, List.getElem_append_right (by omega)] at h1
    simp only [Nat.sub_self, List.getElem_cons_zero] at h1
    exact h1.symm
  · intro y' hy'
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy'
    refine ⟨⟨ys₁.length + (i + 1), by omega⟩, by simp only [Fin.lt_def]; omega, ?_⟩
    have h1 : (List.ofFn f)[ys₁.length + (i + 1)]'(by simp; omega) =
        (ys₁ ++ y :: ys₂)[ys₁.length + (i + 1)]'(by simp; omega) := by simp only [h]
    rw [List.getElem_ofFn] at h1
    simp only [List.getElem_append, Nat.add_sub_cancel_left, List.getElem_cons_succ,
      show ¬ (ys₁.length + (i + 1) < ys₁.length) by omega, dite_false] at h1
    exact h1.symm

theorem rhyp_of {P : M.Par} (l0 : ℕ) (a : List C.Letter) (e : Wd.Ix (Fin a.length)) (ρ : M.Ty P) (Pv : ℝ → ℝ)
    (C : ℝ) : ∀ ys : List ℝ, (∀ ys₁ y ys₂, ys = ys₁ ++ y :: ys₂ →
      0 < (topR l0 (KB.plusW ys₂ a) (KB.firstSt ys₂ e) ρ y).re ∧
      (topR l0 (KB.plusW ys₂ a) (KB.firstSt ys₂ e) ρ y).im = 0 ∧
      |Pv y| ≤ C * (topR l0 (KB.plusW ys₂ a) (KB.firstSt ys₂ e) ρ y).re) → RHyp l0 a e ρ Pv C ys
  | [], _ => trivial
  | y :: ys, H => ⟨H [] y ys rfl, rhyp_of l0 a e ρ Pv C ys fun ys₁ y' ys₂ h => H (y :: ys₁) y' ys₂ (by rw [h]; rfl)⟩

end lists

end

end Formalism.FourierDecayAlt.P.PBL
end

section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Finset
open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

open Classical

section abstract

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {α : Type}

theorem psd_wsum {ι : Type} [Fintype ι] (Y : Finset α) (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (V : ι → α → H) :
    TB.PSDOn Y (fun P Q => ∑ i, (d i : ℂ) * gramH (V i) P Q) := by
  have h := loe_sum (Finset.univ : Finset ι) (Y := Y) (A := fun _ _ _ => (0 : ℂ))
    (B := fun i P Q => (d i : ℂ) * gramH (V i) P Q) fun i _ => by
      have := loe_smul (d i) (hd i) (loe_zero_of_psd (psd_gramH Y (V i)))
      refine loe_congr (fun x _ y _ => by ring) (fun x _ y _ => rfl) this
  exact psd_of_loe_zero (loe_congr (fun x _ y _ => by simp) (fun x _ y _ => rfl) h)

theorem loe_sub_states {ι ι' : Type} [Fintype ι] [Fintype ι'] (Y : Finset α) (g : ι → ι') (hg : Function.Injective g)
    (K : ι' → α → α → ℂ) (hK : ∀ j, TB.PSDOn Y (K j)) :
    Loe Y (fun x y => ∑ i, K (g i) x y) (fun x y => ∑ j, K j x y) := by
  have e : ∀ x y, ∑ j, K j x y = ∑ j ∈ Finset.univ.image g, K j x y +
      ∑ j ∈ Finset.univ \ Finset.univ.image g, K j x y := by
    intro x y
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  have e2 : ∀ x y, ∑ j ∈ Finset.univ.image g, K j x y = ∑ i, K (g i) x y := by
    intro x y
    rw [Finset.sum_image fun i _ i' _ h => hg h]
  have h1 := loe_sum (Finset.univ \ Finset.univ.image g) (Y := Y) (A := fun _ _ _ => (0 : ℂ)) (B := K)
    fun j _ => loe_zero_of_psd (hK j)
  have h2 := loe_add (loe_refl Y (fun x y => ∑ i, K (g i) x y)) h1
  refine loe_congr (fun x _ y _ => by simp) (fun x _ y _ => ?_) h2
  rw [e, e2]

theorem top_kernel {Ea R N : Type} {Ew : N → Type} [Fintype Ea] [∀ n, Fintype (Ew n)] [Fintype R] [Fintype N]
    (Y : Finset α) (g : ∀ n, Ea → Ew n) (hg : ∀ n, Function.Injective (g n)) (Va : Ea → R → α → H)
    (Vn : ∀ n, Ew n → R → α → H) (da : Ea → R → ℝ) (dn : ∀ n, Ew n → R → ℝ) (hda : ∀ e ρ, 0 ≤ da e ρ)
    (hdn : ∀ n e ρ, 0 ≤ dn n e ρ)
    (lam : N → ℝ) (Pn : N → ℝ) (hPn : ∀ n, 0 < Pn n) (c : ℂ) (C0 : ℝ) (K : ℕ) (hC0 : 0 ≤ C0)
    (hdeg : ∀ P ∈ Y, ∀ e ρ, Va e ρ P = c • ∑ n, (lam n : ℂ) • Vn n (g n e) ρ P)
    (hwt : ∀ n e ρ, da e ρ * Pn n ≤ C0 ^ K * dn n (g n e) ρ) :
    Loe Y (fun P Q => ∑ e, ∑ ρ, (da e ρ : ℂ) * gramH (Va e ρ) P Q)
      (fun P Q => ((‖c‖ ^ 2 * (∑ n, |lam n|) * C0 ^ K : ℝ) : ℂ) *
        ∑ n, ((|lam n| / Pn n : ℝ) : ℂ) * ∑ e', ∑ ρ, (dn n e' ρ : ℂ) * gramH (Vn n e' ρ) P Q) := by
  set Λ : ℝ := ∑ n, |lam n| with hΛ

  have s1 : ∀ e ρ, Loe Y (fun P Q => (da e ρ : ℂ) * gramH (Va e ρ) P Q)
      (fun P Q => (da e ρ : ℂ) * ((‖c‖ ^ 2 : ℝ) : ℂ) * (((∑ n, ‖(lam n : ℂ)‖ : ℝ) : ℂ) *
        ∑ n, ((‖(lam n : ℂ)‖ : ℝ) : ℂ) * gramH (Vn n (g n e) ρ) P Q)) := by
    intro e ρ
    have hc := loe_convex Y (fun n => (lam n : ℂ)) (fun n P => Vn n (g n e) ρ P)
    have hc2 := loe_smul (da e ρ * ‖c‖ ^ 2) (mul_nonneg (hda e ρ) (sq_nonneg _)) hc
    refine loe_congr (fun P hP Q hQ => ?_) (fun P _ Q _ => by push_cast; ring) hc2
    have : gramH (Va e ρ) P Q = gramH (fun P => c • ∑ n, (lam n : ℂ) • Vn n (g n e) ρ P) P Q := by
      unfold gramH; rw [hdeg P hP e ρ, hdeg Q hQ e ρ]
    rw [this, gramH_smul]
    push_cast; ring
  have hnorm : ∀ n, ‖(lam n : ℂ)‖ = |lam n| := fun n => by rw [Complex.norm_real, Real.norm_eq_abs]
  simp only [hnorm] at s1

  have s2 : ∀ e ρ n, Loe Y (fun P Q => (da e ρ : ℂ) * gramH (Vn n (g n e) ρ) P Q)
      (fun P Q => ((C0 ^ K / Pn n : ℝ) : ℂ) * ((dn n (g n e) ρ : ℂ) * gramH (Vn n (g n e) ρ) P Q)) := by
    intro e ρ n
    have h := loe_scale (psd_gramH Y (Vn n (g n e) ρ)) (r := da e ρ) (r' := C0 ^ K / Pn n * dn n (g n e) ρ) (by
      have := hwt n e ρ
      rw [sub_nonneg, div_mul_eq_mul_div, le_div_iff₀ (hPn n)]
      linarith)
    refine loe_congr (fun _ _ _ _ => rfl) (fun P _ Q _ => by push_cast; ring) h

  have s3 : ∀ n, Loe Y (fun P Q => ∑ e, ∑ ρ, (dn n (g n e) ρ : ℂ) * gramH (Vn n (g n e) ρ) P Q)
      (fun P Q => ∑ e', ∑ ρ, (dn n e' ρ : ℂ) * gramH (Vn n e' ρ) P Q) :=
    fun n => loe_sub_states Y (g n) (hg n) (fun e' P Q => ∑ ρ, (dn n e' ρ : ℂ) * gramH (Vn n e' ρ) P Q)
      fun e' => psd_wsum Y (fun ρ => dn n e' ρ) (fun ρ => hdn n e' ρ) (fun ρ => Vn n e' ρ)

  have c1 := loe_sum (Finset.univ : Finset Ea) fun e _ => loe_sum (Finset.univ : Finset R) fun ρ _ => s1 e ρ
  refine loe_trans c1 ?_

  have c2 : ∀ e ρ, Loe Y (fun P Q => (da e ρ : ℂ) * ((‖c‖ ^ 2 : ℝ) : ℂ) * ((Λ : ℂ) *
        ∑ n, ((|lam n| : ℝ) : ℂ) * gramH (Vn n (g n e) ρ) P Q))
      (fun P Q => ((‖c‖ ^ 2 * Λ : ℝ) : ℂ) * ∑ n, ((|lam n| : ℝ) : ℂ) *
        (((C0 ^ K / Pn n : ℝ) : ℂ) * ((dn n (g n e) ρ : ℂ) * gramH (Vn n (g n e) ρ) P Q))) := by
    intro e ρ
    have h := loe_smul (‖c‖ ^ 2 * Λ) (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun n _ => abs_nonneg _))
      (loe_sum (Finset.univ : Finset N) fun n _ => loe_smul (|lam n|) (abs_nonneg _) (s2 e ρ n))
    refine loe_congr (fun P _ Q _ => ?_) (fun _ _ _ _ => rfl) h
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast; ring
  have c3 := loe_sum (Finset.univ : Finset Ea) fun e _ => loe_sum (Finset.univ : Finset R) fun ρ _ => c2 e ρ
  refine loe_trans (loe_congr (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) c3) ?_
  have c4 := loe_smul (‖c‖ ^ 2 * Λ) (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun n _ => abs_nonneg _))
    (loe_sum (Finset.univ : Finset N) fun n _ => loe_smul (|lam n| * (C0 ^ K / Pn n))
      (mul_nonneg (abs_nonneg _) (div_nonneg (pow_nonneg hC0 _) (hPn n).le)) (s3 n))
  refine loe_congr (fun P _ Q _ => ?_) (fun P _ Q _ => ?_) c4
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    refine Finset.sum_congr rfl fun ρ _ => ?_
    push_cast; ring
  · simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun ρ _ => ?_
    push_cast; ring

end abstract

end

end Formalism.FourierDecayAlt.P.PBL
end

section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section asm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem rhyp_nodes (hTR : TopRatio) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (hC : 28 * Real.exp 1 ≤ Cc) (v : Fin S.f) (a : List C.Letter)
    (ha : D.AdmAt S v a) {K d : ℕ} (haN : a.length + K ≤ S.Ntop) (grid : Fin K → Fin (d + 1) → ℝ)
    (hmem : ∀ (b : Fin K) j, grid b j ∈ S.grid v (a.length + K - (b : ℕ)))
    (n : Fin K → Fin (d + 1))
    (hcut : KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun b => grid b (n b)) a))
    (e : Wd.Ix (Fin a.length)) (ρ : M.Ty (D.parOf S v)) :
    RHyp (p v).l0 a e ρ (S.P v) (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) *
      (Real.sqrt (S.T * S.T'))⁻¹) (List.ofFn fun b => grid b (n b)) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -⟩ := hv v
  rw [hl0]
  refine rhyp_of _ a e ρ _ _ _ fun ys₁ y ys₂ hsplit => ?_
  obtain ⟨b₀, hb₀, rfl, hlen, hlater⟩ := ofFn_split (fun b => grid b (n b)) ys₁ y ys₂ hsplit

  have hc : KB.CutWord (D.parOf S v) (S.l + 1) ((true, grid b₀ (n b₀)) :: KB.plusW ys₂ a) := by
    rw [PBD.cutWord_iff] at hcut ⊢
    rw [PBF.plusW_eq, hsplit] at hcut
    have hsub : ((true, grid b₀ (n b₀)) :: KB.plusW ys₂ a).Sublist
        ((ys₁ ++ grid b₀ (n b₀) :: ys₂).map (fun y => (true, y)) ++ a) := by
      rw [PBF.plusW_eq, List.map_append, List.map_cons, List.append_assoc, List.cons_append]
      exact List.sublist_append_right _ _
    exact ⟨fun x hx => hcut.1 x (hsub.subset hx), hcut.2.sublist hsub⟩
  have hgr : ∃ m, grid b₀ (n b₀) ∈ S.grid v m := ⟨_, hmem b₀ (n b₀)⟩
  have hl : (KB.plusW ys₂ a).length < S.Ntop := by
    rw [PBF.plusW_eq, List.length_append, List.length_map]; omega
  have hfar : ∀ x ∈ KB.plusW ys₂ a, (S.Ntop : ℝ) ^ 2 + 1 ≤ |grid b₀ (n b₀) - x.2| ∧
      (x.1 = false → (S.Ntop : ℝ) ^ 2 + 1 ≤ |grid b₀ (n b₀) - (x.2 - 1)|) := by
    intro x hx
    rw [PBF.plusW_eq, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hx
      obtain ⟨b', hb', rfl⟩ := hlater y' hy'
      refine ⟨?_, fun h => absurd h (by simp)⟩
      have := PBD.sep_grid S hGo v (hmem b₀ (n b₀)) (hmem b' (n b')) (by
        have : (b₀ : ℕ) < b' := hb'
        have hb'K := b'.isLt
        omega) (e := 0) (e' := 0) (by simp) (by simp)
      simpa using this
    · have hy : (false = false ∧ ∃ a', a.length < a' ∧ a' ≤ S.Ntop ∧ grid b₀ (n b₀) ∈ S.grid v a') ∨
          (false = true ∧ grid b₀ (n b₀) ∈ S.grid1 v ∧ ∀ x ∈ a, PBD.Sep (true, grid b₀ (n b₀)) x) :=
        Or.inl ⟨rfl, a.length + K - (b₀ : ℕ), by have := b₀.isLt; omega, by omega, hmem b₀ (n b₀)⟩
      obtain ⟨h1, h2⟩ := node_far hB v a ha (grid b₀ (n b₀)) false hy x hx
      simp only [Bool.false_eq_true, if_false] at h1 h2
      unfold PBD.nodeOf at h1 h2
      by_cases hx1 : x.1 = true
      · rw [if_pos hx1] at h1
        exact ⟨h1, fun h => absurd h (by simp [hx1])⟩
      · rw [if_neg hx1] at h1 h2
        rw [sub_add_cancel] at h2
        exact ⟨h2, fun _ => h1⟩
  have := hTR Cb Cc E Wp Wq S p f χ A₀ hB hC v (KB.plusW ys₂ a) (grid b₀ (n b₀)) hc hgr hl hfar
    (KB.firstSt ys₂ e) ρ
  exact this

end asm

end

end Formalism.FourierDecayAlt.P.PBL
end

section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem firstSt_inj {w : List C.Letter} : ∀ ys : List ℝ, Function.Injective (KB.firstSt (w := w) ys)
  | [] => fun _ _ h => h
  | _ :: ys => fun e e' h => firstSt_inj ys (Fin.cons_right_injective (α := fun _ => Fin 2) (0 : Fin 2) h)

theorem lam_sum_eq {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) :
    ∑ n : Fin K → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| = ∏ b, ∑ i, |F7.lagCo (grid b) i| := by
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun n _ => Finset.abs_prod _ _

theorem lam_sum_pos {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (hinj : ∀ b, Function.Injective (grid b)) :
    0 < ∑ n : Fin K → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| := by
  rw [lam_sum_eq]
  refine Finset.prod_pos fun b _ => ?_
  exact lt_of_lt_of_le (abs_pos.2 (PBD.lagCo_ne_zero _ (hinj b) 0))
    (Finset.single_le_sum (f := fun i => |F7.lagCo (grid b) i|) (fun i _ => abs_nonneg _) (Finset.mem_univ 0))

theorem thGrid_eq {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (n : Fin K → Fin (d + 1)) :
    F7.thGrid grid n = |∏ b, F7.lagCo (grid b) (n b)| / ∑ m : Fin K → Fin (d + 1), |∏ b, F7.lagCo (grid b) (m b)| := by
  unfold F7.thGrid
  rw [Finset.prod_div_distrib, lam_sum_eq, Finset.abs_prod]

theorem lam_sum_le {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (B : ℝ)
    (hb : ∀ b, ∑ i, |F7.lagCo (grid b) i| ≤ B) :
    ∑ n : Fin K → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| ≤ B ^ K := by
  rw [lam_sum_eq]
  calc ∏ b, ∑ i, |F7.lagCo (grid b) i| ≤ ∏ _b : Fin K, B :=
        Finset.prod_le_prod (fun b _ => Finset.sum_nonneg fun i _ => abs_nonneg _) fun b _ => hb b
    _ = B ^ K := by simp

theorem zpow_sq_eq (x : ℝ) (hx : 0 < x) (ν : ℤ) : (x ^ ν) ^ 2 = x⁻¹ ^ (-(2 * ν)) := by
  rw [inv_zpow', neg_neg, ← zpow_natCast, ← zpow_mul, mul_comm]
  norm_num

section psd

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {α : Type}

theorem psd_dsum {Ea R : Type} [Fintype Ea] [Fintype R] (Y : Finset α) (d : Ea → R → ℝ) (hd : ∀ e ρ, 0 ≤ d e ρ)
    (V : Ea → R → α → H) : TB.PSDOn Y (fun P Q => ∑ e, ∑ ρ, (d e ρ : ℂ) * gramH (V e ρ) P Q) := by
  have h := loe_sum (Finset.univ : Finset Ea) (Y := Y) (A := fun _ _ _ => (0 : ℂ))
    (B := fun e P Q => ∑ ρ, (d e ρ : ℂ) * gramH (V e ρ) P Q) fun e _ => by
      have := loe_sum (Finset.univ : Finset R) (Y := Y) (A := fun _ _ _ => (0 : ℂ))
        (B := fun ρ P Q => (d e ρ : ℂ) * gramH (V e ρ) P Q) fun ρ _ => by
          have := loe_smul (d e ρ) (hd e ρ) (loe_zero_of_psd (psd_gramH Y (V e ρ)))
          exact loe_congr (fun x _ y _ => by ring) (fun x _ y _ => rfl) this
      exact loe_congr (fun x _ y _ => by simp) (fun x _ y _ => rfl) this
  exact psd_of_loe_zero (loe_congr (fun x _ y _ => by simp) (fun x _ y _ => rfl) h)

theorem psd_mixω {N : Type} [Fintype N] (Y : Finset α) (ω : α → ℝ) (θ κ : N → ℝ) (hθ : ∀ n, 0 ≤ θ n)
    (hκ : ∀ n, 0 ≤ κ n) (Kn : N → α → α → ℂ) (hK : ∀ n, TB.PSDOn Y (Kn n)) :
    TB.PSDOn Y (fun P Q => ∑ n, (θ n : ℂ) * ((ω P : ℂ) * (ω Q : ℂ) * ((κ n : ℂ) * Kn n P Q))) := by
  have h := loe_sum (Finset.univ : Finset N) (Y := Y) (A := fun _ _ _ => (0 : ℂ))
    (B := fun n P Q => (θ n : ℂ) * ((ω P : ℂ) * (ω Q : ℂ) * ((κ n : ℂ) * Kn n P Q))) fun n _ => by
      have h1 := loe_diag ω (loe_smul (θ n * κ n) (mul_nonneg (hθ n) (hκ n)) (loe_zero_of_psd (hK n)))
      exact loe_congr (fun x _ y _ => by simp) (fun x _ y _ => by push_cast; ring) h1
  exact psd_of_loe_zero (loe_congr (fun x _ y _ => by simp) (fun x _ y _ => rfl) h)

end psd

theorem mix_alg {N : Type} [Fintype N] (ω1 ω2 ka X L : ℝ) (lam Pn : N → ℝ) (Kn : N → ℂ) (hL : L ≠ 0)
    (hP : ∀ n, Pn n ≠ 0) :
    (ω1 : ℂ) * (ω2 : ℂ) * ((ka : ℂ) * ((X : ℂ) * ∑ n, ((|lam n| / Pn n : ℝ) : ℂ) * Kn n)) =
      ((X * L : ℝ) : ℂ) * ∑ n, ((|lam n| / L : ℝ) : ℂ) * ((ω1 : ℂ) * (ω2 : ℂ) * (((ka / Pn n : ℝ) : ℂ) * Kn n)) := by
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 := hP n
  push_cast
  field_simp

end

end Formalism.FourierDecayAlt.P.PBL
end

section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem topLocB : TopLocB := by
  intro hDT hVT hTR Cb Cc E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hC hB
  refine ⟨fun s hs2 hsr v => lamTop_thr hC hB s hs2 hsr v, fun F hF (v : Fin S.f) => ?_⟩
  have hB' := hB
  obtain ⟨hg1, hg2, -, -, -, -, -, -, -, -, hGo, hGr, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -⟩ := hv v
  have hCI := PBCut.cutInside_of_built hB
  intro s hs2 hsr a ha haN
  have hsr' : s ≤ S.G.r + 1 := hsr
  have ha' : D.AdmAt S v a := ha
  have haN' : a.length + C.Kst ≤ S.Ntop := haN
  set d := S.G.r + 1 - s with hd
  have hds : d + s = S.G.r + 1 := by omega
  have hd2 : d ≤ 2 * S.G.r := by omega
  obtain ⟨-, grid, hinj, hbnd, hmem, hwords, hprob, -⟩ :=
    Formalism.FourierDecayAlt.P.new_letters_admissible E Wp Wq S hGo hGr hCI v a C.Kst d ha' haN' hd2
  refine ⟨PBD.pushU grid (fun ys => KB.plusW ys a), PBD.pushTh grid (fun ys => KB.plusW ys a), hprob, ?_⟩
  intro ε hε t Y ht hY
  have hY' : ∀ P ∈ Y, D.ptSize P = d := fun P hP => by rw [hd]; exact hY P hP
  set Λ : ℝ := ∑ n : Fin C.Kst → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| with hΛ
  set C0 : ℝ := Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) * (Real.sqrt (S.T * S.T'))⁻¹
    with hC0
  set τ : ℂ := ((((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) : ℝ) : ℂ) *
    Complex.I ^ (s - 1) * t with hτ
  set c : ℂ := (((-1 : ℂ) ^ (s - 1) / τ) ^ C.Kst)⁻¹ with hc
  obtain ⟨hg, hk⟩ := glob_posT hB
  have hC0nn : 0 ≤ C0 := mul_nonneg (mul_nonneg (Real.exp_pos 1).le (supA_nonneg S hg hk v false))
    (inv_nonneg.2 (Real.sqrt_nonneg _))
  have hPn : ∀ n : Fin C.Kst → Fin (d + 1), 0 < ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod := by
    intro n
    refine List.prod_pos fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨b, rfl⟩ := List.mem_ofFn.1 hy
    exact abs_pos.2 ((hGo v).2.2.2.2.2 _ (Or.inl ⟨_, hmem b (n b)⟩)).2.2.1

  have hK1 := top_kernel (H := HV S v) (α := C.LPt) (Ea := Wd.Ix (Fin a.length)) (R := M.Ty (D.parOf S v))
    (N := Fin C.Kst → Fin (d + 1)) (Ew := fun n => Wd.Ix (Fin (KB.plusW (List.ofFn fun b => grid b (n b)) a).length))
    Y (fun n => KB.firstSt (List.ofFn fun b => grid b (n b))) (fun n => firstSt_inj _)
    (fun e ρ => vecT S p F v ε s t a e ρ)
    (fun n e' ρ => vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ)
    (fun e ρ => del2 S p v a e ρ) (fun n e' ρ => del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ)
    (fun e ρ => second_defect_nonneg S p v a e ρ) (fun n e' ρ => second_defect_nonneg S p v _ e' ρ)
    (fun n => ∏ b, F7.lagCo (grid b) (n b))
    (fun n => ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod) hPn c C0 C.Kst hC0nn
    (fun P hP e ρ => vecT_deg hDT hB F v ε (hF v ε hε) s hs2 t ht d hds a e ρ grid hinj
      (fun n => (hwords n).2.2.1) P (hY' P hP))
    (fun n e ρ => by
      have h := second_defect_plus_word_le S p v a e ρ C0 hC0nn (List.ofFn fun b => grid b (n b))
        (rhyp_nodes hTR hB hC v a ha' haN' grid hmem n (hwords n).2.2.1 e ρ)
      rwa [List.length_ofFn] at h)

  change Loe Y (fun P Q => KB.gN (setC S p F) v ε (S.G.r + 1) a (P ++ [(s, t)]) (Q ++ [(s, t)]))
    (fun P Q => (((‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) : ℝ) : ℂ) *
      KB.mix (setC S p F) v ε (S.G.r + 1) (PBD.pushU grid fun ys => KB.plusW ys a)
        (PBD.pushTh grid fun ys => KB.plusW ys a) (P ++ [(s, t)]) (Q ++ [(s, t)]))
  have hsz : ∀ P ∈ Y, D.ptSize P + s = S.G.r + 1 := fun P hP => by rw [hY' P hP]; omega
  have hgpos := g_pos_of_built hB
  have hrd := PBD.rd_pos' E
  have hΓ : 0 < ΓS S (S.G.r + 1) := PBD.gamLev_pos _ _ _ _ (by unfold D.kapG; positivity) (by unfold D.deG; positivity) _
  have hsa : 0 < S.sizeAt v a := sizeAt_pos S hGo v a ha'
  set ka : ℝ := 1 / (ΓS S (S.G.r + 1) * S.sizeAt v a) with hka
  have hka0 : 0 ≤ ka := by positivity
  have hΛpos : 0 < Λ := lam_sum_pos grid hinj

  have h1 := loe_diag (omT S s t) (loe_smul ka hka0 hK1)
  have h1' : Loe Y (fun P Q => KB.gN (setC S p F) v ε (S.G.r + 1) a (P ++ [(s, t)]) (Q ++ [(s, t)]))
      (fun P Q => (((‖c‖ ^ 2 * Λ * C0 ^ C.Kst) * Λ : ℝ) : ℂ) * ∑ n : Fin C.Kst → Fin (d + 1),
        ((|∏ b, F7.lagCo (grid b) (n b)| / Λ : ℝ) : ℂ) * ((omT S s t P : ℂ) * (omT S s t Q : ℂ) *
          (((ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod : ℝ) : ℂ) *
            ∑ e', ∑ ρ, (del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ : ℂ) *
              gramH (vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ) P Q))) := by
    refine loe_congr (fun P hP Q hQ => ?_) (fun P _ Q _ => ?_) h1
    · rw [gN_top hVT hB F v ε s hs2 t a P Q (hsz P hP) (hsz Q hQ)]
      ring
    · exact mix_alg _ _ _ _ _ _ _ _ hΛpos.ne' fun n => (hPn n).ne'

  have hmixY : ∀ P ∈ Y, ∀ Q ∈ Y, KB.mix (setC S p F) v ε (S.G.r + 1) (PBD.pushU grid fun ys => KB.plusW ys a)
      (PBD.pushTh grid fun ys => KB.plusW ys a) (P ++ [(s, t)]) (Q ++ [(s, t)]) =
      ∑ n : Fin C.Kst → Fin (d + 1),
        ((|∏ b, F7.lagCo (grid b) (n b)| / Λ : ℝ) : ℂ) * ((omT S s t P : ℂ) * (omT S s t Q : ℂ) *
          (((ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod : ℝ) : ℂ) *
            ∑ e', ∑ ρ, (del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ : ℂ) *
              gramH (vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ) P Q)) := by
    intro P hP Q hQ
    refine (mix_pushT (setC S p F) v ε (S.G.r + 1) grid (fun ys => KB.plusW ys a) _ _).trans ?_
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [thGrid_eq, ← hΛ, gN_top hVT hB F v ε s hs2 t _ P Q (hsz P hP) (hsz Q hQ), sizeAt_plusW]
    have hk : 1 / (ΓS S (S.G.r + 1) * (((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod *
        S.sizeAt v a)) = ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod := by
      rw [hka]; have := (hPn n).ne'; field_simp
    rw [hk]
    ring
  have hpsdY := psd_mixω Y (omT S s t) (fun n : Fin C.Kst → Fin (d + 1) => |∏ b, F7.lagCo (grid b) (n b)| / Λ)
    (fun n => ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod)
    (fun n => div_nonneg (abs_nonneg _) hΛpos.le) (fun n => div_nonneg hka0 (hPn n).le)
    (fun n P Q => ∑ e', ∑ ρ, (del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ : ℂ) *
      gramH (vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ) P Q)
    (fun n => psd_dsum Y _ (fun e' ρ => second_defect_nonneg S p v _ e' ρ) _)
  have hX : 0 ≤ (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) - ‖c‖ ^ 2 * Λ * C0 ^ C.Kst * Λ := by
    have hlv : 0 < ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) :=
      zpow_pos (by positivity) _
    set lv : ℝ := ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) with hlvdef
    have hτn : ‖τ‖ = lv * ‖t‖ := by
      rw [hτ, norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hlv.le]
    have hcn : ‖c‖ = ‖τ‖ ^ C.Kst := by
      rw [hc, norm_inv, norm_pow, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div, inv_pow, inv_inv]
    set B : ℝ := (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ d with hBdef
    have hΛB : Λ ≤ B ^ C.Kst := lam_sum_le grid B hbnd
    have hlenpos := lenI_posT hB (Fin.pos v)
    have hB0 : 0 ≤ B := by
      rw [hBdef, len_eq_lenI']; exact pow_nonneg (div_nonneg (by positivity) hlenpos.le) _

    have hA0 : 0 ≤ (2 * Real.pi / S.G.g) ^ (-(2 * S6.nuBlock S.G.r ((S.G.r + 2 - s : ℕ) : ℤ)
        ((S.G.r : ℤ) + 2 - ((S.G.r + 2 - s : ℕ) : ℤ)))) * Real.exp 1 *
        (28 * S.G.N / S.G.lenI) ^ (2 * (S.G.r + 2 - s - 1)) * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) *
        (√(S.T * S.T'))⁻¹ := by
      have : 0 ≤ S.G.N := by unfold Sz.Glob.N; positivity
      have := supA_nonneg S hg hk v false
      positivity
    have hlam2 : lamTop S (S.G.r + 2 - s) v ^ 2 = lv ^ 2 * B ^ 2 * C0 := by
      unfold lamTop
      rw [Real.sq_sqrt hA0]
      have e1 : ((S.G.r + 2 - s : ℕ) : ℤ) = ((1 + d : ℕ) : ℤ) := by rw [hd]; push_cast; omega
      have e2 : (S.G.r : ℤ) + 2 - ((S.G.r + 2 - s : ℕ) : ℤ) = (s : ℤ) := by push_cast; omega
      have e3 : (S.g : ℝ) = S.G.g := by unfold C.HidaSetting.g Sz.Glob.g; push_cast; ring
      have e4 : S.G.r + 2 - s - 1 = d := by omega
      rw [e2, e1, e4, hlvdef, zpow_sq_eq _ (by positivity), inv_div, e3, hBdef, ← pow_mul, ntop_eq_N'',
        len_eq_lenI', hC0, mul_comm d 2]
      ring
    have hfin : ‖c‖ ^ 2 * Λ * C0 ^ C.Kst * Λ ≤ (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) := by
      have e5 : (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) = (‖t‖ ^ 2 * (lv ^ 2 * B ^ 2 * C0)) ^ C.Kst := by
        rw [pow_mul, mul_pow (‖t‖) (lamTop S (S.G.r + 2 - s) v) 2, hlam2]
      rw [e5, hcn, hτn]
      have hΛ0 : 0 ≤ Λ := hΛpos.le
      have hsq : Λ * Λ ≤ B ^ C.Kst * B ^ C.Kst := mul_le_mul hΛB hΛB hΛ0 (pow_nonneg hB0 _)
      calc ((lv * ‖t‖) ^ C.Kst) ^ 2 * Λ * C0 ^ C.Kst * Λ = ((lv * ‖t‖) ^ C.Kst) ^ 2 * C0 ^ C.Kst * (Λ * Λ) := by ring
        _ ≤ ((lv * ‖t‖) ^ C.Kst) ^ 2 * C0 ^ C.Kst * (B ^ C.Kst * B ^ C.Kst) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = (‖t‖ ^ 2 * (lv ^ 2 * B ^ 2 * C0)) ^ C.Kst := by ring
    linarith
  have h3 := loe_scale hpsdY hX
  exact loe_trans h1' (loe_congr (fun _ _ _ _ => rfl) (fun P hP Q hQ => by rw [hmixY P hP Q hQ]) h3)

end

end Formalism.FourierDecayAlt.P.PBL

theorem Formalism.FourierDecayAlt.P.top_local_built_places : Formalism.FourierDecayAlt.P.PBL.TopLocB := Formalism.FourierDecayAlt.P.PBL.topLocB
end

section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField Finset

noncomputable section

open Classical

section real

theorem pratio (s : Finset ℕ) (lam : ℕ → ℝ) (α β y : ℝ) (hI : 3 ≤ β - α)
    (hroot : ∀ t ∈ s, -lam t < α ∨ β < -lam t) (hy1 : α + (β - α) / 3 ≤ y) (hy2 : y + 1 ≤ β - (β - α) / 3) :
    |∏ t ∈ s, (y + lam t)| ≤ (1 + 3 / (β - α)) ^ s.card * |∏ t ∈ s, (y + 1 + lam t)| := by
  rw [Finset.abs_prod, Finset.abs_prod, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun t _ => abs_nonneg _) fun t ht => ?_
  have hI0 : 0 < β - α := by linarith
  have h3 : 0 ≤ 3 / (β - α) := by positivity
  rcases hroot t ht with h | h
  · have a1 : 0 < y + lam t := by linarith
    rw [abs_of_pos a1, abs_of_pos (by linarith : 0 < y + 1 + lam t)]
    nlinarith
  · have a2 : y + 1 + lam t < 0 := by linarith
    have hd : (β - α) / 3 ≤ -(y + 1 + lam t) := by linarith
    rw [abs_of_neg (by linarith : y + lam t < 0), abs_of_neg a2]
    have : 1 ≤ 3 / (β - α) * -(y + 1 + lam t) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hI0]; linarith
    nlinarith

theorem long_bound (k r N Cc I : ℝ) (hk : 1 ≤ k) (hr : 0 ≤ r) (hN : 20 ≤ N) (hCc : 1 ≤ Cc)
    (h : Cc * (k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3) ≤ I) : 6 * (k + 2 * r + 1) ≤ I := by
  have hb : 0 ≤ k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3 := by positivity
  have h1 : k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3 ≤ I := by nlinarith
  have h2 : 6 * k ≤ k * N * (r + 1) ^ 2 := by
    have : 20 ≤ N * (r + 1) ^ 2 := by nlinarith
    nlinarith
  have h3 : 6 * (2 * r + 1) ≤ N ^ 2 * (r + 1) ^ 2 := by
    have : 400 ≤ N ^ 2 := by nlinarith
    nlinarith
  have h4 : 0 ≤ N ^ 3 := by positivity
  linarith

theorem three_le_len (N I : ℝ) (hN : 20 ≤ N) (h : 6 * N ^ 3 + 6 * N ≤ I) : 3 ≤ I := by
  have : 0 ≤ 6 * N ^ 3 := by positivity
  linarith

theorem two_N_bound (N : ℝ) (hN : 20 ≤ N) : 0 < N ^ 2 - 1 ∧ ((2 : ℕ) : ℝ) * (N / (N ^ 2 - 1)) ≤ 1 / 2 := by
  have hpos : 0 < N ^ 2 - 1 := by nlinarith
  refine ⟨hpos, ?_⟩
  rw [Nat.cast_ofNat, mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem final_cmp (Pa x0 F q TT sA E1 qw : ℝ) (hPa : 0 ≤ Pa) (hx0 : 0 < x0) (hF0 : 0 < F) (hq : 0 < q) (hTT : 0 < TT)
    (hsA : 0 ≤ sA) (hE1 : 0 < E1) (hE1sq : E1 ^ 2 = Real.exp 1) (hP2 : Pa ^ 2 ≤ E1 * (sA ^ 2 * q))
    (hx : x0 ^ 2 ≤ q / TT) (hF : F ^ 2 ≤ E1) (hqw : E1⁻¹ * q ≤ qw) :
    Pa ≤ Real.exp 1 * sA * (√TT)⁻¹ * (qw / (x0 * F)) := by
  have hsq : (√TT)⁻¹ ^ 2 = TT⁻¹ := by rw [inv_pow, Real.sq_sqrt hTT.le]
  have hsq0 : 0 < (√TT)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hTT)
  have hmain : Pa * (x0 * F) ≤ E1 * sA * (√TT)⁻¹ * q := by
    have hl0 : 0 ≤ Pa * (x0 * F) := mul_nonneg hPa (mul_pos hx0 hF0).le
    have hr0 : 0 ≤ E1 * sA * (√TT)⁻¹ * q := mul_nonneg (mul_nonneg (mul_nonneg hE1.le hsA) hsq0.le) hq.le
    rw [← pow_le_pow_iff_left₀ hl0 hr0 two_ne_zero]
    have eL : (Pa * (x0 * F)) ^ 2 = Pa ^ 2 * x0 ^ 2 * F ^ 2 := by ring
    have eR : (E1 * sA * (√TT)⁻¹ * q) ^ 2 = E1 * (sA ^ 2 * q) * (q / TT) * E1 := by
      rw [mul_pow, mul_pow, mul_pow, hsq]; field_simp
    rw [eL, eR]
    have hx2 : 0 ≤ x0 ^ 2 := sq_nonneg _
    have hF2 : 0 ≤ F ^ 2 := sq_nonneg _
    have hA : 0 ≤ E1 * (sA ^ 2 * q) := by positivity
    have hB : 0 ≤ q / TT := by positivity
    calc Pa ^ 2 * x0 ^ 2 * F ^ 2 ≤ E1 * (sA ^ 2 * q) * x0 ^ 2 * F ^ 2 := by gcongr
      _ ≤ E1 * (sA ^ 2 * q) * (q / TT) * F ^ 2 := by gcongr
      _ ≤ E1 * (sA ^ 2 * q) * (q / TT) * E1 := by gcongr
  have hC : Real.exp 1 * sA * (√TT)⁻¹ * (E1⁻¹ * q) = E1 * sA * (√TT)⁻¹ * q := by
    rw [← hE1sq]; field_simp
  have hfin : Pa * (x0 * F) ≤ Real.exp 1 * sA * (√TT)⁻¹ * qw := by
    rw [← hC] at hmain
    refine hmain.trans (mul_le_mul_of_nonneg_left hqw ?_)
    positivity
  rw [← mul_div_assoc, le_div_iff₀ (mul_pos hx0 hF0)]
  exact hfin

theorem one_add_pow_le_exp (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : (1 + x) ^ n ≤ Real.exp (n * x) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) n

end real

section xs

theorem xs_eq_prod {S : Type} [Fintype S] [DecidableEq S] (x0 : ℂ → ℂ) :
    ∀ (L : List (Wd.Letter ℂ S)) (e : Wd.Ix S) (Y : ℂ),
      Fr.xs x0 L e Y = x0 Y * (L.map fun l => if e l.intersection_update_fsHerm_neg_one = 0 then Fr.phiL l Y else 1).prod
  | [], _, _ => by simp [Fr.xs]
  | l :: L, e, Y => by
    simp only [Fr.xs, List.map_cons, List.prod_cons]
    rw [xs_eq_prod x0 L e Y]
    ring

theorem phiL_bound (b : Bool) (pt y D : ℝ) (hD : 2 ≤ D) (hd : D + 2 ≤ |y - pt|) :
    0 < (if b then (y + 1 - pt) / (y - pt) else (pt - y - 1) / (pt - y - 2)) ∧
      (if b then (y + 1 - pt) / (y - pt) else (pt - y - 1) / (pt - y - 2)) ≤ 1 + 1 / D := by
  have hD0 : 0 < D := by linarith
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rcases le_or_gt 0 (y - pt) with h | h
    · rw [abs_of_nonneg h] at hd
      have h1 : pt - y - 2 < 0 := by linarith
      have h2 : pt - y - 1 < 0 := by linarith
      constructor
      · exact div_pos_of_neg_of_neg h2 h1
      · rw [div_le_iff_of_neg h1]
        have : 0 < 1 / D := by positivity
        nlinarith
    · rw [abs_of_neg h] at hd
      have h1 : 0 < pt - y - 2 := by linarith
      constructor
      · exact div_pos (by linarith) h1
      · rw [div_le_iff₀ h1]
        have e1 : (1 + 1 / D) * (pt - y - 2) = pt - y - 2 + (pt - y - 2) / D := by ring
        rw [e1]
        have : 1 ≤ (pt - y - 2) / D := by rw [le_div_iff₀ hD0]; linarith
        linarith
  · simp only [if_true]
    rcases le_or_gt 0 (y - pt) with h | h
    · rw [abs_of_nonneg h] at hd
      have h1 : 0 < y - pt := by linarith
      constructor
      · exact div_pos (by linarith) h1
      · rw [div_le_iff₀ h1]
        have e1 : (1 + 1 / D) * (y - pt) = y - pt + (y - pt) / D := by ring
        rw [e1]
        have : 1 ≤ (y - pt) / D := by rw [le_div_iff₀ hD0]; linarith
        linarith
    · rw [abs_of_neg h] at hd
      have h2 : y + 1 - pt < 0 := by linarith
      constructor
      · exact div_pos_of_neg_of_neg h2 h
      · rw [div_le_iff_of_neg h]
        have : 0 < 1 / D := by positivity
        nlinarith

end xs

end

end Formalism.FourierDecayAlt.P.PBL
end

section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField Finset

noncomputable section

open Classical

theorem topRatio : TopRatio := by
  intro Cb Cc E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB hC v w y hcut hgr hlen hfar e ρ
  have hB' := hB
  obtain ⟨hg1, hg2, -, -, hOkp, hw, hw', hl1, hlk, hne, hGo, -, hLC, hCA, -, hv⟩ := hB'
  have hOK : (D.parOf S v).OK := (p v).hP.1
  have hN20 : (20 : ℝ) ≤ S.Ntop := PBD.ntop_ge S
  set N : ℝ := (S.Ntop : ℝ) with hNdef
  set α := S.cutLo v with hα
  set β := S.cutHi v with hβ

  have hycut : I.OnCut (D.parOf S v).u (D.parOf S v).u' (S.l + 1) y := PBF.cutWord_mem (D.parOf S v) hcut (List.mem_cons_self)
  obtain ⟨m, hm⟩ := hgr
  obtain ⟨hlenI, hpos, -, -, -, hlast⟩ := hGo v
  obtain ⟨hm1, hmN, hgl, hgu⟩ := hpos m y hm
  obtain ⟨hyI, hy1I, hPy, hPy1⟩ := hlast y (Or.inl ⟨m, hm⟩)
  have hI0 : 0 < β - α := by
    have : (0 : ℝ) < 6 * N ^ 3 + 6 * N := by positivity
    linarith
  have hmid1 : α + (β - α) / 3 ≤ y := by
    unfold C.gridL at hgl
    have : 0 ≤ (2 * (m : ℝ) - 2) * ((β - α) / (6 * S.Ntop)) := by
      have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      exact mul_nonneg (by linarith) (by positivity)
    linarith
  have hmid2 : y + 1 ≤ β - (β - α) / 3 := by
    unfold C.gridL at hgu
    have hmN' : (m : ℝ) ≤ S.Ntop := by exact_mod_cast hmN
    have hN0 : (0 : ℝ) < S.Ntop := by linarith
    have h6 : (2 * (m : ℝ) - 2) * ((β - α) / (6 * S.Ntop)) + (β - α) / (6 * S.Ntop) ≤ (β - α) / 3 := by
      have hX : 0 ≤ (β - α) / (6 * S.Ntop) := by positivity
      have e2 : (2 * (S.Ntop : ℝ)) * ((β - α) / (6 * S.Ntop)) = (β - α) / 3 := by field_simp; ring
      have := mul_le_mul_of_nonneg_right (show 2 * (m : ℝ) - 1 ≤ 2 * S.Ntop by linarith) hX
      nlinarith
    linarith

  have hyIcc : y ∈ Set.Icc α β := by rw [hα, hβ, ← cutI_eq]; exact hyI
  have hqy : 0 < (M.qC (D.parOf S v) (y : ℂ)).re := q_pos_cut hB v y hyIcc
  set q' : ℝ → ℝ := fun t => (M.qC (D.parOf S v) (t : ℂ)).re with hq'
  set wr : List (Wd.Letter ℝ (Fin w.length)) :=
    (D.positionted w).map fun l => (⟨l.plus, l.intersection_update_fsHerm_neg_one, l.pt.re⟩ : Wd.Letter ℝ (Fin w.length)) with hwr
  have hQ : Wd.qw (M.qC (D.parOf S v)) (D.positionted w) (y : ℂ) = ((Wd.qw q' wr y : ℝ) : ℂ) :=
    weighted_quadratic_of_real (Fin w.length) (M.qC (D.parOf S v)) (D.positionted w) y
      (by rw [PBF.qC_ofReal, Complex.ofReal_im])
      (by intro l hl; unfold D.positionted at hl; obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl; simp)
  have hLQ : Real.exp (-(1 / 2)) ≤ Wd.qw q' wr y / q' y := by
    have h4 : 4 ≤ S.Ntop := by exact_mod_cast (by linarith : (4 : ℝ) ≤ S.Ntop)
    have hlen' : wr.length ≤ S.Ntop := by simp [hwr, D.positionted]; omega
    refine (lemma_Q_estimate (Fin w.length) q' wr S.Ntop ((S.Ntop : ℝ) ^ 2 + 1) y h4 hlen' le_rfl ?_ hqy.ne').1
    intro l hl
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.1 hl
    unfold D.positionted at hl0
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl0
    have hz := hfar (w.get j) (List.get_mem _ _)
    simp only [Complex.ofReal_re]
    by_cases h1 : (w.get j).1 = true
    · rw [if_pos h1]; exact hz.1
    · rw [if_neg h1]; exact ⟨hz.1, hz.2 (by simpa using h1)⟩
  have hqw : 0 < Wd.qw q' wr y := by
    have := (le_div_iff₀ hqy).1 hLQ
    have : 0 < Real.exp (-(1 / 2)) * q' y := mul_pos (Real.exp_pos _) hqy
    linarith

  set rf : Fin w.length → ℝ := fun j => if e j = 0 then
      (if (w.get j).1 then (y + 1 - (w.get j).2) / (y - (w.get j).2)
        else ((w.get j).2 - y - 1) / ((w.get j).2 - y - 2)) else 1 with hrf
  have hxs : Fr.xs (fun Y => M.sgn (D.parOf S v) (S.l + 1) * M.xC (D.parOf S v) ρ Y) (D.positionted w) e ((y : ℂ) + 1) =
      (M.sgn (D.parOf S v) (S.l + 1) * M.xC (D.parOf S v) ρ ((y : ℂ) + 1)) * ((∏ j, rf j : ℝ) : ℂ) := by
    rw [xs_eq_prod]
    congr 1
    unfold D.positionted
    rw [List.map_ofFn, List.prod_ofFn]
    push_cast
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Function.comp_apply, hrf]
    by_cases he : e j = 0
    · simp only [he, if_true]
      unfold Fr.phiL
      by_cases hb : (w.get j).1 = true
      · simp only [hb, if_true]; push_cast; ring
      · simp only [hb, Bool.false_eq_true, if_false]; push_cast; ring
    · simp only [he, if_false, Complex.ofReal_one]
  set x0r : ℝ := (-1 : ℝ) ^ (S.G.k - (S.l + 1)) * I.xpoly S.G.k (M.rho (D.parOf S v) ρ) (y + 1) with hx0r
  have hx0 : M.sgn (D.parOf S v) (S.l + 1) * M.xC (D.parOf S v) ρ ((y : ℂ) + 1) = ((x0r : ℝ) : ℂ) := by
    simp only [hx0r, M.sgn, M.xC, I.xpoly, D.parOf]
    push_cast
    rfl
  have hinter := Formalism.FourierDecayAlt.P.types_interlace (D.parOf S v) hOK ρ
  have hx0pos : 0 < x0r := Formalism.FourierDecayAlt.P.interlacing_sign S.G.k (D.parOf S v).u (D.parOf S v).u' (M.rho (D.parOf S v) ρ) (S.l + 1) y (by omega)
    (by omega) hinter hycut 1 (by simp)
  have hD2 : (2 : ℝ) ≤ (S.Ntop : ℝ) ^ 2 - 1 := by nlinarith
  have hrf : ∀ j, 0 < rf j ∧ rf j ≤ 1 + 1 / ((S.Ntop : ℝ) ^ 2 - 1) := by
    intro j
    simp only [hrf]
    by_cases he : e j = 0
    · simp only [he, if_true]
      exact phiL_bound (w.get j).1 (w.get j).2 y _ hD2 (by linarith [(hfar (w.get j) (List.get_mem _ _)).1])
    · simp only [he, if_false]
      exact ⟨one_pos, by have : (0 : ℝ) ≤ 1 / ((S.Ntop : ℝ) ^ 2 - 1) := by positivity
                         linarith⟩
  have hF0 : 0 < ∏ j, rf j := Finset.prod_pos fun j _ => (hrf j).1
  have hF1 : ∏ j, rf j ≤ Real.exp ((S.Ntop : ℝ) / ((S.Ntop : ℝ) ^ 2 - 1)) := by
    calc ∏ j, rf j ≤ ∏ _j : Fin w.length, (1 + 1 / ((S.Ntop : ℝ) ^ 2 - 1)) :=
          Finset.prod_le_prod (fun j _ => (hrf j).1.le) fun j _ => (hrf j).2
      _ = (1 + 1 / ((S.Ntop : ℝ) ^ 2 - 1)) ^ w.length := by simp
      _ ≤ Real.exp (w.length * (1 / ((S.Ntop : ℝ) ^ 2 - 1))) := one_add_pow_le_exp _ (by positivity) _
      _ ≤ Real.exp ((S.Ntop : ℝ) / ((S.Ntop : ℝ) ^ 2 - 1)) := by
          apply Real.exp_le_exp.2
          rw [mul_one_div]
          apply div_le_div_of_nonneg_right _ (by linarith)
          exact_mod_cast hlen.le

  have hR : topR (S.l + 1) w e ρ y = ((Wd.qw q' wr y / (x0r * ∏ j, rf j) : ℝ) : ℂ) := by
    unfold topR
    rw [hQ, hxs, hx0]
    push_cast
    ring
  rw [hR, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨div_pos hqw (mul_pos hx0pos hF0), rfl, ?_⟩
  set C0 := Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) * (√(S.T * S.T'))⁻¹ with hC0
  set F := ∏ j, rf j with hFdef
  set Cf := S.G.place (S.pl v) with hCf
  have hT : 0 < S.T := hOK.T_pos
  have hT' : 0 < S.T' := hOK.T'_pos
  have hTT : 0 < S.T * S.T' := mul_pos hT hT'
  obtain ⟨hg, hk⟩ := glob_posT hB
  have hsA := supA_nonneg S hg hk v false

  have hIR := Formalism.FourierDecayAlt.P.interlacing_ratio S.G.k (D.parOf S v).u (D.parOf S v).u' (M.rho (D.parOf S v) ρ)
    (S.l + 1) y (by omega) (by omega) hinter hycut
  have hul : 1 ≤ |y + 1 / 2 + (D.parOf S v).u (S.l + 1)| * |y + 1 / 2 + (D.parOf S v).u' (S.l + 1)| := by
    rcases hycut with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_neg (by linarith), abs_of_pos (by linarith)]; nlinarith
    · rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]; nlinarith
  have hqprod : q' y = -(S.T * S.T') * ((∏ i ∈ Icc 1 S.G.k, (y + 1 / 2 + (D.parOf S v).u i)) *
      ∏ i ∈ Icc 1 S.G.k, (y + 1 / 2 + (D.parOf S v).u' i)) := by
    simp only [hq']
    rw [PBF.qC_ofReal, Complex.ofReal_re, ← Finset.prod_mul_distrib]
  have hx0sq : x0r ^ 2 ≤ q' y / (S.T * S.T') := by
    have e1 : x0r ^ 2 = I.xpoly S.G.k (M.rho (D.parOf S v) ρ) (y + 1) ^ 2 := by
      rw [hx0r, mul_pow, ← pow_mul, mul_comm (S.G.k - (S.l + 1)) 2, pow_mul, neg_one_sq, one_pow, one_mul]
    have hq := hqy
    change 0 < q' y at hq
    rw [hqprod] at hq
    rw [e1, le_div_iff₀ hTT, hqprod]
    generalize (∏ i ∈ Icc 1 S.G.k, (y + 1 / 2 + (D.parOf S v).u i)) = A at hq hIR ⊢
    generalize (∏ i ∈ Icc 1 S.G.k, (y + 1 / 2 + (D.parOf S v).u' i)) = B at hq hIR ⊢
    generalize I.xpoly S.G.k (M.rho (D.parOf S v) ρ) (y + 1) = X at hIR ⊢
    generalize |y + 1 / 2 + (D.parOf S v).u (S.l + 1)| * |y + 1 / 2 + (D.parOf S v).u' (S.l + 1)| = U at hIR hul
    have hAB : A * B < 0 := by
      by_contra h
      push_neg at h
      have h3 := mul_nonneg hTT.le h
      have h4 : -(S.T * S.T') * (A * B) = -(S.T * S.T' * (A * B)) := by ring
      linarith
    rw [abs_of_neg hAB] at hIR
    have hX2 : 0 ≤ X ^ 2 := sq_nonneg X
    have h1 : X ^ 2 ≤ -(A * B) :=
      calc X ^ 2 = X ^ 2 * 1 := (mul_one _).symm
        _ ≤ X ^ 2 * U := mul_le_mul_of_nonneg_left hul hX2
        _ ≤ -(A * B) := hIR
    have h5 := mul_le_mul_of_nonneg_left h1 hTT.le
    have h6 : -(S.T * S.T') * (A * B) = S.T * S.T' * -(A * B) := by ring
    rw [h6, mul_comm (X ^ 2)]
    exact h5

  have hroot : ∀ t ∈ Icc 1 (Cf.k + Cf.m - 1), -Cf.lam t < α ∨ β < -Cf.lam t := by
    intro t ht
    by_contra hcon
    push_neg at hcon
    have hmem : -Cf.lam t ∈ Cf.cutI S.l := by rw [hCf, cutI_eq]; exact ⟨hcon.1, hcon.2⟩
    have hfac := (Formalism.FourierDecayAlt.P.betaFactorisation Cf S.de S.de' S.G.ka S.T S.T' (-Cf.lam t) S.l (hOkp v)
      hw hw' hT hT' hl1 hlk hne hmem).2.1
    apply hfac
    unfold Sz.Cfg.P
    exact Finset.prod_eq_zero ht (by ring)
  have hI3 : 3 ≤ β - α := three_le_len _ _ hN20 hlenI
  have hPr := pratio (Icc 1 (Cf.k + Cf.m - 1)) Cf.lam α β y hI3 hroot hmid1 hmid2
  have hPy : S.P v y = ∏ t ∈ Icc 1 (Cf.k + Cf.m - 1), (y + Cf.lam t) := rfl
  have hPy1 : S.P v (y + 1) = ∏ t ∈ Icc 1 (Cf.k + Cf.m - 1), (y + 1 + Cf.lam t) := rfl
  rw [← hPy, ← hPy1, Nat.card_Icc] at hPr
  have hn6 : 6 * ((Cf.k + Cf.m - 1 + 1 - 1 : ℕ) : ℝ) ≤ β - α := by
    have hLv := hLC v
    have hCc1 : 1 ≤ Cc := by linarith [Real.add_one_le_exp 1]
    have hm : Cf.m = 2 * S.G.r + 2 := rfl
    have hkk : Cf.k = S.G.k := rfl
    rw [hm, hkk]
    have hk1 : 1 ≤ S.G.k := by omega
    push_cast [show S.G.k + (2 * S.G.r + 2) - 1 + 1 - 1 = S.G.k + 2 * S.G.r + 1 by omega]
    have hr0 : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
    have hkR : (1 : ℝ) ≤ S.G.k := by exact_mod_cast hk1
    have := long_bound (S.G.k : ℝ) (S.G.r : ℝ) (S.Ntop : ℝ) Cc (β - α) hkR hr0 hN20 hCc1 hLv
    linarith

  set n := Cf.k + Cf.m - 1 + 1 - 1 with hn
  set E1 := Real.exp (1 / 2) with hE1
  have hE1pos : 0 < E1 := Real.exp_pos _
  have hE1sq : E1 ^ 2 = Real.exp 1 := by rw [hE1, ← Real.exp_nat_mul]; norm_num
  have hEinv : Real.exp (-(1 / 2)) = E1⁻¹ := by rw [hE1, Real.exp_neg]
  have hρP : (1 + 3 / (β - α)) ^ n ≤ E1 := by
    refine (one_add_pow_le_exp _ (by positivity) n).trans (Real.exp_le_exp.2 ?_)
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    linarith
  have hF2 : F ^ 2 ≤ E1 := by
    have hN20' : (20 : ℝ) ≤ S.Ntop := hN20
    have h1 : F ^ 2 ≤ Real.exp ((S.Ntop : ℝ) / ((S.Ntop : ℝ) ^ 2 - 1)) ^ 2 := pow_le_pow_left₀ hF0.le hF1 2
    refine h1.trans ?_
    rw [← Real.exp_nat_mul, hE1]
    exact Real.exp_le_exp.2 (two_N_bound _ hN20').2

  have hyI' : y ∈ Cf.cutI S.l := hyI
  have hcore := core_le_supA hB v false y (by simpa using hyI')
  have hqeq : Cf.q S.de S.de' S.T S.T' y = q' y := (qC_re S v y).symm
  have hcore2 : |S.P v y * S.P v (y + 1)| = Cf.core S.de S.de' S.T S.T' y ^ 2 * q' y := by
    unfold Sz.Cfg.core
    rw [Real.sq_sqrt (abs_nonneg _), hqeq, abs_div, abs_of_pos hqy]
    have hPP : S.P v y * S.P v (y + 1) = Cf.P y * Cf.P (y + 1) := rfl
    rw [hPP, div_mul_cancel₀ _ hqy.ne']
  have hcore0 : 0 ≤ Cf.core S.de S.de' S.T S.T' y := Real.sqrt_nonneg _
  have hP2 : S.P v y ^ 2 ≤ E1 * (J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) ^ 2 * q' y) := by
    have h1 : S.P v y ^ 2 = |S.P v y| * |S.P v y| := by rw [sq, abs_mul_abs_self]
    have h2 : |S.P v y| * |S.P v y| ≤ |S.P v y| * ((1 + 3 / (β - α)) ^ n * |S.P v (y + 1)|) :=
      mul_le_mul_of_nonneg_left hPr (abs_nonneg _)
    have h3 : |S.P v y| * ((1 + 3 / (β - α)) ^ n * |S.P v (y + 1)|) =
        (1 + 3 / (β - α)) ^ n * (Cf.core S.de S.de' S.T S.T' y ^ 2 * q' y) := by
      rw [← hcore2, abs_mul]; ring
    have h4 : Cf.core S.de S.de' S.T S.T' y ^ 2 ≤ J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) ^ 2 :=
      pow_le_pow_left₀ hcore0 hcore 2
    have h5 : (1 + 3 / (β - α)) ^ n * (Cf.core S.de S.de' S.T S.T' y ^ 2 * q' y) ≤
        E1 * (J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) ^ 2 * q' y) := by
      exact mul_le_mul hρP (mul_le_mul_of_nonneg_right h4 hqy.le) (mul_nonneg (pow_nonneg hcore0 2) hqy.le) hE1pos.le
    calc S.P v y ^ 2 = |S.P v y| * |S.P v y| := h1
      _ ≤ _ := h2
      _ = _ := h3
      _ ≤ _ := h5
  have hqw2 : E1⁻¹ * q' y ≤ Wd.qw q' wr y := by rw [← hEinv]; exact (le_div_iff₀ hqy).1 hLQ
  exact final_cmp |S.P v y| x0r F (q' y) (S.T * S.T') _ E1 (Wd.qw q' wr y) (abs_nonneg _) hx0pos hF0 hqy hTT
    hsA hE1pos hE1sq (by rw [sq_abs]; exact hP2) hx0sq hF2 hqw2

end

end Formalism.FourierDecayAlt.P.PBL

theorem Formalism.FourierDecayAlt.P.top_ratio : Formalism.FourierDecayAlt.P.PBL.TopRatio := Formalism.FourierDecayAlt.P.PBL.topRatio
end

section
namespace Formalism.FourierDecayAlt.P

theorem built_bounds_compact_of_head_top (hH : Formalism.FourierDecayAlt.KB.HeadTop) : Formalism.FourierDecayAlt.KB.BuiltBounds2Cpt := fun hA =>
  built_bounds_compact_of_leaves radial_head hH degree_of_lift_pairing top_local_built_places degree_top
    top_ratio (germ_parts_compact_support kernel_continuity_built germ_rate_bound hA)
    (fun hA' => uniform_decay_of_place hA' radial_head hH
      (uniform_decay_of_heads radial_head hH)) hA

end Formalism.FourierDecayAlt.P
end

section
namespace Formalism.FourierDecayAlt.P

theorem pb_builtBounds2Cpt_of_mkTop (hM : CutEX.MkTop) : Formalism.FourierDecayAlt.KB.BuiltBounds2Cpt :=
  built_bounds_compact_of_head_top (pb_headTop_of_mkTop hM)

end Formalism.FourierDecayAlt.P
end

section
namespace Formalism.FourierDecayAlt.P

theorem built_bounds_compact : Formalism.FourierDecayAlt.KB.BuiltBounds2Cpt := pb_builtBounds2Cpt_of_mkTop top_truncation_of_averages

end Formalism.FourierDecayAlt.P
end
