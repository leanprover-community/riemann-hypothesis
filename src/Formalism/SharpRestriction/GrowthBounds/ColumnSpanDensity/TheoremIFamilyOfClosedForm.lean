import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.MeanDefs
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatticeCountPrimeMonoLevel
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FactorizationBoundMonoLattices
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.DensityNumericalFacts
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LocalHypothesisOfGlobal
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ColumnSpanNumericalFacts
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FourDepthLtConductorOfBounds
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TwoHundredLeRadius
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ThresholdDensityFacts
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FinrankLetter
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.InvariantSectionsTransportGL
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FunctorComparisonOfSingleWeight
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TensorKP
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ModelIdentificationOfExplicitMap
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Tensor
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.EdgeLatRS
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RestOIso
import Mathlib
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.CloudPropOfMapsRetractionBasis
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatRetract

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem kF_nonneg (X : Dat) (K : Cst) (R : RS X.p X.n') (al be : X.TT → ℕ) : 0 ≤ X.kF K R al be :=
  Real.sInf_nonneg fun _ h => h.1

open Classical in
theorem kText_nonneg (X : Dat) (K : Cst) (R : RS X.p X.n') (hb : 0 < X.b') (aa bb : X.TT → ℤ) :
    0 ≤ X.kText K R aa bb := by
  unfold Dat.kText
  have h1 : 0 ≤ (if X.Inside aa bb then
      X.kF K R (fun s => (aa s - X.ccl).toNat) (fun s => (bb s - X.ccl).toNat) else 1) := by
    split_ifs
    · exact kF_nonneg _ _ _ _ _
    · exact zero_le_one
  have h2 := kF_nonneg X K R (fun s => (aa s + X.ccl).toNat) (fun s => (bb s + X.ccl).toNat)
  have h3 : 0 ≤ 12 * (X.N : ℝ) * X.k * X.ccl / X.b' := by
    unfold Dat.k
    positivity
  linarith

theorem theorem_I_of_intermediate_bounds (D : Formalism.BasicNotions.D7) (FM : Cst → Dat → Prop) (hR : LPRingIndep) (hLP : ∀ K C, MidLP K C)
    (hMean : ∀ K : Cst, K.Pos → MidMean D K (FM K)) (hN1 : ∀ K : Cst, K.Pos → TransportedAlt K (FactsLP K))
    (hN2 : ∀ K : Cst, K.Pos → TransportedAlt K (fun _ => FM K)) : SecondPartClosed D := by
  intro hA
  obtain ⟨T0, hT0, h0⟩ := hA 4 (by norm_num)
  refine ⟨T0, hT0, fun C₀ hC₀ => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C₀ hC₀
  obtain ⟨T2, hT2, h2⟩ := h1 T1 T1 T1 le_rfl le_rfl le_rfl
  obtain ⟨CA, Ckap, Ct, Cs, hCA, hCkap, hCt, hCs, hAdm⟩ := h2 T2 le_rfl
  let K : Cst := ⟨C₀, T2, CA, T1, T1, T1, Ckap, Ct, Cs⟩
  have hK : K.Pos := ⟨lt_of_lt_of_le hT0 hC₀, hT2, hCA, hT1, hT1, hT1, hCkap, hCt, hCs⟩
  obtain ⟨Ta, Ca, hTa, hCa, hFa⟩ := hN1 K hK
  obtain ⟨Tb, Cb, hTb, hCb, hFb⟩ := hN2 K hK
  refine ⟨max Ta Tb, max (max Ca Cb) K.Cmean, lt_max_of_lt_left hTa,
    lt_max_of_lt_left (lt_max_of_lt_left hCa), fun CH hCH => ?_⟩
  intro p n' m TT G' N₁ Y Yb a b' bl bu ccl Dp cStar hH
  have hm : m ≠ 0 := by
    have := hH.2.2.2.2.2.2.1
    omega
  have hY : 1 ≤ Y := hH.1
  let X : Dat := ⟨p, n', m, hm, TT, G', N₁, Y, Yb, a, b', bl, bu, ccl, Dp, cStar⟩
  have hX : X.Hyp K.C₀ CH := hH
  have hLPf : FactsLP K (max (max Ca Cb) K.Cmean) X :=
    hFa CH (le_trans (le_max_left _ _) hCH) _ (le_trans (le_max_left _ _) (le_max_left _ _)) X hX
  have hMf : FM K X :=
    hFb CH (le_trans (le_max_right _ _) hCH) (max (max Ca Cb) K.Cmean)
      (le_trans (le_max_right _ _) (le_max_left _ _)) X hX
  have hnn : 0 ≤ (TT.card : ℝ) * N₁ / Y := by positivity
  by_cases hne : Nonempty (RS p n')
  · obtain ⟨R₀⟩ := hne
    refine ⟨X.kText K R₀, kText_nonneg X K R₀ hLPf.bpos, ?_, ?_⟩
    · have h := hMean K hK hAdm X hMf R₀
      have h' : K.Cmean * (TT.card : ℝ) * N₁ / Y ≤ max (max Ca Cb) K.Cmean * (TT.card : ℝ) * N₁ / Y := by
        have := mul_le_mul_of_nonneg_right (le_max_right (max Ca Cb) K.Cmean) hnn
        calc K.Cmean * (TT.card : ℝ) * N₁ / Y = K.Cmean * ((TT.card : ℝ) * N₁ / Y) := by ring
          _ ≤ max (max Ca Cb) K.Cmean * ((TT.card : ℝ) * N₁ / Y) := this
          _ = _ := by ring
      exact le_trans h h'
    · intro W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hstd aw bw lam0 hW t ht
      let R : RS p n' := ⟨W, Qq, O, Kf, ι, σ, j, w, hstd⟩
      exact hR p n' R₀ R m 1 lam0 t Dp _ cStar (hLP K _ X hLPf R₀ aw bw lam0 hW t ht)
  · refine ⟨fun _ _ => 0, fun _ _ => le_rfl, ?_, ?_⟩
    · have h0 : meanKap TT m Y a bl bu (fun _ _ => (0 : ℝ)) = 0 := by simp [meanKap]
      rw [h0]
      have hC : 0 ≤ max (max Ca Cb) K.Cmean := le_of_lt (lt_max_of_lt_left (lt_max_of_lt_left hCa))
      have := mul_nonneg hC hnn
      calc (0 : ℝ) ≤ max (max Ca Cb) K.Cmean * ((TT.card : ℝ) * N₁ / Y) := this
        _ = _ := by ring
    · intro W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hstd
      exact absurd ⟨(⟨W, Qq, O, Kf, ι, σ, j, w, hstd⟩ : RS p n')⟩ hne

end Formalism.MainNotions.flipOneThree.Pf

end
end

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def FM (K : Cst) (X : Dat) : Prop := FixedWeightNumericalFacts K X ∧ DensityNumericalFacts K X ∧ MeanKappaNumericalFacts K X ∧ ColumnSpanNumericalFacts K X

theorem midMean_of (D : Formalism.BasicNotions.D7) (h61a : RhoSumLowerBoundEdge) (h60ab : RhoUpperBoundSmallDepth) (hE : RestEdge) (hD : RestDims) (K : Cst)
    (hK : K.Pos) : MidMean D K (FM K) := fun hA X hF R =>
  have hk := keyIneq_of D K hA h61a h60ab hE hD X hF.1 R
  mean_of K hK X hF.2.2.2 R (avg_of hD K X hF.2.1 R hk 0 (Nat.zero_le _)) (avg_of hD K X hF.2.1 R hk X.ccl le_rfl)
    (meanX_of D K hK hA X hF.2.2.1 R)

theorem TransportedAlt.and {K : Cst} {F G : ℝ → Dat → Prop} (hF : TransportedAlt K F) (hG : TransportedAlt K G) : TransportedAlt K fun C X => F C X ∧ G C X := by
  obtain ⟨T, Cn, hT, hCn, h⟩ := hF
  obtain ⟨T', Cn', _, _, h'⟩ := hG
  exact ⟨max T T', max Cn Cn', lt_max_of_lt_left hT, lt_max_of_lt_left hCn, fun CH hCH C hC X hX =>
    ⟨h CH (le_trans (le_max_left _ _) hCH) C (le_trans (le_max_left _ _) hC) X hX,
      h' CH (le_trans (le_max_right _ _) hCH) C (le_trans (le_max_right _ _) hC) X hX⟩⟩

end Formalism.MainNotions.flipOneThree.Pf

end
end

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

open Classical in

def RestOddTops : Prop :=
  ∀ (n' : ℕ) (TT : Finset (Fin n')), 2 ≤ numSeg TT → ∀ f : Fin n' → Fin n' → ℕ → ℝ,
    ∑ j : Fin (numSeg TT), ∑ i : Fin (segS TT j), f (segPos TT j i) (segStart TT j) ((segDists TT j).get i) =
      ∑ y ∈ TT.filter (fun y => ¬ IsTypeV y), f y (yPrev TT y) (dPrev TT y)

theorem tle_abs (Ct C N N1 p k Q L ar a' b' La La' ccl cS n' S S' : ℝ) (hCt : 0 < Ct) (hC : 4 * Ct + 4 ≤ C)
    (hN : 1 ≤ N) (hN1 : 1 ≤ N1) (hp : 0 < p) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (hL : 0 ≤ L) (har : 0 ≤ ar)
    (ha0 : 0 ≤ a') (ha : a' ≤ 2 * ar) (hb : 0 < b') (hLa : 0 ≤ La) (hLa0 : 0 ≤ La') (hLa' : La' ≤ 2 * La)
    (hccl : 0 ≤ ccl) (hcS : 0 ≤ cS) (hn' : 0 ≤ n') (hS : S' ≤ S + N * ccl) :
    (S' + Ct * N * (a' / p ^ 2 + b' / p + La' * a' / (p * k) + La' * b' / k + k * Q +
        Q * (cS + 2 * N * ccl + 2 * n' * ccl))) + N * (La' * b' / k) + 1 + 2 * n' * ccl ≤
      S + C * N * N1 * (ar / p ^ 2 + b' / p + La * ar / (p * k) + La * b' / k) +
        C * N * (Q * (cS + C * N * k * L + 4 * N * ccl + 2 * n' * ccl) + k * Q + k * L + ccl) + 2 * n' * ccl := by
  have hN0 : 0 ≤ N := by linarith
  have hk0 : 0 < k := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hCN1 : C ≤ C * N1 := by nlinarith
  have hp2 : 0 < p ^ 2 := by positivity
  have hA : a' / p ^ 2 ≤ 2 * (ar / p ^ 2) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right ha hp2.le
  have hA0 : 0 ≤ ar / p ^ 2 := by positivity
  have hB0 : 0 ≤ b' / p := by positivity
  have hE : La' * a' / (p * k) ≤ 4 * (La * ar / (p * k)) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := mul_le_mul hLa' ha ha0 (by linarith : (0 : ℝ) ≤ 2 * La)
    linarith
  have hE0 : 0 ≤ La * ar / (p * k) := by positivity
  have hF : La' * b' / k ≤ 2 * (La * b' / k) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hk0.le
    nlinarith
  have hF0 : 0 ≤ La * b' / k := by positivity
  have hF'0 : 0 ≤ La' * b' / k := by positivity
  have t1 : Ct * N * (a' / p ^ 2) ≤ C * N * N1 * (ar / p ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hA (mul_nonneg hCt.le hN0)
    have h2 := mul_le_mul_of_nonneg_right (by linarith : 2 * Ct ≤ C * N1) (mul_nonneg hN0 hA0)
    nlinarith
  have t2 : Ct * N * (b' / p) ≤ C * N * N1 * (b' / p) := by
    have h2 := mul_le_mul_of_nonneg_right (by linarith : Ct ≤ C * N1) (mul_nonneg hN0 hB0)
    nlinarith
  have t3 : Ct * N * (La' * a' / (p * k)) ≤ C * N * N1 * (La * ar / (p * k)) := by
    have h1 := mul_le_mul_of_nonneg_left hE (mul_nonneg hCt.le hN0)
    have h2 := mul_le_mul_of_nonneg_right (by linarith : 4 * Ct ≤ C * N1) (mul_nonneg hN0 hE0)
    nlinarith
  have t4 : Ct * N * (La' * b' / k) + N * (La' * b' / k) ≤ C * N * N1 * (La * b' / k) := by
    have h1 := mul_le_mul_of_nonneg_left hF (mul_nonneg (by linarith : (0 : ℝ) ≤ Ct + 1) hN0)
    have h2 := mul_le_mul_of_nonneg_right (by linarith : 2 * Ct + 2 ≤ C * N1) (mul_nonneg hN0 hF0)
    nlinarith
  have hNkQ : 1 ≤ N * k * Q := by
    have := one_le_mul_of_one_le_of_one_le hN hk
    exact one_le_mul_of_one_le_of_one_le this hQ
  have t5 : Ct * N * (k * Q) + 1 ≤ C * N * (k * Q) := by
    have h2 := mul_le_mul_of_nonneg_right (by linarith : (4 : ℝ) ≤ C - Ct) (by linarith : (0 : ℝ) ≤ N * k * Q)
    nlinarith
  have hX0 : 0 ≤ cS + 2 * N * ccl + 2 * n' * ccl := by positivity
  have hXY : cS + 2 * N * ccl + 2 * n' * ccl ≤ cS + C * N * k * L + 4 * N * ccl + 2 * n' * ccl := by
    have : 0 ≤ C * N * k * L := by positivity
    have : 0 ≤ N * ccl := by positivity
    linarith
  have t6 : Ct * N * (Q * (cS + 2 * N * ccl + 2 * n' * ccl)) ≤
      C * N * (Q * (cS + C * N * k * L + 4 * N * ccl + 2 * n' * ccl)) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hN0)
      (mul_le_mul_of_nonneg_left hXY hQ0) (mul_nonneg hQ0 hX0) (mul_nonneg hC0 hN0)
  have t7 : N * ccl ≤ C * N * (k * L + ccl) := by
    have : 0 ≤ C * N * (k * L) := by positivity
    have h2 := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ C) (mul_nonneg hN0 hccl)
    linarith
  linarith [t1, t2, t3, t4, t5, t6, t7]

theorem initial_level_formula (K : Cst) (X : Dat) (A B : X.TT → ℕ) :
    X.t0 K A B = (∑ j : Fin (numSeg X.TT), ∑ i : Fin (segS X.TT j),
        min ((ex B (segPos X.TT j i) : ℕ) : ℝ)
          (((ex A (segStart X.TT j) : ℕ) : ℝ) / (X.p : ℝ) ^ ((segDists X.TT j).get i))) +
      K.Ct * X.N * ((X.a : ℝ) / (X.p : ℝ) ^ 2 + X.b' / X.p + LaI K.C₀ X.N₁ X.a * X.a / (X.p * X.k) +
        LaI K.C₀ X.N₁ X.a * X.b' / X.k + X.k * (X.p : ℝ) ^ X.G' +
        (X.p : ℝ) ^ X.G' * ((X.cStar : ℝ) + 2 * X.N * X.ccl + 2 * X.n' * X.ccl)) := by
  unfold Dat.t0 t0I t0G4 Dat.c4 Dat.N Dat.k
  push_cast
  ring

end Formalism.MainNotions.flipOneThree.Pf

end
end

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem posAdd_cdist {n' : ℕ} (x y : Fin n') : posAdd x (cdist x y) = y := by
  apply Fin.ext
  show (x.val + (y.val + n' - x.val) % n') % n' = y.val
  rw [Nat.add_mod_mod]
  have h : x.val + (y.val + n' - x.val) = y.val + n' := by
    have := x.isLt
    omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]

theorem mem_segDists {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (d : ℕ) :
    d ∈ segDists TT j ↔ ∃ s ∈ TT, ¬ Even s.val ∧ 0 < cdist (segStart TT j) s ∧
      cdist (segStart TT j) s < segG TT j ∧ cdist (segStart TT j) s = d := by
  unfold segDists
  rw [Finset.mem_sort, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [Finset.mem_filter] at hs
    exact ⟨s, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, rfl⟩
  · rintro ⟨s, hs, h1, h2, h3, rfl⟩
    exact ⟨s, Finset.mem_filter.2 ⟨hs, h1, h2, h3⟩, rfl⟩

theorem segPos_spec {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    segPos TT j i ∈ TT ∧ ¬ Even (segPos TT j i).val ∧
      cdist (segStart TT j) (segPos TT j i) = (segDists TT j).get i ∧ 0 < (segDists TT j).get i ∧
      (segDists TT j).get i < segG TT j := by
  obtain ⟨s, hs, h1, h2, h3, h4⟩ := (mem_segDists TT j _).1 (List.get_mem (segDists TT j) i)
  have e : segPos TT j i = s := by
    unfold segPos
    rw [← h4]
    exact posAdd_cdist _ _
  rw [e]
  exact ⟨hs, h1, h4, h4 ▸ h2, h4 ▸ h3⟩

theorem mem_evenTops {n' : ℕ} (TT : Finset (Fin n')) (x : Fin n') : x ∈ evenTops TT ↔ x ∈ TT ∧ Even x.val := by
  unfold evenTops
  rw [Finset.mem_sort, Finset.mem_filter]

theorem segStart_spec {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) :
    segStart TT j ∈ TT ∧ Even (segStart TT j).val :=
  (mem_evenTops TT _).1 (List.get_mem _ _)

theorem ex_cast {n' : ℕ} {TT : Finset (Fin n')} (z : Fin n' → ℤ) (c : ℕ) (s : Fin n') (hs : s ∈ TT) (h0 : 0 ≤ z s) :
    ((ex (TT := TT) (fun s => (z s + c).toNat) s : ℕ) : ℝ) = (z s : ℝ) + c := by
  unfold ex
  rw [dif_pos hs]
  have h : ((z s + c).toNat : ℤ) = z s + c := Int.toNat_of_nonneg (by positivity)
  have h' : (((z s + c).toNat : ℤ) : ℝ) = ((z s + c : ℤ) : ℝ) := by rw [h]
  push_cast at h'
  exact h'

theorem min_shift (b a c P : ℝ) (hc : 0 ≤ c) (hP : 1 ≤ P) : min (b + c) ((a + c) / P) ≤ min b (a / P) + c := by
  have hP0 : 0 < P := by linarith
  have h1 : c / P ≤ c := div_le_self hc hP
  have h2 : (a + c) / P = a / P + c / P := add_div _ _ _
  rw [← min_add_add_right]
  exact min_le_min le_rfl (by rw [h2]; linarith)

open Classical in
theorem tle_of (hO : RestOddTops) {K : Cst} (hK : K.Pos) {CH : ℝ} {C : ℝ} (hC : 4 * K.Ct + 4 ≤ C)
    {X : Dat} (h : X.Hyp K.C₀ CH) (B : Base K CH X) (aw bw : Fin X.n' → ℤ)
    (hw : ∀ s ∈ X.TT, aw s ∈ IaZ X.m X.Y X.ar ∧ bw s ∈ IbZ X.bl X.bu) :
    (X.tStar K (fun s => (aw s + X.ccl).toNat) (fun s => (bw s + X.ccl).toNat) : ℝ) + 2 * X.n' * X.ccl ≤
      tI K.C₀ C X.p X.n' X.m X.TT X.G' X.N₁ X.ar X.b' X.ccl X.cStar aw bw := by
  have hseg2 : 2 ≤ numSeg X.TT := h.2.2.2.1
  have hbl : 0 ≤ X.bl := by
    have := lowb_of h
    linarith [B.hb8]
  have hp1 : (1 : ℝ) ≤ X.p := by linarith [B.hp25]
  have har200 : (200 : ℝ) ≤ X.ar := by
    have := mul_le_mul B.hp25 B.hb8 (by norm_num) (by linarith [B.hp25])
    linarith [B.hpa]
  have ha0 : ∀ s ∈ X.TT, 0 ≤ aw s := fun s hs =>
    le_trans (Int.ceil_nonneg (by linarith)) (Finset.mem_Icc.1 (hw s hs).1).1
  have hb0 : ∀ s ∈ X.TT, 0 ≤ bw s := fun s hs =>
    le_trans (Int.ceil_nonneg hbl) (Finset.mem_Icc.1 (hw s hs).2).1
  set S : ℝ := ∑ y ∈ X.TT.filter (fun y => ¬ IsTypeV y),
      min (bw y : ℝ) ((aw (yPrev X.TT y) : ℝ) / (X.p : ℝ) ^ dPrev X.TT y) with hS
  set S' : ℝ := ∑ j : Fin (numSeg X.TT), ∑ i : Fin (segS X.TT j),
        min ((ex (TT := X.TT) (fun s => (bw s + X.ccl).toNat) (segPos X.TT j i) : ℕ) : ℝ)
          (((ex (TT := X.TT) (fun s => (aw s + X.ccl).toNat) (segStart X.TT j) : ℕ) : ℝ) /
            (X.p : ℝ) ^ ((segDists X.TT j).get i)) with hS'
  have hcount : (∑ j : Fin (numSeg X.TT), ∑ _i : Fin (segS X.TT j), (X.ccl : ℝ)) ≤ X.N * X.ccl := by
    have := hO X.n' X.TT hseg2 (fun _ _ _ => (X.ccl : ℝ))
    rw [this, Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    unfold Dat.N
    exact_mod_cast Finset.card_filter_le _ _
  have hSS : S' ≤ S + X.N * X.ccl := by
    have e := hO X.n' X.TT hseg2 (fun y x d => min (bw y : ℝ) ((aw x : ℝ) / (X.p : ℝ) ^ d))
    have h1 : S' ≤ ∑ j : Fin (numSeg X.TT), ∑ i : Fin (segS X.TT j),
        (min (bw (segPos X.TT j i) : ℝ) ((aw (segStart X.TT j) : ℝ) / (X.p : ℝ) ^ ((segDists X.TT j).get i)) +
          (X.ccl : ℝ)) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro i _
      rw [ex_cast bw X.ccl _ (segPos_spec X.TT j i).1 (hb0 _ (segPos_spec X.TT j i).1),
        ex_cast aw X.ccl _ (segStart_spec X.TT j).1 (ha0 _ (segStart_spec X.TT j).1)]
      exact min_shift _ _ _ _ (by positivity) (one_le_pow₀ hp1)
    simp only [Finset.sum_add_distrib] at h1
    rw [e] at h1
    linarith
  have hS'0 : 0 ≤ S' := by
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro i _
    exact le_min (by positivity) (by positivity)

  have ha1 : (1 : ℝ) ≤ X.a := by linarith [B.haa]
  have hlog0 : 0 ≤ Real.log X.a := Real.log_nonneg ha1
  have hlog2 : Real.log X.a ≤ 2 * Real.log X.ar := by
    have h10 : (X.a : ℝ) ≤ X.ar ^ 2 := by
      have : 2 * X.ar ≤ X.ar * X.ar := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have e : X.ar ^ 2 = X.ar * X.ar := by ring
      rw [e]
      linarith [B.haa1]
    have := Real.log_le_log (by linarith) h10
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hC0 : 0 < K.C₀ := hK.1
  have hcn : 0 ≤ K.C₀ * (X.N₁ : ℝ) ^ 2 := by positivity
  have hLa'0 : 0 ≤ LaI K.C₀ X.N₁ X.a := by unfold LaI; exact mul_nonneg hcn hlog0
  have hLa'2 : LaI K.C₀ X.N₁ X.a ≤ 2 * LaI K.C₀ X.N₁ X.ar := by
    unfold LaI
    have := mul_le_mul_of_nonneg_left hlog2 hcn
    linarith
  have hk1 : (1 : ℝ) ≤ X.k := by linarith [B.hk5]
  have hb : 0 < X.b' := by linarith [B.hb8]
  have hp0 : (0 : ℝ) < X.p := by linarith
  have hJ : X.J0 K = LaI K.C₀ X.N₁ X.a * X.b' / X.k := rfl
  have key := tle_abs K.Ct C X.N X.N₁ X.p X.k ((X.p : ℝ) ^ X.G') (Real.logb X.p X.ar) X.ar X.a X.b'
    (LaI K.C₀ X.N₁ X.ar) (LaI K.C₀ X.N₁ X.a) X.ccl X.cStar X.n' S S' hK.2.2.2.2.2.2.2.1 hC (by linarith [B.hN2])
    B.hN1 hp0 hk1 B.hQ (by linarith [B.hL1]) (by linarith) (by linarith) (by linarith [B.haa1]) hb
    (by linarith [B.hLa1]) hLa'0 hLa'2 (by positivity) (by positivity) (by positivity) hSS
  have hx0 : 0 ≤ X.t0 K (fun s => (aw s + X.ccl).toNat) (fun s => (bw s + X.ccl).toNat) + X.N * X.J0 K := by
    rw [initial_level_formula, hJ]
    have hCt : 0 < K.Ct := hK.2.2.2.2.2.2.2.1
    have hk0 : 0 < X.k := by linarith
    have hQ0 : (0 : ℝ) < (X.p : ℝ) ^ X.G' := by positivity
    have := hS'0
    positivity
  have hceil : (X.tStar K (fun s => (aw s + X.ccl).toNat) (fun s => (bw s + X.ccl).toNat) : ℝ) ≤
      (S' + K.Ct * X.N * ((X.a : ℝ) / (X.p : ℝ) ^ 2 + X.b' / X.p + LaI K.C₀ X.N₁ X.a * X.a / (X.p * X.k) +
        LaI K.C₀ X.N₁ X.a * X.b' / X.k + X.k * (X.p : ℝ) ^ X.G' +
        (X.p : ℝ) ^ X.G' * ((X.cStar : ℝ) + 2 * X.N * X.ccl + 2 * X.n' * X.ccl))) +
        X.N * (LaI K.C₀ X.N₁ X.a * X.b' / X.k) + 1 := by
    have h1 := (Nat.ceil_lt_add_one hx0).le
    have h2 := initial_level_formula K X (fun s => (aw s + X.ccl).toNat) (fun s => (bw s + X.ccl).toNat)
    unfold Dat.tStar
    calc _ ≤ _ := h1
      _ = _ := by rw [h2, hJ]
  have htI : tI K.C₀ C X.p X.n' X.m X.TT X.G' X.N₁ X.ar X.b' X.ccl X.cStar aw bw =
      S + C * X.N * X.N₁ * (X.ar / (X.p : ℝ) ^ 2 + X.b' / X.p + LaI K.C₀ X.N₁ X.ar * X.ar / (X.p * X.k) +
          LaI K.C₀ X.N₁ X.ar * X.b' / X.k) +
        C * X.N * ((X.p : ℝ) ^ X.G' * ((X.cStar : ℝ) + C * X.N * X.k * Real.logb X.p X.ar + 4 * X.N * X.ccl +
          2 * X.n' * X.ccl) + X.k * (X.p : ℝ) ^ X.G' + X.k * Real.logb X.p X.ar + X.ccl) + 2 * X.n' * X.ccl := rfl
  rw [htI]
  linarith

end Formalism.MainNotions.flipOneThree.Pf

end
end

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem mod2 {a n : ℕ} (h : a < 2 * n) : (a < n ∧ a % n = a) ∨ (n ≤ a ∧ a % n = a - n) := by
  rcases lt_or_ge a n with h1 | h1
  · exact Or.inl ⟨h1, Nat.mod_eq_of_lt h1⟩
  · right
    refine ⟨h1, ?_⟩
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]

theorem ar1 {n x d y : ℕ} (hx : x < n) (hd : d < n) (h : (x + d) % n = y) : (y + n - x) % n = d := by
  rcases mod2 (a := x + d) (n := n) (by omega) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
  rcases mod2 (a := y + n - x) (n := n) (by omega) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega

theorem ar2 {n x d y : ℕ} (hx : x < n) (hd : d < n) (h : (x + d) % n = y) : (y + (n - d)) % n = x := by
  rcases mod2 (a := x + d) (n := n) (by omega) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
  rcases mod2 (a := y + (n - d)) (n := n) (by omega) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega

theorem ar3 {n x x' d d' y : ℕ} (hx : x < n) (hx' : x' < n) (hd : d < n) (hd' : d' < d) (h : (x + d) % n = y)
    (h' : (x' + d') % n = y) : (x' + n - x) % n = d - d' := by
  rcases mod2 (a := x + d) (n := n) (by omega) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
  rcases mod2 (a := x' + d') (n := n) (by omega) with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
  rcases mod2 (a := x' + n - x) (n := n) (by omega) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega

theorem ar4 {n x g d nx y : ℕ} (hx : x < n) (hd : d < n) (hg : g ≤ d) (h1 : (x + g) % n = nx)
    (h : (x + d) % n = y) : (nx + (d - g)) % n = y := by
  rcases mod2 (a := x + d) (n := n) (by omega) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
  rcases mod2 (a := x + g) (n := n) (by omega) with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
  rcases mod2 (a := nx + (d - g)) (n := n) (by omega) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega

theorem cd_le {n a b : ℕ} (hb : b < n) (hab : a ≤ b) : (b + n - a) % n = b - a := by
  have e : b + n - a = (b - a) + n := by omega
  rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem cd_gt {n a b : ℕ} (ha : a < n) (hab : b < a) : (b + n - a) % n = b + n - a :=
  Nat.mod_eq_of_lt (by omega)

section

variable {n' : ℕ}

theorem evenTops_mono (TT : Finset (Fin n')) : StrictMono (evenTops TT).get :=
  (Finset.sortedLT_sort _).strictMono_get

theorem segDists_mono (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : StrictMono (segDists TT j).get :=
  (Finset.sortedLT_sort _).strictMono_get

theorem next_min (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (e : Fin n') (he : e ∈ TT)
    (hev : Even e.val) (hne : e ≠ segStart TT j) :
    0 < cdist (segStart TT j) (segNext TT j) ∧
      cdist (segStart TT j) (segNext TT j) ≤ cdist (segStart TT j) e := by
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp ((mem_evenTops TT e).mpr ⟨he, hev⟩)
  have hm := evenTops_mono TT
  have hkj : k ≠ j := by
    rintro rfl
    exact hne hk.symm
  have hc : ∀ a b : Fin n', cdist a b = (b.val + n' - a.val) % n' := fun _ _ => rfl
  have hx : segStart TT j = (evenTops TT).get j := rfl
  have hkl : k.val < numSeg TT := k.isLt
  by_cases hj : j.val + 1 < numSeg TT
  · have hnext : segNext TT j = (evenTops TT).get ⟨j.val + 1, hj⟩ := by
      unfold segNext
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt hj)
    have h1 : (evenTops TT).get j < (evenTops TT).get ⟨j.val + 1, hj⟩ := hm (Fin.mk_lt_mk.mpr (Nat.lt_succ_self _))
    rw [hc, hc, hnext, hx, ← hk]
    have h1' : ((evenTops TT).get j).val < ((evenTops TT).get ⟨j.val + 1, hj⟩).val := h1
    have b1 := ((evenTops TT).get j).isLt
    have b2 := ((evenTops TT).get ⟨j.val + 1, hj⟩).isLt
    have b3 := ((evenTops TT).get k).isLt
    rw [cd_le b2 h1'.le]
    rcases lt_or_gt_of_ne hkj with hlt | hgt
    · have h3 : ((evenTops TT).get k).val < ((evenTops TT).get j).val := hm hlt
      rw [cd_gt b1 h3]
      omega
    · have h3 : ((evenTops TT).get ⟨j.val + 1, hj⟩).val ≤ ((evenTops TT).get k).val :=
        hm.monotone (Fin.mk_le_of_le_val (Nat.succ_le_of_lt hgt))
      rw [cd_le b3 (by omega)]
      omega
  · have hjl : j.val < numSeg TT := j.isLt
    have hje : j.val + 1 = numSeg TT := by omega
    have h0 : 0 < numSeg TT := by omega
    have hnext : segNext TT j = (evenTops TT).get ⟨0, h0⟩ := by
      unfold segNext
      congr 1
      apply Fin.ext
      show (j.val + 1) % numSeg TT = 0
      rw [hje, Nat.mod_self]
    have hklt : k < j := by
      apply Fin.lt_def.mpr
      have : k.val ≠ j.val := fun h => hkj (Fin.ext h)
      omega
    have h1 : ((evenTops TT).get ⟨0, h0⟩).val < ((evenTops TT).get j).val :=
      hm (Fin.lt_def.mpr (by show 0 < j.val; omega))
    have h3 : ((evenTops TT).get k).val < ((evenTops TT).get j).val := hm hklt
    have h4 : ((evenTops TT).get ⟨0, h0⟩).val ≤ ((evenTops TT).get k).val :=
      hm.monotone (Fin.le_def.mpr (Nat.zero_le _))
    have b1 := ((evenTops TT).get j).isLt
    rw [hc, hc, hnext, hx, ← hk, cd_gt b1 h1, cd_gt b1 h3]
    omega

theorem segNext_spec (TT : Finset (Fin n')) (j : Fin (numSeg TT)) :
    segNext TT j ∈ TT ∧ Even (segNext TT j).val :=
  (mem_evenTops TT _).1 (List.get_mem _ _)

theorem other_even (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (j : Fin (numSeg TT)) :
    ∃ e ∈ TT, Even e.val ∧ e ≠ segStart TT j := by
  have hj := j.isLt
  let j' : Fin (numSeg TT) := if j.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hne : j' ≠ j := by
    intro h
    have hv : j'.val = j.val := congrArg Fin.val h
    by_cases h0 : j.val = 0
    · have e : j'.val = 1 := by simp [j', h0]
      omega
    · have e : j'.val = 0 := by simp [j', h0]
      omega
  refine ⟨segStart TT j', (segStart_spec TT j').1, (segStart_spec TT j').2, fun h => hne ?_⟩
  exact (evenTops_mono TT).injective h

theorem segG_eq (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (j : Fin (numSeg TT)) :
    segG TT j = cdist (segStart TT j) (segNext TT j) ∧ 0 < segG TT j ∧ segG TT j < n' := by
  obtain ⟨e, he, hev, hne⟩ := other_even TT h2 j
  have h := (next_min TT j e he hev hne).1
  have e1 : segG TT j = cdist (segStart TT j) (segNext TT j) := by
    unfold segG
    rw [if_neg (by omega)]
  refine ⟨e1, by omega, ?_⟩
  rw [e1]
  exact Nat.mod_lt _ (segStart TT j).pos

theorem prev_segPos (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    dPrev TT (segPos TT j i) = (segDists TT j).get i ∧ yPrev TT (segPos TT j i) = segStart TT j := by
  obtain ⟨hy, hodd, hcd, hd0, hdG⟩ := segPos_spec TT j i
  obtain ⟨hG, -, hGn⟩ := segG_eq TT h2 j
  set d := (segDists TT j).get i with hd
  set x := segStart TT j with hx
  set y := segPos TT j i with hyy
  have hxy : (x.val + d) % n' = y.val := rfl
  have hdn : d < n' := by omega
  have h1 : dPrev TT y = d := by
    unfold dPrev
    apply le_antisymm
    · exact Nat.sInf_le ⟨hd0, x, (segStart_spec TT j).1, (segStart_spec TT j).2, rfl⟩
    · have hne0 : ({d : ℕ | 1 ≤ d ∧ ∃ x ∈ TT, IsTypeV x ∧ posAdd x d = y}).Nonempty :=
        ⟨d, hd0, x, (segStart_spec TT j).1, (segStart_spec TT j).2, rfl⟩
      apply le_csInf hne0
      rintro d' ⟨hd'1, x', hx', hx'e, hx'y⟩
      by_contra hlt
      have hlt' : d' < d := by omega
      have hx'y' : (x'.val + d') % n' = y.val := congrArg Fin.val hx'y
      have hc : cdist x x' = d - d' := ar3 x.isLt x'.isLt hdn hlt' hxy hx'y'
      have hne : x' ≠ x := by
        intro hxx
        rw [hxx] at hc
        have : cdist x x = 0 := by
          show (x.val + n' - x.val) % n' = 0
          have : x.val + n' - x.val = n' := by omega
          rw [this, Nat.mod_self]
        omega
      have := (next_min TT j x' hx' hx'e hne).2
      rw [← hx] at this
      omega
  refine ⟨h1, ?_⟩
  apply Fin.ext
  show (y.val + (n' - dPrev TT y % n')) % n' = x.val
  rw [h1, Nat.mod_eq_of_lt hdn]
  exact ar2 x.isLt hdn hxy

theorem odd_in_seg (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (y : Fin n') (hy : y ∈ TT) (hodd : ¬ Even y.val) :
    ∃ (j : Fin (numSeg TT)) (i : Fin (segS TT j)), segPos TT j i = y := by
  let j0 : Fin (numSeg TT) := ⟨0, by omega⟩
  have hx0 := segStart_spec TT j0
  set x0 := segStart TT j0 with hx0d
  have hd0 : 1 ≤ cdist x0 y := by
    by_contra h
    have h0 : cdist x0 y = 0 := by omega
    have := posAdd_cdist x0 y
    rw [h0] at this
    have hv : (x0.val + 0) % n' = y.val := congrArg Fin.val this
    rw [Nat.add_zero, Nat.mod_eq_of_lt x0.isLt] at hv
    exact hodd (hv ▸ hx0.2)
  have hmem0 : cdist x0 y ∈ {d : ℕ | 1 ≤ d ∧ ∃ x ∈ TT, IsTypeV x ∧ posAdd x d = y} :=
    ⟨hd0, x0, hx0.1, hx0.2, posAdd_cdist x0 y⟩
  have hmem : dPrev TT y ∈ {d : ℕ | 1 ≤ d ∧ ∃ x ∈ TT, IsTypeV x ∧ posAdd x d = y} := Nat.sInf_mem ⟨_, hmem0⟩
  have hle : dPrev TT y ≤ cdist x0 y := Nat.sInf_le hmem0
  have hmin : ∀ d', 1 ≤ d' → (∃ x ∈ TT, IsTypeV x ∧ posAdd x d' = y) → dPrev TT y ≤ d' :=
    fun d' h1 h3 => Nat.sInf_le ⟨h1, h3⟩
  obtain ⟨hd1, x, hx, hxe, hxy⟩ := hmem
  set d := dPrev TT y with hd
  have hdn : d < n' := lt_of_le_of_lt hle (Nat.mod_lt _ x0.pos)
  have hxy' : (x.val + d) % n' = y.val := congrArg Fin.val hxy
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((mem_evenTops TT x).mpr ⟨hx, hxe⟩)
  have hjx : segStart TT j = x := hj
  obtain ⟨hG, -, hGn⟩ := segG_eq TT h2 j
  have hcd : cdist (segStart TT j) y = d := by
    rw [hjx]
    exact ar1 x.isLt hdn hxy'
  have hlt : d < segG TT j := by
    by_contra hge
    have hge' : cdist x (segNext TT j) ≤ d := by
      rw [← hjx, ← hG]
      omega
    have hn := segNext_spec TT j
    have hnx : (x.val + cdist x (segNext TT j)) % n' = (segNext TT j).val :=
      congrArg Fin.val (posAdd_cdist x (segNext TT j))
    have h4 : ((segNext TT j).val + (d - cdist x (segNext TT j))) % n' = y.val := ar4 x.isLt hdn hge' hnx hxy'
    rcases Nat.eq_or_lt_of_le hge' with heq | hlt'
    · rw [heq, Nat.sub_self, Nat.add_zero, Nat.mod_eq_of_lt (segNext TT j).isLt] at h4
      exact hodd (h4 ▸ hn.2)
    · have := hmin (d - cdist x (segNext TT j)) (by omega) ⟨segNext TT j, hn.1, hn.2, Fin.ext h4⟩
      have hpos : 0 < cdist x (segNext TT j) := by
        rw [← hjx, ← hG]
        exact (segG_eq TT h2 j).2.1
      omega
  have hdm : d ∈ segDists TT j := (mem_segDists TT j d).2 ⟨y, hy, hodd, by omega, by omega, hcd⟩
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hdm
  refine ⟨j, i, ?_⟩
  unfold segPos
  rw [hi, hjx]
  exact hxy

end

open Classical in
theorem restOddTops : RestOddTops := by
  intro n' TT h2 f
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun (x : Σ j : Fin (numSeg TT), Fin (segS TT j)) _ => segPos TT x.1 x.2) ?_ ?_ ?_ ?_
  · rintro ⟨j, i⟩ _
    exact Finset.mem_filter.2 ⟨(segPos_spec TT j i).1, (segPos_spec TT j i).2.1⟩
  · rintro ⟨j, i⟩ _ ⟨j', i'⟩ _ h
    have h' : segPos TT j i = segPos TT j' i' := h
    have a1 := prev_segPos TT h2 j i
    have a2 := prev_segPos TT h2 j' i'
    have hj : j = j' := (evenTops_mono TT).injective (by
      show segStart TT j = segStart TT j'
      rw [← a1.2, ← a2.2, h'])
    subst hj
    have hi : i = i' := (segDists_mono TT j).injective (by rw [← a1.1, ← a2.1, h'])
    subst hi
    rfl
  · intro y hy
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
    obtain ⟨j, i, hji⟩ := odd_in_seg TT h2 y hy1 hy2
    exact ⟨⟨j, i⟩, Finset.mem_sigma.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hji⟩
  · rintro ⟨j, i⟩ _
    have a1 := prev_segPos TT h2 j i
    show f (segPos TT j i) (segStart TT j) ((segDists TT j).get i) = _
    rw [a1.1, a1.2]

end Formalism.MainNotions.flipOneThree.Pf

end
end

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem TLP_pos (K : Cst) : 0 < K.TLP := by
  unfold Cst.TLP
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 108) (le_trans (le_max_left _ _) (le_max_left _ _))

theorem thrLP_of (hO : RestOddTops) (K : Cst) (hK : K.Pos) : TransportedAlt K (FactsLP K) := by
  have hK' := hK
  unfold Cst.Pos at hK'
  have hCt : 0 < K.Ct := hK'.2.2.2.2.2.2.2.1
  refine ⟨K.TLP, 4 * K.Ct + 4, TLP_pos K, by linarith, ?_⟩
  intro CH hCH C hC X h
  have B := base_of K hK CH hCH X h
  have h' := h
  unfold Dat.Hyp HypI at h'
  obtain ⟨-, -, -, -, -, -, hm, -, hb, -, -, -, -, -, -, -, -, -, -, -, -, -, hcs, -⟩ := h'
  have hd := dle_of hK hCH h B
  have hp := B.hp25
  exact
    { cst := hcs
      bpos := hb
      ppos := by exact_mod_cast (show (0 : ℝ) < X.p by linarith)
      m2 := by omega
      D1nn := D1nn_of hK B
      four_depth_lt_conductor := four_depth_lt_conductor_of_bounds hd hcs
      dle := hd
      a8 := second_moment_of_columns hCH B
      eps := eps_of hCH B
      lowa := lowa_of B
      lowb := lowb_of h
      tle := fun aw bw hw => tle_of hO hK hC h B aw bw hw }

theorem thrLP (K : Cst) (hK : K.Pos) : TransportedAlt K (FactsLP K) := by
  exact thrLP_of restOddTops K hK

end Formalism.MainNotions.flipOneThree.Pf

end
end

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

structure JFacts (K : Cst) (X : Dat) : Prop where
  j3 : 3 ≤ X.J0 K
  jb : X.J0 K ≤ X.b' / 216
  cj : (X.ccl : ℝ) ≤ X.J0 K
  jn3 : (3 : ℝ) ≤ X.Jn K
  jnle : (X.Jn K : ℝ) ≤ X.J0 K
  uale : (X.ua : ℝ) ≤ X.ar + X.ar / (((X.m : ℝ) + 1) * X.Y)
  ualt : X.ar + X.ar / (((X.m : ℝ) + 1) * X.Y) < X.ua + 1
  uble : (X.ub : ℝ) ≤ X.bu
  blge : X.b' / 2 ≤ X.bl
  bule : X.bu ≤ 3 * X.b' / 2
  lbge : X.bl ≤ X.lb

theorem jFacts_of {K : Cst} (hK : K.Pos) {CH : ℝ} (hCH : K.TM ≤ CH) {X : Dat} (h : X.Hyp K.C₀ CH) (B : Base K CH X) :
    JFacts K X := by
  have H' := hyp_round hK hCH h B
  obtain ⟨hY, -, -, -, -, -, -, -, hb, hbl, hbu, -, hIb2, hYb, hk2, -, -, -, -, -, hccl, -, -, -⟩ := H'
  obtain ⟨l1, -, -⟩ := La_round hK B
  have hT : K.TLP ≤ CH := le_trans (le_max_left _ _) hCH
  have h108 : (108 : ℝ) ≤ CH := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hYbC : CH ≤ X.Yb := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk5 : (5 : ℝ) ≤ (X.m : ℝ) + 1 := B.hk5
  have hk0 : (0 : ℝ) < (X.m : ℝ) + 1 := by linarith
  have hN2 : (2 : ℝ) ≤ (X.TT.card : ℝ) := B.hN2
  have hLa1 : 1 ≤ LaI K.C₀ X.N₁ X.ar := B.hLa1
  have hLa' : 1 ≤ LaI K.C₀ X.N₁ (X.a : ℝ) := le_trans hLa1 l1
  have h200 := two_hundred_le_radius B
  have hJ : X.J0 K = LaI K.C₀ X.N₁ (X.a : ℝ) * X.b' / ((X.m : ℝ) + 1) := rfl
  have hbk : 24 * ((X.m : ℝ) + 1) ≤ X.b' := by
    have h1 := B.hsz X.k 8 (by linarith [B.hk5]) (k_le_G B) (by norm_num) (by
      have h8 : 8 ≤ X.cStar := by
        have := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        omega
      have h8' : (8 : ℝ) ≤ X.cStar := by exact_mod_cast h8
      have h1 : (0 : ℝ) ≤ (X.N : ℝ) * X.ccl := by positivity
      have h2 : (0 : ℝ) ≤ (X.n' : ℝ) * X.ccl := by positivity
      linarith)
    have h2 : 108 * (X.k * 8) ≤ CH * (X.k * 8) := mul_le_mul_of_nonneg_right h108 (by linarith [B.hk5])
    have h3 : X.k = (X.m : ℝ) + 1 := rfl
    rw [h3] at h1 h2
    linarith
  have j3 : 3 ≤ X.J0 K := by
    rw [hJ, le_div_iff₀ hk0]
    have : 1 * X.b' ≤ LaI K.C₀ X.N₁ (X.a : ℝ) * X.b' := mul_le_mul_of_nonneg_right hLa' hb.le
    linarith
  have jb : X.J0 K ≤ X.b' / 216 := by
    rw [hJ, div_le_div_iff₀ hk0 (by norm_num)]
    have h1 : 216 * LaI K.C₀ X.N₁ (X.a : ℝ) ≤ (X.m : ℝ) + 1 := by
      have e1 : (108 : ℝ) * 2 ≤ X.Yb * X.TT.card := mul_le_mul (by linarith) hN2 (by norm_num) (by linarith)
      have e2 : 108 * 2 * LaI K.C₀ X.N₁ (X.a : ℝ) ≤ X.Yb * X.TT.card * LaI K.C₀ X.N₁ (X.a : ℝ) :=
        mul_le_mul_of_nonneg_right e1 (by linarith)
      linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hb.le
    linarith
  have hx0 : 0 ≤ X.ar + X.ar / (((X.m : ℝ) + 1) * X.Y) := by
    have : 0 ≤ X.ar := by linarith
    positivity
  refine ⟨j3, jb, hccl, ?_, Nat.floor_le (by linarith), Nat.floor_le hx0, Nat.lt_floor_add_one _,
    Nat.floor_le (by linarith), by linarith, by linarith, Nat.le_ceil _⟩
  have : 3 ≤ X.Jn K := Nat.le_floor (by exact_mod_cast j3)
  exact_mod_cast this

theorem cb_of {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) : CBoundI 4 X.p X.m X.TT X.a X.ccl X.cStar X.c4 := by
  obtain ⟨-, -, h3, -⟩ := logs_of B
  unfold CBoundI Dat.c4 Dat.N
  push_cast
  have h1 : (0 : ℝ) ≤ (X.TT.card : ℝ) * ((X.m : ℝ) + 1) * Real.logb X.p X.a := by positivity
  have h2 : (0 : ℝ) ≤ (X.TT.card : ℝ) * X.ccl := by positivity
  have h4 : (0 : ℝ) ≤ (X.n' : ℝ) * X.ccl := by positivity
  have h5 : (0 : ℝ) ≤ (X.cStar : ℝ) := by positivity
  linarith

theorem D0nn_of {K : Cst} (hK : K.Pos) {CH : ℝ} {X : Dat} (B : Base K CH X) : 0 ≤ X.D0 K := by
  obtain ⟨h1, -, h3, -⟩ := logs_of B
  rw [D0_eq_numSeg_mul_add]
  have hCA : 0 < K.CA := hK.2.2.1
  have hk : 0 ≤ X.k := by linarith [B.hk5]
  have hlg : 0 ≤ lgA X.p X.a X.m := by linarith
  positivity

theorem small_depth_le_large_depth (K : Cst) (X : Dat) : X.D0 K ≤ X.D1 K := by
  unfold Dat.D1
  have : (0 : ℝ) ≤ 4 * (X.N : ℝ) * X.u0c := by positivity
  linarith

theorem window_lower_bound_of_base {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) (J : JFacts K X) :
    (X.a : ℝ) + X.a / (((X.m : ℝ) + 1) * X.Y) ≤ ((X.ua + X.Jn K + X.ccl : ℕ) : ℝ) := by
  have hk5 : (5 : ℝ) ≤ (X.m : ℝ) + 1 := B.hk5
  have hkY : 1 ≤ ((X.m : ℝ) + 1) * X.Y := one_le_mul_of_one_le_of_one_le (by linarith) B.hY
  have hkY0 : 0 < ((X.m : ℝ) + 1) * X.Y := by linarith
  have h1 : (X.a : ℝ) / (((X.m : ℝ) + 1) * X.Y) ≤ X.ar / (((X.m : ℝ) + 1) * X.Y) + 1 := by
    have e1 : (X.a : ℝ) / (((X.m : ℝ) + 1) * X.Y) ≤ (X.ar + 1) / (((X.m : ℝ) + 1) * X.Y) :=
      div_le_div_of_nonneg_right B.haa1.le hkY0.le
    have e2 : 1 / (((X.m : ℝ) + 1) * X.Y) ≤ 1 := (div_le_one hkY0).2 hkY
    rw [add_div] at e1
    linarith
  push_cast
  have := J.ualt
  have := J.jn3
  have := B.haa1
  have : (0 : ℝ) ≤ X.ccl := by positivity
  linarith

theorem winA_of {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) (J : JFacts K X) :
    ((X.ua + X.Jn K + X.ccl : ℕ) : ℝ) ≤ X.a + X.a / (((X.m : ℝ) + 1) * X.Y) + 2 * X.J0 K := by
  have hk5 : (5 : ℝ) ≤ (X.m : ℝ) + 1 := B.hk5
  have hkY0 : 0 < ((X.m : ℝ) + 1) * X.Y := mul_pos (by linarith) (by linarith [B.hY])
  have e1 : X.ar / (((X.m : ℝ) + 1) * X.Y) ≤ (X.a : ℝ) / (((X.m : ℝ) + 1) * X.Y) :=
    div_le_div_of_nonneg_right B.haa hkY0.le
  push_cast
  linarith [J.uale, J.jnle, J.cj, B.haa]

theorem winB_of {K : Cst} {X : Dat} (J : JFacts K X) :
    ((X.ub + X.Jn K + X.ccl : ℕ) : ℝ) ≤ X.bu + 2 * X.J0 K := by
  push_cast
  linarith [J.uble, J.jnle, J.cj]

theorem jA_of {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) (J : JFacts K X) : X.Jn K ≤ X.a := by
  have h : (X.Jn K : ℝ) ≤ X.a := by linarith [J.jnle, J.jb, b_le_a B, B.hb8]
  exact_mod_cast h

theorem jB_of {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) (J : JFacts K X) : X.Jn K ≤ X.lb := by
  have h : (X.Jn K : ℝ) ≤ X.lb := by linarith [J.jnle, J.jb, J.blge, J.lbge, B.hb8]
  exact_mod_cast h

theorem degree_sum_le_eight_mul {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) (J : JFacts K X) :
    (X.ua + X.Jn K + X.ccl) + (X.ub + X.Jn K + X.ccl) + 1 ≤ 8 * X.a := by
  have hk5 : (5 : ℝ) ≤ (X.m : ℝ) + 1 := B.hk5
  have hkY : 1 ≤ ((X.m : ℝ) + 1) * X.Y := one_le_mul_of_one_le_of_one_le (by linarith) B.hY
  have h200 := two_hundred_le_radius B
  have e1 : X.ar / (((X.m : ℝ) + 1) * X.Y) ≤ X.ar := div_le_self (by linarith) hkY
  have h : ((X.ua : ℝ) + X.Jn K + X.ccl) + ((X.ub : ℝ) + X.Jn K + X.ccl) + 1 ≤ 8 * (X.a : ℝ) := by
    linarith [J.uale, J.jnle, J.cj, J.jb, J.uble, J.bule, b_le_a B, B.haa, B.hb8]
  exact_mod_cast h

theorem logl_of {K : Cst} (hK : K.Pos) {CH : ℝ} (hCH : K.TM ≤ CH) {X : Dat} (h : X.Hyp K.C₀ CH) (B : Base K CH X) :
    ((X.m : ℝ) + 1) * X.Y ^ 2 * Real.log X.a ≤ X.a / X.b' := by
  have H' := hyp_round hK hCH h B
  have h16 := H'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨l1, -, -⟩ := La_round hK B
  obtain ⟨g1, -⟩ := log_round B
  have hT : K.TLP ≤ CH := le_trans (le_max_left _ _) hCH
  have h108 : (108 : ℝ) ≤ CH := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hYbC : CH ≤ X.Yb := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk5 : (5 : ℝ) ≤ (X.m : ℝ) + 1 := B.hk5
  have hN2 : (2 : ℝ) ≤ (X.TT.card : ℝ) := B.hN2
  have hLa' : 1 ≤ LaI K.C₀ X.N₁ (X.a : ℝ) := le_trans B.hLa1 l1
  have hl : 0 ≤ Real.log (X.a : ℝ) := by linarith [B.hlog1]
  refine le_trans ?_ h16
  have e1 : (1 : ℝ) ≤ X.Yb / 2 * X.TT.card * LaI K.C₀ X.N₁ (X.a : ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)) hLa'
  have hP : 0 ≤ ((X.m : ℝ) + 1) * X.Y ^ 2 * Real.log X.a := by positivity
  have e2 := mul_le_mul_of_nonneg_left e1 hP
  calc _ = ((X.m : ℝ) + 1) * X.Y ^ 2 * Real.log X.a * 1 := by ring
    _ ≤ _ := e2
    _ = _ := by ring

theorem multiplicity_bound_nonneg (K : Cst) (hK : K.Pos) (X : Dat) : 0 ≤ m0I K.Cm X.p X.m X.G' X.N₁ X.c4 := by
  unfold m0I m0G4 m1G4
  have : 0 < K.Cm := hK.2.2.2.2.2.1
  positivity

theorem multiplicity_bound_abstract (Cm CH k N1 Q Y N c S b' : ℝ) (hCm : 0 < Cm) (hCH : 2 * Cm + 24 ≤ CH) (hk : 1 ≤ k) (hN1 : 1 ≤ N1)
    (hQ : 1 ≤ Q) (hY : 1 ≤ Y) (hc0 : 0 ≤ c)
    (hsz : CH * (k ^ 2 * N1 * Q ^ 2 * Y) * (c / 2) ≤ b') :
    (Cm * k * N1 * Q * c + 12 * c) * (k * Q * Y) ≤ b' := by
  refine le_trans ?_ hsz
  have hP : 0 ≤ k ^ 2 * N1 * Q ^ 2 * Y * (c / 2) := by positivity
  have e1 := mul_le_mul_of_nonneg_right hCH hP
  have e2 : k * Q * Y * c ≤ k ^ 2 * N1 * Q ^ 2 * Y * c := by
    have a1 : (1 : ℝ) ≤ k * N1 * Q := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hk hN1) hQ
    have a2 : 0 ≤ k * Q * Y * c := by positivity
    have := mul_le_mul_of_nonneg_right a1 a2
    calc k * Q * Y * c = 1 * (k * Q * Y * c) := by ring
      _ ≤ k * N1 * Q * (k * Q * Y * c) := this
      _ = _ := by ring
  calc (Cm * k * N1 * Q * c + 12 * c) * (k * Q * Y) = Cm * (k ^ 2 * N1 * Q ^ 2 * Y * c) + 12 * (k * Q * Y * c) := by
        ring
    _ ≤ Cm * (k ^ 2 * N1 * Q ^ 2 * Y * c) + 12 * (k ^ 2 * N1 * Q ^ 2 * Y * c) := by linarith
    _ = (2 * Cm + 24) * (k ^ 2 * N1 * Q ^ 2 * Y * (c / 2)) := by ring
    _ ≤ CH * (k ^ 2 * N1 * Q ^ 2 * Y * (c / 2)) := e1
    _ = _ := by ring

theorem multiplicity_bound_le_ratio {K : Cst} (hK : K.Pos) {CH : ℝ} (hCH : K.TM ≤ CH) {X : Dat} (B : Base K CH X) :
    m0I K.Cm X.p X.m X.G' X.N₁ X.c4 ≤ X.b' / (((X.m : ℝ) + 1) * (X.p : ℝ) ^ X.G' * X.Y) := by
  have hk5 : (5 : ℝ) ≤ (X.m : ℝ) + 1 := B.hk5
  have hk1 : (1 : ℝ) ≤ X.k := by linarith [B.hk5]
  have hQ := B.hQ
  have hY := B.hY
  have hpos : 0 < ((X.m : ℝ) + 1) * (X.p : ℝ) ^ X.G' * X.Y := by
    have : (0 : ℝ) < (X.p : ℝ) ^ X.G' := by linarith
    have : (0 : ℝ) < X.Y := by linarith
    positivity
  rw [le_div_iff₀ hpos]
  unfold m0I m0G4 m1G4
  have hCm : 2 * K.Cm + 24 ≤ CH := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCH
  have sq_level_le_degree : (X.N₁ : ℝ) ≤ X.k := le_trans (le_self_pow₀ B.hN1 (by norm_num)) B.sq_level_le_degree
  have hw : X.k ^ 2 * X.N₁ * ((X.p : ℝ) ^ X.G') ^ 2 * X.Y ≤ X.k ^ 3 * X.N * ((X.p : ℝ) ^ X.G') ^ 4 * X.Y := by
    have a1 : X.k ^ 2 * X.N₁ ≤ X.k ^ 3 * X.N := by
      have : X.k ^ 2 * X.N₁ ≤ X.k ^ 2 * X.k := mul_le_mul_of_nonneg_left sq_level_le_degree (by positivity)
      have h2 : X.k ^ 3 * 1 ≤ X.k ^ 3 * X.N := mul_le_mul_of_nonneg_left (by linarith [B.hN2]) (by positivity)
      calc X.k ^ 2 * X.N₁ ≤ X.k ^ 2 * X.k := this
        _ = X.k ^ 3 * 1 := by ring
        _ ≤ _ := h2
    have a2 : ((X.p : ℝ) ^ X.G') ^ 2 ≤ ((X.p : ℝ) ^ X.G') ^ 4 := pow_le_pow_right₀ hQ (by norm_num)
    have a3 : X.k ^ 2 * X.N₁ * ((X.p : ℝ) ^ X.G') ^ 2 ≤ X.k ^ 3 * X.N * ((X.p : ℝ) ^ X.G') ^ 4 :=
      mul_le_mul a1 a2 (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right a3 (by linarith)
  have hu : (X.c4 : ℝ) / 2 ≤ (X.cStar : ℝ) + X.N * X.ccl + X.n' * X.ccl := by
    unfold Dat.c4
    push_cast
    have : (0 : ℝ) ≤ X.cStar := by positivity
    linarith
  have hsz := B.hsz _ _ (by positivity) hw (by positivity) hu
  exact multiplicity_bound_abstract K.Cm CH X.k X.N₁ ((X.p : ℝ) ^ X.G') X.Y X.N X.c4 0 X.b' hK.2.2.2.2.2.1 hCm hk1 B.hN1 hQ hY
    (by positivity) hsz

theorem fixed_weight_facts_of_hyp {K : Cst} (hK : K.Pos) {CH : ℝ} (hCH : K.TM ≤ CH) {X : Dat} (h : X.Hyp K.C₀ CH) : FixedWeightNumericalFacts K X := by
  have hT : K.TLP ≤ CH := le_trans (le_max_left _ _) hCH
  have B := base_of K hK CH hT X h
  have J := jFacts_of hK hCH h B
  have hd := dle_of hK hT h B
  have hcs : 8 * (X.Dp + 1) ≤ X.cStar := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h4 := four_depth_lt_conductor_of_bounds hd hcs
  have h1nn := D1nn_of hK B
  have hm : 2 * X.N₁ + 2 ≤ X.m := h.2.2.2.2.2.2.1
  exact ⟨hyp_round hK hCH h B, cb_of B, by linarith [small_depth_le_large_depth K X], D0nn_of hK B, by linarith, by linarith [J.j3],
    winA_of B J, winB_of J, jA_of B J, jB_of B J, degree_sum_le_eight_mul B J, by omega⟩

theorem mean_kappa_facts_of_hyp {K : Cst} (hK : K.Pos) {CH : ℝ} (hCH : K.TM ≤ CH) {X : Dat} (h : X.Hyp K.C₀ CH) : MeanKappaNumericalFacts K X := by
  have hT : K.TLP ≤ CH := le_trans (le_max_left _ _) hCH
  have B := base_of K hK CH hT X h
  have J := jFacts_of hK hCH h B
  exact ⟨hyp_round hK hCH h B, cb_of B, by linarith [J.j3], window_lower_bound_of_base B J, winA_of B J, winB_of J,
    logl_of hK hCH h B, multiplicity_bound_nonneg K hK X, multiplicity_bound_le_ratio hK hCH B⟩

theorem threshold_fixed_weight_facts (K : Cst) (hK : K.Pos) : TransportedAlt K (fun _ => FixedWeightNumericalFacts K) :=
  ⟨K.TM, 1, TM_pos K, one_pos, fun _ hCH _ _ _ h => fixed_weight_facts_of_hyp hK hCH h⟩

theorem threshold_mean_kappa_facts (K : Cst) (hK : K.Pos) : TransportedAlt K (fun _ => MeanKappaNumericalFacts K) :=
  ⟨K.TM, 1, TM_pos K, one_pos, fun _ hCH _ _ _ h => mean_kappa_facts_of_hyp hK hCH h⟩

end Formalism.MainNotions.flipOneThree.Pf

end
end

section
namespace Formalism.MainNotions.flipOneThree.Pf

private theorem exists_linearMap_prod_rename_eq {K : Type} [Field K] (I β γ : Type) [Fintype I] [DecidableEq I]
    (f : I → MvPolynomial β K →ₗ[K] MvPolynomial γ K) :
    ∃ Φ : MvPolynomial (I × β) K →ₗ[K] MvPolynomial (I × γ) K,
      ∀ P : I → MvPolynomial β K,
        Φ (∏ i, MvPolynomial.rename (fun v : β => (i, v)) (P i)) =
          ∏ i, MvPolynomial.rename (fun v : γ => (i, v)) (f i (P i)) := by
  classical
  let Φ : MvPolynomial (I × β) K →ₗ[K] MvPolynomial (I × γ) K :=
    (MvPolynomial.basisMonomials (I × β) K).constr K
      (fun m => ∏ i, MvPolynomial.rename (fun v : γ => (i, v))
        (f i (MvPolynomial.monomial (m.curry i) 1)))
  have hΦb : ∀ m, Φ (MvPolynomial.basisMonomials (I × β) K m) =
      ∏ i, MvPolynomial.rename (fun v : γ => (i, v))
        (f i (MvPolynomial.monomial (m.curry i) 1)) :=
    fun m => Module.Basis.constr_basis _ _ _ _
  have hcur : ∀ (g : I → β →₀ ℕ) (i : I),
      (∑ j, Finsupp.mapDomain (fun v : β => (j, v)) (g j)).curry i = g i := by
    intro g i
    ext b
    rw [Finsupp.curry_apply, Finsupp.finset_sum_apply, Finset.sum_eq_single i]
    · exact Finsupp.mapDomain_apply (fun a c h => (Prod.ext_iff.1 h).2) _ _
    · intro j _ hj
      apply Finsupp.mapDomain_notin_range
      rintro ⟨c, hc⟩
      exact hj (congrArg Prod.fst hc)
    · intro h
      exact absurd (Finset.mem_univ i) h
  refine ⟨Φ, fun P => ?_⟩
  let L : MultilinearMap K (fun _ : I => MvPolynomial β K) (MvPolynomial (I × γ) K) :=
    Φ.compMultilinearMap ((MultilinearMap.mkPiAlgebra K I (MvPolynomial (I × β) K)).compLinearMap
      (fun i => (MvPolynomial.rename (fun v : β => (i, v))).toLinearMap))
  let M : MultilinearMap K (fun _ : I => MvPolynomial β K) (MvPolynomial (I × γ) K) :=
    (MultilinearMap.mkPiAlgebra K I (MvPolynomial (I × γ) K)).compLinearMap
      (fun i => (MvPolynomial.rename (fun v : γ => (i, v))).toLinearMap ∘ₗ f i)
  have hLM : L = M := by
    refine Module.Basis.ext_multilinear (fun _ => MvPolynomial.basisMonomials β K) fun g => ?_
    simp only [L, M, LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, MvPolynomial.coe_basisMonomials, AlgHom.toLinearMap_apply,
      LinearMap.comp_apply, MvPolynomial.rename_monomial]
    rw [← MvPolynomial.monomial_sum_one]
    have hb : (MvPolynomial.monomial (∑ i, Finsupp.mapDomain (fun v : β => (i, v)) (g i)) (1 : K)) =
        MvPolynomial.basisMonomials (I × β) K (∑ i, Finsupp.mapDomain (fun v : β => (i, v)) (g i)) := by
      rw [MvPolynomial.coe_basisMonomials]
    rw [hb, hΦb]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hcur]
  have h := congrArg (fun F => F P) hLM
  simpa [L, M] using h

theorem existsIO' : ExistsIO := by
  intro K _ S α _ _ TT i
  classical
  let f : S → MvPolynomial α K →ₗ[K] MvPolynomial (Bool × α) K := fun s =>
    if h : s ∈ TT then i ⟨s, h⟩
    else (MvPolynomial.aeval (fun _ : α => (0 : MvPolynomial (Bool × α) K))).toLinearMap
  obtain ⟨Φ, hΦ⟩ := exists_linearMap_prod_rename_eq (K := K) S α (Bool × α) f
  let ψ : MvPolynomial (S × (Bool × α)) K →ₐ[K] MvPolynomial ((TT × Bool) × α) K :=
    MvPolynomial.aeval (fun x : S × (Bool × α) =>
      if h : x.1 ∈ TT then (MvPolynomial.X ((⟨x.1, h⟩, x.2.1), x.2.2) : MvPolynomial ((TT × Bool) × α) K)
      else 0)
  refine ⟨ψ.toLinearMap ∘ₗ Φ, fun P hP => ?_⟩
  rw [LinearMap.comp_apply, hΦ, AlgHom.toLinearMap_apply, map_prod]
  have key : ∀ s : S, ψ (MvPolynomial.rename (fun v : Bool × α => (s, v)) (f s (P s))) =
      if h : s ∈ TT then
        MvPolynomial.rename (fun v : Bool × α => (((⟨s, h⟩ : TT), v.1), v.2)) (i ⟨s, h⟩ (P s))
      else 1 := by
    intro s
    by_cases h : s ∈ TT
    · rw [dif_pos h]
      have hf : f s = i ⟨s, h⟩ := by simp only [f, dif_pos h]
      rw [hf]
      have hc : ψ.comp (MvPolynomial.rename (fun v : Bool × α => (s, v))) =
          MvPolynomial.rename (fun v : Bool × α => (((⟨s, h⟩ : TT), v.1), v.2)) := by
        apply MvPolynomial.algHom_ext
        intro v
        simp [ψ, h]
      exact congrArg (fun F : MvPolynomial (Bool × α) K →ₐ[K] MvPolynomial ((TT × Bool) × α) K =>
        F (i ⟨s, h⟩ (P s))) hc
    · rw [dif_neg h]
      have hf : f s = (MvPolynomial.aeval (fun _ : α => (0 : MvPolynomial (Bool × α) K))).toLinearMap := by
        simp only [f, dif_neg h]
      rw [hf, hP s h]
      simp
  rw [Finset.prod_congr rfl fun s _ => key s]
  rw [← Finset.prod_subset (Finset.subset_univ TT) (fun s _ hs => dif_neg hs)]
  rw [← Finset.prod_coe_sort TT]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [dif_pos s.2]

theorem existsPR' : ExistsPR := by
  intro K _ S α _ _ TT pr
  obtain ⟨Φ, hΦ⟩ := exists_linearMap_prod_rename_eq (K := K) TT (Bool × α) α pr
  refine ⟨(MvPolynomial.rename (fun x : TT × α => ((x.1 : S), x.2))).toLinearMap ∘ₗ Φ ∘ₗ
    (MvPolynomial.rename (fun x : (TT × Bool) × α => (x.1.1, (x.1.2, x.2)))).toLinearMap, fun Y => ?_⟩
  have h1 : (MvPolynomial.rename (fun x : (TT × Bool) × α => (x.1.1, (x.1.2, x.2))))
      (∏ s : TT, MvPolynomial.rename (fun v : Bool × α => ((s, v.1), v.2)) (Y s)) =
      ∏ s : TT, MvPolynomial.rename (fun v : Bool × α => (s, v)) (Y s) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun s _ => (MvPolynomial.rename_rename _ _ _).trans rfl
  have h2 : ∀ s : TT, MvPolynomial.rename (fun x : TT × α => ((x.1 : S), x.2))
      (MvPolynomial.rename (fun v : α => (s, v)) (pr s (Y s))) =
      MvPolynomial.rename (fun v : α => ((s : S), v)) (pr s (Y s)) :=
    fun s => (MvPolynomial.rename_rename _ _ _).trans rfl
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [h1, hΦ, map_prod]
  exact Finset.prod_congr rfl fun s _ => h2 s

theorem regroupP : RegroupP := fun _ _ _ _ _ _ _ _ _ N y hy => KP.regroup N y hy

theorem functor_comparison_of_single_weight_facts (h : SingleWeightLatticeComparison) : LatticeFunctorComparison := functor_comparison_of_single_weight existsIO' existsPR' regroupP h

end Formalism.MainNotions.flipOneThree.Pf
end

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems

theorem restLeLat : RestLeLat := by
  intro p n' R m e he s
  obtain ⟨gs, hgs, -, h2, -⟩ := edgeLat_RS R e he
  refine ⟨_, ?_, h2 s⟩
  rw [Matrix.det_mul]
  exact (hgs s).mul (lb_D_det (m + 1) 1 _ (RS.w_ne R))

theorem restTensor : RestTensor := restTensor_of restLeLat

end Formalism.MainNotions.flipOneThree.Pf

end
end

section
namespace Formalism.MainNotions.flipOneThree.Pf.KP

def BlockSplit : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {J : Type} [Fintype J] (n : ℕ) (z : O), z ≠ 0 →
    ∀ (A : J → Matrix (Fin n) (Fin n) O), ∑ j, A j = z • (1 : Matrix (Fin n) (Fin n) O) →
    ∃ ν : J → ℕ, n ≤ ∑ j, ν j ∧ ∀ j, ∃ (P : Matrix (Fin (ν j)) (Fin n) O) (Q : Matrix (Fin n) (Fin (ν j)) O),
      P * A j * Q = z • (1 : Matrix (Fin (ν j)) (Fin (ν j)) O)

open Module

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private noncomputable def bspZ (n : ℕ) (z : O) : Submodule O (Fin n → O) :=
  LinearMap.range (z • (LinearMap.id : (Fin n → O) →ₗ[O] (Fin n → O)))

private theorem bsp_one (n : ℕ) (z : O) (A : Matrix (Fin n) (Fin n) O) :
    ∃ (ν : ℕ) (v : Fin ν → (Fin n → O)),
      LinearMap.range (Matrix.mulVecLin A) ≤
        Submodule.span O (Set.range v) ⊔ IsLocalRing.maximalIdeal O • bspZ n z ∧
      ∃ (P : Matrix (Fin ν) (Fin n) O) (Q : Matrix (Fin n) (Fin ν) O),
        P * A * Q = z • (1 : Matrix (Fin ν) (Fin ν) O) := by
  classical
  haveI : ValuationRing O :=
    ((IsDiscreteValuationRing.TFAE O (IsDiscreteValuationRing.not_isField O)).out 0 1).mp
      (inferInstance : IsDiscreteValuationRing O)
  obtain ⟨m, S⟩ := Submodule.smithNormalForm (Pi.basisFun O (Fin n))
    (LinearMap.range (Matrix.mulVecLin A))
  let T : Finset (Fin m) := Finset.univ.filter (fun k => S.a k ∣ z)
  let e : Fin T.card ≃ T := T.equivFin.symm
  choose x hx using fun k : Fin m => (S.bN k).2
  have hc : ∀ t : T, ∃ c, z = S.a t.1 * c := fun t => (Finset.mem_filter.mp t.2).2
  choose c hc' using hc
  let w : Fin T.card → (Fin n → O) := fun i => c (e i) • x (e i).1
  have hAw : ∀ i, Matrix.mulVec A (w i) = z • S.bM (S.f (e i).1) := by
    intro i
    have h1 := hx (e i).1
    rw [Matrix.mulVecLin_apply] at h1
    show Matrix.mulVec A (c (e i) • x (e i).1) = _
    rw [Matrix.mulVec_smul, h1, S.snf, smul_smul, hc' (e i), mul_comm]
  refine ⟨T.card, fun i => S.bM (S.f (e i).1), ?_, ?_⟩
  · intro y hy
    have e2 := congrArg Subtype.val (S.bN.sum_repr ⟨y, hy⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e2
    rw [← e2]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    rw [S.snf]
    by_cases hk : S.a k ∣ z
    · apply Submodule.mem_sup_left
      apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨e.symm ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩, by simp⟩
    · apply Submodule.mem_sup_right
      obtain ⟨d, hd⟩ := (ValuationRing.dvd_total (S.a k) z).resolve_left hk
      have hdm : d ∈ IsLocalRing.maximalIdeal O := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact hk ⟨↑hu.unit⁻¹, by rw [hd, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
      rw [hd, mul_comm, ← smul_smul]
      exact Submodule.smul_mem_smul hdm ⟨S.bM (S.f k), rfl⟩
  · refine ⟨Matrix.of fun i r => S.bM.coord (S.f (e i).1) (fun j => if r = j then 1 else 0),
      Matrix.of fun r i => w i r, ?_⟩
    ext i i'
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    have hcol : ∀ r, (A * Matrix.of fun r i => w i r) r i' = (z • S.bM (S.f (e i').1)) r := by
      intro r
      rw [← hAw i']
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    simp only [hcol, Matrix.of_apply]
    have hφ : ∑ r, S.bM.coord (S.f (e i).1) (fun j => if r = j then 1 else 0) *
        (z • S.bM (S.f (e i').1)) r = S.bM.coord (S.f (e i).1) (z • S.bM (S.f (e i').1)) := by
      rw [LinearMap.pi_apply_eq_sum_univ (S.bM.coord (S.f (e i).1)) (z • S.bM (S.f (e i').1))]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [smul_eq_mul, mul_comm]
    rw [hφ, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, smul_eq_mul]
    by_cases hii : i = i'
    · subst hii
      simp
    · have hne : S.f (e i).1 ≠ S.f (e i').1 := fun h =>
        hii (e.injective (Subtype.ext (S.f.injective h)))
      simp [Finsupp.single_apply, hne, hii]

theorem blockSplit {J : Type} [Fintype J] (n : ℕ) (z : O) (hz : z ≠ 0)
    (A : J → Matrix (Fin n) (Fin n) O) (h : ∑ j, A j = z • (1 : Matrix (Fin n) (Fin n) O)) :
    ∃ ν : J → ℕ, n ≤ ∑ j, ν j ∧ ∀ j, ∃ (P : Matrix (Fin (ν j)) (Fin n) O)
      (Q : Matrix (Fin n) (Fin (ν j)) O), P * A j * Q = z • (1 : Matrix _ _ O) := by
  classical
  choose ν v hv P Q hPQ using fun j => bsp_one n z (A j)
  refine ⟨ν, ?_, fun j => ⟨P j, Q j, hPQ j⟩⟩
  let V : (Σ j, Fin (ν j)) → (Fin n → O) := fun jk => v jk.1 jk.2
  let W : Submodule O (Fin n → O) := Submodule.span O (Set.range V)
  have hvW : ∀ j, Submodule.span O (Set.range (v j)) ≤ W := by
    intro j
    apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨j, k⟩, rfl⟩
  have hsum : ∀ (s : Finset J) (x : Fin n → O), Matrix.mulVec (∑ j ∈ s, A j) x = ∑ j ∈ s, Matrix.mulVec (A j) x := by
    intro s x
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Matrix.add_mulVec, ih]
  have hZ : bspZ n z ≤ W ⊔ IsLocalRing.maximalIdeal O • bspZ n z := by
    rintro _ ⟨x, rfl⟩
    have hx : (z • (LinearMap.id : (Fin n → O) →ₗ[O] (Fin n → O))) x = ∑ j, Matrix.mulVec (A j) x := by
      rw [LinearMap.smul_apply, LinearMap.id_apply, ← hsum, h, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    rw [hx]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact sup_le_sup_right (hvW j) _ (hv j ⟨x, rfl⟩)
  have hfg : (bspZ n z).FG := by
    unfold bspZ
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  have hjac : IsLocalRing.maximalIdeal O ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hZW : bspZ n z ≤ W := Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac hZ
  let f := z • (LinearMap.id : (Fin n → O) →ₗ[O] (Fin n → O))
  have hinj : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    exact smul_right_injective _ hz hxy
  have hli : LinearIndependent O (fun i : Fin n => f (Pi.basisFun O (Fin n) i)) :=
    (Pi.basisFun O (Fin n)).linearIndependent.map' f hinj
  have hle := linearIndependent_le_span' _ hli (Set.range V) (by
    rintro _ ⟨i, rfl⟩
    exact hZW ⟨_, rfl⟩)
  calc n = Fintype.card (Fin n) := (Fintype.card_fin n).symm
    _ ≤ Fintype.card (Set.range V) := by
        rw [Cardinal.mk_fintype] at hle
        exact_mod_cast hle
    _ ≤ Fintype.card (Σ j, Fin (ν j)) := Fintype.card_range_le V
    _ = ∑ j, ν j := by simp [Fintype.card_sigma]


end Formalism.MainNotions.flipOneThree.Pf.KP
end

section
namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem latRetract : LatRetract := by
  unfold LatRetract
  intro O K V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι ι' _ _ b b' io hio
  classical
  set L := Submodule.span O (Set.range b) with hL
  set L' := Submodule.span O (Set.range b') with hL'
  have hcoord : ∀ x ∈ L, ∀ i, ∃ a : O, algebraMap O K a = b.repr x i := by
    intro x hx i
    exact ⟨(b.restrictScalars O).repr ⟨x, hx⟩ i, Module.Basis.restrictScalars_repr_apply O b ⟨x, hx⟩ i⟩
  have hinj : Function.Injective io := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro F hF
    rw [LinearMap.mem_ker] at hF
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, b.repr F i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (b.ext_elem (fun j => by simp [h j]))
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hϖ0 : algebraMap O K ϖ ≠ 0 := fun h0 =>
      hϖ.ne_zero (IsFractionRing.injective O K (by rw [h0, map_zero]))
    have hmem : ((algebraMap O K ϖ)⁻¹ * (b.repr F i)⁻¹) • F ∈ L := by
      rw [← hio, map_smul, hF, smul_zero]
      exact Submodule.zero_mem _
    obtain ⟨a, ha⟩ := hcoord _ hmem i
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hi, mul_one] at ha
    apply hϖ.not_isUnit
    refine isUnit_iff_exists_inv.mpr ⟨a, ?_⟩
    apply IsFractionRing.injective O K
    rw [map_mul, ha, map_one, mul_inv_cancel₀ hϖ0]
  let φ : L →ₗ[O] L' :=
    LinearMap.codRestrict L' ((io.restrictScalars O).domRestrict L) (fun x => (hio x).2 x.2)
  have hφ : Function.Injective φ := fun x y h => Subtype.ext (hinj (congrArg Subtype.val h))
  haveI : Module.Finite O L' := Module.Finite.span_of_finite O (Set.finite_range b')
  haveI : NoZeroSMulDivisors O (L' ⧸ LinearMap.range φ) := by
    refine ⟨fun {a q} h => ?_⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    rcases eq_or_ne a 0 with ha | ha
    · exact Or.inl ha
    right
    rw [Submodule.Quotient.mk_eq_zero]
    obtain ⟨x, hx⟩ := h
    have hx' : io (x : V) = a • (y : V') := congrArg Subtype.val hx
    have hK : algebraMap O K a ≠ 0 := fun h0 =>
      ha (IsFractionRing.injective O K (by rw [h0, map_zero]))
    have hyio : (y : V') = io ((algebraMap O K a)⁻¹ • (x : V)) := by
      rw [map_smul, hx', ← algebraMap_smul K a (y : V'), smul_smul, inv_mul_cancel₀ hK, one_smul]
    have hmem : (algebraMap O K a)⁻¹ • (x : V) ∈ L := (hio _).1 (hyio ▸ y.2)
    exact ⟨⟨_, hmem⟩, Subtype.ext hyio.symm⟩
  haveI : Module.Free O (L' ⧸ LinearMap.range φ) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range φ).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  let pr : L' →ₗ[O] L' := LinearMap.id - s ∘ₗ (LinearMap.range φ).mkQ
  have hpr : ∀ y, pr y ∈ LinearMap.range φ := by
    intro y
    have h2 := LinearMap.congr_fun hs ((LinearMap.range φ).mkQ y)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2
    rw [← Submodule.ker_mkQ (LinearMap.range φ), LinearMap.mem_ker]
    simp only [pr, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h2, sub_self]
  let e := LinearEquiv.ofInjective φ hφ
  let r0 : L' →ₗ[O] L := e.symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range φ) pr hpr
  have hr0 : ∀ x : L, r0 (φ x) = x := by
    intro x
    have h1 : (LinearMap.range φ).mkQ (φ x) = 0 := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact LinearMap.mem_range_self φ x
    show e.symm (LinearMap.codRestrict _ pr hpr (φ x)) = x
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    simp [LinearMap.codRestrict_apply, h1, e, pr, LinearEquiv.ofInjective_apply]
  let ret : V' →ₗ[K] V := b'.constr K (fun j => ((r0 ⟨b' j, Submodule.subset_span ⟨j, rfl⟩⟩ : L) : V))
  have hA : ∀ y : L', ret (y : V') = (r0 y : V) := by
    have h3 : (ret.restrictScalars O) ∘ₗ L'.subtype = L.subtype ∘ₗ r0 := by
      refine (b'.restrictScalars O).ext (fun j => ?_)
      have hj : (b'.restrictScalars O) j = ⟨b' j, Submodule.subset_span ⟨j, rfl⟩⟩ :=
        Subtype.ext (Module.Basis.restrictScalars_apply _ _ _)
      rw [hj]
      simp [ret, Module.Basis.constr_basis]
    intro y
    exact LinearMap.congr_fun h3 y
  refine ⟨ret, ?_, ?_⟩
  · have h4 : ret ∘ₗ io = LinearMap.id := by
      refine b.ext (fun i => ?_)
      have hbi : b i ∈ L := Submodule.subset_span ⟨i, rfl⟩
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      have h5 := hA (φ ⟨b i, hbi⟩)
      rw [hr0] at h5
      exact h5
    intro F
    exact LinearMap.congr_fun h4 F
  · intro G hG
    rw [hA ⟨G, hG⟩]
    exact (r0 ⟨G, hG⟩).2

theorem cloud_prop_of_maps_basis (hC : RestCloudMaps) (hBP : BePerfect) (hD3 : DualHeightBasis) : CloudLowerBoundWeyl :=
  cloud_prop_of_maps_retraction_basis hC latRetract hBP hD3

theorem cloud_bound_of_maps (hC : RestCloudMaps) (hBP : BePerfect) (hD3 : DualHeightBasis) (hW : WeylV) : CloudWeightLowerBound :=
  cloud_bound_of_prop_and_weyl_dimension (cloud_prop_of_maps_basis hC hBP hD3) hW

end Formalism.MainNotions.flipOneThree.Pf
end

section
namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem tools_of_admitted_statements (D : Formalism.BasicNotions.D7) (hA : AdmBE D) : AdmT D := by
  obtain ⟨T0, _, h0⟩ := hA 4 (by norm_num)
  obtain ⟨T1, _, h1⟩ := h0 T0 le_rfl
  obtain ⟨T2, _, h2⟩ := h1 T1 T1 T1 le_rfl le_rfl le_rfl
  obtain ⟨CA, Ckap, Ct, Cs, _, _, _, _, hAdm⟩ := h2 T2 le_rfl
  exact hAdm.2.2.2.2

theorem thrFM (K : Cst) (hK : K.Pos) : TransportedAlt K (fun _ => FM K) :=
  (threshold_fixed_weight_facts K hK).and ((threshold_density_facts K hK).and ((threshold_mean_kappa_facts K hK).and (threshold_final_facts K hK)))

theorem restEdge : RestEdge := restEdge_of restFunct

theorem blockSplit' : BlockSplit := fun _ _ _ _ _ _ n z hz A h => KP.blockSplit n z hz A h

theorem second_estimate_of_restrictions (D : Formalism.BasicNotions.D7) (hR : LPRingIndep) (h61a : RhoSumLowerBoundEdge) (h62 : CloudWeightLowerBound) (h63 : ResidueClassCount) :
    SecondPartClosed D := by
  intro hA
  have hT := tools_of_admitted_statements D hA
  have h16 : PairedPathIndependence D := hT.2.2.2.2.2.2.2.2.2.2.2
  have hD : RestDims := restDims_of D h16.1 h16.2
  exact theorem_I_of_intermediate_bounds D FM hR (midLP_of rho_lower_bound_large_conductor h62 h63)
    (fun K hK => midMean_of D h61a rho_upper_bound_small_depth restEdge hD K hK) thrLP thrFM hA

theorem theorem_I_of_finer_open_statements (D : Formalism.BasicNotions.D7) (hR : LPRingIndep) (h61 : LatticeFunctorComparison) (hC : RestCloudMaps) : SecondPartClosed D := by
  intro hA
  have hT := tools_of_admitted_statements D hA
  have h16 : PairedPathIndependence D := hT.2.2.2.2.2.2.2.2.2.2.2
  have h13 : TypeDecompositionsCommute D := hT.2.2.2.2.2.2.2.2.1
  exact second_estimate_of_restrictions D hR (rho_sum_bound_of_maps_splitting (lattice_maps_of_functor_comparison h61) blockSplit') (cloud_bound_of_maps hC h13.2.2.1 h13.1 h16.2)
    (tensor_bound_of_order_bound restTensor restOrdBound h13.1 h13.2.1) hA

theorem theorem_I_of_lattice_functor_comparison (D : Formalism.BasicNotions.D7) (h61 : LatticeFunctorComparison) (hC : RestCloudMaps) : SecondPartClosed D := by
  intro hA
  have h12 : NestedTypeBound D := (tools_of_admitted_statements D hA).2.2.2.2.2.2.2.1
  exact theorem_I_of_finer_open_statements D (lpRingIndep_of'' h12.1 restOIso) h61 hC hA

theorem theorem_I_of_model_identification (D : Formalism.BasicNotions.D7) (hTie : TwoLetterModelIdentification) (hC : RestCloudMaps) : SecondPartClosed D :=
  theorem_I_of_lattice_functor_comparison D (functor_comparison_of_single_weight_facts (single_weight_of_model_identification hTie)) hC

theorem theorem_I_of_explicit_minor_map (D : Formalism.BasicNotions.D7) (hPsi : TiePsi) (hC : RestCloudMaps) : SecondPartClosed D :=
  theorem_I_of_model_identification D (model_identification_of_explicit_map hPsi) hC

end Formalism.MainNotions.flipOneThree.Pf
end

section
namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem ClosedA.mono {P Q : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop} (h : ClosedA P)
    (hPQ : ∀ a b c d e f g i j k, P a b c d e f g i j k → Q a b c d e f g i j k) : ClosedA Q := by
  intro Cc hCc
  obtain ⟨T0, hT0, h0⟩ := h Cc hCc
  refine ⟨T0, hT0, fun C₀ hC₀ => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C₀ hC₀
  refine ⟨T1, hT1, fun CE1 CE2 Cm a1 a2 a3 => ?_⟩
  obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 Cm a1 a2 a3
  refine ⟨T2, hT2, fun CH hCH => ?_⟩
  obtain ⟨CA, Ckap, Ct, Cs, b1, b2, b3, b4, hP⟩ := h2 CH hCH
  exact ⟨CA, Ckap, Ct, Cs, b1, b2, b3, b4, hPQ _ _ _ _ _ _ _ _ _ _ hP⟩

theorem ClosedP.mono {P Q : ℝ → ℝ → ℝ → Prop} (h : ClosedP P) (hPQ : ∀ a b c, P a b c → Q a b c) : ClosedP Q := by
  obtain ⟨T0, hT0, h0⟩ := h
  refine ⟨T0, hT0, fun C₀ hC₀ => ?_⟩
  obtain ⟨T2, C, hT2, hC, h1⟩ := h0 C₀ hC₀
  exact ⟨T2, C, hT2, hC, fun CH hCH => hPQ _ _ _ (h1 CH hCH)⟩

end Formalism.MainNotions.flipOneThree.Pf
end
