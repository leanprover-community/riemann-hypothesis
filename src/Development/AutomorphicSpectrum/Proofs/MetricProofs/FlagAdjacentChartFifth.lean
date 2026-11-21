import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameMinorValueFormulaStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockLUFactorization
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatementStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFirst
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSecond
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameLUMinorValue

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv

theorem lastCol_mem {N j : ℕ} {a ca : Fin N} (hj : j ≤ N) (hca : (ca : ℕ) = lastCol N j a) :
    ca ∈ stepCols N j a ∧ ∀ r ∈ stepCols N j a, r ≤ ca := by
  unfold lastCol at hca
  refine ⟨?_, ?_⟩
  · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs at hca ⊢ <;> omega
  · intro r hr
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hr
    rw [Fin.le_iff_val_le_val]
    split_ifs at hca hr <;> omega

theorem transv_mul_transv {N : ℕ} {ca cb : Fin N} (hne : ca ≠ cb) (s : ℂ) :
    (1 + Matrix.single cb ca s) * (1 + Matrix.single cb ca (-s)) = (1 : Matrix (Fin N) (Fin N) ℂ) := by
  rw [add_mul, one_mul, mul_add, mul_one, Matrix.single_mul_single_of_ne s cb ca cb hne (-s), add_zero,
    add_assoc, ← Matrix.single_add, neg_add_cancel, Matrix.single_zero, add_zero]

theorem main : ∀ (N j : ℕ) (a ca cb : Fin N) (L U : Matrix (Fin N) (Fin N) ℂ) (t' : ℂ), j ≤ N → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → IsBlockDiag j L → IsLowerUni L → IsBlockDiag j U → U.BlockTriangular id → (∀ c, U c c ≠ 0) → minorIJ (L * U * (1 + Matrix.single cb ca t')) (stepCols N j a) (stepCols N j a) ≠ 0 → ∃ (t : ℂ) (V : Matrix (Fin N) (Fin N) ℂ), IsBlockDiag j V ∧ V.BlockTriangular id ∧ (∀ c ∈ stepCols N j a, V c c ≠ 0) ∧ U * (1 + Matrix.single cb ca t') = (1 + Matrix.single cb ca t) * V := by
  intro N j a ca cb L U t' hj hca hcb hblk hL hLu hU hUt hUd hmin
  have hne : ca ≠ cb := by
    intro h
    have h1 := congrArg Fin.val h
    omega
  obtain ⟨hcaS, hmax⟩ := lastCol_mem hj hca
  have hLM : L * U * (1 + Matrix.single cb ca t') = L * (U * (1 + Matrix.single cb ca t')) :=
    Matrix.mul_assoc _ _ _
  set M := U * (1 + Matrix.single cb ca t') with hMdef
  have hMe : ∀ x y, M x y = U x y + if y = ca then U x cb * t' else 0 := by
    intro x y
    rw [hMdef, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
    split_ifs with hy
    · rw [hy, Matrix.mul_single_apply_same]
    · rw [Matrix.mul_single_apply_of_ne t' cb ca x y hy U]
  have hUz : ∀ x y : Fin N, y < x → U x y = 0 := fun x y h => hUt (show id y < id x from h)
  have hMut : ∀ x y : Fin N, y < x → x ≠ cb → M x y = 0 := by
    intro x y hxy hx
    rw [hMe, hUz x y hxy]
    split_ifs with hy
    · rw [hy] at hxy
      have h1 : cb < x := by
        rw [Fin.lt_iff_val_lt_val] at hxy ⊢
        have h2 : (x : ℕ) ≠ cb := fun h => hx (Fin.ext h)
        omega
      rw [hUz x cb h1]
      simp
    · simp
  have hMca : M ca ca ≠ 0 := by
    intro h0
    apply hmin
    rw [hLM]
    unfold minorIJ
    rw [dif_pos rfl]
    set f := (stepCols N j a).orderEmbOfFin (rfl : (stepCols N j a).card = (stepCols N j a).card) with hf
    have hfmem : ∀ r, f r ∈ stepCols N j a := fun r => Finset.orderEmbOfFin_mem _ _ r
    have hSmap : Finset.univ.map f.toEmbedding = stepCols N j a := Finset.map_orderEmbOfFin_univ _ _
    have hrange : Set.range f = ↑(stepCols N j a) := Finset.range_orderEmbOfFin _ _
    have hprod : (L * M).submatrix f f = L.submatrix f f * M.submatrix f f := by
      ext p q
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      have hfpS := hfmem p
      have hz : ∀ i ∈ (Finset.univ : Finset (Fin N)), i ∉ stepCols N j a → L (f p) i * M i (f q) = 0 := by
        intro i _ hi
        by_cases hic : (ca : ℕ) < i
        · have hfp := hmax (f p) hfpS
          have hlt : f p < i := by
            rw [Fin.le_iff_val_le_val] at hfp
            rw [Fin.lt_iff_val_lt_val]
            omega
          rw [hLu.2 (f p) i hlt, zero_mul]
        · have hLz : L (f p) i = 0 := by
            apply hL
            intro hiff
            simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hi hfpS
            unfold lastCol at hca
            split_ifs at hi hfpS hca
            · have h3 := hiff.mpr (by omega)
              omega
            · omega
          rw [hLz, zero_mul]
      have hm := Finset.sum_map Finset.univ f.toEmbedding (fun x => L (f p) x * M x (f q))
      rw [hSmap] at hm
      rw [← Finset.sum_subset (Finset.subset_univ (stepCols N j a)) hz]
      exact hm
    have hUT : (M.submatrix f f).IsUpperTriangular := by
      intro p q hpq
      rw [Matrix.submatrix_apply]
      have hfpcb : f p ≠ cb := by
        intro hfp
        have h4 := hmax (f p) (hfmem p)
        rw [hfp, Fin.le_iff_val_le_val] at h4
        omega
      exact hMut (f p) (f q) (f.strictMono hpq) hfpcb
    have hdetM : (M.submatrix f f).det = 0 := by
      rw [Matrix.det_of_upperTriangular hUT]
      obtain ⟨p0, hp0⟩ : ∃ p0, f p0 = ca := by
        have h1 : ca ∈ Set.range f := by
          rw [hrange]
          exact hcaS
        exact h1
      exact Finset.prod_eq_zero (Finset.mem_univ p0) (by rw [Matrix.submatrix_apply, hp0]; exact h0)
    rw [hprod, Matrix.det_mul, hdetM, mul_zero]
  have hMb : ∀ x y : Fin N, ¬((x : ℕ) < N - j ↔ (y : ℕ) < N - j) → M x y = 0 := by
    intro x y hxy
    rw [hMe, hU x y hxy]
    split_ifs with hy
    · rw [hy] at hxy
      rw [hU x cb (fun h => hxy (h.trans hblk.symm))]
      simp
    · simp
  set t := M cb ca / M ca ca with ht
  have hVe : ∀ x y, ((1 + Matrix.single cb ca (-t)) * M) x y = M x y + if x = cb then -t * M ca y else 0 := by
    intro x y
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
    split_ifs with hx
    · rw [hx, Matrix.single_mul_apply_same]
    · rw [Matrix.single_mul_apply_of_ne (-t) cb ca x y hx M]
  refine ⟨t, (1 + Matrix.single cb ca (-t)) * M, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    rw [hVe, hMb x y hxy]
    split_ifs with hx
    · rw [hx] at hxy
      rw [hMb ca y (fun h => hxy (hblk.symm.trans h))]
      simp
    · simp
  · intro x y hxy
    change y < x at hxy
    rw [hVe]
    by_cases hx : x = cb
    · rw [if_pos hx, hx]
      rw [hx] at hxy
      by_cases hy : y = ca
      · rw [hy, ht, neg_mul, div_mul_cancel₀ _ hMca, add_neg_cancel]
      · have hylt : y < ca := by
          rw [Fin.lt_iff_val_lt_val] at hxy ⊢
          have h2 : (y : ℕ) ≠ ca := fun h => hy (Fin.ext h)
          omega
        rw [hMe cb y, if_neg hy, hUz cb y hxy, hMe ca y, if_neg hy, hUz ca y hylt]
        simp
    · rw [if_neg hx, add_zero]
      exact hMut x y hxy hx
  · intro c hc
    rw [hVe]
    have hcle := hmax c hc
    have hccb : c ≠ cb := by
      intro h
      rw [h, Fin.le_iff_val_le_val] at hcle
      omega
    rw [if_neg hccb, add_zero]
    by_cases hcc : c = ca
    · rw [hcc]
      exact hMca
    · rw [hMe, if_neg hcc, add_zero]
      exact hUd c
  · rw [← Matrix.mul_assoc, transv_mul_transv hne t, Matrix.one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv
end
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.LU_twist_refactorization : ∀ (N j : ℕ) (a ca cb : Fin N) (L U : Matrix (Fin N) (Fin N) ℂ) (t' : ℂ), j ≤ N → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → IsBlockDiag j L → IsLowerUni L → IsBlockDiag j U → U.BlockTriangular id → (∀ c, U c c ≠ 0) → minorIJ (L * U * (1 + Matrix.single cb ca t')) (stepCols N j a) (stepCols N j a) ≠ 0 → ∃ (t : ℂ) (V : Matrix (Fin N) (Fin N) ℂ), IsBlockDiag j V ∧ V.BlockTriangular id ∧ (∀ c ∈ stepCols N j a, V c c ≠ 0) ∧ U * (1 + Matrix.single cb ca t') = (1 + Matrix.single cb ca t) * V := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv.main | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv.main <;> assumption)
end

section
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto

section Scale

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

def normScale (M : FlagModel y Ψ N j) (c : NonPluckerBlocks M.blk → ℂ) : Option K → ℂ
  | some k => if h : ∀ p, M.blk p ≠ some k then c ⟨k, h⟩ else 1
  | none => 1

theorem normScale_ne (M : FlagModel y Ψ N j) {c : NonPluckerBlocks M.blk → ℂ} (hc : ∀ k, c k ≠ 0) (o : Option K) :
    normScale M c o ≠ 0 := by
  cases o with
  | none => exact one_ne_zero
  | some k =>
    by_cases h : ∀ p, M.blk p ≠ some k
    · show dite _ _ _ ≠ 0
      rw [dif_pos h]
      exact hc ⟨k, h⟩
    · show dite _ _ _ ≠ 0
      rw [dif_neg h]
      exact one_ne_zero

theorem normScale_base (M : FlagModel y Ψ N j) (c : NonPluckerBlocks M.blk → ℂ) (k : NonPluckerBlocks M.blk) :
    normScale M c (some k.1) = c k := by
  simp [normScale, k.2]

theorem normScale_step (M : FlagModel y Ψ N j) (c : NonPluckerBlocks M.blk → ℂ) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) : normScale M c (some k) = 1 := by
  have h : ¬ ∀ p, M.blk p ≠ some k := fun h => h p hp
  show dite _ _ _ = 1
  rw [dif_neg h]

end Scale

theorem norm : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) ∧ SameOrbit (bl (Rb.A.chart kb (r (baseOf M k₀ z)))) (baseOf M k₀ z) ∧ ∃ (h' : Ψ → Matrix (Fin N) (Fin N) ℂ) (t' : ℂ), (∀ τ', IsBlockDiag j (h' τ') ∧ (h' τ').det ≠ 0) ∧ (∀ p k, M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, fstPt k₀ z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) * minorIJ (h' p.1) I (stepCols N j p.2)) ∧ ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k₀, sndPt k₀ z ⟨k₀, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) * minorIJ (h' τ * (1 + Matrix.single cb ca t')) I (stepCols N j a) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h hctx z hzO
  obtain ⟨hb, hba, hk₀, hca, hcb, hAV, hF, hBC, hr, -, -⟩ := hctx
  obtain ⟨hz, hsrc, hV₀, -, -⟩ := hzO
  have z₀ : fstPt k₀ z ∈ mcPts (mCoordIdeal y) :=
    CPts.comp_mem_mcPts (Pts.isBlockMap_v₀ k₀) (algebraMap Φ (RatFunc Φ)) (funext fun _ => rfl) hz
  have hbm : baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) := CPts.base_mem M z₀
  obtain ⟨hblm, hbl1, hblG, horb⟩ := hBC.2.2.2.2 _ hV₀
  rw [(Rb.A.chart kb).left_inv hsrc] at horb
  have horbit : SameOrbit (bl (Rb.A.chart kb (r (baseOf M k₀ z)))) (baseOf M k₀ z) :=
    orbit_trans (orbit_symm horb) (hr _ hbm)
  have hG : M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) := by
    rwa [← CovMap.mCoordIdeal_eq_of_sameOrbit horbit]
  refine ⟨hbm, hG, horbit, ?_⟩
  obtain ⟨c, hc, hce⟩ := id horbit
  let z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun q => normScale M c q.1 * z q
  have hz' : z' ∈ mcPts (wP M τ a k₀ ca cb) :=
    mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal _) _ (normScale_ne M hc) hz
  have hbase : basePart M.blk (fstPt k₀ z') = bl (Rb.A.chart kb (r (baseOf M k₀ z))) := by
    rw [hce]
    funext q
    show normScale M c (some q.1.1) * z _ = c q.1 * z _
    rw [normScale_base]
  have hval : ∀ s : M.Ω, valAt M.x s (basePart M.blk (fstPt k₀ z')) = valAt M.x s (baseOf M k₀ z) := fun s => by
    rw [hbase]
    exact CovMap.LocImg.valAt_orbit horbit hbm s
  obtain ⟨h', t', H, H'⟩ := (GlobalTheory.T.log_period_statement K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hba hk₀ hca hcb hAV F z' hF
    (by rw [hbase]; exact hblm) (by rw [hbase]; exact hblG) (by rw [hbase]; exact hbl1)).1 hz'
  refine ⟨h', t', H.2.1, fun p k hp => ?_, ?_⟩
  · obtain ⟨α, hα, e⟩ := H.2.2 p k hp
    refine ⟨α, hα, fun m => ?_⟩
    have e' := e m
    simp only [hval] at e'
    rw [← e']
    show z _ = normScale M c (some k) * z _
    rw [normScale_step M c hp, one_mul]
  · obtain ⟨α, hα, e⟩ := H'.2.2 (τ, a) k₀ hk₀
    refine ⟨α, hα, fun m => ?_⟩
    have e' := e m
    rw [Pts.basePart_snd M hk₀] at e'
    simp only [hval, Function.update_self] at e'
    rw [← e', Pts.snd_self, Pts.snd_self]
    show z _ = 1 * z _
    rw [one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_chart_tenth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) ∧ SameOrbit (bl (Rb.A.chart kb (r (baseOf M k₀ z)))) (baseOf M k₀ z) ∧ ∃ (h' : Ψ → Matrix (Fin N) (Fin N) ℂ) (t' : ℂ), (∀ τ', IsBlockDiag j (h' τ') ∧ (h' τ').det ≠ 0) ∧ (∀ p k, M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, fstPt k₀ z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) * minorIJ (h' p.1) I (stepCols N j p.2)) ∧ ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k₀, sndPt k₀ z ⟨k₀, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) * minorIJ (h' τ * (1 + Matrix.single cb ca t')) I (stepCols N j a) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto.norm
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_LU_minor_value : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (hh : Ψ → Matrix (Fin N) (Fin N) ℂ) (τ' : Ψ) (a' b' : Fin N) (z : (Σ k, ι k) → ℂ) (A L U : Matrix (Fin N) (Fin N) ℂ), M.IsFrame F → zb ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal zb) → IsBlockDiag j A → (hh τ')⁻¹ * A = L * U → IsBlockDiag j L → IsLowerUni L → IsBlockDiag j U → U.BlockTriangular id → (∀ c ∈ stepCols N j (stepOf N j b'), U c c ≠ 0) → b' < a' → ((a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) → (∀ k, M.blk (τ', stepOf N j b') = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j (stepOf N j b'))) → lowRead M F zb hh z τ' a' b' = L a' b' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.LowRead.main | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.LowRead.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.LowRead.main <;> assumption)
end

section
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem sameOrbit_sqZ_of_flags : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (zb₂ : (Σ k, baseIdx ι M.blk k) → ℂ) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) (H U : Ψ → Matrix (Fin N) (Fin N) ℂ) (V : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.blk (τ, a) = some k₀ → baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) → SameOrbit zb₂ (baseOf M k₀ z) → (∀ τ', IsBlockDiag j (U τ') ∧ (U τ').BlockTriangular id ∧ ∀ c, U τ' c c ≠ 0) → IsBlockDiag j V → V.BlockTriangular id → (∀ c ∈ stepCols N j a, V c c ≠ 0) → (∀ p k, M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, fstPt k₀ z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) * minorIJ (H p.1 * U p.1) I (stepCols N j p.2)) → (∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k₀, sndPt k₀ z ⟨k₀, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) * minorIJ (H τ * (1 + Matrix.single cb ca t) * V) I (stepCols N j a)) → SameOrbit (sqZ M F zb₂ H k₀ τ ca cb t) z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a k₀ ca cb F zb₂ z H U V t hτ hz hG ho hU hV hVt hVd h1 h2
  have hval : ∀ s, valAt M.x s zb₂ = valAt M.x s (baseOf M k₀ z) := fun s =>
    CovMap.LocImg.valAt_orbit ho hz s
  have block : ∀ o : Option K, ∃ c : ℂ, c ≠ 0 ∧ ∀ m : ι (o.getD k₀),
      sqZ M F zb₂ H k₀ τ ca cb t ⟨o, m⟩ = c * z ⟨o, m⟩ := by
    rintro (_ | k)
    · have e : ∃ p, M.blk p = some k₀ := ⟨_, hτ⟩
      have hc : e.choose = (τ, a) := M.blk_inj _ _ k₀ e.choose_spec hτ
      obtain ⟨α, hα, hm⟩ := (WSq.Pts.step_mul_right M.j_le a hV hVt hVd
        (fun m : ι k₀ => sndPt k₀ z ⟨k₀, m⟩)
        (fun m I => valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z))).1 h2
      refine ⟨α⁻¹, inv_ne_zero hα, fun m => ?_⟩
      have hs : sqZ M F zb₂ H k₀ τ ca cb t ⟨none, m⟩ =
          ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) *
            minorIJ (H τ * (1 + Matrix.single cb ca t)) I (stepCols N j a) := by
        show flagZ M F zb₂ (Function.update H τ (H τ * (1 + Matrix.single cb ca t))) ⟨k₀, m⟩ = _
        refine (dif_pos e).trans ?_
        simp only [hc, Function.update_self, hval]
      have hn : z ⟨none, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) *
          minorIJ (H τ * (1 + Matrix.single cb ca t)) I (stepCols N j a) :=
        (WSq.Pts.snd_self z m).symm.trans (hm m)
      rw [hs, hn, inv_mul_cancel_left₀ hα]
    · by_cases e : ∃ p, M.blk p = some k
      · obtain ⟨α, hα, hm⟩ := (WSq.Pts.step_mul_right M.j_le e.choose.2 (hU e.choose.1).1 (hU e.choose.1).2.1
          (fun c _ => (hU e.choose.1).2.2 c) (fun m : ι k => fstPt k₀ z ⟨k, m⟩)
          (fun m I => valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z))).1 (h1 e.choose k e.choose_spec)
        refine ⟨α⁻¹, inv_ne_zero hα, fun m => ?_⟩
        have hs : sqZ M F zb₂ H k₀ τ ca cb t ⟨some k, m⟩ =
            ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) *
              minorIJ (H e.choose.1) I (stepCols N j e.choose.2) := by
          show flagZ M F zb₂ H ⟨k, m⟩ = _
          refine (dif_pos e).trans ?_
          simp only [hval]
        have hn : z ⟨some k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) *
            minorIJ (H e.choose.1) I (stepCols N j e.choose.2) := hm m
        rw [hs, hn, inv_mul_cancel_left₀ hα]
      · obtain ⟨c, hc, hcz⟩ := ho
        have hk : ∀ p, M.blk p ≠ some k := fun p hp => e ⟨p, hp⟩
        refine ⟨c ⟨k, hk⟩, hc _, fun m => ?_⟩
        show flagZ M F zb₂ H ⟨k, m⟩ = _
        refine (dif_neg e).trans ?_
        rw [hcz]
        rfl
  choose c hc hcz using block
  exact ⟨c, hc, funext fun p => hcz p.1 p.2⟩

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_frame_value_formula : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (zb₂ : (Σ k, baseIdx ι M.blk k) → ℂ) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) (H U : Ψ → Matrix (Fin N) (Fin N) ℂ) (V : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.blk (τ, a) = some k₀ → baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) → SameOrbit zb₂ (baseOf M k₀ z) → (∀ τ', IsBlockDiag j (U τ') ∧ (U τ').BlockTriangular id ∧ ∀ c, U τ' c c ≠ 0) → IsBlockDiag j V → V.BlockTriangular id → (∀ c ∈ stepCols N j a, V c c ≠ 0) → (∀ p k, M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, fstPt k₀ z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) * minorIJ (H p.1 * U p.1) I (stepCols N j p.2)) → (∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k₀, sndPt k₀ z ⟨k₀, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) * minorIJ (H τ * (1 + Matrix.single cb ca t) * V) I (stepCols N j a)) → SameOrbit (sqZ M F zb₂ H k₀ τ ca cb t) z := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.WMan.sameOrbit_sqZ_of_flags
end

section
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, wRho M Rb τ k₀ ca cb F kb r h ε z ∈ wD ε V ∧ SameOrbit (wPhi M F bl h ε k₀ τ ca cb (wRho M Rb τ k₀ ca cb F kb r h ε z)) z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hctx z hz
  have hctx' := hctx
  obtain ⟨hb, hab, hk, hca, hcb, hy, hF, hBC, hr, hrc, hh⟩ := hctx'
  obtain ⟨hmem, hsrc, hV, hden, hden2⟩ := hz
  obtain ⟨hzb, hG, horb, h', t', hh', Hf, Hs⟩ := GlobalTheory.T.flag_adjacent_chart_tenth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h hctx z
    ⟨hmem, hsrc, hV, hden, hden2⟩
  have hS := Pts.same_summand hb hab hca hcb
  have hj := M.j_le
  set zb := baseOf M k₀ z with hzbdef
  set w := wRho M Rb τ k₀ ca cb F kb r h ε z with hw
  have hwB : wB ε w = Rb.A.chart kb (r zb) := by
    funext i
    simp [wB, hw, wRho, zb]
  have hwL : ∀ q, wL ε w q = lowRead M F zb h (fstPt k₀ z) q.1.1 q.1.2.1 q.1.2.2 := fun q => by
    simp [wL, hw, wRho, zb]
  have hwT : wT ε w = lowRead M F zb h (sndPt k₀ z) τ cb ca - lowRead M F zb h (fstPt k₀ z) τ cb ca := by
    simp [wT, hw, wRho, zb]
  refine ⟨show wB ε w ∈ V by rw [hwB]; exact hV, ?_⟩
  have hdu : ∀ τ', IsUnit (h τ').det := fun τ' => (hh τ').2.isUnit
  let G : Ψ → Matrix (Fin N) (Fin N) ℂ := fun τ' => (h τ')⁻¹ * h' τ'
  have hGb : ∀ τ', IsBlockDiag j (G τ') := fun τ' => ((hh τ').1.inv (hdu τ')).mul (hh' τ').1
  have hinvd : ∀ τ', ((h τ')⁻¹).det ≠ 0 := fun τ' h0 => by
    have h1 := Matrix.det_nonsing_inv_mul_det (h τ') (hdu τ')
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hGd : ∀ τ', (G τ').det ≠ 0 := fun τ' => by
    show ((h τ')⁻¹ * h' τ').det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hinvd τ') (hh' τ').2
  have hmin : ∀ τ' i, IsProperStep N j i → minorIJ (G τ') (stepCols N j i) (stepCols N j i) ≠ 0 := by
    intro τ' i hi h0
    obtain ⟨k, hp⟩ : ∃ k, M.blk (τ', i) = some k := Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
    obtain ⟨α, hα, hz₁⟩ := Hf (τ', i) k hp
    refine hden (τ', i) k hp ?_
    rw [GlobalTheory.T.frame_minor_value_formula K ι Φ y Ψ N j M F zb (τ', i) k (h' τ') (h τ')⁻¹ (fstPt k₀ z) α _ hF hzb hG hp (hh' τ').1 hz₁]
    show α * minorIJ (G τ') _ _ = 0
    rw [h0, mul_zero]
  choose L U hLb hLu hUb hUt hUd hLU using fun τ' => GlobalTheory.T.block_LU_factorization N j (G τ') hj (hGb τ') (hGd τ') (hmin τ')
  have hhL : ∀ τ', h τ' * (L τ' * U τ') = h' τ' := fun τ' => by
    rw [← hLU]
    exact Matrix.mul_nonsing_inv_cancel_left _ _ (hdu τ')
  have hlow : ∀ τ' (a' b' : Fin N), b' < a' → ((a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) →
      lowRead M F zb h (fstPt k₀ z) τ' a' b' = L τ' a' b' := fun τ' a' b' e e' =>
    GlobalTheory.T.frame_LU_minor_value K ι Φ y Ψ N j M F zb h τ' a' b' (fstPt k₀ z) (h' τ') (L τ') (U τ') hF hzb hG (hh' τ').1 (hLU τ')
      (hLb τ') (hLu τ') (hUb τ') (hUt τ') (fun c _ => hUd τ' c) e e' (fun k hp => Hf (τ', stepOf N j b') k hp)
  have hlm : ∀ τ', lowMat (wL ε w) τ' = L τ' := fun τ' => by
    ext a' b'
    unfold lowMat
    split_ifs with e e'
    · rw [hwL]
      exact hlow τ' a' b' e.1 e.2
    · rw [e', (hLu τ').1]
    · rcases lt_or_gt_of_ne e' with e' | e'
      · exact ((hLu τ').2 _ _ e').symm
      · exact ((hLb τ') _ _ fun e'' => e ⟨e', e''⟩).symm
  obtain ⟨α₂, hα₂, hz₂⟩ := Hs
  have hne2 : minorIJ (L τ * U τ * (1 + Matrix.single cb ca t')) (stepCols N j a) (stepCols N j a) ≠ 0 := by
    intro h0
    refine hden2 ?_
    rw [GlobalTheory.T.frame_minor_value_formula K ι Φ y Ψ N j M F zb (τ, a) k₀ (h' τ * (1 + Matrix.single cb ca t')) (h τ)⁻¹ (sndPt k₀ z) α₂ _ hF hzb hG hk
      ((hh' τ).1.mul (Pts.transv_block hS t')) hz₂, ← Matrix.mul_assoc]
    show α₂ * minorIJ (G τ * _) _ _ = 0
    rw [hLU, h0, mul_zero]
  obtain ⟨t, Vm, hVb, hVt, hVd, hUV⟩ := GlobalTheory.T.LU_twist_refactorization N j a ca cb (L τ) (U τ) t' hj hca hcb hS (hLb τ) (hLu τ) (hUb τ) (hUt τ)
    (hUd τ) hne2
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  have hstep : stepOf N j ca = a := by
    have := a.2
    apply Fin.ext
    simp only [stepOf, hca, lastCol]
    split_ifs <;> omega
  have hcc : ∀ c, c ∈ stepCols N j (stepOf N j ca) → Vm c c ≠ 0 := fun c hc => hVd c (hstep ▸ hc)
  have hLe : ∀ r c, (L τ * (1 + Matrix.single cb ca t)) r c = L τ r c + if c = ca then L τ r cb * t else 0 := by
    intro r c
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
    congr 1
    by_cases e : c = ca
    · subst e
      simp [Matrix.mul_single_apply_same]
    · rw [if_neg e, Matrix.mul_single_apply_of_ne _ _ _ _ _ e]
  have hL2 : IsLowerUni (L τ * (1 + Matrix.single cb ca t)) := by
    refine ⟨fun r => ?_, fun r c e => ?_⟩
    · rw [hLe, (hLu τ).1]
      split_ifs with e
      · rw [e, (hLu τ).2 _ _ hlt, zero_mul, add_zero]
      · rw [add_zero]
    · rw [hLe, (hLu τ).2 _ _ e]
      split_ifs with e'
      · rw [(hLu τ).2 r cb (e.trans (e' ▸ hlt)), zero_mul, add_zero]
      · rw [add_zero]
  have hL2c : (L τ * (1 + Matrix.single cb ca t)) cb ca = L τ cb ca + t := by
    rw [hLe, if_pos rfl, (hLu τ).1, one_mul]
  have hsnd : lowRead M F zb h (sndPt k₀ z) τ cb ca = L τ cb ca + t := by
    rw [← hL2c]
    refine GlobalTheory.T.frame_LU_minor_value K ι Φ y Ψ N j M F zb h τ cb ca (sndPt k₀ z) (h' τ * (1 + Matrix.single cb ca t')) _ Vm hF hzb hG
      ((hh' τ).1.mul (Pts.transv_block hS t')) ?_ ((hLb τ).mul (Pts.transv_block hS t)) hL2 hVb hVt hcc hlt hS.symm ?_
    · rw [← Matrix.mul_assoc]
      show G τ * _ = _
      rw [hLU, Matrix.mul_assoc, hUV, Matrix.mul_assoc]
    · intro k hp
      rw [hstep, hk] at hp
      obtain rfl := Option.some.inj hp
      exact ⟨α₂, hα₂, by rw [hstep]; exact hz₂⟩
  have hwt : wT ε w = t := by
    rw [hwT, hsnd, hlow τ cb ca hlt hS.symm]
    ring
  have hHU : ∀ τ', (fun τ' => wH h ε τ' w) τ' * U τ' = h' τ' := fun τ' => by
    show h τ' * lowMat (wL ε w) τ' * U τ' = _
    rw [hlm, Matrix.mul_assoc, hhL]
  show SameOrbit (sqZ M F (bl (wB ε w)) (fun τ' => wH h ε τ' w) k₀ τ ca cb (wT ε w)) z
  rw [hwB, hwt]
  refine GlobalTheory.T.twisted_frame_value_formula K ι Φ y Ψ N j M τ a k₀ ca cb F _ z _ U Vm t hk hzb hG horb
    (fun τ' => ⟨hUb τ', hUt τ', hUd τ'⟩) hVb hVt hVd (fun p k hp => ?_) ⟨α₂, hα₂, fun m => ?_⟩
  · rw [hHU]
    exact Hf p k hp
  · have e : (fun τ' => wH h ε τ' w) τ * (1 + Matrix.single cb ca t) * Vm = h' τ * (1 + Matrix.single cb ca t') := by
      rw [← hHU τ, Matrix.mul_assoc, Matrix.mul_assoc, hUV]
    rw [e]
    exact hz₂ m

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_chart_fifth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, wRho M Rb τ k₀ ca cb F kb r h ε z ∈ wD ε V ∧ SameOrbit (wPhi M F bl h ε k₀ τ ca cb (wRho M Rb τ k₀ ca cb F kb r h ε z)) z := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto.main
end
