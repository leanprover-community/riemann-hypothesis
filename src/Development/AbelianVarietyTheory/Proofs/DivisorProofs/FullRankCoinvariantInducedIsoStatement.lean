import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableFullRankZetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaStdMaxParab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Matrix Topology

noncomputable section

namespace GlobalTheory.FullRankOnto

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

local notation "Yo" => GlobalTheory.FullRankCoinv.Y0 k n d

theorem Y0_mul_apply (hnd : n ≤ d) {β : Type*} (M : Matrix (Fin d) β k) (i : Fin n) (j : β) :
    (Yo * M) i j = M ⟨d - n + i, by omega⟩ j := by
  have e : ∀ l : Fin d, ((l : ℕ) = d - n + i) ↔ l = ⟨d - n + i, by omega⟩ := fun l => by rw [Fin.ext_iff]
  simp [GlobalTheory.FullRankCoinv.Y0, Matrix.mul_apply, e]

theorem mul_Y0_apply (hnd : n ≤ d) {β : Type*} [Fintype β] (A : Matrix β (Fin n) k) (i : β) (j : Fin n) :
    (A * Yo) i ⟨d - n + j, by omega⟩ = A i j := by
  have e : ∀ l : Fin n, (d - n + (j : ℕ) = d - n + l) ↔ l = j := fun l => by rw [Fin.ext_iff]; omega
  simp [GlobalTheory.FullRankCoinv.Y0, Matrix.mul_apply, e, Fin.val_inj]

theorem mul_Y0_apply_lt {β : Type*} [Fintype β] (A : Matrix β (Fin n) k) (i : β) (j : Fin d)
    (hj : (j : ℕ) < d - n) : (A * Yo) i j = 0 := by
  simp only [GlobalTheory.FullRankCoinv.Y0, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  simp only [mul_ite, mul_one, mul_zero]
  rw [if_neg (by omega)]

theorem Y0_mul_transpose (hnd : n ≤ d) : Yo * (Yo)ᵀ = 1 := by
  ext i j
  rw [Y0_mul_apply hnd, transpose_apply]
  simp only [GlobalTheory.FullRankCoinv.Y0, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff]
  by_cases h : (i : ℕ) = j
  · simp [h]
  · rw [if_neg (by omega), if_neg h]

def blkEquiv (hnd : n ≤ d) : Fin (d - n) ⊕ Fin n ≃ Fin d :=
  finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel hnd))

theorem blkEquiv_inl (hnd : n ≤ d) (a : Fin (d - n)) : ((blkEquiv hnd (Sum.inl a) : Fin d) : ℕ) = a := by
  simp [blkEquiv]

theorem blkEquiv_inr (hnd : n ≤ d) (b : Fin n) : blkEquiv hnd (Sum.inr b) = ⟨d - n + b, by omega⟩ := by
  ext; simp [blkEquiv]

def blkMat (hnd : n ≤ d) : Matrix (Fin n) (Fin n) k →* Matrix (Fin d) (Fin d) k where
  toFun M := reindex (blkEquiv hnd) (blkEquiv hnd) (fromBlocks 1 0 0 M)
  map_one' := by simp [fromBlocks_one]
  map_mul' A B := by
    simp only [reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
    simp

def blkGL (hnd : n ≤ d) : GL (Fin n) k →* GL (Fin d) k := Units.map (blkMat hnd)

theorem blkGL_val (hnd : n ≤ d) (g : GL (Fin n) k) :
    (blkGL hnd g).val = reindex (blkEquiv hnd) (blkEquiv hnd) (fromBlocks 1 0 0 g.val) := rfl

theorem Y0_mul_blkGL (hnd : n ≤ d) (g : GL (Fin n) k) : Yo * (blkGL hnd g).val = g.val * Yo := by
  ext i j
  rw [Y0_mul_apply hnd, blkGL_val, ← blkEquiv_inr hnd]
  obtain ⟨x, rfl⟩ := (blkEquiv hnd).surjective j
  rcases x with a | b
  · rw [mul_Y0_apply_lt _ _ _ (by rw [blkEquiv_inl]; exact a.2)]
    simp
  · rw [blkEquiv_inr hnd b, mul_Y0_apply hnd, ← blkEquiv_inr hnd]
    simp

theorem blkGL_mem_KO (hnd : n ≤ d) {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : blkGL hnd g ∈ KO k (Fin d) := by
  have key : ∀ h : GL (Fin n) k, (∀ i j, h.val i j ∈ 𝒪[k]) → ∀ i j, (blkGL hnd h).val i j ∈ 𝒪[k] := by
    intro h hh i j
    obtain ⟨x, rfl⟩ := (blkEquiv hnd).surjective i
    obtain ⟨y, rfl⟩ := (blkEquiv hnd).surjective j
    rw [blkGL_val, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases x with a | a <;> rcases y with b | b <;> simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply]
    · rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
    · exact zero_mem _
    · exact zero_mem _
    · exact hh a b
  rw [mem_KO_iff] at hg ⊢
  refine ⟨key g hg.1, ?_⟩
  rw [← map_inv]
  exact key g⁻¹ hg.2

def lrMat (hnd : n ≤ d) (M : Matrix (Fin d) (Fin d) k) : Matrix (Fin n) (Fin n) k :=
  Matrix.of fun i j => M ⟨d - n + i, by omega⟩ ⟨d - n + j, by omega⟩

theorem Y0_mul_parab (hnd : n ≤ d) {p : GL (Fin d) k}
    (hp : p ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.stdMaxParab k (Nat.sub_add_cancel hnd)) : Yo * p.val = lrMat hnd p.val * Yo := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.mem_stdMaxParab] at hp
  ext i j
  rw [Y0_mul_apply hnd]
  by_cases hj : (j : ℕ) < d - n
  · rw [mul_Y0_apply_lt _ _ _ hj, hp _ _ hj (by simp)]
  · have e : j = ⟨d - n + (⟨j - (d - n), by omega⟩ : Fin n), by simp; omega⟩ := by ext; simp; omega
    rw [e, mul_Y0_apply hnd]
    rfl

theorem exists_Y0_mul_parab (hnd : n ≤ d) {p : GL (Fin d) k}
    (hp : p ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.stdMaxParab k (Nat.sub_add_cancel hnd)) :
    ∃ D : GL (Fin n) k, Yo * p.val = D.val * Yo := by
  have h1 := Y0_mul_parab hnd hp
  have h2 := Y0_mul_parab hnd (inv_mem hp)
  have key : ∀ A B : Matrix (Fin n) (Fin n) k, ∀ q r : GL (Fin d) k, q * r = 1 →
      Yo * q.val = A * Yo → Yo * r.val = B * Yo → A * B = 1 := by
    intro A B q r hqr hq hr
    have : Yo = A * B * Yo := by
      calc Yo = Yo * (q * r).val := by rw [hqr]; simp
        _ = A * B * Yo := by rw [Units.val_mul, ← Matrix.mul_assoc, hq, Matrix.mul_assoc, hr, Matrix.mul_assoc]
    have := congrArg (· * (Yo)ᵀ) this
    simpa [Matrix.mul_assoc, Y0_mul_transpose hnd] using this.symm
  exact ⟨⟨_, _, key _ _ _ _ (mul_inv_cancel p) h1 h2, key _ _ _ _ (inv_mul_cancel p) h2 h1⟩, h1⟩

section Psi
open Classical in

def psi (f : GL (Fin d) k → ℂ) (Y : Matrix (Fin n) (Fin d) k) : ℂ :=
  if h : ∃ κ ∈ KO k (Fin d), Y = GlobalTheory.FullRankCoinv.Y0 k n d * κ.val then f h.choose else 0

variable {ν : kˣ →* ℂˣ} {f : GL (Fin d) k → ℂ}

theorem psi_Y0_mul (hf : f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν) {κ : GL (Fin d) k} (hκ : κ ∈ KO k (Fin d)) :
    psi f (Yo * κ.val) = f κ := by
  have hex : ∃ κ' ∈ KO k (Fin d), Yo * κ.val = Yo * κ'.val := ⟨κ, hκ, rfl⟩
  rw [psi, dif_pos hex]
  have e := hex.choose_spec.2
  set κ' := hex.choose
  have hb : Yo * (κ' * κ⁻¹).val = (1 : GL (Fin n) k).val * Yo := by
    rw [Units.val_mul, ← Matrix.mul_assoc, ← e, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]; simp
  have := hf.2 (κ' * κ⁻¹) κ 1 hb
  rw [inv_mul_cancel_right] at this
  rw [this]
  simp

theorem psi_eq_zero {Y : Matrix (Fin n) (Fin d) k} (h : ¬ ∃ κ ∈ KO k (Fin d), Y = Yo * κ.val) : psi f Y = 0 := by
  rw [psi, dif_neg h]

theorem integral_of_mul_Y0 (hnd : n ≤ d) {A : Matrix (Fin n) (Fin n) k} {M : Matrix (Fin d) (Fin d) k}
    (h : A * Yo = Yo * M) (hM : ∀ i j, M i j ∈ 𝒪[k]) : ∀ i j, A i j ∈ 𝒪[k] := by
  intro i j
  have := congrFun (congrFun h i) ⟨d - n + j, by omega⟩
  rw [mul_Y0_apply hnd, Y0_mul_apply hnd] at this
  rw [this]; exact hM _ _

theorem mem_KO_of_mul_Y0 (hnd : n ≤ d) {g : GL (Fin n) k} {κ₀ κ : GL (Fin d) k} (h₀ : κ₀ ∈ KO k (Fin d))
    (hκ : κ ∈ KO k (Fin d)) (h : g.val * (Yo * κ₀.val) = Yo * κ.val) : g ∈ KO k (Fin n) := by
  set κ' := κ * κ₀⁻¹
  have hκ' : κ' ∈ KO k (Fin d) := mul_mem hκ (inv_mem h₀)
  have e1 : g.val * Yo = Yo * κ'.val := by
    rw [Units.val_mul, ← Matrix.mul_assoc, ← h, Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have e2 : (g⁻¹).val * Yo = Yo * (κ'⁻¹).val := by
    calc (g⁻¹).val * Yo = (g⁻¹).val * (Yo * κ'.val) * (κ'⁻¹).val := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      _ = Yo * (κ'⁻¹).val := by rw [← e1, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [mem_KO_iff] at hκ' ⊢
  exact ⟨integral_of_mul_Y0 hnd e1 hκ'.1, integral_of_mul_Y0 hnd e2 hκ'.2⟩

variable [MeasurableSpace k] [BorelSpace k]

theorem smallF_psi_Y0_mul (hnd : n ≤ d) (hf : f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν) {κ₀ : GL (Fin d) k}
    (h₀ : κ₀ ∈ KO k (Fin d)) : smallF (haarVol (KO k (Fin n))) ν (psi f) (Yo * κ₀.val) = f κ₀ := by
  have key : (fun g : GL (Fin n) k => psi f (g.val * (Yo * κ₀.val)) * (ν (gdet g) : ℂ) *
      apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)) = (KO k (Fin n) : Set (GL (Fin n) k)).indicator
      (fun _ => f κ₀) := by
    funext g
    by_cases hg : g ∈ KO k (Fin n)
    · rw [Set.indicator_of_mem hg]
      have e : g.val * (Yo * κ₀.val) = Yo * (blkGL hnd g * κ₀).val := by
        rw [Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Y0_mul_blkGL]
      rw [e, psi_Y0_mul hf (mul_mem (blkGL_mem_KO hnd hg) h₀), hf.2 _ _ g (Y0_mul_blkGL hnd g),
        apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg), apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg)]
      have : (ν (gdet g) : ℂ) ≠ 0 := Units.ne_zero _
      rw [Units.val_inv_eq_inv_val]
      field_simp
    · rw [Set.indicator_of_notMem hg, psi_eq_zero, zero_mul, zero_mul]
      rintro ⟨κ, hκ, e⟩
      exact hg (mem_KO_of_mul_Y0 hnd h₀ hκ e)
  have hK : @MeasurableSet (GL (Fin n) k) Units.instMeasurableSpace (KO k (Fin n) : Set (GL (Fin n) k)) :=
    @IsOpen.measurableSet _ _ _ Units.instMeasurableSpace
      (@BorelSpace.opensMeasurable _ _ Units.instMeasurableSpace borel_GL) isOpen_KO
  rw [smallF, key]
  refine (integral_indicator_const (μ := haarVol (KO k (Fin n))) (f κ₀) hK).trans ?_
  simp [Measure.real, haarVol_self isOpen_KO le_rfl]

end Psi

section Support
variable {ν : kˣ →* ℂˣ} {f : GL (Fin d) k → ℂ}

def rowsMat (hnd : n ≤ d) (Z : Matrix (Fin n) (Fin d) k) : Matrix (Fin d) (Fin d) k :=
  Matrix.of fun i j => if h : d - n ≤ (i : ℕ) then Z ⟨i - (d - n), by omega⟩ j else (1 : Matrix (Fin d) (Fin d) k) i j

theorem continuous_rowsMat (hnd : n ≤ d) : Continuous (rowsMat (k := k) hnd) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [rowsMat, Matrix.of_apply]
  split_ifs
  · exact (continuous_apply j).comp (continuous_apply _)
  · exact continuous_const

theorem Y0_mul_rowsMat (hnd : n ≤ d) (Z : Matrix (Fin n) (Fin d) k) : Yo * rowsMat hnd Z = Z := by
  ext i j
  rw [Y0_mul_apply hnd]
  simp only [rowsMat, Matrix.of_apply, dif_pos (show d - n ≤ d - n + (i : ℕ) by omega)]
  congr 1; ext; simp

theorem rowsMat_Y0 (hnd : n ≤ d) : rowsMat hnd (Yo) = 1 := by
  ext i j
  simp only [rowsMat, Matrix.of_apply]
  split_ifs with h
  · simp only [GlobalTheory.FullRankCoinv.Y0, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff]
    congr 1
    apply propext; omega
  · rfl

theorem eventually_Y0_mul (hnd : n ≤ d) {V : Set (GL (Fin d) k)} (hV : V ∈ 𝓝 1) :
    ∀ᶠ Z in 𝓝 (Yo), ∃ u ∈ V, Z = Yo * u.val := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  rw [isEmbedding_val_GL.isInducing.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨O, hO, hOV⟩ := hV
  have hdet : {M : Matrix (Fin d) (Fin d) k | M.det ≠ 0} ∈ 𝓝 (1 : Matrix (Fin d) (Fin d) k) :=
    (isOpen_ne_fun (continuous_id.matrix_det) continuous_const).mem_nhds (by simp)
  have hc : Filter.Tendsto (rowsMat hnd) (𝓝 (Yo)) (𝓝 1) := by
    have := (continuous_rowsMat (k := k) hnd).tendsto (Yo)
    rwa [rowsMat_Y0] at this
  filter_upwards [hc (Filter.inter_mem hO hdet)] with Z hZ
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (rowsMat hnd Z) hZ.2, hOV hZ.1, ?_⟩
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Y0_mul_rowsMat]

theorem isLocallyConstant_psi (hnd : n ≤ d) (hf : f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν) :
    IsLocallyConstant (psi f : Matrix (Fin n) (Fin d) k → ℂ) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  rw [IsLocallyConstant.iff_eventually_eq]
  intro Y
  set S : Set (Matrix (Fin n) (Fin d) k) := (fun κ : GL (Fin d) k => Yo * κ.val) '' (KO k (Fin d))
  have hS : IsCompact S := isCompact_KO.image (continuous_const.matrix_mul Units.continuous_val)
  have hmem : ∀ Y, Y ∈ S ↔ ∃ κ ∈ KO k (Fin d), Y = Yo * κ.val := fun Y =>
    ⟨fun ⟨κ, hκ, e⟩ => ⟨κ, hκ, e.symm⟩, fun ⟨κ, hκ, e⟩ => ⟨κ, hκ, e.symm⟩⟩
  by_cases hY : ∃ κ ∈ KO k (Fin d), Y = Yo * κ.val
  · obtain ⟨κ, hκ, rfl⟩ := hY
    obtain ⟨U, hU, hfU⟩ := hf.1
    set V : Set (GL (Fin d) k) := {u | u ∈ KO k (Fin d) ∧ κ⁻¹ * u * κ ∈ U}
    have hV : V ∈ 𝓝 1 := by
      refine Filter.inter_mem (isOpen_KO.mem_nhds (one_mem _)) ?_
      have hc : Continuous fun u : GL (Fin d) k => κ⁻¹ * u * κ := (continuous_const.mul continuous_id).mul continuous_const
      have := hc.tendsto 1
      simp only [mul_one, inv_mul_cancel] at this
      exact this hU
    have ht : Filter.Tendsto (fun Y : Matrix (Fin n) (Fin d) k => Y * (κ⁻¹).val) (𝓝 (Yo * κ.val)) (𝓝 (Yo)) := by
      have := ((continuous_id.matrix_mul continuous_const :
        Continuous fun Y : Matrix (Fin n) (Fin d) k => Y * (κ⁻¹).val)).tendsto (Yo * κ.val)
      simpa only [id, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] using this
    filter_upwards [ht (eventually_Y0_mul hnd hV)] with Z hZ
    obtain ⟨u, ⟨hu, hu'⟩, e⟩ := hZ
    have e' : Z = Yo * (u * κ).val := by
      rw [Units.val_mul, ← Matrix.mul_assoc, ← e, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [e', psi_Y0_mul hf (mul_mem hu hκ), psi_Y0_mul hf hκ]
    have := hfU κ _ hu'
    rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at this
  · have hO : Sᶜ ∈ 𝓝 Y := hS.isClosed.isOpen_compl.mem_nhds (fun h => hY ((hmem Y).1 h))
    filter_upwards [hO] with Z hZ
    rw [psi_eq_zero (fun h => hZ ((hmem Z).2 h)), psi_eq_zero hY]

theorem hasCompactSupport_psi : HasCompactSupport (psi f : Matrix (Fin n) (Fin d) k → ℂ) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  refine HasCompactSupport.intro (K := (fun κ : GL (Fin d) k => Yo * κ.val) '' (KO k (Fin d)))
    (isCompact_KO.image (continuous_const.matrix_mul Units.continuous_val)) ?_
  intro Y hY
  exact psi_eq_zero fun ⟨κ, hκ, e⟩ => hY ⟨κ, hκ, e.symm⟩

theorem rank_zeroth_component_eq (hnd : n ≤ d) : (Yo).rank = n := by
  refine le_antisymm (Matrix.rank_le_height _) ?_
  have := Matrix.rank_mul_le_left (Yo) (Yo)ᵀ
  rwa [Y0_mul_transpose hnd, Matrix.rank_one, Fintype.card_fin] at this

theorem psi_mem_fullRk (hnd : n ≤ d) (hf : f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν) :
    psi f ∈ GlobalTheory.FullRankCoinv.fullRk k n d := by
  refine ⟨⟨isLocallyConstant_psi hnd hf, hasCompactSupport_psi⟩, fun Y hY => psi_eq_zero ?_⟩
  rintro ⟨κ, _, rfl⟩
  exact hY (by rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 κ.isUnit), rank_zeroth_component_eq hnd])

end Support

theorem exists_fullRk_smallF_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d →
    GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν,
    ∃ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ h : GL (Fin d) k,
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (GlobalTheory.FullRankCoinv.Y0 k n d * h.val) = f h := by
  intro k _ _ _ _ _ _ n d ν hnd _ f hf
  refine ⟨psi f, psi_mem_fullRk hnd hf, fun h => ?_⟩
  obtain ⟨p, hp, κ₀, h₀, rfl⟩ := (GlobalTheory.MaxParabIwasawa.iwasawa_stdMaxParab k d (d - n) n
    (Nat.sub_add_cancel hnd) h).2
  obtain ⟨D, hD⟩ := exists_Y0_mul_parab hnd hp
  have e : GlobalTheory.FullRankCoinv.Y0 k n d * (p * κ₀).val = D.val * (GlobalTheory.FullRankCoinv.Y0 k n d * κ₀.val) := by
    rw [Units.val_mul, ← Matrix.mul_assoc, hD, Matrix.mul_assoc]
  have h1 := smallF_mul_left (haarVol (KO k (Fin n))) ν (psi f) D (GlobalTheory.FullRankCoinv.Y0 k n d * κ₀.val)
  rw [smallF_psi_Y0_mul hnd hf h₀] at h1
  rw [e, hf.2 p κ₀ D hD, ← h1, Units.val_inv_eq_inv_val, Fintype.card_fin, neg_div, apow_neg]
  have h2 : (ν (gdet D) : ℂ) ≠ 0 := Units.ne_zero _
  have h3 := apow_ne_zero (gdet D) ((d : ℂ) / 2)
  field_simp

end GlobalTheory.FullRankOnto
end
end

section
open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_rank_zeta_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν,
    ∃ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ h : GL (Fin d) k,
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (GlobalTheory.FullRankCoinv.Y0 k n d * h.val) = f h := by
  first | exact @GlobalTheory.FullRankOnto.exists_fullRk_smallF_eq | exact GlobalTheory.FullRankOnto.exists_fullRk_smallF_eq | (intros; apply GlobalTheory.FullRankOnto.exists_fullRk_smallF_eq <;> assumption)
end

section
section
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv.UnitMinor

theorem isClopen_setOf_valuation_eq_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : IsClopen {x : k | valuation k x = 1} := by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hy
    rw [IsValuativeTopology.mem_nhds_iff']
    by_cases h0 : y = 0
    · subst h0
      refine ⟨1, fun z hz ↦ ?_⟩
      simp only [Set.mem_ofPred_eq, Units.val_one, sub_zero, Set.mem_compl_iff, Set.mem_setOf_eq] at hz ⊢
      exact hz.ne
    · have hv : valuation k y ≠ 0 := by simpa using h0
      refine ⟨Units.mk0 _ hv, fun z hz ↦ ?_⟩
      simp only [Set.mem_ofPred_eq, Units.val_mk0, Set.mem_compl_iff, Set.mem_setOf_eq] at hz ⊢
      have : z = y + (z - y) := by ring
      rw [this, (valuation k).map_add_eq_of_lt_left hz]
      exact hy
  · rw [isOpen_iff_mem_nhds]
    intro y hy
    rw [IsValuativeTopology.mem_nhds_iff']
    refine ⟨1, fun z hz ↦ ?_⟩
    simp only [Set.mem_ofPred_eq, Units.val_one, Set.mem_setOf_eq] at hz hy ⊢
    have : z = y + (z - y) := by ring
    rw [this, (valuation k).map_add_eq_of_lt_left (by rw [hy]; exact hz), hy]

theorem isClopen_unitMinorSet (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n d : ℕ) : IsClopen (unitMinorSet k n d) := by
  have hI : IsClopen {A : Matrix (Fin n) (Fin d) k | ∀ i j, A i j ∈ 𝒪[k]} := by
    obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
    exact ⟨isCompact_intMatrix.isClosed, isOpen_intMatrix⟩
  have hU : IsClopen (⋃ f : Fin n ↪ Fin d,
      (fun Y : Matrix (Fin n) (Fin d) k ↦ (Y.submatrix id f).det) ⁻¹' {x : k | valuation k x = 1}) := by
    refine isClopen_iUnion_of_finite fun f ↦ (isClopen_setOf_valuation_eq_one k).preimage ?_
    exact Continuous.matrix_det (Continuous.matrix_submatrix continuous_id _ _)
  have e : unitMinorSet k n d = {A : Matrix (Fin n) (Fin d) k | ∀ i j, A i j ∈ 𝒪[k]} ∩ ⋃ f : Fin n ↪ Fin d,
      (fun Y : Matrix (Fin n) (Fin d) k ↦ (Y.submatrix id f).det) ⁻¹' {x : k | valuation k x = 1} := by
    ext Y; simp [unitMinorSet]
  rw [e]; exact hI.inter hU

end GlobalTheory.FullRankCoinv.UnitMinor
end

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClopen_unit_minor_set : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ),
    IsClopen (GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d) := by
  atlas_forward_decl GlobalTheory.FullRankCoinv.UnitMinor.isClopen_unitMinorSet
end

section
section
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory

theorem unitMinorSet_rank_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (Y : Matrix (Fin n) (Fin d) k), Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → Y.rank = n := by
  intro k _ _ _ _ n d Y hY
  obtain ⟨-, f, hf⟩ := hY
  have hdet : (Y.submatrix id f).det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hf
    exact zero_ne_one hf
  have hunit : IsUnit (Y.submatrix id f) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hsub : (Y.submatrix id f).rank = n := by
    rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin]
  have hmul : Y * (1 : Matrix (Fin d) (Fin d) k).submatrix (Equiv.refl (Fin d)) f = Y.submatrix id f := by
    rw [Matrix.mul_submatrix_one]; rfl
  apply le_antisymm (Matrix.rank_le_height Y)
  calc n = (Y.submatrix id f).rank := hsub.symm
    _ = (Y * (1 : Matrix (Fin d) (Fin d) k).submatrix (Equiv.refl (Fin d)) f).rank := by rw [hmul]
    _ ≤ Y.rank := Matrix.rank_mul_le_left _ _

end GlobalTheory
end

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_eq_of_unit_minor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (Y : Matrix (Fin n) (Fin d) k), Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → Y.rank = n := by
  atlas_forward_decl GlobalTheory.unitMinorSet_rank_eq
end

section
section
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section

namespace GlobalTheory.FullRankCoinv.UnitMinor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem adjugate_integral {n : ℕ} (X : Matrix (Fin n) (Fin n) k) (hX : ∀ i j, X i j ∈ 𝒪[k]) :
    ∀ i j, X.adjugate i j ∈ 𝒪[k] := by
  let X' : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨X i j, hX i j⟩
  have e : X = (algebraMap 𝒪[k] k).mapMatrix X' := by ext i j; rfl
  intro i j
  rw [e, ← RingHom.map_adjugate]
  exact (X'.adjugate i j).2

theorem mul_integral {a b c : ℕ} (X : Matrix (Fin a) (Fin b) k) (W : Matrix (Fin b) (Fin c) k)
    (hX : ∀ i j, X i j ∈ 𝒪[k]) (hW : ∀ i j, W i j ∈ 𝒪[k]) : ∀ i j, (X * W) i j ∈ 𝒪[k] := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hX i l) (hW l j)

theorem integral_of_mul {n d : ℕ} (M : Matrix (Fin n) (Fin n) k) (Z : Matrix (Fin n) (Fin d) k)
    (hZ : Z ∈ unitMinorSet k n d) (hMZ : ∀ i j, (M * Z) i j ∈ 𝒪[k]) : ∀ i j, M i j ∈ 𝒪[k] := by
  obtain ⟨hZi, f, hf⟩ := hZ
  set Zf := Z.submatrix id f with hZf
  have hsub : (M * Z).submatrix id f = M * Zf := by
    ext i j; simp [Zf, Matrix.mul_apply]
  have hdet : Zf.det ≠ 0 := by
    intro h0; rw [h0, map_zero] at hf; exact zero_ne_one hf
  have hM : M = (M * Z).submatrix id f * Zf⁻¹ := by
    rw [hsub, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.mul_one]
  have hZfi : ∀ i j, Zf i j ∈ 𝒪[k] := fun i j => hZi _ _
  have hinv : ∀ i j, Zf⁻¹ i j ∈ 𝒪[k] := by
    intro i j
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
    refine Subring.mul_mem _ ?_ (adjugate_integral Zf hZfi i j)
    rw [Valuation.mem_integer_iff, map_inv₀, hf, inv_one]
  rw [hM]
  exact mul_integral _ _ (fun i j => hMZ _ _) hinv

theorem mem_KO_of_mul_mem_unitMinorSet (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n d : ℕ)
    (E : GL (Fin n) k) (Y : Matrix (Fin n) (Fin d) k) (hY : Y ∈ unitMinorSet k n d)
    (hEY : E.val * Y ∈ unitMinorSet k n d) : E ∈ GlobalTheory.SplitWeil.KO k (Fin n) := by
  refine (mem_KO_iff E).2 ⟨integral_of_mul _ Y hY hEY.1, integral_of_mul _ (E.val * Y) hEY ?_⟩
  rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  exact hY.1

end GlobalTheory.FullRankCoinv.UnitMinor
end
end

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_group_of_unit_minor_stable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (E : GL (Fin n) k) (Y : Matrix (Fin n) (Fin d) k), Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d →
    E.val * Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → E ∈ GlobalTheory.SplitWeil.KO k (Fin n) := by
  atlas_forward_decl GlobalTheory.FullRankCoinv.UnitMinor.mem_KO_of_mul_mem_unitMinorSet
end

section
section
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.UnitMinorStable

theorem mul_mem_unitMinorSet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (E : GL (Fin n) k) (Y : Matrix (Fin n) (Fin d) k), E ∈ GlobalTheory.SplitWeil.KO k (Fin n) →
    Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → E.val * Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d := by
  intro k _ _ _ _ n d E Y hE hY
  obtain ⟨hYi, f, hf⟩ := hY
  have hEi := ((GlobalTheory.SplitFlip.mem_KO_iff E).1 hE).1
  refine ⟨fun i j => ?_, f, ?_⟩
  · rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hEi i l) (hYi l j)
  · have hsub : (E.val * Y).submatrix id f = E.val * Y.submatrix id f := by
      ext i j; rfl
    have hdet := GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO hE
    have hg : ((GlobalTheory.SplitFlip.gdet E : kˣ) : k) = E.val.det := rfl
    rw [hsub, Matrix.det_mul, map_mul, hf, mul_one, ← hg, hdet]

end GlobalTheory.UnitMinorStable
end

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_minor_stable_integral_group : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (E : GL (Fin n) k) (Y : Matrix (Fin n) (Fin d) k), E ∈ GlobalTheory.SplitWeil.KO k (Fin n) →
    Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → E.val * Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d := by
  atlas_forward_decl GlobalTheory.UnitMinorStable.mul_mem_unitMinorSet
end

section
section
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section

namespace GlobalTheory.FullRankCoinv.UnitMinor

theorem det_one_updateCol_eq {K : Type} [Field K] {n : ℕ} (i : Fin n) (c : Fin n → K) :
    ((1 : Matrix (Fin n) (Fin n) K).updateCol i c).det = c i := by
  rw [← Matrix.cramer_apply, Matrix.cramer_one]; rfl

theorem exists_minor_det_ne_zero {K : Type} [Field K] {n d : ℕ} (Y : Matrix (Fin n) (Fin d) K)
    (hY : Y.rank = n) : ∃ f : Fin n ↪ Fin d, (Y.submatrix id f).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K (fun j => Yᵀ j)
  have htop : Submodule.span K (Set.range (fun j => Yᵀ j)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]; rw [Matrix.rank_eq_finrank_span_cols] at hY; exact hY
  have hsp : ⊤ ≤ Submodule.span K (Set.range ((fun j => Yᵀ j) ∘ a)) := by rw [hspan, htop]
  let b := Module.Basis.mk hli hsp
  let e : κ ≃ Fin n := b.indexEquiv (Pi.basisFun K (Fin n))
  let f : Fin n ↪ Fin d := e.symm.toEmbedding.trans ⟨a, ha⟩
  refine ⟨f, ?_⟩
  have hli' : LinearIndependent K (fun i => (Y.submatrix id f)ᵀ i) := by
    have : (fun i => (Y.submatrix id f)ᵀ i) = ((fun j => Yᵀ j) ∘ a) ∘ e.symm := by
      funext i r; rfl
    rw [this]; exact hli.comp _ e.symm.injective
  have hu := Matrix.linearIndependent_cols_iff_isUnit.mp hli'
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

theorem submatrix_mul_left {K : Type} [Field K] {n d : ℕ} (B : Matrix (Fin n) (Fin n) K)
    (Y : Matrix (Fin n) (Fin d) K) (g : Fin n ↪ Fin d) :
    (B * Y).submatrix id g = B * Y.submatrix id g := by
  ext r s; simp [Matrix.mul_apply]

theorem exists_GL_mul_mem_unitMinorSet (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n d : ℕ) (Y : Matrix (Fin n) (Fin d) k) (hY : Y.rank = n) :
    ∃ E : GL (Fin n) k, E.val * Y ∈ unitMinorSet k n d := by
  classical
  obtain ⟨f0, hf0⟩ := exists_minor_det_ne_zero Y hY
  haveI : Nonempty (Fin n ↪ Fin d) := ⟨f0⟩
  obtain ⟨f, hf⟩ := Finite.exists_max (fun g : Fin n ↪ Fin d => valuation k (Y.submatrix id g).det)
  have hAdet : (Y.submatrix id f).det ≠ 0 := by
    intro h0
    have h1 := hf f0
    simp only [h0, map_zero] at h1
    exact hf0 ((map_eq_zero _).mp (le_antisymm h1 zero_le'))
  have hAu : IsUnit (Y.submatrix id f).det := isUnit_iff_ne_zero.mpr hAdet
  let E : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero (Y.submatrix id f)⁻¹
    (by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hAdet)
  have hEv : E.val = (Y.submatrix id f)⁻¹ := rfl
  set Z := E.val * Y with hZ
  have hZf : Z.submatrix id f = 1 := by
    rw [hZ, submatrix_mul_left, hEv, Matrix.nonsing_inv_mul _ hAu]
  have hZg : ∀ g : Fin n ↪ Fin d, valuation k (Z.submatrix id g).det ≤ 1 := by
    intro g
    rw [hZ, submatrix_mul_left, hEv, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
      map_mul, map_inv₀, inv_mul_le_one₀ (zero_lt_iff.mpr (by simpa using hAdet))]
    exact hf g
  refine ⟨E, fun i j => ?_, f, by rw [hZf, Matrix.det_one, map_one]⟩
  rw [Valuation.mem_integer_iff]
  show valuation k (Z i j) ≤ 1
  by_cases hj : ∃ i', f i' = j
  · obtain ⟨i', rfl⟩ := hj
    have := congrFun (congrFun hZf i) i'
    simp only [Matrix.submatrix_apply, id] at this
    rw [this, Matrix.one_apply]
    split_ifs <;> simp
  · push_neg at hj
    have hsub : Z.submatrix id (f.setValue i j) = (1 : Matrix (Fin n) (Fin n) k).updateCol i (fun r => Z r j) := by
      ext r s
      by_cases hs : s = i
      · subst hs; simp [Function.Embedding.setValue_eq]
      · rw [Matrix.updateCol_ne hs]
        have h2 : f.setValue i j s = f s := by
          simp [Function.Embedding.setValue, hs, hj s]
        simp only [Matrix.submatrix_apply, id, h2]
        exact congrFun (congrFun hZf r) s
    have := hZg (f.setValue i j)
    rwa [hsub, det_one_updateCol_eq] at this

end GlobalTheory.FullRankCoinv.UnitMinor
end
end

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_minor_translate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (Y : Matrix (Fin n) (Fin d) k), Y.rank = n →
    ∃ E : GL (Fin n) k, E.val * Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d := by
  atlas_forward_decl GlobalTheory.FullRankCoinv.UnitMinor.exists_GL_mul_mem_unitMinorSet
end

section
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv

theorem exists_eq_normal_form_mul_of_rank_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n d : ℕ) (hnd : n ≤ d)
    (Y : Matrix (Fin n) (Fin d) k) (hY : Y.rank = n) :
    ∃ h : GL (Fin d) k, Y = GlobalTheory.FullRankCoinv.Y0 k n d * h.val := by
  let σ : Fin n ⊕ Fin (d - n) ≃ Fin d :=
    (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))
  have hσ : ∀ i : Fin n, ((σ (Sum.inl i) : Fin d) : ℕ) = d - n + i := fun i => by
    simp [σ]
  have hX : X0 k σ = GlobalTheory.FullRankCoinv.Y0 k n d := by
    ext i j
    simp only [X0, GlobalTheory.FullRankCoinv.Y0, Matrix.of_apply]
    congr 1
    apply propext
    rw [← hσ i, eq_comm]
    exact Fin.val_inj.symm
  have hc : Y.rank = Fintype.card (Fin n) := by simpa using hY
  obtain ⟨h, hh⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ Y).1 hc
  exact ⟨invT h, by rw [hh, hX]⟩

end GlobalTheory.FullRankCoinv
end

section
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_rank_normal_form_orbit : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ), n ≤ d →
    ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank = n → ∃ h : GL (Fin d) k, Y = GlobalTheory.FullRankCoinv.Y0 k n d * h.val := by
  first | exact @GlobalTheory.FullRankCoinv.exists_eq_normal_form_mul_of_rank_eq | exact GlobalTheory.FullRankCoinv.exists_eq_normal_form_mul_of_rank_eq | (intros; apply GlobalTheory.FullRankCoinv.exists_eq_normal_form_mul_of_rank_eq <;> assumption)
end

section
section
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem GlobalTheory.FullRankCoinv.fullRk_support_finite_cover : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (S : Set (Matrix (Fin n) (Fin d) k)), IsOpen S →
    (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank = n → ∃ E : GL (Fin n) k, E.val * Y ∈ S) →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∃ s : Finset (GL (Fin n) k), ∀ Y, Ψ Y ≠ 0 → ∃ E ∈ s, E.val * Y ∈ S := by
  intro k _ _ _ _ n d S hS hcov Ψ hΨ
  obtain ⟨⟨hlc, hcs⟩, hz⟩ := hΨ
  have hcl : IsClosed (Function.support Ψ) := by
    have h := (hlc.isOpen_fiber 0).isClosed_compl
    convert h using 1
    ext Y; simp [Function.mem_support]
  have hK : IsCompact (Function.support Ψ) :=
    IsCompact.of_isClosed_subset hcs hcl (subset_tsupport Ψ)
  have hU : ∀ E : GL (Fin n) k, IsOpen ((fun Y : Matrix (Fin n) (Fin d) k => E.val * Y) ⁻¹' S) := fun E =>
    hS.preimage (Continuous.matrix_mul continuous_const continuous_id)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun E : GL (Fin n) k => (fun Y : Matrix (Fin n) (Fin d) k => E.val * Y) ⁻¹' S) hU
    (by
      intro Y hY
      have hr : Y.rank = n := by
        by_contra h
        exact hY (hz Y h)
      obtain ⟨E, hE⟩ := hcov Y hr
      exact Set.mem_iUnion.2 ⟨E, hE⟩)
  refine ⟨t, fun Y hY => ?_⟩
  have := ht hY
  simp only [Set.mem_iUnion, Set.mem_preimage] at this
  obtain ⟨E, hEt, hE⟩ := this
  exact ⟨E, hEt, hE⟩
end

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_cover_finite_translates_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (S : Set (Matrix (Fin n) (Fin d) k)), IsOpen S →
    (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank = n → ∃ E : GL (Fin n) k, E.val * Y ∈ S) →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∃ s : Finset (GL (Fin n) k), ∀ Y, Ψ Y ≠ 0 → ∃ E ∈ s, E.val * Y ∈ S := by
  atlas_forward_decl GlobalTheory.FullRankCoinv.fullRk_support_finite_cover
end

section
noncomputable section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv.Reduce

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem lact_mem {n d : ℕ} (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) {Ψ : Matrix (Fin n) (Fin d) k → ℂ}
    (hΨ : Ψ ∈ fullRk k n d) : lact ν g Ψ ∈ fullRk k n d := by
  have hmem : (fun Y => Ψ ((g.1)ᵀ * Y)) ∈ fullRk k n d := by
    let e : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k :=
      { toFun := fun X => (g.1)ᵀ * X
        invFun := fun X => ((g⁻¹).1)ᵀ * X
        left_inv := fun X => by
          simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
            Matrix.one_mul]
        right_inv := fun X => by
          simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
            Matrix.one_mul]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    refine ⟨⟨hΨ.1.1.comp_continuous e.continuous, hΨ.1.2.comp_homeomorph e⟩, fun Y hY => hΨ.2 _ ?_⟩
    rwa [Matrix.rank_mul_eq_right_of_isUnit_det _ _
      (by rw [Matrix.det_transpose]; exact Matrix.isUnits_det_units g)]
  exact (fullRk k n d).smul_mem ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) hmem

theorem indicator_mem {n d : ℕ} {T : Set (Matrix (Fin n) (Fin d) k)} (hT : IsClopen T)
    {Ψ : Matrix (Fin n) (Fin d) k → ℂ} (hΨ : Ψ ∈ fullRk k n d) : T.indicator Ψ ∈ fullRk k n d := by
  refine ⟨⟨?_, ?_⟩, fun Y hY => ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ T
    · filter_upwards [hT.isOpen.mem_nhds hx, hΨ.1.1.eventually_eq x] with y hy h
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, h]
    · filter_upwards [hT.compl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  · refine HasCompactSupport.mono hΨ.1.2 fun y hy h => hy ?_
    by_cases hy' : y ∈ T
    · rw [Set.indicator_of_mem hy', h]
    · exact Set.indicator_of_notMem hy' _
  · by_cases hy' : Y ∈ T
    · rw [Set.indicator_of_mem hy', hΨ.2 Y hY]
    · exact Set.indicator_of_notMem hy' _

end

theorem reduce_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ) (S : Set (Matrix (Fin n) (Fin d) k)), IsClopen S →
    (∀ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ Y : Matrix (Fin n) (Fin d) k, Integrable (fun g : GL (Fin n) k =>
      Φ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2))
      (haarVol (GlobalTheory.SplitWeil.KO k (Fin n)))) →
    ∀ (s : Finset (GL (Fin n) k)), ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    (∀ Y, Ψ Y ≠ 0 → ∃ E ∈ s, E.val * Y ∈ S) →
    ∃ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, (∀ Y, Y ∉ S → Φ Y = 0) ∧ Ψ - Φ ∈ GlobalTheory.FullRankCoinv.augRk n d ν ∧
      ∀ Y, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y = smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y := by
  intro k _ _ _ _ _ _ n d ν S hS hint s
  classical
  have hadd : ∀ Ψ ∈ fullRk k n d, ∀ Φ ∈ fullRk k n d, ∀ Y,
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν (Ψ + Φ) Y =
        smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y + smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y := by
    intro Ψ hΨ Φ hΦ Y
    simp only [smallF, Pi.add_apply]
    rw [← integral_add (hint Ψ hΨ Y) (hint Φ hΦ Y)]
    congr 1; funext g; ring
  induction s using Finset.induction_on with
  | empty =>
    intro Ψ hΨ h
    refine ⟨Ψ, hΨ, fun Y _ => ?_, by simp, fun _ => rfl⟩
    by_contra h0
    simpa using h Y h0
  | insert E s _ ih =>
    intro Ψ hΨ h
    set T : Set (Matrix (Fin n) (Fin d) k) := (fun Y => E.val * Y) ⁻¹' S with hTdef
    have hT : IsClopen T := hS.preimage (by fun_prop)
    have h1 := indicator_mem hT hΨ
    have h2 := indicator_mem hT.compl hΨ
    have hsum : T.indicator Ψ + Tᶜ.indicator Ψ = Ψ := Set.indicator_self_add_compl T Ψ
    obtain ⟨Φ₂, hΦ₂, hS₂, ha₂, hF₂⟩ := ih _ h2 fun Y hY => by
      have hYT : Y ∈ Tᶜ := by
        by_contra hc
        exact hY (Set.indicator_of_notMem hc _)
      rw [Set.indicator_of_mem hYT] at hY
      obtain ⟨E', hE', hS'⟩ := h Y hY
      rcases Finset.mem_insert.1 hE' with rfl | hE'
      · exact absurd hS' hYT
      · exact ⟨E', hE', hS'⟩
    have hΦ₁ := lact_mem ν (invT E) h1
    refine ⟨lact ν (invT E) (T.indicator Ψ) + Φ₂, add_mem hΦ₁ hΦ₂, fun Y hY => ?_, ?_, fun Y => ?_⟩
    · have hn : (invT E).1ᵀ * Y ∉ T := by
        intro hc
        apply hY
        have hc' : E.val * ((invT E).1ᵀ * Y) ∈ S := hc
        rwa [invT_val, Matrix.transpose_transpose, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] at hc'
      simp only [Pi.add_apply, hS₂ Y hY, lact, Set.indicator_of_notMem hn, mul_zero, add_zero]
    · have ha₁ : lact ν (invT E) (T.indicator Ψ) - T.indicator Ψ ∈ augRk n d ν :=
        Submodule.subset_span ⟨_, _, h1, rfl⟩
      have : Ψ - (lact ν (invT E) (T.indicator Ψ) + Φ₂) =
          (Tᶜ.indicator Ψ - Φ₂) - (lact ν (invT E) (T.indicator Ψ) - T.indicator Ψ) := by
        linear_combination -hsum
      rw [this]
      exact sub_mem ha₂ ha₁
    · rw [hadd _ hΦ₁ _ hΦ₂, UnitMinor.smallF_lact, hF₂, ← hadd _ h1 _ h2, hsum]

end GlobalTheory.FullRankCoinv.Reduce
end
end

section
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.clopen_integrability_full_rank_orbit : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ) (S : Set (Matrix (Fin n) (Fin d) k)), IsClopen S →
    (∀ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ Y : Matrix (Fin n) (Fin d) k, Integrable (fun g : GL (Fin n) k =>
      Φ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2))
      (haarVol (GlobalTheory.SplitWeil.KO k (Fin n)))) →
    ∀ (s : Finset (GL (Fin n) k)), ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    (∀ Y, Ψ Y ≠ 0 → ∃ E ∈ s, E.val * Y ∈ S) →
    ∃ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, (∀ Y, Y ∉ S → Φ Y = 0) ∧ Ψ - Φ ∈ GlobalTheory.FullRankCoinv.augRk n d ν ∧
      ∀ Y, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y = smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y := by
  first | exact @GlobalTheory.FullRankCoinv.Reduce.reduce_support | exact GlobalTheory.FullRankCoinv.Reduce.reduce_support | (intros; apply GlobalTheory.FullRankCoinv.Reduce.reduce_support <;> assumption)
end

section
section
noncomputable section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix Topology

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv.Average

theorem integral_comp_finite {G V : Type*} [MeasurableSpace G] (μ : Measure G) [IsFiniteMeasure μ] (F : G → V)
    (T : Finset V) (hT : ∀ᵐ g ∂μ, F g ∈ T) (hm : ∀ v, MeasurableSet (F ⁻¹' {v})) (φ : V → ℂ) :
    ∫ g, φ (F g) ∂μ = ∑ v ∈ T, (μ.real (F ⁻¹' {v}) : ℂ) * φ v := by
  classical
  have h1 : (fun g => φ (F g)) =ᵐ[μ] fun g => ∑ v ∈ T, (F ⁻¹' {v}).indicator (fun _ => φ v) g := by
    filter_upwards [hT] with g hg
    rw [Finset.sum_eq_single (F g)]
    · rw [Set.indicator_of_mem (by simp)]
    · intro v _ hv
      exact Set.indicator_of_notMem (by simpa using hv.symm) _
    · exact fun h => absurd hg h
  rw [integral_congr_ae h1, integral_finset_sum _ fun v _ => (integrable_const _).indicator (hm v)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [integral_indicator_const _ (hm v), Complex.real_smul]

theorem sb_left_invariant {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n d : ℕ} (Ψ : Matrix (Fin n) (Fin d) k → ℂ) (hΨ : Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k)) :
    ∀ᶠ u in 𝓝 (1 : GL (Fin n) k), ∀ X : Matrix (Fin n) (Fin d) k, Ψ (u.val * X) = Ψ X := by
  have h1 : ∀ᶠ u in 𝓝 (1 : GL (Fin n) k), ∀ X ∈ tsupport Ψ, Ψ (u.val * X) = Ψ X := by
    refine IsCompact.eventually_forall_of_forall_eventually hΨ.2 fun y _ => ?_
    have h2 : IsLocallyConstant fun q : GL (Fin n) k × Matrix (Fin n) (Fin d) k => (Ψ (q.1.val * q.2), Ψ q.2) :=
      (hΨ.1.comp_continuous (by fun_prop)).prodMk (hΨ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (1, y)] with q hq
    simp only [Prod.mk.injEq, Units.val_one, Matrix.one_mul] at hq
    rw [hq.1, hq.2]
  have h3 : ∀ᶠ u in 𝓝 (1 : GL (Fin n) k), ∀ X ∈ tsupport Ψ, Ψ ((u⁻¹).val * X) = Ψ X := by
    have ht : Filter.Tendsto (fun u : GL (Fin n) k => u⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv.tendsto (1 : GL (Fin n) k))
    exact ht.eventually h1
  filter_upwards [h1, h3] with u hu1 hu2 X
  by_cases hX : X ∈ tsupport Ψ
  · exact hu1 X hX
  by_cases hX' : u.val * X ∈ tsupport Ψ
  · have := hu2 _ hX'
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hX, image_eq_zero_of_notMem_tsupport hX']

theorem mem_augRk_of_smallF_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ (S : Set (Matrix (Fin n) (Fin d) k)),
    (∀ (E : GL (Fin n) k), ∀ Y ∈ S, E.val * Y ∈ S → E ∈ GlobalTheory.SplitWeil.KO k (Fin n)) →
    (∀ E ∈ GlobalTheory.SplitWeil.KO k (Fin n), ∀ Y ∈ S, E.val * Y ∈ S) →
    ∀ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, (∀ Y, Y ∉ S → Φ Y = 0) →
    (∀ Y ∈ S, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y = 0) → Φ ∈ GlobalTheory.FullRankCoinv.augRk n d ν := by
  intro k _ _ _ _ _ _ n d ν hν S hrig hst Φ hΦ hsupp h0
  have : BorelSpace (GL (Fin n) k) := borel_GL
  set K := GlobalTheory.SplitWeil.KO k (Fin n) with hK
  have hKo : IsOpen (K : Set (GL (Fin n) k)) := isOpen_KO
  have hKm : MeasurableSet (K : Set (GL (Fin n) k)) := hKo.measurableSet
  have hK1 : haarVol K K = 1 := haarVol_self isOpen_KO le_rfl
  let F : GL (Fin n) k → Matrix (Fin n) (Fin d) k → ℂ :=
    fun g Y => Φ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)
  have hFl : ∀ g, F g = lact ν (invT g)⁻¹ Φ := fun g => by
    funext Y
    have e1 : gdet (invT g)⁻¹ = gdet g := by
      rw [show gdet (invT g)⁻¹ = (gdet (invT g))⁻¹ from map_inv _ _, gdet_invT, inv_inv]
    simp only [F, lact, e1, invT_inv_val, Matrix.transpose_transpose, Fintype.card_fin]
    ring
  have hev : ∀ᶠ u in 𝓝 (1 : GL (Fin n) k), ∀ g, F (u * g) = F g := by
    have h2 : ∀ᶠ u in 𝓝 (1 : GL (Fin n) k), ν (gdet u) = 1 := by
      have : IsOpen ((fun u : GL (Fin n) k => Matrix.GeneralLinearGroup.det u) ⁻¹' (ν.ker : Set kˣ)) :=
        IsOpen.preimage Matrix.GeneralLinearGroup.continuous_det hν
      exact this.mem_nhds (by simp)
    filter_upwards [sb_left_invariant Φ hΦ.1, h2, hKo.mem_nhds (one_mem K)] with u h1 h2 h3 g
    funext Y
    simp only [F, gdet_mul, map_mul, h2, apow_mul, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO h3),
      Units.val_mul, Matrix.mul_assoc, h1, one_mul]
  have hlc : IsLocallyConstant F := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have ht : Filter.Tendsto (fun y : GL (Fin n) k => y * x⁻¹) (𝓝 x) (𝓝 1) := by
      simpa using ((continuous_mul_const x⁻¹).tendsto x)
    filter_upwards [ht.eventually hev] with y hy
    simpa using hy x
  have hfin : (F '' K).Finite := by
    have : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_KO (k := k) (n := Fin n))
    have h := (hlc.comp_continuous (continuous_subtype_val (p := fun g => g ∈ K))).range_finite
    refine h.subset ?_
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  set μ := (haarVol K).restrict K with hμ
  have hμ1 : μ Set.univ = 1 := by rw [hμ, Measure.restrict_apply_univ, hK1]
  have : IsFiniteMeasure μ := ⟨by rw [hμ1]; exact ENNReal.one_lt_top⟩
  have hI := integral_comp_finite μ F hfin.toFinset
    (by
      filter_upwards [ae_restrict_mem hKm] with g hg
      exact hfin.mem_toFinset.2 ⟨g, hg, rfl⟩)
    (fun v => (hlc.isOpen_fiber v).measurableSet)
  have hs1 : ∑ v ∈ hfin.toFinset, (μ.real (F ⁻¹' {v}) : ℂ) = 1 := by
    have := hI fun _ => 1
    simpa [Measure.real, hμ1] using this.symm
  have hA : ∑ v ∈ hfin.toFinset, (μ.real (F ⁻¹' {v}) : ℂ) • v = 0 := by
    funext Y
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hI fun v => v Y]
    by_cases hY : Y ∈ S
    · rw [hμ, setIntegral_eq_integral_of_forall_compl_eq_zero]
      · exact h0 Y hY
      · intro g hg
        have : g.val * Y ∉ S := fun h => hg (hrig g Y hY h)
        simp [F, hsupp _ this]
    · refine setIntegral_eq_zero_of_forall_eq_zero fun g hg => ?_
      have : g.val * Y ∉ S := fun h => hY (by
        have := hst g⁻¹ (inv_mem hg) _ h
        rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this)
      simp [F, hsupp _ this]
  have hΦe : Φ = -∑ v ∈ hfin.toFinset, (μ.real (F ⁻¹' {v}) : ℂ) • (v - Φ) := by
    simp only [smul_sub, Finset.sum_sub_distrib, hA, ← Finset.sum_smul, hs1, one_smul, zero_sub, neg_neg]
  rw [hΦe]
  refine neg_mem (Submodule.sum_mem _ fun v hv => Submodule.smul_mem _ _ ?_)
  obtain ⟨g, -, rfl⟩ := hfin.mem_toFinset.1 hv
  exact Submodule.subset_span ⟨(invT g)⁻¹, Φ, hΦ, by rw [hFl]⟩

end GlobalTheory.FullRankCoinv.Average
end
end

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_character_orbital_integral_stable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ (S : Set (Matrix (Fin n) (Fin d) k)),
    (∀ (E : GL (Fin n) k), ∀ Y ∈ S, E.val * Y ∈ S → E ∈ GlobalTheory.SplitWeil.KO k (Fin n)) →
    (∀ E ∈ GlobalTheory.SplitWeil.KO k (Fin n), ∀ Y ∈ S, E.val * Y ∈ S) →
    ∀ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, (∀ Y, Y ∉ S → Φ Y = 0) →
    (∀ Y ∈ S, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y = 0) → Φ ∈ GlobalTheory.FullRankCoinv.augRk n d ν := by
  atlas_forward_decl GlobalTheory.FullRankCoinv.Average.mem_augRk_of_smallF_eq_zero
end

section
section
noncomputable section

open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix

namespace GlobalTheory.FullRankCoinv

theorem mem_augRk_of_fibre_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    (∀ h : GL (Fin d) k, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (GlobalTheory.FullRankCoinv.Y0 k n d * h.val) = 0) →
      Ψ ∈ GlobalTheory.FullRankCoinv.augRk n d ν := by
  intro k _ _ _ _ _ _ n d ν hnd hν Ψ hΨ hT
  have hT' : ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank = n →
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y = 0 := fun Y hY => by
    obtain ⟨h, rfl⟩ := GlobalTheory.T.full_rank_normal_form_orbit k n d hnd Y hY
    exact hT h
  obtain ⟨s, hs⟩ := GlobalTheory.T.open_cover_finite_translates_support k n d _ (GlobalTheory.T.isClopen_unit_minor_set k n d).isOpen (GlobalTheory.T.exists_unit_minor_translate k n d) Ψ hΨ
  obtain ⟨Φ, hΦ, hS, hdiff, hF⟩ := GlobalTheory.T.clopen_integrability_full_rank_orbit k n d ν _ (GlobalTheory.T.isClopen_unit_minor_set k n d)
    (fun Φ hΦ Y => GlobalTheory.T.integrable_full_rank_zeta k n d ν hν Φ hΦ Y) s Ψ hΨ hs
  have hA := GlobalTheory.T.smooth_character_orbital_integral_stable k n d ν hν _ (GlobalTheory.T.integral_group_of_unit_minor_stable k n d) (fun E hE Y hY => GlobalTheory.T.unit_minor_stable_integral_group k n d E Y hE hY) Φ hΦ hS
    (fun Y hY => by rw [hF]; exact hT' Y (GlobalTheory.T.rank_eq_of_unit_minor k n d Y hY))
  have e : Ψ = (Ψ - Φ) + Φ := by abel
  rw [e]; exact add_mem hdiff hA

end GlobalTheory.FullRankCoinv
end
end

open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_rank_zeta_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    (∀ h : GL (Fin d) k, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (GlobalTheory.FullRankCoinv.Y0 k n d * h.val) = 0) →
      Ψ ∈ GlobalTheory.FullRankCoinv.augRk n d ν := by
  atlas_forward_decl GlobalTheory.FullRankCoinv.mem_augRk_of_fibre_eq_zero
end

section
noncomputable section

open MeasureTheory GlobalTheory.SplitFlip
open scoped Topology Matrix

namespace GlobalTheory.FullRankCoinv

theorem sb_right_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (Ψ : Matrix (Fin n) (Fin d) k → ℂ), Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) →
    ∃ U ∈ nhds (1 : GL (Fin d) k), ∀ u ∈ U, ∀ X : Matrix (Fin n) (Fin d) k, Ψ (X * u.val) = Ψ X := by
  intro k _ _ _ _ n d Ψ hΨ
  have h1 : ∀ᶠ u in 𝓝 (1 : GL (Fin d) k), ∀ X ∈ tsupport Ψ, Ψ (X * u.val) = Ψ X := by
    refine IsCompact.eventually_forall_of_forall_eventually hΨ.2 fun y _ => ?_
    have h2 : IsLocallyConstant fun q : GL (Fin d) k × Matrix (Fin n) (Fin d) k => (Ψ (q.2 * q.1.val), Ψ q.2) :=
      (hΨ.1.comp_continuous (by fun_prop)).prodMk (hΨ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (1, y)] with q hq
    simp only [Prod.mk.injEq, Units.val_one, Matrix.mul_one] at hq
    rw [hq.1, hq.2]
  have h3 : ∀ᶠ u in 𝓝 (1 : GL (Fin d) k), ∀ X ∈ tsupport Ψ, Ψ (X * (u⁻¹).val) = Ψ X := by
    have ht : Filter.Tendsto (fun u : GL (Fin d) k => u⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv.tendsto (1 : GL (Fin d) k))
    exact ht.eventually h1
  refine ⟨_, h1.and h3, fun u hu X => ?_⟩
  by_cases hX : X ∈ tsupport Ψ
  · exact hu.1 X hX
  by_cases hX' : X * u.val ∈ tsupport Ψ
  · have := hu.2 _ hX'
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hX, image_eq_zero_of_notMem_tsupport hX']

theorem fibre_coinvariants : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∃ Z : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] (GL (Fin d) k → ℂ),
      (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ ∈ GlobalTheory.FullRankCoinv.indSp k n d ν) ∧
      (∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν, ∃ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ = f) ∧
      (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ = 0 → Ψ ∈ GlobalTheory.FullRankCoinv.augRk n d ν) ∧
      ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ h₀ : GL (Fin d) k,
        Z (fun Y => Ψ (Y * h₀.1)) = fun h => Z Ψ (h * h₀) := by
  intro k _ _ _ _ n d ν hnd hν
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  let Z₀ : fullRk k n d →ₗ[ℂ] (GL (Fin d) k → ℂ) :=
    { toFun := fun Ψ h => smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ.1 (Y0 k n d * h.val)
      map_add' := fun Ψ Φ => by
        funext h
        simp only [smallF, Submodule.coe_add, Pi.add_apply]
        rw [← integral_add (GlobalTheory.T.integrable_full_rank_zeta k n d ν hν Ψ.1 Ψ.2 _) (GlobalTheory.T.integrable_full_rank_zeta k n d ν hν Φ.1 Φ.2 _)]
        congr 1; funext g; ring
      map_smul' := fun c Ψ => by
        funext h
        simp only [smallF, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext g; ring }
  obtain ⟨Z, hZ⟩ := LinearMap.exists_extend Z₀
  have hZΨ : ∀ Ψ (hΨ : Ψ ∈ fullRk k n d),
      Z Ψ = fun h => smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (Y0 k n d * h.val) :=
    fun Ψ hΨ => LinearMap.congr_fun hZ ⟨Ψ, hΨ⟩
  refine ⟨Z, fun Ψ hΨ => ?_, fun f hf => ?_, fun Ψ hΨ h0 => ?_, fun Ψ hΨ h₀ => ?_⟩
  · rw [hZΨ Ψ hΨ]
    refine ⟨?_, fun b h D hD => ?_⟩
    · obtain ⟨U, hU, hinv⟩ := sb_right_invariant k n d Ψ hΨ.1
      refine ⟨U, hU, fun h u hu => ?_⟩
      simp only [smallF]
      congr 1; funext g
      rw [Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv u hu, Matrix.mul_assoc]
    · have e1 : Y0 k n d * (b * h).val = D.val * (Y0 k n d * h.val) := by
        rw [Units.val_mul, ← Matrix.mul_assoc, hD, Matrix.mul_assoc]
      have key := smallF_mul_left (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ D (Y0 k n d * h.val)
      simp only [Fintype.card_fin] at key
      show smallF _ ν Ψ (Y0 k n d * (b * h).val) = _
      rw [e1]
      beta_reduce
      rw [← key, Units.val_inv_eq_inv_val, neg_div, apow_neg]
      have h1 : (ν (gdet D) : ℂ) ≠ 0 := Units.ne_zero _
      have h2 := apow_ne_zero (gdet D) ((d : ℂ) / 2)
      field_simp
  · obtain ⟨Ψ, hΨ, hf'⟩ := GlobalTheory.T.full_rank_zeta_surjective k n d ν hnd hν f hf
    exact ⟨Ψ, hΨ, by rw [hZΨ Ψ hΨ]; funext h; exact hf' h⟩
  · refine GlobalTheory.T.full_rank_zeta_kernel k n d ν hnd hν Ψ hΨ fun h => ?_
    have := congrFun h0 h
    rwa [hZΨ Ψ hΨ] at this
  · have hmem : (fun Y => Ψ (Y * h₀.1)) ∈ fullRk k n d := by
      let e : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k :=
        { toFun := fun X => X * h₀.1
          invFun := fun X => X * (h₀⁻¹).1
          left_inv := fun X => by simp [Matrix.mul_assoc]
          right_inv := fun X => by simp [Matrix.mul_assoc]
          continuous_toFun := by fun_prop
          continuous_invFun := by fun_prop }
      refine ⟨⟨hΨ.1.1.comp_continuous e.continuous, hΨ.1.2.comp_homeomorph e⟩, fun Y hY => hΨ.2 _ ?_⟩
      rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units h₀)]
    rw [hZΨ _ hmem, hZΨ _ hΨ]
    funext h
    simp only [smallF, Units.val_mul, Matrix.mul_assoc]

end GlobalTheory.FullRankCoinv
end
end

section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_rank_coinvariant_induced_iso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∃ Z : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] (GL (Fin d) k → ℂ),
      (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ ∈ GlobalTheory.FullRankCoinv.indSp k n d ν) ∧
      (∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν, ∃ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ = f) ∧
      (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ = 0 → Ψ ∈ GlobalTheory.FullRankCoinv.augRk n d ν) ∧
      ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ h₀ : GL (Fin d) k,
        Z (fun Y => Ψ (Y * h₀.1)) = fun h => Z Ψ (h * h₀) := by
  first | exact @GlobalTheory.FullRankCoinv.fibre_coinvariants | exact GlobalTheory.FullRankCoinv.fibre_coinvariants | (intros; apply GlobalTheory.FullRankCoinv.fibre_coinvariants <;> assumption)
end
