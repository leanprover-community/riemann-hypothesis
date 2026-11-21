import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaZeroEqProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataConductorOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointComponentMemSpanOfLatticeGenerators
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsCombAt

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocMod.SevPl

open GlobalTheory.IdemSupport

theorem ev_sum {D : D7} {Φ : Formalism.L2.Theta.AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} {ι : Type}
    (s : Finset ι) (f : ι → Formalism.L2.Theta.AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ (∑ i ∈ s, f i) Q = ∑ i ∈ s, Φ (f i) Q := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty]; exact ev_zero Q
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ev_add, ih]

theorem cP_cP {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) : cP (D := D) (cP (D := D) P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by
    show cO D (cO D x) ∈ P.asIdeal ↔ x ∈ P.asIdeal
    rw [cO_cO])

theorem mul_conj_add_eq_zero {D : D7} {Pg : Finset (HeightOneSpectrum (𝓞 D.host.E))} {E : Formalism.L2.Theta.AE D}
    (hE : IsIdemSum E Pg) {P P' : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ Pg) (hP' : P' ∈ Pg) (hne : P ≠ P')
    {e e' : Formalism.L2.Theta.AE D} (he : Formalism.L2.NTheta.IsIdemAt e P) (he' : Formalism.L2.NTheta.IsIdemAt e' P') :
    e * (e' + cA D e') = 0 := by
  classical
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hd := delta_of_isIdemAt hΦ he
  have hd' := delta_of_isIdemAt hΦ he'
  have hc' := delta_conj hΦ hd'
  have hne2 : P ≠ cP (D := D) P' := by
    intro hPc
    obtain ⟨⟨es, hes, rfl⟩, h0⟩ := hE
    have h1 : Φ (∑ Q ∈ Pg, es Q) P = 1 := by
      rw [ev_sum, Finset.sum_eq_single_of_mem P hP fun Q hQ hQP => ?_]
      · exact (delta_of_isIdemAt hΦ (hes P hP)).2.1
      · exact (delta_of_isIdemAt hΦ (hes Q hQ)).2.2 P (Ne.symm hQP)
    have h2 : Φ (cA D (∑ Q ∈ Pg, es Q)) P = 1 := by
      rw [map_sum, ev_sum, Finset.sum_eq_single_of_mem P' hP' fun Q hQ hQP => ?_]
      · rw [hPc]; exact (delta_conj hΦ (delta_of_isIdemAt hΦ (hes P' hP'))).2.1
      · refine (delta_conj hΦ (delta_of_isIdemAt hΦ (hes Q hQ))).2.2 P fun h => hQP ?_
        have h4 := congrArg (cP (D := D)) (h.symm.trans hPc)
        rwa [cP_cP, cP_cP] at h4
    have h3 := ev_mul (Φ := Φ) (∑ Q ∈ Pg, es Q) (cA D (∑ Q ∈ Pg, es Q)) P
    rw [h0, ev_zero, h1, h2, one_mul] at h3
    exact zero_ne_one h3
  refine hΦ.ext' (by rw [map_mul, hd.1, zero_mul, map_zero]) fun Q => ?_
  rw [ev_mul, ev_add, ev_zero]
  by_cases hQ : Q = P
  · subst hQ; rw [hd'.2.2 Q hne, hc'.2.2 Q hne2, add_zero, mul_zero]
  · rw [hd.2.2 Q hQ, zero_mul]

theorem pr_eq_zero {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {f : Formalism.L2.Theta.AE D} (h : q.e * f = 0) : q.pr f = 0 := by
  rw [← q.pr_sec (q.pr f), q.sec_pr, h, map_zero]

theorem map_mt_eq_one {D : D7} {k : Type} [Field k] (π : Formalism.L2.Theta.AE D →+* k) {e : Formalism.L2.Theta.AE D}
    (V : HSp D) (g : GA D V) (hs : Formalism.L2.Theta.SuppAt e V g) (h0 : π (e + cA D e) = 0) :
    (mt V g).map π = 1 := by
  ext i j
  have h1 := congrArg π (hs i j)
  rw [map_mul, h0, zero_mul, Matrix.sub_apply, map_sub] at h1
  rw [Matrix.map_apply, sub_eq_zero.1 h1.symm]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

def locHom {D : D7} {k : Type} [Field k] (π : Formalism.L2.Theta.AE D →+* k) (V : HSp D) :
    GA D V →* Matrix (Fin V.rank) (Fin V.rank) k where
  toFun g := (mt V g).map π
  map_one' := by rw [GlobalTheory.IdemSupport.mt_one]; exact Matrix.map_one π π.map_zero π.map_one
  map_mul' g h := by rw [GlobalTheory.IdemSupport.mt_mul, Matrix.map_mul]

theorem prod_map_single {M α : Type} [Monoid M] (g : α → M) (a : α) :
    ∀ l : List α, l.Nodup → a ∈ l → (∀ x ∈ l, x ≠ a → g x = 1) → (l.map g).prod = g a
  | [], _, ha, _ => by simp at ha
  | x :: l, hn, ha, h1 => by
    rw [List.map_cons, List.prod_cons]
    obtain ⟨hx, hl⟩ := List.nodup_cons.1 hn
    by_cases hxa : x = a
    · subst hxa
      rw [List.prod_eq_one fun y hy => ?_, mul_one]
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      exact h1 z (List.mem_cons_of_mem _ hz) fun h => hx (h ▸ hz)
    · rw [h1 x (by simp) hxa, one_mul]
      exact prod_map_single g a l hl ((List.mem_cons.1 ha).resolve_left (Ne.symm hxa))
        fun y hy => h1 y (List.mem_cons_of_mem _ hy)

end GlobalTheory.LocMod.SevPl

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_data_conductor_one : ∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), d.c.Is → PP ∈ d.c.Pg → Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ ψk : AddChar k Circle, (ofSplit q).IsChar d.c.ψ ψk → HasConductor ψk 1 → ∀ s ρ : ℕ, s = 2 * ρ → ∃ S : SymData k s D.R.k, S.ψ = ψk ∧ ∀ j, 1 ≤ j → j ≤ D.R.m → (ofSplit q).IsComp (d.c.chS j)⁻¹ (S.μ j) := by
  first | exact @GlobalTheory.LocMod.SymChainAt.exists_symData_at | exact GlobalTheory.LocMod.SymChainAt.exists_symData_at | (intros; apply GlobalTheory.LocMod.SymChainAt.exists_symData_at <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.TopFrames

theorem exists_frame {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (hc : Fintype.card Y = N) (M : Matrix (Fin N) Y k) (hM : ∀ y, M *ᵥ y = 0 → y = 0) :
    ∃ F : GlobalTheory.LocMod.Frame k N Y, F.β = M := by
  classical
  let e : Y ≃ Fin N := Fintype.equivFinOfCardEq hc
  have hinj : Function.Injective (M.submatrix id e.symm).mulVec := by
    intro y y' h
    have h0 : (M.submatrix id e.symm) *ᵥ (y - y') = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
    rw [Matrix.submatrix_mulVec_equiv] at h0
    have h1 := hM _ (by simpa using h0)
    funext i
    have := congrFun h1 (e.symm i)
    simpa [sub_eq_zero] using this
  obtain ⟨U, hU⟩ := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hM' : M = (U.val).submatrix id e := by
    rw [hU]; ext i j; simp
  refine ⟨⟨M, (U⁻¹).val.submatrix e id, ?_, ?_⟩, rfl⟩
  · rw [hM', Matrix.submatrix_mul_equiv, Units.mul_inv]; rfl
  · rw [hM']
    have := Matrix.submatrix_mul_equiv (U⁻¹).val U.val e (Equiv.refl _) e
    simp only [Equiv.coe_refl] at this
    rw [this, Units.inv_mul, Matrix.submatrix_one_equiv]

theorem eq_zero_of_mul_int {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a : k) (h : ∀ c : k, c * a ∈ 𝒪[k]) : a = 0 := by
  by_contra ha
  obtain ⟨x, hx⟩ := Valuation.IsNontrivial.exists_one_lt (v := valuation k)
  have := h (x / a)
  rw [div_mul_cancel₀ _ ha, Valuation.mem_integer_iff] at this
  exact absurd hx (not_lt.mpr this)

theorem top_frames : ∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (s : ℕ) (hs : s + 1 + 1 = D.R.m), d.Lz.rank = 1 → Fintype.card (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2)) = D.sp.X'.rank → ∀ (a : k) (z₀ : Fin d.Lz.rank → k), valuation k a = 1 → (∀ h, (τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * a)) • fun i => (ofSplit q).pr ((d.bes s 0 h).ζ i)) → (∀ B : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) (AE D), B.map (toEAf D) = d.top.β.val → ∀ (y : Fin D.sp.X'.rank → k) (b : k), (fun i => q.sec (((d.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr *ᵥ (B.map (ofSplit q).π *ᵥ y) + b • ((d.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀)) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X (s + 1 + 1)) (d.x (s + 1 + 1)).L (· = q.v) ↔ (∀ i, y i ∈ 𝒪[k]) ∧ b ∈ 𝒪[k]) → ∃ (FT : GlobalTheory.LocMod.Frame k D.sp.X'.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2))) (FM : GlobalTheory.LocMod.Frame k (D.sp.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)) (c : k), valuation k c = 1 ∧ FM.β = fromCols ((d.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β) (Matrix.of fun r _ => ((d.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r) ∧ (∀ h, (τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * c)) • fun i => (ofSplit q).pr ((d.bes s 0 h).ζ i)) ∧ (∀ y : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FM.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X (s + 1 + 1)) (d.x (s + 1 + 1)).L (· = q.v)) ∧ ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ≃ Fin D.sp.X'.rank, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) D.sp.X' 1 d.top.β (FT.β.submatrix id e.symm) := by
  intro D u d τ k _ _ _ _ q s hs hr hc a z₀ ha hτ hsp
  obtain ⟨e, he⟩ := PinModel.exists_ord _ _ _ _ _ hc
  choose f hf using PinModel.toEAf_surj D
  have hB : (d.top.β.val.map f).map (toEAf D) = d.top.β.val := by
    ext i j; exact hf _
  have H := hsp _ hB
  set P := (d.top.β.val.map f).map (ofSplit q).π with hP
  set A := (d.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr with hA
  set w := (d.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀ with hw
  have H0 : ∀ (y : Fin D.sp.X'.rank → k) (b : k), A *ᵥ (P *ᵥ y) + b • w = 0 → y = 0 ∧ b = 0 := by
    intro y b h
    have key : ∀ c : k, (∀ i, c * y i ∈ 𝒪[k]) ∧ c * b ∈ 𝒪[k] := by
      intro c
      refine (H (c • y) (c * b)).mp ?_
      have : A *ᵥ (P *ᵥ (c • y)) + (c * b) • w = 0 := by
        rw [Matrix.mulVec_smul, Matrix.mulVec_smul, mul_smul, ← smul_add, h, smul_zero]
      rw [this]
      simp only [Pi.zero_apply, map_zero]
      exact zero_mem _
    exact ⟨funext fun i => eq_zero_of_mul_int _ fun c => (key c).1 i,
      eq_zero_of_mul_int _ fun c => (key c).2⟩
  have hsub : ∀ y, P.submatrix id e *ᵥ y = P *ᵥ (y ∘ e.symm) := by
    intro y; rw [Matrix.submatrix_mulVec_equiv]; rfl
  obtain ⟨FT, hFT⟩ := exists_frame hc (P.submatrix id e) (by
    intro y hy
    rw [hsub] at hy
    have := (H0 (y ∘ e.symm) 0 (by rw [hy]; simp)).1
    funext i
    simpa using congrFun this (e i))
  have hmul : ∀ y : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit → k,
      fromCols (A * FT.β) (Matrix.of fun r (_ : Unit) => w r) *ᵥ y
        = A *ᵥ (P *ᵥ ((y ∘ Sum.inl) ∘ e.symm)) + y (Sum.inr ()) • w := by
    intro y
    rw [Matrix.fromCols_mulVec, ← Matrix.mulVec_mulVec, hFT, hsub]
    congr 1
    funext r
    simp [Matrix.mulVec, dotProduct, mul_comm]
  obtain ⟨FM, hFM⟩ := exists_frame (N := (D.sp.X (s + 1 + 1)).rank)
    (Y := Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)
    (by rw [Fintype.card_sum, hc, ← (d.oT (s + 1 + 1) hs).rank_add, hr]; simp)
    (fromCols (A * FT.β) (Matrix.of fun r (_ : Unit) => w r)) (by
      intro y hy
      rw [hmul] at hy
      obtain ⟨h1, h2⟩ := H0 _ _ hy
      funext i
      rcases i with i | i
      · simpa using congrFun h1 (e i)
      · exact h2)
  refine ⟨FT, FM, a, ha, hFM, hτ, ?_, e, he, ?_⟩
  · intro y
    rw [hFM, hmul, H]
    constructor
    · intro h; exact ⟨fun i => h _, h _⟩
    · rintro ⟨h1, h2⟩ (i | i)
      · simpa using h1 (e i)
      · exact h2
  · intro b hb
    have h1 : Formalism.L2.Theta.mt D.sp.X' 1 = 1 := by simp [Formalism.L2.Theta.mt]
    rw [h1, Matrix.one_mul, hFT]
    ext i j
    simp only [hP, Matrix.map_apply, Matrix.submatrix_apply, id, Equiv.apply_symm_apply]
    apply PinModel.pi_congr
    rw [hf]
    exact congrFun (congrFun hb i) j

end GlobalTheory.LocMod.TopFrames
end

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.PinInhab

section SlopeTestRemainingChoices
open GlobalTheory.FinPl (SplitPt idAt idOff grpAt grpOff congGrp compAt)
open GlobalTheory.IdemSupport GlobalTheory.LocMod.SevPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mul_add (q : SplitPt D k) : q.e * (q.e + cA D q.e) = q.e := by
  obtain ⟨h1, h2, -⟩ := q.split
  rw [mul_add, h1, h2, add_zero]

theorem v_eq_under (q : SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt q.e P) :
    q.v = P.under (𝓞 D.host.F) := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨ε, hε, hs⟩ := q.above
  by_contra hne
  have h0 := (place_comp hΦ hε).2.2 P (fun e => hne e.symm)
  have h1 := ev_mul (Φ := Φ) q.e (q.e + cA D q.e) P
  rw [e_mul_add, hs, h0, mul_zero, (delta_of_isIdemAt hΦ h).2.1] at h1
  exact one_ne_zero h1

theorem idem_unique {P : HeightOneSpectrum (𝓞 D.host.E)} {e e' : Formalism.L2.Theta.AE D} (h : Formalism.L2.NTheta.IsIdemAt e P)
    (h' : Formalism.L2.NTheta.IsIdemAt e' P) : e = e' := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hd := delta_of_isIdemAt hΦ h
  have hd' := delta_of_isIdemAt hΦ h'
  refine hΦ.ext' (by rw [hd.1, hd'.1]) fun Q => ?_
  by_cases hQ : Q = P
  · subst hQ; rw [hd.2.1, hd'.2.1]
  · rw [hd.2.2 Q hQ, hd'.2.2 Q hQ]

theorem mem_congGrp {V : HSp D} {I : Ideal (Formalism.L2.Theta.AE D)} {g : GA D V} :
    g ∈ congGrp V I ↔ ∀ i j, (mt V g - 1) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun x : GL (Fin V.rank) (Formalism.L2.Theta.AE D ⧸ I) => x.1 i j) h
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this
  · intro h
    ext i j
    have := h i j
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq] at this
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this

theorem mem_idAt_of_supp (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {a : Formalism.L2.Theta.AE D}
    (h : (q.e + cA D q.e) * a = a) : a ∈ idAt D P := by
  obtain ⟨ε, hε, hs⟩ := q.above
  have h1 := ((GlobalTheory.FinPl.placeIdem_acts D q.v ε hε).1 a).2 (hs ▸ h)
  rw [GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at h1 ⊢
  exact ⟨h1.1, fun w hw => h1.2 w fun e => hw (e ▸ hP)⟩

theorem mem_grpAt_of_supp (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {V : HSp D} {g : GA D V}
    (hg : SuppAt q.e V g) : g ∈ grpAt V P :=
  mem_congGrp.2 fun i j => mem_idAt_of_supp q hP (hg i j)

theorem pr_eq_zero_of_off (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {a : Formalism.L2.Theta.AE D}
    (ha : a ∈ idOff D P) : q.pr a = 0 := by
  have he : q.e ∈ idAt D (· = q.v) := mem_idAt_of_supp q (P := (· = q.v)) rfl (by rw [mul_comm, e_mul_add])
  rw [GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at he
  have hv : compAt D q.v a = 0 := by
    unfold idOff at ha
    rw [Submodule.mem_iInf] at ha
    exact RingHom.mem_ker.1 (ha ⟨q.v, hP⟩)
  refine pr_eq_zero q (GlobalTheory.FinPl.CMAdele_eq_zero_of_infinite_and_finite_components_zero D _ ?_ fun w => ?_)
  · rw [RingHom.map_mul, he.1, zero_mul]
  · rw [RingHom.map_mul]
    by_cases hw : w = q.v
    · rw [hw, hv, mul_zero]
    · rw [he.2 w hw, zero_mul]

theorem map_mt_eq_one_of_off (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {V : HSp D} {g : GA D V}
    (hg : g ∈ grpOff V P) : (mt V g).map q.pr = 1 := by
  ext i j
  have h1 := pr_eq_zero_of_off q hP (mem_congGrp.1 hg i j)
  rw [Matrix.sub_apply, map_sub] at h1
  rw [Matrix.map_apply, sub_eq_zero.1 h1]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

theorem exists_gAt_all_places_mul : ∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E), d.c.Is → (∀ PP : d.c.Pg, ∃ (e : Formalism.L2.Theta.AE D) (t : ∀ j, GA D (d.st j).V), Formalism.L2.NTheta.IsIdemAt e PP.1 ∧ (∀ j, SuppAt e (d.st j).V (t j)) ∧ Nonempty (GAt (d := { d with t := t }) τ PP.1)) → ∀ t₀ : ∀ j, GA D (d.st j).V, (∀ j, t₀ j ∈ GlobalTheory.FinPl.grpOff (d.st j).V (· ∈ d.c.S)) → ∃ t' : ∀ j, GA D (d.st j).V, (∀ j, t' j * (t₀ j)⁻¹ ∈ GlobalTheory.FinPl.grpAt (d.st j).V (· ∈ d.c.S)) ∧ (∀ j, t₀ j ∈ GfC (d.st j).V → t' j ∈ GfC (d.st j).V) ∧ Nonempty (∀ PP : d.c.Pg, GAt (d := { d with t := t' }) τ PP.1) := by
  intro D u d τ hIs h t₀ ht₀
  classical
  have h' : ∀ PP : d.c.Pg, ∃ (t : ∀ j, GA D (d.st j).V) (G : GAt (d := { d with t := t }) τ PP.1),
      ∀ j, SuppAt G.q.e (d.st j).V (t j) := fun PP => by
    obtain ⟨e, t, he, ht, ⟨G⟩⟩ := h PP
    exact ⟨t, G, by rw [idem_unique G.idem he]; exact ht⟩
  choose T G hS using h'
  obtain ⟨E, hE⟩ := hIs.split
  have hv : ∀ PP : d.c.Pg, (G PP).q.v ∈ d.c.S := fun PP => by
    rw [v_eq_under (G PP).q (G PP).idem]
    exact Finset.mem_image_of_mem _ PP.2
  let t' : ∀ j, GA D (d.st j).V := fun j => (d.c.Pg.attach.toList.map fun PP => T PP j).prod * t₀ j
  refine ⟨t', fun j => ?_, fun j h0 => mul_mem (list_prod_mem fun x hx => ?_) h0, ⟨fun PP => ?_⟩⟩
  · rw [mul_inv_cancel_right]
    refine list_prod_mem fun x hx => ?_
    obtain ⟨Q, -, rfl⟩ := List.mem_map.1 hx
    exact mem_grpAt_of_supp (G Q).q (hv Q) (hS Q j)
  · obtain ⟨Q, -, rfl⟩ := List.mem_map.1 hx
    exact GlobalTheory.WeilProduct.mem_GfC_of_suppAt (G Q).q.split (hS Q j)
  have key : ∀ j, (mt (d.st j).V (t' j)).map (ofSplit (G PP).q).π =
      (mt (d.st j).V (T PP j)).map (ofSplit (G PP).q).π := by
    intro j
    change locHom (ofSplit (G PP).q).π (d.st j).V _ = locHom (ofSplit (G PP).q).π (d.st j).V _
    have h0 : locHom (ofSplit (G PP).q).π (d.st j).V (t₀ j) = 1 := map_mt_eq_one_of_off (G PP).q (hv PP) (ht₀ j)
    rw [map_mul, h0, mul_one, map_list_prod, List.map_map]
    refine prod_map_single _ PP _ (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_attach _ _)) fun PP' _ hne => ?_
    exact map_mt_eq_one _ _ _ (hS PP' j) (pr_eq_zero (G PP).q
      (mul_conj_add_eq_zero hE PP.2 PP'.2 (fun h => hne (Subtype.ext h).symm) (G PP).idem (G PP').idem))
  have hfr : ∀ j c (hc : j + c = (G PP).s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin ((G PP).s + 1)) (Fin D.R.t) j ≃ Fin (d.st j).V.rank,
      GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit (G PP).q) (d.st j).V (t' j) (d.st j).β
        ((((G PP).FY j c hc).β * (((G PP).S.T (Fin D.R.t)).bas j c hc).val).submatrix id
          fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i)) := by
    intro j c hc
    obtain ⟨e, ho, hm⟩ := (G PP).frame j c hc
    refine ⟨e, ho, fun b hb => ?_⟩
    refine Eq.trans ?_ (hm b hb)
    rw [Matrix.map_mul, Matrix.map_mul]
    exact congrArg (· * b.map _) (key j)
  exact { G PP with frame := hfr }

end SlopeTestRemainingChoices

theorem main :
    (∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) τ (G : ∀ PP : d.c.Pg, GAt d τ PP.1), d.c.Is → (∃ P : Formalism.L2.DIV.LevelP d.c.Pg D.R.r ℂ, (∀ g, g ∈ P.H ↔ ∀ PP, ∃ x, (G PP).Red x (g PP)) ∧ ∀ (g : P.H) (x : ∀ PP, (G PP).S.P.J), (∀ PP, (G PP).Red (x PP) (g.1 PP)) → P.chi g = ∏ PP, (G PP).S.P.lam (x PP)) ∧ ∃ cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ, (∀ j, ∀ w ∈ (cG j).support, GlobalTheory.FinPl.MxAt (· ∈ d.c.S) w) ∧ ∀ j, j < D.R.m → ∀ f, IsThetaFunO d.c.ψ _ _ f → comb d.c.ψ _ _ (cG j) f = d.c.Pg.attach.toList.foldr (fun PP f' => comb d.c.ψ _ _ ((G PP).cg j) f') f) ∧
    (∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E), d.c.Is → (∀ PP : d.c.Pg, ∃ (t : ∀ j, GA D (d.st j).V) (G : GAt (d := { d with t := t }) τ PP.1), ∀ j, SuppAt G.q.e (d.st j).V (t j)) → ∀ t₀ : ∀ j, GA D (d.st j).V, (∀ j, t₀ j ∈ GlobalTheory.FinPl.grpOff (d.st j).V (· ∈ d.c.S)) → ∃ t' : ∀ j, GA D (d.st j).V, (∀ j, t' j * (t₀ j)⁻¹ ∈ GlobalTheory.FinPl.grpAt (d.st j).V (· ∈ d.c.S)) ∧ (∀ j, t₀ j ∈ GfC (d.st j).V → t' j ∈ GfC (d.st j).V) ∧ Nonempty (∀ PP : d.c.Pg, GAt (d := { d with t := t' }) τ PP.1)) ∧
    (∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), d.c.Is → PP ∈ d.c.Pg → Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ ψk : AddChar k Circle, (ofSplit q).IsChar d.c.ψ ψk → HasConductor ψk 1 → ∀ s ρ : ℕ, s = 2 * ρ → ∃ S : SymData k s D.R.k, S.ψ = ψk ∧ ∀ j, 1 ≤ j → j ≤ D.R.m → (ofSplit q).IsComp (d.c.chS j)⁻¹ (S.μ j)) ∧
    (∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y], q.UnitAA → Submodule.IsLattice D.host.E L → Fintype.card Y = S.rank → ∃ F : GlobalTheory.LocMod.Frame k S.rank Y, ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v)) ∧
    (∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (s : ℕ) (hs : s + 1 + 1 = D.R.m), d.Lz.rank = 1 → Fintype.card (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2)) = D.sp.X'.rank → ∀ (a : k) (z₀ : Fin d.Lz.rank → k), valuation k a = 1 → (∀ h, (τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * a)) • fun i => (ofSplit q).pr ((d.bes s 0 h).ζ i)) → (∀ B : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) (AE D), B.map (toEAf D) = d.top.β.val → ∀ (y : Fin D.sp.X'.rank → k) (b : k), (fun i => q.sec (((d.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr *ᵥ (B.map (ofSplit q).π *ᵥ y) + b • ((d.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀)) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X (s + 1 + 1)) (d.x (s + 1 + 1)).L (· = q.v) ↔ (∀ i, y i ∈ 𝒪[k]) ∧ b ∈ 𝒪[k]) → ∃ (FT : GlobalTheory.LocMod.Frame k D.sp.X'.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2))) (FM : GlobalTheory.LocMod.Frame k (D.sp.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)) (c : k), valuation k c = 1 ∧ FM.β = fromCols ((d.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β) (Matrix.of fun r _ => ((d.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r) ∧ (∀ h, (τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * c)) • fun i => (ofSplit q).pr ((d.bes s 0 h).ζ i)) ∧ (∀ y : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FM.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X (s + 1 + 1)) (d.x (s + 1 + 1)).L (· = q.v)) ∧ ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ≃ Fin D.sp.X'.rank, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) D.sp.X' 1 d.top.β (FT.β.submatrix id e.symm)) ∧
    (∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (q : GlobalTheory.FinPl.SplitPt D k) (s : ℕ) (S : SymData k s D.R.k) (FX : ∀ j, j ≤ s + 1 → GlobalTheory.LocMod.Frame k (D.sp.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j)) (FM : GlobalTheory.LocMod.Frame k (D.sp.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)), IsStdChar D d.c.ψ (-1) → ∃ cg : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ, (∀ j c (H : j + 1 + c = s), (ofSplit q).IsCombAt d.c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) (cg j) ((S.T (Fin D.R.t)).entry S.ψ ν j c H 1 1)) ∧ (ofSplit q).IsCombAt d.c.ψ (FX s (by omega)) (FX (s + 1) le_rfl) (cg s) (fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))) ∧ (ofSplit q).IsCombAt d.c.ψ (FX (s + 1) le_rfl) FM (cg (s + 1)) ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))) :=
  ⟨GlobalTheory.LevelComb.main,
    fun D u d τ hIs h => exists_gAt_all_places_mul D u d τ hIs fun PP =>
      let ⟨t, G, ht⟩ := h PP
      ⟨G.q.e, t, G.idem, ht, ⟨G⟩⟩,
    GlobalTheory.T.exists_symmetric_data_conductor_one, GlobalTheory.LocMod.FullLatFrame.exists_frame, GlobalTheory.LocMod.TopFrames.top_frames, GlobalTheory.LocMod.CombAt.exists_cg⟩

end GlobalTheory.LocMod.PinInhab
end
end
