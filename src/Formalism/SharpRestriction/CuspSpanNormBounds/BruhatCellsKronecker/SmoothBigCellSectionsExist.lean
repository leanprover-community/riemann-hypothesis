import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.StandardHypothesesOfScaleHyp
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TopsChoicePartA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalVolumePositivity

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.MainNotions.S.LocalFrameAxioms Formalism.MainNotions.LocalBesselAndTopKernel Formalism.QuantumDeterminants NumberField IsDedekindDomain ValuativeRel
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


theorem rho_eq {L : LatticeDataWithDual D} (h : IsLatGLOB D L) : L.ρ = rhoReal D := by
  funext i s
  exact (h i s).2.2







section Steps

variable (D) (large₂ : SizeData₂ D) (X : TermTie D) (Cw : ℝ) (Y : ∀ u u', LoopTie D large₂ X u u' Cw) (Z : TermLocs D X)
  (cN : D.what₂.Word → D.what₂.Word → ℝ) (Vm : ValMap D.R.k D.R.rS)

def AmplitudeIsBesselCoefficient : Prop :=
  ∀ (u u' : D.what₂.Word), u ≠ u' → ∀ (hT : 0 < Tr D u) (hT' : 0 < Tr D u'),
    ∃ f : ∀ v, MatKR D.R.k D.R.rS → ((localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp),
      IsAmpCoef (Y u u') hT hT' f

def SmoothBigCellSectionsExist : Prop :=
  ∀ (u u' : D.what₂.Word) (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (v : D.what₂.Tau),
    ∃ μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
      IsSection D.R.k D.R.rS (localBesselDatumAtRealPlace (Y u u') hT hT' v).z (localBesselDatumAtRealPlace (Y u u') hT hT' v).z' μsec

def DensityBound (Ce : ℝ) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word),
    ∃ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) (Dsup : ℝ), (∀ p, Irreducible (ϖ p)) ∧ 1 ≤ Dsup ∧ Dsup ≤ 2 ∧
      Dsup ≤ 1 + eSum D Ce ∧
      ∀ γ : D.s.Term u u', D.s.generic γ → Gpt (D.mem u).A.T (D.mem u').A.T (D.s.ptOf γ) ≠ 0 →
        densT (Z δ M hA u u') ϖ γ ≤ Dsup

def ColumnDominationBound : Prop :=
  ∀ (u u' : D.what₂.Word), u ≠ u' → ∀ (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (f : ∀ v, MatKR D.R.k D.R.rS → ((localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp)),
    IsAmpCoef (Y u u') hT hT' f →
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p), (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    GLOB.G2 δ M (Z δ M hA) cN → GLOB.CNT (Z δ M hA u u') (cN u u') →
  ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) (Dsup : ℝ), (∀ p, Irreducible (ϖ p)) → 0 ≤ Dsup →
    (∀ γ : D.s.Term u u', D.s.generic γ → Gpt (D.mem u).A.T (D.mem u').A.T (D.s.ptOf γ) ≠ 0 →
      densT (Z δ M hA u u') ϖ γ ≤ Dsup) →
  ∀ (L : LatticeDataWithDual D) (Kd : KernelData D), IsLatGLOB D L → PSDK (Kd.K (D.R.rS + 1)) →
    (∀ h h', Kd.K (D.R.rS + 1) h h' = KA δ M (D.mem u).A.T (D.mem u').A.T Dsup (D.R.rS + 1) h h') →
  ∀ cW : ℝ, 0 < cW →
    (∀ w : Point D.host.E (D.R.rS + 1), TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w) →
      n0 (cN u u') (D.mem u).A.T (D.mem u').A.T w * phiA δ M (D.mem u).A.T (D.mem u').A.T w ^ 2 =
        cW * ptWeightG D L.ρ (Tr D u) (Tr D u') w.1) →
  ∃ (ι : Type) (_ : Countable ι) (c : ι → Point D.host.E (D.R.rS + 1) → ℂ),
    RowsAx (fun v => (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp) (fun _ => hsInner)
      (Kd.K (D.R.rS + 1)) (fun h => ptWeightG D L.ρ (Tr D u) (Tr D u') h.1) c
      (fun v h => Vm.V (localBesselDatumAtRealPlace (Y u u') hT hT' v) (f v) (locBlocks D L.ρ v h.1)) ∧
    ENNReal.ofReal (∑' q, formTerm (Y u u') hT hT' Vm f q).re ≤
      ENNReal.ofReal cW *
        SRowForm (fun v => (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp) (fun _ => hsInner)
          (fun h => ptWeightG D L.ρ (Tr D u) (Tr D u') h.1) c
          (fun v h => Vm.V (localBesselDatumAtRealPlace (Y u u') hT hT' v) (f v) (locBlocks D L.ρ v h.1))

def qS : ℝ := ∑' p : PlF D, (Nat.card 𝓀[(D.s.atP p).Fp] : ℝ) ^ (-(D.R.k : ℤ))

def ConstantBoundAlt : Prop :=
  ∀ (u u' : D.what₂.Word), u ≠ u' → ∀ (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (f : ∀ v, MatKR D.R.k D.R.rS → ((localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp)),
    IsAmpCoef (Y u u') hT hT' f →
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p), GLOB.CNT (Z δ M hA u u') (cN u u') →
  ∀ L : LatticeDataWithDual D, IsLatGLOB D L → LatAx D (gE D) L →
    (∀ i s, IsBlockSL2Embedding D i s → (L.La i s : Set D.host.E) = La M δ (nu D.R.rS i (i + s - 1)) s ∧
      (L.La' i s : Set D.host.E) = LaP (D := D) (nu D.R.rS i (i + s - 1)) s) →
  ∀ cW : ℝ, 0 < cW →
    (∀ w : Point D.host.E (D.R.rS + 1), TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w) →
      n0 (cN u u') (D.mem u).A.T (D.mem u').A.T w * phiA δ M (D.mem u).A.T (D.mem u').A.T w ^ 2 =
        cW * ptWeightG D L.ρ (Tr D u) (Tr D u') w.1) →
  ∀ μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
    (∀ v, IsSection D.R.k D.R.rS (localBesselDatumAtRealPlace (Y u u') hT hT' v).z (localBesselDatumAtRealPlace (Y u u') hT hT' v).z' (μsec v)) →
    ENNReal.ofReal ((D.duS u : ℝ) / dimPi (hc := D.hcW) u * cW) *
        jNorm2One (fun v => (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp) (fun _ => hsNormSq)
          D.R.k D.R.rS (Tr D u) (Tr D u') L.κ
          (fun v p => (localBesselDatumAtRealPlace (Y u u') hT hT' v).J (f v) (bigCell D.R.k D.R.rS p.1 (μsec v p.2))) ≤
      ENNReal.ofReal (Real.exp (8 * qS D) * ((D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar))

end Steps


theorem k_ge_of_hyp {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ} (hH : hyp D large₂ C0 C' Cl Cg cb Cu cT CT) :
    4 * D.R.rS + 8 ≤ D.R.k := by
  obtain ⟨_, _, h3, h4, _⟩ := hH.2.1
  obtain ⟨t, ht⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  have hr : 4 * D.R.rS + 8 = 2 * D.R.m + 4 := by
    simp only [Ranks.rS]; omega
  have h5 : 2 * D.R.m + 4 ≤ D.R.m ^ 4 := by nlinarith [Nat.pow_le_pow_left h2 2, Nat.pow_le_pow_left h2 3, sq_nonneg (D.R.m : ℤ)]
  omega


theorem dimPi_nonneg (D : D7) (u : D.what₂.Word) : 0 ≤ dimPi (hc := D.hcW) u := by
  unfold dimPi
  positivity

theorem Dstar_pos (D : D7) : 0 < D.what₂.Dstar := by
  rw [← D.Dstar_eq D.u₀]; exact (D.mem D.u₀).A.Dstar_pos


theorem section_exists : ∀ (k r : ℕ) (L : LocBessel k r), 1 ≤ k → ∃ μsec, IsSection k r L.z L.z' μsec
  | 0, _, _, h => absurd h (by norm_num)
  | _ + 1, _, L, _ => Formalism.MainNotions.S.Inh.big_cell_section_of_local_bessel L




open Formalism.FourierDecayAlt.S3 in

theorem massData_const {P : Type} [Fintype P] (B : MassData P) (hP : B.Pos) (hI : 0 ≤ B.IntN) (h1 : B.InMass) (h2 : B.InJacMod)
    (h3 : B.InNu) (h4 : B.InInfinity) (h5 : B.InVolumes) (h6 : B.InLevelS) (h7 : B.InMasses) (h8 : B.InColumns)
    (h9 : B.InOrdinary) (h10 : B.InTyped) (h11 : B.InIndices) :
    B.d / B.dimπ * (B.n0c * (B.IntN / (B.c0 * B.c0'))) ≤ B.d * B.d' / B.Dstar := by
  obtain ⟨hp, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23,
    q24, q25, q26, q27, q28, q29, q30, q31, q32, q33, _, _⟩ := hP
  have hc0 : 0 < B.c0 := div_pos (mul_pos q23 q21) q27
  have hc0' : 0 < B.c0' := div_pos (mul_pos q24 q22) q28
  let B' : MassData P := { B with
    δ := 0, supdens := 1, e1 := 1, KtopV := B.IntN / (B.c0 * B.c0'), KV := B.n0c * (B.IntN / (B.c0 * B.c0')),
    Sig := B.ρ0 * (B.n0c * (B.IntN / (B.c0 * B.c0'))),
    Kgs2 := B.tt * B.Gam1 * (B.ρ0 * (B.n0c * (B.IntN / (B.c0 * B.c0')))) }
  have hK0 : 0 ≤ B.IntN / (B.c0 * B.c0') := div_nonneg hI (mul_pos hc0 hc0').le
  have hmain := Formalism.FourierDecayAlt.P.mass_formula_constant_one P B'
    ⟨hp, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23,
      q24, q25, q26, q27, q28, q29, q30, q31, q32, q33, zero_le_one, le_rfl⟩
    (le_refl _) rfl
    ⟨by show B.n0c * (B.IntN / (B.c0 * B.c0')) ≤ 1 * B.n0c * (B.IntN / (B.c0 * B.c0')); rw [one_mul], hK0⟩
    h1 (le_refl _)
    (by
      show B.c0 * B.c0' * (B.IntN / (B.c0 * B.c0')) ≤ (1 + 0) * B.IntN
      rw [mul_div_cancel₀ _ (mul_pos hc0 hc0').ne']; linarith)
    h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  have h := hmain.2.1
  have htt : 0 < B.tt := Finset.prod_pos fun p _ => by
    have := (hp p).1
    positivity
  have h' : B.tt * (B.d / B.dimπ) * (B.n0c * (B.IntN / (B.c0 * B.c0'))) ≤
      (1 + 0) * 1 * B.tt * (B.d * B.d' / B.Dstar) := h
  have h'' : B.tt * (B.d / B.dimπ * (B.n0c * (B.IntN / (B.c0 * B.c0')))) ≤ B.tt * (B.d * B.d' / B.Dstar) := by
    calc _ = B.tt * (B.d / B.dimπ) * (B.n0c * (B.IntN / (B.c0 * B.c0'))) := by ring
      _ ≤ _ := h'
      _ = _ := by ring
  exact le_of_mul_le_mul_left h'' htt

section MassDataStep

variable (D) (large₂ : SizeData₂ D) (X : TermTie D) (Cw : ℝ) (Y : ∀ u u', LoopTie D large₂ X u u' Cw) (Z : TermLocs D X)
  (cN : D.what₂.Word → D.what₂.Word → ℝ)

open Formalism.FourierDecayAlt.S3 in

def ParamsBound : Prop :=
  ∀ (u u' : D.what₂.Word), u ≠ u' → ∀ (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (f : ∀ v, MatKR D.R.k D.R.rS → ((localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp)),
    IsAmpCoef (Y u u') hT hT' f →
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p), GLOB.CNT (Z δ M hA u u') (cN u u') →
  ∀ L : LatticeDataWithDual D, IsLatGLOB D L → LatAx D (gE D) L →
    (∀ i s, IsBlockSL2Embedding D i s → (L.La i s : Set D.host.E) = La M δ (nu D.R.rS i (i + s - 1)) s ∧
      (L.La' i s : Set D.host.E) = LaP (D := D) (nu D.R.rS i (i + s - 1)) s) →
  ∀ cW : ℝ, 0 < cW →
    (∀ w : Point D.host.E (D.R.rS + 1), TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w) →
      n0 (cN u u') (D.mem u).A.T (D.mem u').A.T w * phiA δ M (D.mem u).A.T (D.mem u').A.T w ^ 2 =
        cW * ptWeightG D L.ρ (Tr D u) (Tr D u') w.1) →
  ∀ μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
    (∀ v, IsSection D.R.k D.R.rS (localBesselDatumAtRealPlace (Y u u') hT hT' v).z (localBesselDatumAtRealPlace (Y u u') hT hT' v).z' (μsec v)) →
    ∃ (P : Type) (_ : Fintype P) (B : MassData P), B.Pos ∧ 0 ≤ B.IntN ∧ B.InMass ∧ B.InJacMod ∧ B.InNu ∧ B.InInfinity ∧
      B.InVolumes ∧ B.InLevelS ∧ B.InMasses ∧ B.InColumns ∧ B.InOrdinary ∧ B.InTyped ∧ B.InIndices ∧ B.al⁻¹ ≤ Real.exp (8 * qS D) ∧
      B.d = (D.duS u : ℝ) ∧ B.d' = (D.duS u' : ℝ) ∧ B.Dstar = D.what₂.Dstar ∧ B.dimπ = dimPi (hc := D.hcW) u ∧
      ENNReal.ofReal cW *
        jNorm2One (fun v => (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp) (fun _ => hsNormSq)
          D.R.k D.R.rS (Tr D u) (Tr D u') L.κ
          (fun v p => (localBesselDatumAtRealPlace (Y u u') hT hT' v).J (f v) (bigCell D.R.k D.R.rS p.1 (μsec v p.2))) =
        ENNReal.ofReal (B.n0c / B.al * (B.IntN / (B.c0 * B.c0')))


end MassDataStep


section RowsLemmas

open Finset
open scoped ComplexOrder


theorem sum_split {α : Type} [DecidableEq α] (X : Finset α) (p : α → Prop) [DecidablePred p] (F : α → α → ℂ)
    (h1 : ∀ x y, p x → ¬ p y → F x y = 0) (h2 : ∀ x y, ¬ p x → p y → F x y = 0) :
    ∑ x ∈ X, ∑ y ∈ X, F x y =
      ∑ x ∈ X.filter p, ∑ y ∈ X.filter p, F x y + ∑ x ∈ X.filter (fun x => ¬ p x), ∑ y ∈ X.filter (fun x => ¬ p x), F x y := by
  have e : ∀ x, ∑ y ∈ X, F x y = ∑ y ∈ X.filter p, F x y + ∑ y ∈ X.filter (fun x => ¬ p x), F x y :=
    fun x => (Finset.sum_filter_add_sum_filter_not X p (F x)).symm
  have z1 : ∑ x ∈ X.filter p, ∑ y ∈ X.filter (fun x => ¬ p x), F x y = 0 :=
    Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy =>
      h1 x y (Finset.mem_filter.1 hx).2 (Finset.mem_filter.1 hy).2
  have z2 : ∑ x ∈ X.filter (fun x => ¬ p x), ∑ y ∈ X.filter p, F x y = 0 :=
    Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy =>
      h2 x y (Finset.mem_filter.1 hx).2 (Finset.mem_filter.1 hy).2
  rw [← Finset.sum_filter_add_sum_filter_not X p]
  simp only [e, Finset.sum_add_distrib]
  rw [z1, z2, add_zero, zero_add]



theorem local_norm_nonneg_alt {c : ℝ} (hc : 0 ≤ c) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) : 0 ≤ n0 c T T' w := by
  unfold n0
  positivity


end RowsLemmas

section RowsAbstract

open Finset
open scoped ComplexOrder


variable {P ι : Type}



variable {Tau : Type} [Fintype Tau] (HSv : Tau → Type) (ip : ∀ v, HSv v → HSv v → ℂ) (n : P → ℝ) (c c0 : ι → P → ℂ)
  (V : ∀ v, P → HSv v) (cW : ℝ)



end RowsAbstract

theorem ptEntry_col {K : Type} [Zero K] : ∀ (bs : List (K × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) →
    ∀ j, j < (bs.map Prod.snd).sum → ∃ i, i < (bs.map Prod.snd).sum ∧ ∃ t : K, t ≠ 0 ∧
      ∀ j', ptEntry bs i j' = if j' = j then t else 0
  | [], _, j, hj => absurd hj (by simp)
  | (t, s) :: rest, h, j, hj => by
    simp only [List.map_cons, List.sum_cons] at hj ⊢
    by_cases hjs : j < s
    · refine ⟨s - 1 - j, by omega, t, (h (t, s) (by simp)).1, fun j' => ?_⟩
      simp only [ptEntry]
      by_cases hj' : j' = j
      · subst hj'
        rw [if_pos ⟨by omega, hjs⟩, if_pos (by omega), if_pos rfl]
      · rw [if_neg hj']
        by_cases h2 : j' < s
        · rw [if_pos ⟨by omega, h2⟩, if_neg (by omega)]
        · rw [if_neg (fun hh => h2 hh.2), if_neg (fun hh => by omega)]
    · obtain ⟨i0, hi0, t0, ht0, h0⟩ := ptEntry_col rest (fun b hb => h b (by simp [hb])) (j - s) (by omega)
      refine ⟨i0 + s, by omega, t0, ht0, fun j' => ?_⟩
      simp only [ptEntry]
      rw [if_neg (fun hh => by omega)]
      by_cases h2 : s ≤ j'
      · rw [if_pos ⟨by omega, h2⟩, Nat.add_sub_cancel, h0]
        by_cases hj' : j' = j
        · rw [if_pos (by omega), if_pos hj']
        · rw [if_neg (by omega), if_neg hj']
      · rw [if_neg (fun hh => h2 hh.2), if_neg (by omega)]

theorem ptMat_det_ne {K : Type} [Field K] {n : ℕ} (p : Point K n) : (ptMat p).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hv
  funext j
  obtain ⟨i, hi, t, ht, hcol⟩ := ptEntry_col p.1 p.2.1 j.val (by rw [p.2.2]; exact j.2)
  have h1 := congrFun h0 ⟨i, by rw [← p.2.2]; exact hi⟩
  simp only [Matrix.mulVec, dotProduct, ptMat, hcol, Pi.zero_apply] at h1
  rw [Finset.sum_eq_single j (fun b _ hb => by rw [if_neg (fun hh => hb (Fin.ext hh)), zero_mul])
    (fun hh => absurd (Finset.mem_univ j) hh), if_pos rfl] at h1
  exact (mul_eq_zero.1 h1).resolve_left ht

theorem Dmin_top_ne (w : Point D.host.E (D.R.rS + 1)) : LocalSplitGroups.Dmin w (D.R.rS + 1) ≠ 0 := by
  unfold LocalSplitGroups.Dmin
  rw [dif_pos le_rfl]
  have : (ptMat w).submatrix (Fin.castLE (le_refl (D.R.rS + 1))) (Fin.castLE (le_refl (D.R.rS + 1))) = ptMat w := by
    ext a b; rfl
  rw [this]
  exact ptMat_det_ne w

section RowsStep

open Finset
open scoped ComplexOrder

variable (D) (large₂ : SizeData₂ D) (X : TermTie D) (Cw : ℝ) (Y : ∀ u u', LoopTie D large₂ X u u' Cw) (Z : TermLocs D X)
  (cN : D.what₂.Word → D.what₂.Word → ℝ) (Vm : ValMap D.R.k D.R.rS)

def ColumnDecomposition : Prop :=
  ∀ (u u' : D.what₂.Word), u ≠ u' → ∀ (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (f : ∀ v, MatKR D.R.k D.R.rS → ((localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp)),
    IsAmpCoef (Y u u') hT hT' f →
  ∃ (ι : Type) (_ : Countable ι) (c0 : ι → Point D.host.E (D.R.rS + 1) → ℂ),
    (∀ ρ w, c0 ρ w ≠ 0 → Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 ∧ TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w) ∧
      0 < ptWeightG D (rhoReal D) (Tr D u) (Tr D u') w.1) ∧
    (∀ (R : Finset ι) (J : Type) [Fintype J] (w : J → Point D.host.E (D.R.rS + 1)),
      (∀ x, Gpt (D.mem u).A.T (D.mem u').A.T (w x) ≠ 0) →
      (Matrix.of fun x y => Kgs D.s u u' (w x) (w y) - ∑ ρ ∈ R, c0 ρ (w x) * star (c0 ρ (w y))).PosSemidef) ∧
    (∀ ρ, Summable fun w : Point D.host.E (D.R.rS + 1) => ‖c0 ρ w‖ *
      ∏ v, Real.sqrt (hsInner (Vm.V (localBesselDatumAtRealPlace (Y u u') hT hT' v) (f v) (locBlocks D (rhoReal D) v w.1))
        (Vm.V (localBesselDatumAtRealPlace (Y u u') hT hT' v) (f v) (locBlocks D (rhoReal D) v w.1))).re) ∧
    ENNReal.ofReal (∑' q, formTerm (Y u u') hT hT' Vm f q).re ≤
      ∑' ρ, ENNReal.ofReal (∑' q : Point D.host.E (D.R.rS + 1) × Point D.host.E (D.R.rS + 1),
        c0 ρ q.1 * star (c0 ρ q.2) *
          ∏ v, hsInner (Vm.V (localBesselDatumAtRealPlace (Y u u') hT hT' v) (f v) (locBlocks D (rhoReal D) v q.1.1))
            (Vm.V (localBesselDatumAtRealPlace (Y u u') hT hT' v) (f v) (locBlocks D (rhoReal D) v q.2.1))).re


end RowsStep

section Dens

variable (D) (X : TermTie D) (Z : TermLocs D X)

def PrimeSumStep (Ce : ℝ) : Prop :=
  Summable (fun p : PlF D => (Nat.card 𝓀[(D.s.atP p).Fp] : ℝ) ^ (-((D.R.k : ℤ) - 2 * D.R.rS - 2))) ∧
  Real.exp (4 * ∑' p : PlF D, (Nat.card 𝓀[(D.s.atP p).Fp] : ℝ) ^ (-((D.R.k : ℤ) - 2 * D.R.rS - 2))) ≤ 2 ∧
  Real.exp (4 * ∑' p : PlF D, (Nat.card 𝓀[(D.s.atP p).Fp] : ℝ) ^ (-((D.R.k : ℤ) - 2 * D.R.rS - 2))) ≤ 1 + eSum D Ce


end Dens



end Formalism.MainNotions.BridgeLemma

end
