import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerRepK
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiPositiveDefiniteCholeskyFormula
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KTypeExtendsHolomorphicComplexifiedK
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiPolarDecompositionEquivariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiRestrictionHolomorphicNearOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiEntriesRealAnalytic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiEntriesCentreEigenfunctionsDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivedModuleCoefficientsAndStableFlows
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsDerLowKSub
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightDerivativeSumZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightGapBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiCentreEigenfunctionDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarOfMultOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsoPartStable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightLeOfMemWtSpan
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotCdomAdd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneLargeGaps

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.Jet.Line

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

theorem smooth_comb {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f') : SmoothOnG ε (fun h => f h + c * f' h) := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, e⟩ := hf g hg
  obtain ⟨U', F', hU', hgU', hF', e'⟩ := hf' g hg
  refine ⟨U ∩ U', fun h => F h + c * F' h, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (contDiffOn_const.mul (hF'.mono Set.inter_subset_right)), ?_⟩
  intro x hx hxJ
  simp only [e x hx.1 hxJ, e' x hx.2 hxJ]

theorem smooth_word {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f)
    (w : List (Fin n × Fin n)) : SmoothOnG ε (Eword ε w f) := by
  induction w with
  | nil => exact hf
  | cons p w ih =>
    have hc := cpartMem n ε (Matrix.single p.1 p.2 1)
    exact smooth_comb Complex.I (rdSmooth n ε _ _ ih hc.1) (rdSmooth n ε _ _ ih hc.2.1)

theorem word_comb {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f') (w : List (Fin n × Fin n)) :
    ∀ g, inUJ ε g → Eword ε w (fun h => f h + c * f' h) g = Eword ε w f g + c * Eword ε w f' g := by
  induction w with
  | nil => intro g _; rfl
  | cons p w ih =>
    intro g hg
    have hc := cpartMem n ε (Matrix.single p.1 p.2 1)
    have h1 := Eword_congr ε ih [p] g hg
    have h2 := fun X hX => (rdLin n ε _ _ X X 0 c g (smooth_word hf w) (smooth_word hf' w) hX hX hg).2.2
    refine Eq.trans h1 ?_
    simp only [Eword, Eab, Ec, id, h2 _ hc.1, h2 _ hc.2.1]
    ring

theorem word_append (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (w v : List (Fin n × Fin n)) :
    Eword ε (w ++ v) f = Eword ε w (Eword ε v f) := by
  induction w with
  | nil => rfl
  | cons p w ih => simp only [List.cons_append, Eword, ih]

def ZeroJet (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  SmoothOnG ε f ∧ ∀ w : List (Fin n × Fin n), Eword ε w f 1 = 0

theorem one_mem : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]

theorem zeroJet_zero : ZeroJet ε (fun _ => 0) := by
  refine ⟨fun g _ => ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩, fun w => ?_⟩
  cases w with
  | nil => rfl
  | cons p w => rw [Eword_const]

theorem zeroJet_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i, ZeroJet ε (F i)) : ZeroJet ε (fun g => ∑ i ∈ s, c i * F i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zeroJet_zero
  | insert i s hi ih =>
    have e : (fun g => ∑ j ∈ insert i s, c j * F j g) = fun g => (∑ j ∈ s, c j * F j g) + c i * F i g := by
      funext g; rw [Finset.sum_insert hi, add_comm]
    rw [e]
    refine ⟨smooth_comb _ ih.1 (hF i).1, fun w => ?_⟩
    rw [word_comb _ ih.1 (hF i).1 w 1 one_mem, ih.2, (hF i).2]
    simp

theorem cpart1_smul (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε (c • Z) = c.re • cpart1 ε Z + (-c.im) • cpart2 ε Z := by
  have hI : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by
    field_simp; simp
  simp only [cpart1, cpart2, hI, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
  generalize Jm ε * Zᴴ * Jm ε = W
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Complex.real_smul]
  apply Complex.ext <;> simp <;> ring

theorem cpart2_smul (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε (c • Z) = c.re • cpart2 ε Z + c.im • cpart1 ε Z := by
  have hI : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by
    field_simp; simp
  simp only [cpart1, cpart2, hI, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
  generalize Jm ε * Zᴴ * Jm ε = W
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Complex.real_smul]
  apply Complex.ext <;> simp <;> ring

theorem rd_eq_sum {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    Rd X f g = ∑ p : Fin n × Fin n, X p.1 p.2 * Eab ε p.1 p.2 f g := by
  obtain ⟨U, F, hU, hgU, hF, e⟩ := hf g hg
  have hE : ∀ Z, Ec ε Z f g =
      fderiv ℝ F g (g * cpart1 ε Z) + Complex.I * fderiv ℝ F g (g * cpart2 ε Z) := fun Z => by
    have hc := cpartMem n ε Z
    simp only [Ec, rdExt n ε f F U g _ hU hgU hg hF e hc.1, rdExt n ε f F U g _ hU hgU hg hF e hc.2.1]
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun Z => Ec ε Z f g
      map_add' := fun Y Z => by
        have h1 : cpart1 ε (Y + Z) = cpart1 ε Y + cpart1 ε Z := by
          simp only [cpart1, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]
          congr 1; abel
        have h2 : cpart2 ε (Y + Z) = cpart2 ε Y + cpart2 ε Z := by
          simp only [cpart2, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]
          congr 1; abel
        simp only [hE, h1, h2, Matrix.mul_add, map_add]
        ring
      map_smul' := fun c Z => by
        simp only [hE, cpart1_smul, cpart2_smul, Matrix.mul_add, Matrix.mul_smul, map_add, map_smul,
          RingHom.id_apply, smul_eq_mul, Complex.real_smul]
        apply Complex.ext <;> simp <;> ring }
  have hc := (cpartMem n ε X).2.2.2 hX
  have h0 : Rd X f g = L X := by
    change _ = Ec ε X f g
    rw [hE, hc.1, hc.2, rdExt n ε f F U g _ hU hgU hg hF e hX]
    simp
  have h1 : X = ∑ p : Fin n × Fin n, X p.1 p.2 • Matrix.single p.1 p.2 (1 : ℂ) := by
    rw [Fintype.sum_prod_type]
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp
  rw [h0]
  conv_lhs => rw [h1]
  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul]
  rfl

theorem zeroJet_rd {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : ZeroJet ε f) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) : ZeroJet ε (Rd X f) := by
  refine ⟨rdSmooth n ε _ _ hf.1 hX, fun w => ?_⟩
  rw [Eword_congr ε (rd_eq_sum hf.1 hX) w 1 one_mem]
  refine (zeroJet_sum Finset.univ (fun p : Fin n × Fin n => X p.1 p.2) (fun p => Eab ε p.1 p.2 f)
    (fun p => ⟨smooth_word hf.1 [p], fun v => ?_⟩)).2 w
  have := hf.2 (v ++ [p])
  rwa [word_append] at this

theorem deriv_line (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    deriv (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => Rd X f (NormedSpace.exp ((t : ℂ) • X)) := by
  funext s
  simp only [Rd, ← oneParam n X s]
  rw [deriv_comp_const_add (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) s 0, add_zero]

theorem iteratedDeriv_line {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (j : ℕ) :
    ∀ f : Matrix (Fin n) (Fin n) ℂ → ℂ, ZeroJet ε f →
      iteratedDeriv j (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) 0 = 0 := by
  induction j with
  | zero =>
    intro f hf
    simpa [Eword] using hf.2 []
  | succ j ih =>
    intro f hf
    rw [iteratedDeriv_succ', deriv_line]
    exact ih _ (zeroJet_rd hf hX)

theorem vanish_of_zero_jet : ∀ (n : ℕ) (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (X : Matrix (Fin n) (Fin n) ℂ), SmoothOnG ε f → inG ε X → (∀ w : List (Fin n × Fin n), Eword ε w f 1 = 0) → AnalyticOnNhd ℝ (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) Set.univ → f (NormedSpace.exp X) = 0 := by
  intro n ε f X hf hX hw hA
  have htop : analyticOrderAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) 0 = ⊤ := by
    refine ENat.eq_top_iff_forall_ge.2 fun m => ?_
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hA 0 trivial)).2
      fun i _ => iteratedDeriv_line hX i f ⟨hf, hw⟩
  have h := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
    (analyticOrderAt_eq_top.1 htop) (Set.mem_univ 1)
  simpa using h

end GlobalTheory.Jet.Line
end

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_derivative_sum_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V), IsHCParam lam → IsDS ε lam σ → IsDer ε σ V E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → ∀ G ∈ Vminus ε E (LamOf ε lam) u, ∑ a, ∑ b, E a b (at1 G a b) = 0 := by
  first | exact @GlobalTheory.Jet.Schmid.mul_vminus_eq_zero | exact GlobalTheory.Jet.Schmid.mul_vminus_eq_zero | (intros; apply GlobalTheory.Jet.Schmid.mul_vminus_eq_zero <;> assumption)
end

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.PhiConjDeriv

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma analyticAt_Phi (lam : Fin n → ℝ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ Omega n) :
    AnalyticAt ℂ (Phi lam) z := by
  have h := GlobalTheory.PhiEigenfun.analytic_Phi lam (1 : Matrix (Fin n) (Fin n) ℂ) 1 z (by simpa using hz)
  simpa using h

lemma fderiv_Phi_single (lam : Fin n → ℝ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ Omega n) {a b : Fin n}
    (hab : a < b) : fderiv ℂ (Phi lam) z (z * Matrix.single a b 1) = 0 := by
  have hne : a ≠ b := ne_of_lt hab
  have hγ : HasDerivAt (fun t : ℂ => z + t • (z * Matrix.single a b 1)) (z * Matrix.single a b 1) 0 := by
    have h0 := ((hasDerivAt_id' (0 : ℂ)).smul_const (z * Matrix.single a b 1)).const_add z
    rwa [one_smul] at h0
  have hP : HasFDerivAt (Phi lam) (fderiv ℂ (Phi lam) z) (z + (0 : ℂ) • (z * Matrix.single a b 1)) := by
    rw [zero_smul, add_zero]
    exact (analyticAt_Phi lam hz).differentiableAt.hasFDerivAt
  have h1 := hP.comp_hasDerivAt (0 : ℂ) hγ
  have hc : ∀ᶠ t : ℂ in nhds 0, 1 + t ≠ 0 := by
    have hca : ContinuousAt (fun t : ℂ => 1 + t) 0 := (continuous_const.add continuous_id).continuousAt
    exact hca.eventually_ne (by norm_num)
  have hev : (fun t : ℂ => Phi lam (z + t • (z * Matrix.single a b 1))) =ᶠ[nhds 0] fun _ => Phi lam z := by
    filter_upwards [hc] with t ht
    have hm := GlobalTheory.PhiEigenfun.Phi_mul_single lam hz hab.le ht
    rw [if_neg hne, one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul] at hm
    exact hm
  have h2 : HasDerivAt (fun t : ℂ => Phi lam (z + t • (z * Matrix.single a b 1))) 0 0 :=
    (hasDerivAt_const (0 : ℂ) (Phi lam z)).congr_of_eventuallyEq hev
  exact h1.unique h2

def sgn (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

lemma star_entry {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) (a b : Fin n) :
    star (Y a b) = -(sgn ε b * sgn ε a) * Y b a := by
  have h' : Yᴴ * Jm ε + Jm ε * Y = 0 := h
  have h1 := congrFun (congrFun h' b) a
  simp only [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply] at h1
  unfold sgn
  rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
    rcases Bool.eq_false_or_eq_true (ε b) with hb | hb <;>
    simp only [ha, hb, if_true, if_false, Bool.false_eq_true] at h1 ⊢ <;>
    first | linear_combination h1 | linear_combination -h1

lemma inG_conj {ε : Fin n → Bool} {k X : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (hX : inG ε X) :
    inG ε (k⁻¹ * X * k) := by
  obtain ⟨hu, hJ⟩ := hk
  have hkk : kᴴ * k = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hu
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hkk
  have hJ' : Jm ε * kᴴ = kᴴ * Jm ε := by
    have h2 := congrArg Matrix.conjTranspose hJ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjTranspose] at h2
    exact h2
  have hX' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  show (k⁻¹ * X * k)ᴴ * Jm ε + Jm ε * (k⁻¹ * X * k) = 0
  rw [hinv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc kᴴ * (Xᴴ * k) * Jm ε + Jm ε * (kᴴ * X * k)
      = kᴴ * Xᴴ * (k * Jm ε) + Jm ε * kᴴ * X * k := by simp only [Matrix.mul_assoc]
    _ = kᴴ * (Xᴴ * Jm ε + Jm ε * X) * k := by
        rw [hJ, hJ']; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX', Matrix.mul_zero, Matrix.zero_mul]

theorem exists_deriv_Phi_conj : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), ∃ l : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ → ℂ, (∀ c d z, d < c → l c d z = 0) ∧ (∀ c d, ContinuousOn (l c d) (Omega n)) ∧ ∀ k ∈ Kset ε, ∀ g ∈ UJset ε, k⁻¹ * g * k ∈ Omega n → ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → HasDerivAt (fun t : ℝ => Phi lam ((k⁻¹ * (g * NormedSpace.exp ((t : ℂ) • X)) * k).map star)) (∑ c, ∑ d, (k⁻¹ * X * k) c d * l c d (k⁻¹ * g * k)) 0 := by
  intro n ε lam
  refine ⟨fun c d z => if d < c then 0 else
    -(sgn ε c * sgn ε d) * star (fderiv ℂ (Phi lam) z (z * Matrix.single d c 1)), ?_, ?_, ?_⟩
  · intro c d z hdc
    simp only [hdc, if_true]
  · intro c d
    by_cases hdc : d < c
    · simp only [hdc, if_true]
      exact continuousOn_const
    · simp only [hdc, if_false]
      have hA : AnalyticOnNhd ℂ (Phi lam) (Omega n) := fun z hz => analyticAt_Phi lam hz
      have hF : ContinuousOn (fderiv ℂ (Phi lam)) (Omega n) := hA.fderiv.continuousOn
      have hv : ContinuousOn (fun z : Matrix (Fin n) (Fin n) ℂ => z * Matrix.single d c 1) (Omega n) :=
        (continuous_id.matrix_mul continuous_const).continuousOn
      exact continuousOn_const.mul (hF.clm_apply hv).star
  · intro k hk g hg hw X hX
    have hkk : kᴴ * k = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hk.1
    have hkk' : k * kᴴ = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hk.1
    have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hkk
    have hYG : inG ε (k⁻¹ * X * k) := inG_conj hk hX

    let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
      LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℂ k⁻¹).comp (LinearMap.mulRight ℂ k))
    have hL : ∀ M, L M = k⁻¹ * (M * k) := fun M => rfl
    have hcurve : HasDerivAt (fun s : ℂ => k⁻¹ * (g * NormedSpace.exp (s • X)) * k)
        ((k⁻¹ * g * k) * (k⁻¹ * X * k)) 0 := by
      have h0 := L.hasFDerivAt.comp_hasDerivAt (0 : ℂ) (GlobalTheory.PhiEigenfun.hasDerivAt_curve g X)
      have hLgX : L (g * X) = (k⁻¹ * g * k) * (k⁻¹ * X * k) := by
        rw [hL, hinv]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc k kᴴ (X * k), hkk', Matrix.one_mul]
      refine (h0.congr_deriv hLgX).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      exact Matrix.mul_assoc _ _ _
    have hP : HasFDerivAt (Phi lam) (fderiv ℂ (Phi lam) (k⁻¹ * g * k))
        (k⁻¹ * (g * NormedSpace.exp ((0 : ℂ) • X)) * k) := by
      rw [zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
      exact (analyticAt_Phi lam hw).differentiableAt.hasFDerivAt
    have hφ := hP.comp_hasDerivAt (0 : ℂ) hcurve
    have hφ' : HasDerivAt (fun s : ℂ => Phi lam (k⁻¹ * (g * NormedSpace.exp (s • X)) * k))
        (fderiv ℂ (Phi lam) (k⁻¹ * g * k) ((k⁻¹ * g * k) * (k⁻¹ * X * k))) ((0 : ℝ) : ℂ) := by
      rw [Complex.ofReal_zero]
      exact hφ
    have hst := hφ'.comp_ofReal.star

    have hexp : ∀ (w Y : Matrix (Fin n) (Fin n) ℂ), fderiv ℂ (Phi lam) w (w * Y) =
        ∑ c, ∑ d, Y c d * fderiv ℂ (Phi lam) w (w * Matrix.single c d 1) := by
      intro w Y
      conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
      simp only [Matrix.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      have hs : Matrix.single c d (Y c d) = Y c d • Matrix.single c d (1 : ℂ) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [hs, Matrix.mul_smul, map_smul, smul_eq_mul]
    have hD0 : ∀ c d : Fin n, d < c → fderiv ℂ (Phi lam) (k⁻¹ * g * k) ((k⁻¹ * g * k) * Matrix.single d c 1) = 0 :=
      fun c d h => fderiv_Phi_single lam hw h
    have hfun : (fun t : ℝ => Phi lam ((k⁻¹ * (g * NormedSpace.exp ((t : ℂ) • X)) * k).map star)) =
        fun t : ℝ => star (Phi lam (k⁻¹ * (g * NormedSpace.exp ((t : ℂ) • X)) * k)) := by
      funext t
      exact GlobalTheory.Dec.FormF.Phi_star lam _
    rw [hfun]
    refine hst.congr_deriv ?_
    rw [hexp, star_sum]
    simp only [star_sum, star_mul', star_entry hYG]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    split_ifs with h
    · rw [hD0 _ _ h]
      simp
    · ring

end GlobalTheory.PhiConjDeriv
end
end

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.VminusK

theorem flow_vanish {W : Type} [AddCommGroup W] [Module ℂ W] (S : Submodule ℂ W) [FiniteDimensional ℂ S]
    (A : W →ₗ[ℂ] W) (hA : ∀ x ∈ S, A x ∈ S) (φ : ℝ → W →ₗ[ℂ] ℂ)
    (hφ : ∀ t x, HasDerivAt (fun s => φ s x) (φ t (A x)) t) (h0 : ∀ x ∈ S, φ 0 x = 0) :
    ∀ t, ∀ x ∈ S, φ t x = 0 := by
  let b := Module.finBasis ℂ S
  let M : Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ :=
    Matrix.of fun i j => b.repr ⟨A (b i), hA _ (b i).2⟩ j
  let L : (Fin (Module.finrank ℂ S) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ S) → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.toLin' M)
  have hexp : ∀ t (x : S), φ t x = ∑ j, b.repr x j * φ t (b j) := by
    intro t x
    have h := congrArg (φ t ∘ₗ S.subtype) (b.sum_repr x)
    rw [map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    exact h.symm
  have key : (fun t i => φ t (b i)) = fun _ => 0 := by
    refine ODE_solution_unique_univ (v := fun _ y => L y) (s := fun _ => Set.univ) (K := ‖L‖₊) (t₀ := 0)
      (fun _ => L.lipschitz.lipschitzOnWith) (fun t => ⟨?_, trivial⟩) (fun t => ⟨?_, trivial⟩) ?_
    · refine hasDerivAt_pi.2 fun i => ?_
      refine (hφ t (b i)).congr_deriv ?_
      rw [hexp t ⟨A (b i), hA _ (b i).2⟩]
      simp [L, M, Matrix.mulVec, dotProduct]
    · simpa using hasDerivAt_const t (0 : Fin (Module.finrank ℂ S) → ℂ)
    · funext i
      exact h0 _ (b i).2
  intro t x hx
  rw [hexp t ⟨x, hx⟩]
  refine Finset.sum_eq_zero fun j _ => ?_
  have := congrFun (congrFun key t) j
  simp only [Pi.zero_apply] at this
  rw [this, mul_zero]

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem deriv_exp_entry {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (i j : Fin n) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • Y) i j)
      ((NormedSpace.exp ((s : ℂ) • Y) * Y) i j) s := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℂ) Y (s : ℂ)
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  have h1 : HasDerivAt (fun u : ℂ => NormedSpace.exp (u • Y) i j)
      ((NormedSpace.exp ((s : ℂ) • Y) * Y) i j) (s : ℂ) :=
    L.hasFDerivAt.comp_hasDerivAt (s : ℂ) h
  exact h1.comp_ofReal

theorem deriv_exp_entry' {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (i j : Fin n) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • Y) i j)
      ((Y * NormedSpace.exp ((s : ℂ) • Y)) i j) s := by
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℂ) Y (s : ℂ)
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  have h1 : HasDerivAt (fun u : ℂ => NormedSpace.exp (u • Y) i j)
      ((Y * NormedSpace.exp ((s : ℂ) • Y)) i j) (s : ℂ) :=
    L.hasFDerivAt.comp_hasDerivAt (s : ℂ) h
  exact h1.comp_ofReal

end Linfty

theorem deriv_mul_entry {r : ℕ} (G H : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (G' H' : Matrix (Fin r) (Fin r) ℂ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t)
    (hH : ∀ i j, HasDerivAt (fun s => H s i j) (H' i j) t) (i j : Fin r) :
    HasDerivAt (fun s => (G s * H s) i j) ((G' * H t + G t * H') i j) t := by
  have := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hG i k).fun_mul (hH k j))
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib] using this

theorem deriv_orbit {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {V : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ V}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDer ε σ V E) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inG ε Y)
    (v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • Y)) (v : H))
      (σ (NormedSpace.exp ((t : ℂ) • Y)) ((∑ a, ∑ b, Y a b • E a b v : V) : H)) t := by
  have h1 := hD.2.2.1 Y hY v
  have h2 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (((s - t : ℝ) : ℂ) • Y)) (v : H))
      ((∑ a, ∑ b, Y a b • E a b v : V) : H) t := by
    have h3 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • Y)) (v : H))
      ((∑ a, ∑ b, Y a b • E a b v : V) : H) (t - t) := by rw [sub_self]; exact h1
    exact h3.comp_sub_const t t
  have h4 := ((σ (NormedSpace.exp ((t : ℂ) • Y))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h2
  refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  beta_reduce
  have h5 := oneParam n Y t (s - t)
  rw [add_sub_cancel] at h5
  rw [h5, hσ.1.2 _ (expUJ n ε Y hY t) _ (expUJ n ε Y hY (s - t))]
  rfl

def matOf {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ℓ : V →ₗ[ℂ] ℂ) :
    Arr V n 1 →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun G := Matrix.of fun a b => ℓ (at1 G a b)
  map_add' G G' := by
    ext a b
    simp [at1]
  map_smul' c G := by
    ext a b
    simp [at1]

theorem matOf_act {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (ℓ : V →ₗ[ℂ] ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) (G : Arr V n 1) :
    matOf ℓ ((∑ c, ∑ d, Y c d • arrE E 1 c d) G) =
      Y * matOf ℓ G - matOf ℓ G * Y +
        Matrix.of fun a b => ℓ (∑ c, ∑ d, Y c d • E c d (at1 G a b)) := by
  have h : ∀ c d a b, matOf ℓ (arrE E 1 c d G) a b =
      (if a = c then matOf ℓ G d b else 0) - (if b = d then matOf ℓ G a c else 0) + ℓ (E c d (at1 G a b)) := by
    intro c d a b
    have := congrArg ℓ (arr_operator_one_apply E c d G a b)
    rw [map_add, map_sub, apply_ite ℓ, apply_ite ℓ, map_zero] at this
    exact this
  ext a b
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Matrix.sum_apply,
    Matrix.smul_apply, h, smul_eq_mul, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Matrix.add_apply, Matrix.sub_apply, Matrix.of_apply, Matrix.mul_apply, mul_ite, mul_zero]
  congr 2
  · rw [Finset.sum_comm]
    simp
  · simp [mul_comm]

theorem inK_entry {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) {c d : Fin n}
    (h : ε c ≠ ε d) : Y c d = 0 := by
  have h1 := congrFun (congrFun hY.2 c) d
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  cases hc : ε c <;> cases hd : ε d <;> simp [hc, hd] at h h1
  · linear_combination h1 / 2
  · linear_combination -h1 / 2

theorem vminus_K : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (abelian₂ : Fin n → ℝ) (u : V), IsURepOn (UJset ε) σ → IsDer ε σ V E → KHighest ε E abelian₂ u → FiniteDimensional ℂ (kSpan ε E u) → ∀ G ∈ Vminus ε E abelian₂ u, ∀ k ∈ Kset ε, ∀ c d : Fin n, ¬ d < c → ∑ a, ∑ b, k⁻¹ c a * k b d * ⟪σ k (u : H), (at1 G a b : V)⟫_ℂ = 0 := by
  intro n ε H _ _ _ σ V E abelian₂ u hσ hD hΛ hfd G hG k hk c d hcd
  obtain ⟨hst, -, hfm, hvan⟩ := VminusComp.vminus_comp V n ε E abelian₂ u hD.1 hD.2.1 hΛ hfd
  have hks := Kset_star ε hk
  have hinv : k⁻¹ = star k := Matrix.inv_eq_left_inv hk.1.1
  obtain ⟨Y, hY, hexp, -⟩ := compact_exponential_surjective n ε _ hks
  have hexp' : NormedSpace.exp (-Y) = k := by
    rw [Matrix.exp_neg, hexp]
    exact Matrix.inv_eq_left_inv hk.1.2
  let ℓ : ℝ → V →ₗ[ℂ] ℂ := fun t =>
    (innerₛₗ ℂ (u : H)) ∘ₗ (σ (NormedSpace.exp ((t : ℂ) • Y))).toLinearMap ∘ₗ V.subtype
  have hℓ : ∀ t (v : V), ℓ t v = ⟪(u : H), σ (NormedSpace.exp ((t : ℂ) • Y)) v⟫_ℂ := fun _ _ => rfl
  let φ : ℝ → Arr V n 1 →ₗ[ℂ] ℂ := fun t =>
    Matrix.entryLinearMap ℂ ℂ c d ∘ₗ LinearMap.mulRight ℂ (NormedSpace.exp ((t : ℂ) • (-Y))) ∘ₗ
      LinearMap.mulLeft ℂ (NormedSpace.exp ((t : ℂ) • Y)) ∘ₗ matOf (ℓ t)
  have hφ : ∀ t G, φ t G = (NormedSpace.exp ((t : ℂ) • Y) * matOf (ℓ t) G *
      NormedSpace.exp ((t : ℂ) • (-Y))) c d := fun _ _ => rfl
  have main := flow_vanish (Vminus ε E abelian₂ u) (∑ c, ∑ d, Y c d • arrE E 1 c d) ?_ φ ?_ ?_ 1 G hG
  · rw [hφ, Complex.ofReal_one, one_smul, one_smul, hexp, hexp', ← hinv] at main
    rw [← main]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    have e1 : matOf (ℓ 1) G a b = ⟪σ k (u : H), (at1 G a b : V)⟫_ℂ := by
      show ℓ 1 (at1 G a b) = _
      rw [hℓ, Complex.ofReal_one, one_smul, hexp]
      have hkU : k ∈ UJset ε := (kFacts n ε).1 k hk
      have hsU : star k ∈ UJset ε := (kFacts n ε).1 _ hks
      have h1 : σ k (σ (star k) (at1 G a b : V)) = (at1 G a b : V) := by
        have := hσ.1.2 k hkU _ hsU
        rw [hk.1.2, hσ.1.1] at this
        exact (congrArg (fun T : H →L[ℂ] H => T (at1 G a b : V)) this).symm
      let I : H →ₗᵢ[ℂ] H := ⟨(σ k).toLinearMap, hσ.2.1 k hkU⟩
      have h2 := I.inner_map_map (u : H) (σ (star k) (at1 G a b : V))
      rw [← h2]
      show ⟪σ k (u : H), σ k (σ (star k) (at1 G a b : V))⟫_ℂ = _
      rw [h1]
    rw [e1]
    ring
  · intro x hx
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    by_cases h : ε a = ε b
    · exact Submodule.smul_mem _ _ (hst a b h x hx)
    · rw [inK_entry hY h, zero_smul]
      exact Submodule.zero_mem _
  · intro t x
    have hM : ∀ a b, HasDerivAt (fun s => matOf (ℓ s) x a b)
        ((Matrix.of fun a b => ℓ t (∑ c, ∑ d, Y c d • E c d (at1 x a b))) a b) t := by
      intro a b
      exact ((innerSL ℂ (u : H)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
        (deriv_orbit hσ hD hY.1 (at1 x a b) t)
    have h1 := deriv_mul_entry _ _ _ _ t
      (deriv_mul_entry _ _ _ _ t (deriv_exp_entry Y t) hM) (deriv_exp_entry' (-Y) t) c d
    simp only [hφ]
    refine h1.congr_deriv ?_
    rw [matOf_act]
    refine congrFun (congrFun ?_ c) d
    noncomm_ring
  · intro x hx
    rw [hφ]
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one]
    show ℓ 0 (at1 x c d) = 0
    rw [hℓ, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1]
    exact hvan x hx c d hcd

end GlobalTheory.Jet.VminusK
end
end

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.SchmidIntegral

variable {n : ℕ}

local notation "Mt" => Matrix (Fin n) (Fin n) ℂ

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma continuous_inv_toMK (ε : Fin n → Bool) : Continuous (fun k : KG ε => (toMK k)⁻¹) := by
  have e : (fun k : KG ε => (toMK k)⁻¹) =
      fun k : KG ε => ((((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ) := by
    funext k
    exact (Matrix.coe_units_inv _).symm
  rw [e]
  exact Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_subtype_val)

private lemma one_mem_Omega : (1 : Mt) ∈ Omega n := by
  simp only [GlobalTheory.Dec.Omega, Set.mem_setOf_eq]
  intro i
  simp only [Formalism.MainNotions.S.leadMinor, Matrix.submatrix_one _ (Fin.castLE_injective _), Matrix.det_one]
  exact one_ne_zero

lemma eventually_mem_kConjNonzeroMinorsSet (ε : Fin n → Bool) : ∀ᶠ z : Mt in nhds 1, z ∈ U1 ε := by
  have hK : IsCompact (Kset ε) := (Formalism.REAL.kFacts n ε).2.1
  have hc : Continuous (fun p : Mt × Mt => p.2ᴴ * p.1 * p.2) :=
    (continuous_snd.matrix_conjTranspose.matrix_mul continuous_fst).matrix_mul continuous_snd
  have hev : ∀ᶠ z : Mt in nhds 1, ∀ k ∈ Kset ε, kᴴ * z * k ∈ Omega n := by
    refine hK.eventually_forall_of_forall_eventually fun k hk => ?_
    have h1 : kᴴ * (1 : Mt) * k ∈ Omega n := by
      have hu : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk.1
      rw [Matrix.mul_one, ← Matrix.star_eq_conjTranspose, hu]
      exact one_mem_Omega
    exact hc.continuousAt.preimage_mem_nhds (GlobalTheory.Dec.PsiEig.isOpen_Omega.mem_nhds h1)
  filter_upwards [hev] with z hz
  intro k hk
  have hu : kᴴ * k = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hk.1
  rw [Matrix.inv_eq_left_inv hu]
  exact hz k hk

private lemma toMK_mem_Kset {ε : Fin n → Bool} (k : KG ε) : toMK k ∈ Kset ε :=
  (Formalism.REAL.mem_KG ε k).mp k.2

private lemma continuous_toMK_inv_mul_mul_toMK' (ε : Fin n → Bool) (Y : Mt) :
    Continuous (fun k : KG ε => (toMK k)⁻¹ * Y * toMK k) :=
  ((continuous_inv_toMK ε).matrix_mul continuous_const).matrix_mul (GlobalTheory.Dec.PsiEig.continuous_toMK ε)

def dInt {ε : Fin n → Bool} (l : Fin n → Fin n → Mt → ℂ) (X z : Mt) (k : KG ε) : ℂ :=
  ∑ c, ∑ d, ((toMK k)⁻¹ * X * toMK k) c d * l c d ((toMK k)⁻¹ * z * toMK k)

lemma continuousOn_dInt {ε : Fin n → Bool} {l : Fin n → Fin n → Mt → ℂ}
    (hl : ∀ c d, ContinuousOn (l c d) (Omega n)) (X : Mt) :
    ContinuousOn (fun x : Mt × KG ε => dInt l X x.1 x.2) (U1 ε ×ˢ Set.univ) := by
  show ContinuousOn (fun x : Mt × KG ε => ∑ c, ∑ d, ((toMK x.2)⁻¹ * X * toMK x.2) c d *
    l c d ((toMK x.2)⁻¹ * x.1 * toMK x.2)) _
  have hc : Continuous (fun x : Mt × KG ε => (toMK x.2)⁻¹ * x.1 * toMK x.2) :=
    (((continuous_inv_toMK ε).comp continuous_snd).matrix_mul continuous_fst).matrix_mul
      ((GlobalTheory.Dec.PsiEig.continuous_toMK ε).comp continuous_snd)
  have hX : Continuous (fun x : Mt × KG ε => (toMK x.2)⁻¹ * X * toMK x.2) :=
    (continuous_toMK_inv_mul_mul_toMK' ε X).comp continuous_snd
  have hmaps : Set.MapsTo (fun x : Mt × KG ε => (toMK x.2)⁻¹ * x.1 * toMK x.2) (U1 ε ×ˢ Set.univ) (Omega n) :=
    fun x hx => hx.1 _ (toMK_mem_Kset x.2)
  refine continuousOn_finset_sum _ fun c _ => continuousOn_finset_sum _ fun d _ => ?_
  exact (hX.matrix_elem c d).continuousOn.mul ((hl c d).comp hc.continuousOn hmaps)

lemma integrable_dInt {ε : Fin n → Bool} {l : Fin n → Fin n → Mt → ℂ}
    (hl : ∀ c d, ContinuousOn (l c d) (Omega n)) (X : Mt) {z : Mt} (hz : z ∈ U1 ε) {w : KG ε → ℂ}
    (hw : Continuous w) : Integrable (fun k => dInt l X z k * w k) (muK ε) := by
  have hcont : Continuous (fun k => dInt l X z k * w k) :=
    ((continuousOn_dInt hl X).comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hz, Set.mem_univ _⟩).mul hw
  exact integrableOn_univ.mp (hcont.continuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ)

private lemma leadMinor_map_star (M : Mt) (m : ℕ) (hm : m ≤ n) :
    Formalism.MainNotions.S.leadMinor (M.map star) m hm = star (Formalism.MainNotions.S.leadMinor M m hm) := by
  simp only [Formalism.MainNotions.S.leadMinor]
  have e : (M.map star).submatrix (Fin.castLE hm) (Fin.castLE hm) =
      ((M.submatrix (Fin.castLE hm) (Fin.castLE hm))ᴴ)ᵀ := by
    ext a b
    simp [Matrix.conjTranspose_apply]
  rw [e, Matrix.det_transpose, Matrix.det_conjTranspose]

private lemma map_star_mem_Omega {M : Mt} (h : M ∈ Omega n) : M.map star ∈ Omega n := by
  simp only [GlobalTheory.Dec.Omega, Set.mem_setOf_eq] at h ⊢
  intro i
  rw [leadMinor_map_star]
  exact star_ne_zero.mpr (h i)

private lemma mul_mem_UJset_flag_measures {ε : Fin n → Bool} {a b : Mt} (ha : inUJ ε a) (hb : inUJ ε b) :
    a * b ∈ UJset ε := by
  have ha' : aᴴ * Jm ε * a = Jm ε := ha
  have hb' : bᴴ * Jm ε * b = Jm ε := hb
  show (a * b)ᴴ * Jm ε * (a * b) = Jm ε
  have e : (a * b)ᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e, ha', hb']

lemma rd_integral {ε : Fin n → Bool} {lam : Fin n → ℝ} {l : Fin n → Fin n → Mt → ℂ}
    (hl : ∀ c d, ContinuousOn (l c d) (Omega n))
    (hd : ∀ k ∈ Kset ε, ∀ g ∈ UJset ε, k⁻¹ * g * k ∈ Omega n → ∀ X : Mt, inG ε X →
      HasDerivAt (fun t : ℝ => Phi lam ((k⁻¹ * (g * NormedSpace.exp ((t : ℂ) • X)) * k).map star))
        (∑ c, ∑ d, (k⁻¹ * X * k) c d * l c d (k⁻¹ * g * k)) 0)
    {w : KG ε → ℂ} (hw : Continuous w) {z X : Mt} (hz : inUJ ε z) (hX : inG ε X)
    (h : ∀ᶠ y in nhds z, y ∈ U1 ε) :
    Rd X (fun z => ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) * w k ∂(muK ε)) z =
      ∫ k, dInt l X z k * w k ∂(muK ε) := by
  have hcurve : Continuous (fun s : ℝ => z * NormedSpace.exp ((s : ℂ) • X)) :=
    continuous_iff_continuousAt.mpr fun t => (GlobalTheory.Dec.PsiEig.hasDerivAt_curveR z X t).continuousAt
  have hS0 : ∀ᶠ s : ℝ in nhds 0, z * NormedSpace.exp ((s : ℂ) • X) ∈ U1 ε := by
    have ht : Filter.Tendsto (fun s : ℝ => z * NormedSpace.exp ((s : ℂ) • X)) (nhds 0) (nhds z) := by
      simpa using hcurve.tendsto 0
    exact ht.eventually h
  have hF : ∀ t ∈ {s : ℝ | z * NormedSpace.exp ((s : ℂ) • X) ∈ U1 ε}, Continuous (fun k : KG ε =>
      Phi lam (((toMK k)⁻¹ * (z * NormedSpace.exp ((t : ℂ) • X)) * toMK k).map star) * w k) := by
    intro t ht
    have hmem : ∀ k : KG ε,
        ((toMK k)⁻¹ * (z * NormedSpace.exp ((t : ℂ) • X)) * toMK k).map star ∈ Omega n :=
      fun k => map_star_mem_Omega (ht _ (toMK_mem_Kset k))
    have hcm : Continuous (fun k : KG ε =>
        ((toMK k)⁻¹ * (z * NormedSpace.exp ((t : ℂ) • X)) * toMK k).map star) :=
      (continuous_toMK_inv_mul_mul_toMK' ε _).matrix_map continuous_star
    refine Continuous.mul ?_ hw
    exact continuous_iff_continuousAt.mpr fun k =>
      ContinuousAt.comp (g := Phi lam) (GlobalTheory.PhiConjDeriv.analyticAt_Phi lam (hmem k)).continuousAt
        hcm.continuousAt
  have hF' : ContinuousOn (fun x : ℝ × KG ε => dInt l X (z * NormedSpace.exp ((x.1 : ℂ) • X)) x.2 * w x.2)
      ({s : ℝ | z * NormedSpace.exp ((s : ℂ) • X) ∈ U1 ε} ×ˢ Set.univ) := by
    have h1 : ContinuousOn (fun x : ℝ × KG ε => dInt l X (z * NormedSpace.exp ((x.1 : ℂ) • X)) x.2)
        ({s : ℝ | z * NormedSpace.exp ((s : ℂ) • X) ∈ U1 ε} ×ˢ Set.univ) :=
      (continuousOn_dInt hl X).comp
        (f := fun x : ℝ × KG ε => (z * NormedSpace.exp ((x.1 : ℂ) • X), x.2))
        ((hcurve.comp continuous_fst).prodMk continuous_snd).continuousOn
        fun x hx => Set.mk_mem_prod (hx.1 : z * NormedSpace.exp ((x.1 : ℂ) • X) ∈ U1 ε) (Set.mem_univ _)
    exact h1.mul (hw.comp continuous_snd).continuousOn
  have hD : ∀ k : KG ε, ∀ t ∈ {s : ℝ | z * NormedSpace.exp ((s : ℂ) • X) ∈ U1 ε},
      HasDerivAt (fun s : ℝ =>
        Phi lam (((toMK k)⁻¹ * (z * NormedSpace.exp ((s : ℂ) • X)) * toMK k).map star) * w k)
        (dInt l X (z * NormedSpace.exp ((t : ℂ) • X)) k * w k) t := by
    intro k t ht
    have hk := toMK_mem_Kset k
    have hgU : z * NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε :=
      mul_mem_UJset_flag_measures hz (Formalism.REAL.expUJ n ε X hX t)
    have hgO : (toMK k)⁻¹ * (z * NormedSpace.exp ((t : ℂ) • X)) * toMK k ∈ Omega n := ht _ hk
    have H := hd (toMK k) hk _ hgU hgO X hX
    have H2 := (HasDerivAt.comp_sub_const (f := fun u : ℝ => Phi lam (((toMK k)⁻¹ *
      (z * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((u : ℂ) • X)) * toMK k).map star)) t t
      (by rw [sub_self]; exact H)).mul_const (w k)
    have hfun : (fun s : ℝ =>
        Phi lam (((toMK k)⁻¹ * (z * NormedSpace.exp ((s : ℂ) • X)) * toMK k).map star) * w k) =
        fun s : ℝ => Phi lam (((toMK k)⁻¹ * (z * NormedSpace.exp ((t : ℂ) • X) *
          NormedSpace.exp (((s - t : ℝ) : ℂ) • X)) * toMK k).map star) * w k := by
      funext s
      have e : t + (s - t) = s := by ring
      rw [Matrix.mul_assoc z, ← Formalism.REAL.oneParam n X t (s - t), e]
    rw [hfun]
    exact H2
  have key := GlobalTheory.Dec.PsiEig.hasDerivAt_integral_compact (muK ε) hS0 hF hF' hD
  have e0 : z * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = z := by simp
  simp only [e0] at key
  exact key.deriv

private lemma dInt_add_smul {ε : Fin n → Bool} (l : Fin n → Fin n → Mt → ℂ) (X Y z : Mt) (k : KG ε)
    (c : ℂ) : dInt l (X + c • Y) z k = dInt l X z k + c * dInt l Y z k := by
  simp only [dInt, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

lemma eab_integral {ε : Fin n → Bool} {lam : Fin n → ℝ} {l : Fin n → Fin n → Mt → ℂ}
    (hl : ∀ c d, ContinuousOn (l c d) (Omega n))
    (hd : ∀ k ∈ Kset ε, ∀ g ∈ UJset ε, k⁻¹ * g * k ∈ Omega n → ∀ X : Mt, inG ε X →
      HasDerivAt (fun t : ℝ => Phi lam ((k⁻¹ * (g * NormedSpace.exp ((t : ℂ) • X)) * k).map star))
        (∑ c, ∑ d, (k⁻¹ * X * k) c d * l c d (k⁻¹ * g * k)) 0)
    {w : KG ε → ℂ} (hw : Continuous w) {z : Mt} (hz : inUJ ε z) (h : ∀ᶠ y in nhds z, y ∈ U1 ε)
    (a b : Fin n) :
    Eab ε a b (fun z => ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) * w k ∂(muK ε)) z =
      ∫ k, dInt l (Matrix.single a b 1) z k * w k ∂(muK ε) := by
  have hc := Formalism.REAL.cpartMem n ε (Matrix.single a b 1)
  have hz1 : z ∈ U1 ε := h.self_of_nhds
  have i1 := integrable_dInt hl (cpart1 ε (Matrix.single a b 1)) hz1 hw
  have i2 := integrable_dInt hl (cpart2 ε (Matrix.single a b 1)) hz1 hw
  show Rd (cpart1 ε (Matrix.single a b 1)) _ z + Complex.I * Rd (cpart2 ε (Matrix.single a b 1)) _ z = _
  rw [rd_integral hl hd hw hz hc.1 h, rd_integral hl hd hw hz hc.2.1 h, ← integral_const_mul,
    ← integral_add i1 (i2.const_mul _)]
  conv_rhs => rw [hc.2.2.1]
  congr 1
  funext k
  rw [dInt_add_smul]
  ring

lemma conj_single_apply (A B : Mt) (a b c d : Fin n) :
    (A * Matrix.single a b (1 : ℂ) * B) c d = A c a * B b d := by
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · rw [Matrix.mul_single_apply_same, mul_one]
  · intro j _ hj
    simp [hj]
  · intro hb
    exact absurd (Finset.mem_univ b) hb

lemma sum_comm_four (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem eab_integral_eq_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V), IsURepOn (UJset ε) σ → IsDer ε σ V E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → ∀ G ∈ Vminus ε E (LamOf ε lam) u, ∀ y : H, ∀ᶠ g : UJ ε in nhds 1, ∑ a, ∑ b, Eab ε a b (fun z => ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) * (⟪y, σ (toMK k) (u : H)⟫_ℂ * ⟪σ (toMK k) (u : H), (at1 G a b : V)⟫_ℂ) ∂(muK ε)) (umat g) = 0 := by
  intro n ε H _ _ _ σ V E lam u hσ hD hK hfin G hG y
  obtain ⟨l, hl0, hlc, hd⟩ := GlobalTheory.PhiConjDeriv.exists_deriv_Phi_conj n ε lam
  have hσc : Continuous (fun k : KG ε => σ (toMK k) (u : H)) :=
    (hσ.2.2 (u : H)).comp_continuous (GlobalTheory.Dec.PsiEig.continuous_toMK ε) fun k => (k : UJ ε).2
  have hw : ∀ a b : Fin n, Continuous (fun k : KG ε =>
      ⟪y, σ (toMK k) (u : H)⟫_ℂ * ⟪σ (toMK k) (u : H), (at1 G a b : V)⟫_ℂ) :=
    fun a b => (continuous_const.inner hσc).mul (hσc.inner continuous_const)
  have hU : ∀ᶠ g : UJ ε in nhds 1, ∀ᶠ x in nhds (umat g), x ∈ U1 ε := by
    have h1 : ∀ᶠ x : Matrix (Fin n) (Fin n) ℂ in nhds 1, ∀ᶠ x' in nhds x, x' ∈ U1 ε :=
      (eventually_mem_kConjNonzeroMinorsSet ε).eventually_nhds
    have hc : Continuous (fun g : UJ ε => umat g) := Units.continuous_val.comp continuous_subtype_val
    exact (hc.tendsto 1).eventually h1
  have hpt : ∀ k : KG ε, ∀ z : Matrix (Fin n) (Fin n) ℂ, ∑ a, ∑ b, dInt l (Matrix.single a b 1) z k *
      (⟪y, σ (toMK k) (u : H)⟫_ℂ * ⟪σ (toMK k) (u : H), (at1 G a b : V)⟫_ℂ) = 0 := by
    intro k z
    have hk := toMK_mem_Kset k
    simp only [dInt, conj_single_apply, Finset.sum_mul]
    rw [sum_comm_four]
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    by_cases hdc : d < c
    · simp [hl0 c d _ hdc]
    · have hv := GlobalTheory.Jet.VminusK.vminus_K n ε H σ V E (LamOf ε lam) u hσ hD hK hfin G hG (toMK k) hk c d hdc
      rw [← mul_zero (l c d ((toMK k)⁻¹ * z * toMK k) * ⟪y, σ (toMK k) (u : H)⟫_ℂ), ← hv, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
  filter_upwards [hU] with g hg
  have hz : inUJ ε (umat g) := g.2
  have hz1 : umat g ∈ U1 ε := hg.self_of_nhds
  calc _ = ∑ a, ∑ b, ∫ k, dInt l (Matrix.single a b 1) (umat g) k *
        (⟪y, σ (toMK k) (u : H)⟫_ℂ * ⟪σ (toMK k) (u : H), (at1 G a b : V)⟫_ℂ) ∂(muK ε) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        exact eab_integral hlc hd (hw a b) hz hg a b
    _ = ∫ k, ∑ a, ∑ b, dInt l (Matrix.single a b 1) (umat g) k *
        (⟪y, σ (toMK k) (u : H)⟫_ℂ * ⟪σ (toMK k) (u : H), (at1 G a b : V)⟫_ℂ) ∂(muK ε) := by
        rw [integral_finset_sum _ fun a _ =>
          integrable_finset_sum _ fun b _ => integrable_dInt hlc _ hz1 (hw a b)]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [integral_finset_sum _ fun b _ => integrable_dInt hlc _ hz1 (hw a b)]
    _ = 0 := by simp only [hpt, integral_zero]

end GlobalTheory.Jet.SchmidIntegral
end
end

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_eventually_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V), IsURepOn (UJset ε) σ → IsDer ε σ V E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → ∀ G ∈ Vminus ε E (LamOf ε lam) u, ∀ y : H, ∀ᶠ g : UJ ε in nhds 1, ∑ a, ∑ b, Eab ε a b (fun z => ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) * (⟪y, σ (toMK k) (u : H)⟫_ℂ * ⟪σ (toMK k) (u : H), (at1 G a b : V)⟫_ℂ) ∂(muK ε)) (umat g) = 0 := by
  first | exact @GlobalTheory.Jet.SchmidIntegral.eab_integral_eq_zero | exact GlobalTheory.Jet.SchmidIntegral.eab_integral_eq_zero | (intros; apply GlobalTheory.Jet.SchmidIntegral.eab_integral_eq_zero <;> assumption)
end

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.Anal

private theorem hasDerivAt_taylor_remainder {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] (f : ℕ → ℝ → H)
    (hd : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t) (s : ℝ) (N : ℕ) (z : ℝ) :
    HasDerivAt (fun w : ℝ => f 0 (s + w) - ∑ k ∈ range (N + 1 + 1), (w ^ k / (k.factorial : ℝ)) • f k s)
      (f 1 (s + z) - ∑ k ∈ range (N + 1), (z ^ k / (k.factorial : ℝ)) • f (k + 1) s) z := by
  have e : ∀ w : ℝ, ∑ k ∈ range (N + 1 + 1), (w ^ k / (k.factorial : ℝ)) • f k s =
      ∑ k ∈ range (N + 1), (w ^ (k + 1) / ((k + 1).factorial : ℝ)) • f (k + 1) s + f 0 s := by
    intro w
    rw [Finset.sum_range_succ']
    simp
  have h1 : HasDerivAt (fun w : ℝ => f 0 (s + w)) (f 1 (s + z)) z := (hd 0 (s + z)).comp_const_add s z
  have h2 : HasDerivAt (fun w : ℝ => ∑ k ∈ range (N + 1), (w ^ (k + 1) / ((k + 1).factorial : ℝ)) • f (k + 1) s)
      (∑ k ∈ range (N + 1), (z ^ k / (k.factorial : ℝ)) • f (k + 1) s) z := by
    apply HasDerivAt.fun_sum
    intro k _
    have hp := ((hasDerivAt_pow (k + 1) z).div_const ((k + 1).factorial : ℝ)).smul_const (f (k + 1) s)
    convert hp using 2
    rw [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    have : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  have h3 := h1.sub (h2.add_const (f 0 s))
  convert h3 using 1
  funext w
  rw [e w]
  rfl

private theorem norm_taylor_remainder_le {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] (N : ℕ) :
    ∀ (f : ℕ → ℝ → H) (M : ℕ → ℝ), (∀ k t, HasDerivAt (f k) (f (k + 1) t) t) → (∀ k t, ‖f k t‖ ≤ M k) →
      ∀ s z : ℝ, ‖f 0 (s + z) - ∑ k ∈ range (N + 1), (z ^ k / (k.factorial : ℝ)) • f k s‖ ≤
        |z| ^ (N + 1) / ((N + 1).factorial : ℝ) * M (N + 1) := by
  induction N with
  | zero =>
    intro f M hd hM s z
    have hφ : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => f 0 (s + τ * z)) (z • f 1 (s + τ * z)) τ := by
      intro τ
      have h2 : HasDerivAt (fun τ : ℝ => s + τ * z) z τ := by
        simpa using ((hasDerivAt_id τ).mul_const z).const_add s
      exact (hd 0 (s + τ * z)).scomp τ h2
    have key := norm_image_sub_le_of_norm_deriv_right_le_segment (a := 0) (b := 1)
      (f := fun τ : ℝ => f 0 (s + τ * z)) (C := |z| * M 1)
      (fun τ _ => (hφ τ).continuousAt.continuousWithinAt) (fun τ _ => (hφ τ).hasDerivWithinAt)
      (fun τ _ => by rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hM 1 _) (abs_nonneg z))
      1 ⟨zero_le_one, le_rfl⟩
    simpa [mul_comm] using key
  | succ N ih =>
    intro f M hd hM s z
    have hφ : ∀ τ : ℝ, HasDerivAt
        (fun τ : ℝ => f 0 (s + τ * z) - ∑ k ∈ range (N + 1 + 1), ((τ * z) ^ k / (k.factorial : ℝ)) • f k s)
        (z • (f 1 (s + τ * z) - ∑ k ∈ range (N + 1), ((τ * z) ^ k / (k.factorial : ℝ)) • f (k + 1) s)) τ := by
      intro τ
      have h2 : HasDerivAt (fun τ : ℝ => τ * z) z τ := by simpa using (hasDerivAt_id τ).mul_const z
      exact (hasDerivAt_taylor_remainder f hd s N (τ * z)).scomp τ h2
    have hB : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => |z| ^ (N + 1 + 1) * τ ^ (N + 1 + 1) / ((N + 1 + 1).factorial : ℝ) * M (N + 1 + 1))
        (|z| ^ (N + 1 + 1) * τ ^ (N + 1) / ((N + 1).factorial : ℝ) * M (N + 1 + 1)) τ := by
      intro τ
      have hp := (((hasDerivAt_pow (N + 1 + 1) τ).const_mul (|z| ^ (N + 1 + 1))).div_const
        ((N + 1 + 1).factorial : ℝ)).mul_const (M (N + 1 + 1))
      refine hp.congr_deriv ?_
      rw [Nat.add_sub_cancel, Nat.factorial_succ (N + 1)]
      push_cast
      have : ((N + 1).factorial : ℝ) ≠ 0 := by positivity
      field_simp
    have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := 1)
      (fun τ _ => (hφ τ).continuousAt.continuousWithinAt) (fun τ _ => (hφ τ).hasDerivWithinAt)
      (by simp [Finset.sum_range_succ']) hB
      (fun τ hτ => by
        rw [norm_smul, Real.norm_eq_abs]
        have h := ih (fun k => f (k + 1)) (fun k => M (k + 1)) (fun k t => hd (k + 1) t) (fun k t => hM (k + 1) t)
          s (τ * z)
        calc |z| * ‖f 1 (s + τ * z) - ∑ k ∈ range (N + 1), ((τ * z) ^ k / (k.factorial : ℝ)) • f (k + 1) s‖
            ≤ |z| * (|τ * z| ^ (N + 1) / ((N + 1).factorial : ℝ) * M (N + 1 + 1)) :=
              mul_le_mul_of_nonneg_left h (abs_nonneg z)
          _ = |z| ^ (N + 1 + 1) * τ ^ (N + 1) / ((N + 1).factorial : ℝ) * M (N + 1 + 1) := by
              rw [abs_mul, abs_of_nonneg hτ.1]
              ring)
      (x := 1) ⟨zero_le_one, le_rfl⟩
    simpa using key

theorem analytic_chain {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] (f : ℕ → ℝ → H)
    (M : ℕ → ℝ) (hd : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t) (hM : ∀ k t, ‖f k t‖ ≤ M k) (r : ℝ) (hr : 0 < r)
    (hs : Summable fun k : ℕ => r ^ k * M k / (k.factorial : ℝ)) : AnalyticOnNhd ℝ (f 0) Set.univ := by
  have hM0 : ∀ k, 0 ≤ M k := fun k => (norm_nonneg _).trans (hM k 0)
  have hg0 : ∀ k, 0 ≤ r ^ k * M k / (k.factorial : ℝ) := fun k => by
    have := hM0 k
    positivity
  intro s _
  let p : FormalMultilinearSeries ℝ ℝ H := fun k =>
    ContinuousMultilinearMap.mkPiRing ℝ (Fin k) ((1 / (k.factorial : ℝ)) • f k s)
  have hp : ∀ (k : ℕ) (y : ℝ), (p k fun _ => y) = (y ^ k / (k.factorial : ℝ)) • f k s := by
    intro k y
    simp only [p, ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_smul]
    congr 1
    ring
  have hpn : ∀ k, ‖p k‖ ≤ M k / (k.factorial : ℝ) := by
    intro k
    simp only [p, ContinuousMultilinearMap.norm_mkPiRing, norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (k.factorial : ℝ)), one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right (hM k s) (by positivity)
  let ρ : NNReal := ⟨r, hr.le⟩
  have hrad : (ρ : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_bound (∑' k, r ^ k * M k / (k.factorial : ℝ)) fun k => ?_
    calc ‖p k‖ * (ρ : ℝ) ^ k ≤ M k / (k.factorial : ℝ) * r ^ k :=
          mul_le_mul_of_nonneg_right (hpn k) (by positivity)
      _ = r ^ k * M k / (k.factorial : ℝ) := by ring
      _ ≤ _ := hs.le_tsum k fun j _ => hg0 j
  refine ⟨p, ρ, hrad, ENNReal.coe_pos.mpr (NNReal.coe_pos.mp hr), ?_⟩
  intro y hy
  have hy' : |y| ≤ r := by
    rw [Metric.mem_eball, edist_lt_coe, ← NNReal.coe_lt_coe, coe_nndist, Real.dist_eq, sub_zero] at hy
    exact hy.le
  have hsum : Summable fun k : ℕ => (y ^ k / (k.factorial : ℝ)) • f k s := by
    refine hs.of_norm_bounded fun k => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
    calc |y| ^ k / (k.factorial : ℝ) * ‖f k s‖ ≤ r ^ k / (k.factorial : ℝ) * M k := by
          gcongr
          all_goals first | exact hM k s | exact hM0 k | exact hy'
      _ = r ^ k * M k / (k.factorial : ℝ) := by ring
  have hlim : Filter.Tendsto (fun N : ℕ => ∑ k ∈ range (N + 1), (y ^ k / (k.factorial : ℝ)) • f k s)
      Filter.atTop (nhds (f 0 (s + y))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
      ((hs.tendsto_atTop_zero).comp (Filter.tendsto_add_atTop_nat 1))
    rw [norm_sub_rev]
    calc _ ≤ |y| ^ (N + 1) / ((N + 1).factorial : ℝ) * M (N + 1) := norm_taylor_remainder_le N f M hd hM s y
      _ ≤ r ^ (N + 1) / ((N + 1).factorial : ℝ) * M (N + 1) := by
          gcongr
          all_goals first | exact hM0 (N + 1) | exact hy'
      _ = r ^ (N + 1) * M (N + 1) / ((N + 1).factorial : ℝ) := by ring
  have hlim2 := (hsum.hasSum.tendsto_sum_nat).comp (Filter.tendsto_add_atTop_nat 1)
  have heq := tendsto_nhds_unique hlim2 hlim
  have hfun : (fun k : ℕ => p k fun _ => y) = fun k => (y ^ k / (k.factorial : ℝ)) • f k s :=
    funext fun k => hp k y
  rw [hfun, ← heq]
  exact hsum.hasSum

theorem cas_real {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} (hU : IsUnitary ε E) {u : V} (hu : u ≠ 0) {c : ℂ}
    (h : Cas E u = c • u) : c = (c.re : ℂ) := by
  have hsa : ⟪Cas E u, u⟫_ℂ = ⟪u, Cas E u⟫_ℂ := by
    simp only [Cas, LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hU a b, hU b a, ← mul_assoc]
    have hs : (Formalism.REAL.sgn ε a b : ℂ) * (Formalism.REAL.sgn ε b a : ℂ) = 1 := by
      unfold Formalism.REAL.sgn
      by_cases hab : ε a = ε b
      · simp [hab]
      · simp [hab, Ne.symm hab]
    rw [hs, one_mul]
  rw [h, inner_smul_left, inner_smul_right] at hsa
  have hne : ⟪u, u⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hu
  have hc : (starRingEnd ℂ) c = c := mul_right_cancel₀ hne hsa
  exact (Complex.conj_eq_iff_re.mp hc).symm

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {V : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ V}

theorem cas_eigen (hσ : IsURepOn (UJset ε) σ) (hD : IsDer ε σ V E) {μ : Fin n → ℝ} {u : V} (hu0 : u ≠ 0)
    (hu : KHighest ε E μ u) (hf : FiniteDimensional ℂ (kSpan ε E u))
    (hall : ∀ S, IsKTypeOf ε σ μ S → S ≤ (kSpan ε E u).map V.subtype) : ∃ c : ℝ, Cas E u = (c : ℂ) • u := by
  obtain ⟨hGl, hU, -, -⟩ := id hD
  have hcomm := (Formalism.REAL.casCentral (Module.End ℂ V) n ε E hGl).1
  have hKR : KRel ε E := glRel_kRel ε E hGl
  have hKU : KUnit ε E := isUnitary_kUnit ε E hU
  have hyc : ∀ a b w, E a b (Cas E w) = Cas E (E a b w) := fun a b w => by
    rw [← Module.End.mul_apply, ← hcomm a b, Module.End.mul_apply]
  have hyK : KHighest ε E μ (Cas E u) := by
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · rw [hyc, hu.1 a, map_smul]
    · rw [hyc, hu.2 a b hab he, map_zero]
  by_cases hy0 : Cas E u = 0
  · exact ⟨0, by rw [hy0]; simp⟩
  · have hle : kSpan ε E (Cas E u) ≤ (kSpan ε E u).map (Cas E) := by
      refine compactSpan_le_of_mem ε E ⟨u, mem_compactSpan_self ε E u, rfl⟩ ?_
      intro a b hab z hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨E a b w, compactSpan_isCompactInvariant ε E u a b hab w hw, (hyc a b w).symm⟩
    have hfy : FiniteDimensional ℂ (kSpan ε E (Cas E u)) := by
      haveI := hf
      exact Submodule.finiteDimensional_of_le hle
    have hT := (GlobalTheory.Jet.KType.kType_iff n ε H σ V E hσ hD).1 μ (Cas E u) hy0 hyK hfy
    have hymem : Cas E u ∈ kSpan ε E u := by
      obtain ⟨w, hw, hwy⟩ := hall _ hT ⟨Cas E u, mem_compactSpan_self ε E (Cas E u), rfl⟩
      exact (Subtype.ext hwy : w = Cas E u) ▸ hw
    rcases Formalism.REAL.kHiUniq V n ε E μ μ u (Cas E u) hKR hKU hu hymem hyK with h0 | ⟨-, c', hc'⟩
    · exact absurd h0 hy0
    · refine ⟨c'.re, ?_⟩
      have hre := cas_real hU hu0 hc'
      rw [hc', ← hre]

omit [CompleteSpace H] in

theorem pow_growth (hD : IsDer ε σ V E) {μ : Fin n → ℝ} {u : V} (hu : KHighest ε E μ u)
    (hf : FiniteDimensional ℂ (kSpan ε E u)) {c : ℝ} (hc : Cas E u = (c : ℂ) • u) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ w ∈ kSpan ε E u, ∀ k : ℕ,
      ‖(Coef.act E X ^ k) w‖ ≤ C ^ k * (B + k) ^ k * ‖w‖ := by
  obtain ⟨hGl, hU, -, -⟩ := hD
  have hpf := Formalism.REAL.pfilFacts V n ε E u hGl
  have hug := GlobalTheory.FilGrowth.uGrowth V n ε E μ c u hGl hU hu hc hf
  set S : ℝ := ∑ a, ∑ b, ‖X a b‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _
  set s0 : ℝ := Real.sqrt (ckv ε μ) with hs0
  set q : ℝ := Real.sqrt (2 * (n : ℝ)) with hq
  set r0 : ℝ := Real.sqrt |c| with hr0
  have hs0' : 0 ≤ s0 := Real.sqrt_nonneg _
  have hq' : 0 ≤ q := Real.sqrt_nonneg _
  have hr0' : 0 ≤ r0 := Real.sqrt_nonneg _
  have hqq : q ^ 2 = 2 * (n : ℝ) := Real.sq_sqrt (by positivity)
  have hrr : r0 ^ 2 = |c| := Real.sq_sqrt (abs_nonneg c)
  have hstep : ∀ (j : ℕ), ∀ x ∈ pfil ε E u j, Coef.act E X x ∈ pfil ε E u (j + 1) ∧
      ‖Coef.act E X x‖ ≤ S * (q + 1) * (s0 + n + r0 + j) * ‖x‖ := by
    intro j x hx
    constructor
    · rw [Coef.act_apply]
      exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
        Submodule.smul_mem _ _ (hpf.2.2.2.1 j a b x hx)
    · have hD2 := hug j x hx
      have hT : 0 ≤ s0 + j + n := by positivity
      have k1 : q * (s0 + j + n) + r0 ≤ (q + 1) * (s0 + n + r0 + j) := by nlinarith
      have k2 : 2 * (n : ℝ) * (s0 + j + n) ^ 2 + |c| ≤ ((q + 1) * (s0 + n + r0 + j)) ^ 2 := by
        rw [← hqq, ← hrr]
        have h0 : 0 ≤ q * (s0 + j + n) + r0 := by positivity
        nlinarith [mul_self_le_mul_self h0 k1, mul_nonneg (mul_nonneg hq' hT) hr0']
      have hsq : ∀ a b, ‖E a b x‖ ≤ (q + 1) * (s0 + n + r0 + j) * ‖x‖ := by
        intro a b
        have h1 : ‖E a b x‖ ^ 2 ≤ ∑ a, ∑ b, ‖E a b x‖ ^ 2 := by
          have ha := Finset.single_le_sum (f := fun a' => ∑ b, ‖E a' b x‖ ^ 2)
            (fun i _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ a)
          have hb := Finset.single_le_sum (f := fun b' => ‖E a b' x‖ ^ 2) (fun i _ => sq_nonneg _)
            (Finset.mem_univ b)
          exact hb.trans ha
        have h2 : (2 * (n : ℝ) * (s0 + j + n) ^ 2 + |c|) * ‖x‖ ^ 2 ≤
            ((q + 1) * (s0 + n + r0 + j) * ‖x‖) ^ 2 := by
          calc _ ≤ ((q + 1) * (s0 + n + r0 + j)) ^ 2 * ‖x‖ ^ 2 :=
                mul_le_mul_of_nonneg_right k2 (sq_nonneg _)
            _ = _ := by ring
        calc ‖E a b x‖ = Real.sqrt (‖E a b x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt (((q + 1) * (s0 + n + r0 + j) * ‖x‖) ^ 2) := Real.sqrt_le_sqrt (h1.trans (hD2.trans h2))
          _ = (q + 1) * (s0 + n + r0 + j) * ‖x‖ := Real.sqrt_sq (by positivity)
      rw [Coef.act_apply]
      calc ‖∑ a, ∑ b, X a b • E a b x‖ ≤ ∑ a, ∑ b, ‖X a b • E a b x‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
        _ ≤ ∑ a, ∑ b, ‖X a b‖ * ((q + 1) * (s0 + n + r0 + j) * ‖x‖) :=
            Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => by
              rw [norm_smul]
              exact mul_le_mul_of_nonneg_left (hsq a b) (norm_nonneg _)
        _ = S * (q + 1) * (s0 + n + r0 + j) * ‖x‖ := by
          rw [hS]
          simp only [← Finset.sum_mul]
          ring
  refine ⟨s0 + n + r0, S * (q + 1), by positivity, by positivity, ?_⟩
  intro w hw k
  have hw0 : w ∈ pfil ε E u 0 := by
    rw [hpf.1]
    exact hw
  have hg := Formalism.REAL.growthIter V (Coef.act E X) (pfil ε E u) (s0 + n + r0) (S * (q + 1)) (by positivity)
    (by positivity) hstep 0 k w hw0
  simpa only [Nat.cast_zero, add_zero] using hg

theorem lowK_analytic : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ), IsURepOn (UJset ε) σ → IsDer ε σ V E → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → lowKSub ε lam σ ≤ V → ∀ x ∈ lowKSub ε lam σ, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → AnalyticOnNhd ℝ (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) x) Set.univ := by
  intro n ε H _ _ _ σ V E lam hσ hD hK hle x hx X hX
  obtain ⟨-, -, -, ⟨v0, hv0S, hv0, hv0w⟩, -⟩ := id hK
  have hv0V : v0 ∈ V := hle hv0S
  have hu0 : (⟨v0, hv0V⟩ : V) ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  obtain ⟨huK, hspan, hfin⟩ := (GlobalTheory.Jet.KType.kType_iff n ε H σ V E hσ hD).2 (lowK ε lam) (lowKSub ε lam σ)
    ⟨v0, hv0V⟩ hK hle hv0S hu0 hv0w
  obtain ⟨c, hc⟩ := cas_eigen hσ hD hu0 huK hfin (fun S' h => by rw [hspan]; exact le_sSup h)
  obtain ⟨B, C, hB, hC, hgrow⟩ := pow_growth hD huK hfin hc X
  have hxV : x ∈ V := hle hx
  have hvmem : (⟨x, hxV⟩ : V) ∈ kSpan ε E ⟨v0, hv0V⟩ := by
    rw [← hspan] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    exact (Subtype.ext hwx : w = ⟨x, hxV⟩) ▸ hw
  have hd : ∀ (k : ℕ) (t : ℝ),
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (((Coef.act E X ^ k) ⟨x, hxV⟩ : V) : H))
        (σ (NormedSpace.exp ((t : ℂ) • X)) (((Coef.act E X ^ (k + 1)) ⟨x, hxV⟩ : V) : H)) t := by
    intro k t
    rw [pow_succ', Module.End.mul_apply]
    exact Coef.der_flow hσ hD hX _ t
  have hM : ∀ (k : ℕ) (t : ℝ), ‖σ (NormedSpace.exp ((t : ℂ) • X)) (((Coef.act E X ^ k) ⟨x, hxV⟩ : V) : H)‖ ≤
      C ^ k * (B + k) ^ k * ‖(⟨x, hxV⟩ : V)‖ := by
    intro k t
    have hexp : NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε := Formalism.REAL.expUJ n ε X hX t
    rw [hσ.2.1 _ hexp]
    exact hgrow _ hvmem k
  have hr : 0 < 1 / (C * Real.exp 1 + 1) := by positivity
  have hCr : C * (1 / (C * Real.exp 1 + 1)) * Real.exp 1 < 1 := by
    have hpos : 0 < C * Real.exp 1 + 1 := by positivity
    rw [show C * (1 / (C * Real.exp 1 + 1)) * Real.exp 1 = C * Real.exp 1 / (C * Real.exp 1 + 1) by ring,
      div_lt_one hpos]
    linarith
  have hsum := (Formalism.REAL.taylorRadius C B (1 / (C * Real.exp 1 + 1)) hC hB hr.le hCr).mul_right ‖(⟨x, hxV⟩ : V)‖
  have hs : Summable fun k : ℕ => (1 / (C * Real.exp 1 + 1)) ^ k * (C ^ k * (B + k) ^ k * ‖(⟨x, hxV⟩ : V)‖) /
      (k.factorial : ℝ) := by
    refine hsum.congr fun k => ?_
    rw [mul_pow]
    ring
  have h := analytic_chain (fun k t => σ (NormedSpace.exp ((t : ℂ) • X)) (((Coef.act E X ^ k) ⟨x, hxV⟩ : V) : H))
    (fun k => C ^ k * (B + k) ^ k * ‖(⟨x, hxV⟩ : V)‖) hd hM _ hr hs
  simpa using h

end GlobalTheory.Jet.Anal
end
end

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowest_K_type_analytic : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ), IsURepOn (UJset ε) σ → IsDer ε σ V E → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → lowKSub ε lam σ ≤ V → ∀ x ∈ lowKSub ε lam σ, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → AnalyticOnNhd ℝ (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) x) Set.univ := by
  first | exact @GlobalTheory.Jet.Anal.lowK_analytic | exact GlobalTheory.Jet.Anal.lowK_analytic | (intros; apply GlobalTheory.Jet.Anal.lowK_analytic <;> assumption)
end

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.FormGap

open GlobalTheory.Dec.FormF GlobalTheory.Dec.PsiEig Filter Topology

variable {n : ℕ} {ε : Fin n → Bool}

local notation "Mt" => Matrix (Fin n) (Fin n) ℂ

section Local
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem locAn_conj {f : Mt → ℂ} (h : LocAn ε f) : LocAn ε (fun g => f (g.map star)) := by
  intro g hg
  obtain ⟨F, hF, he⟩ := h _ (UJ_star hg)
  let c : Mt →ₗ[ℝ] Mt :=
    { toFun := fun x => x.map star
      map_add' := fun x y => by ext i j; simp
      map_smul' := fun r x => by ext i j; simp }
  have hc : AnalyticAt ℝ (fun x : Mt => x.map star) g := (LinearMap.toContinuousLinearMap c).analyticAt g
  refine ⟨fun x => F (x.map star), hF.comp_of_eq hc rfl, ?_⟩
  filter_upwards [hc.continuousAt.eventually he] with z hz hzJ
  exact hz (UJ_star hzJ)

theorem locAn_line {f : Mt → ℂ} (h : LocAn ε f) {X : Mt} (hX : inG ε X) :
    AnalyticOnNhd ℝ (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) Set.univ := by
  intro t _
  obtain ⟨F, hF, he⟩ := h _ (exp_indefinite_unitary_holds n ε X hX t)
  have h1 := analyticAt_curveR 1 X t
  simp only [Matrix.one_mul] at h1
  refine (hF.comp_of_eq h1 rfl).congr ?_
  filter_upwards [h1.continuousAt.eventually he] with s hs
  exact (hs (exp_indefinite_unitary_holds n ε X hX s)).symm

theorem eab_local {f f' : Mt → ℂ} {g : Mt} (hg : inUJ ε g) (h : ∀ᶠ z in 𝓝 g, inUJ ε z → f z = f' z) (a b : Fin n) :
    Eab ε a b f g = Eab ε a b f' g := by
  have hR : ∀ X, inG ε X → Rd X f g = Rd X f' g := fun X hX => by
    have h1 := (analyticAt_curveR g X 0).continuousAt.tendsto
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at h1
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [h1.eventually h] with t ht
    exact ht (indefinite_unitary_mul_mem ε hg (exp_indefinite_unitary_holds n ε X hX t))
  have hc := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  simp only [Eab, Ec, hR _ hc.1, hR _ hc.2.1]

end Local

theorem eab_const_mul (c : ℂ) (f : Mt → ℂ) (a b : Fin n) (g : Mt) :
    Eab ε a b (fun z => c * f z) g = c * Eab ε a b f g := by
  simp only [Eab, Ec, Rd, deriv_const_mul_field']
  ring

theorem eventually_UJ {p : Mt → Prop} (h : ∀ᶠ g : UJ ε in 𝓝 1, p (umat g)) :
    ∀ᶠ y in 𝓝 (1 : Mt), inUJ ε y → p y := by
  rw [(isClosedEmbeddingMatrix n ε).1.isEmbedding.isInducing.nhds_eq_comap, eventually_comap] at h
  filter_upwards [h] with y hy hyJ
  obtain ⟨a, rfl⟩ : y ∈ Set.range (fun g : UJ ε => toM g) := by
    rw [(isClosedEmbeddingMatrix n ε).2]; exact hyJ
  exact hy a rfl

theorem exists_gap {lam : Fin n → ℝ} (hlam : IsHCParam lam) {h : ℝ} (hgap : GapAtLeast ε lam h)
    (hh : 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) :
    ∃ g₀ : ℝ, (∀ a b : Fin n, a < b → ε a ≠ ε b → g₀ ≤ lam a - lam b) ∧ 2 * (n : ℝ) < g₀ := by
  by_cases hex : ∃ a b, ε a ≠ ε b
  · refine ⟨h, fun a b hab hne => ?_, ?_⟩
    · have := hgap a b hne
      rwa [abs_of_pos (sub_pos.2 (hlam.1 hab))] at this
    · obtain ⟨a, b, hab⟩ := hex
      have hn : (0 : ℝ) < n := by exact_mod_cast a.pos
      have hq : 1 ≤ rkR ε := by
        unfold rkR
        simp only [le_min_iff, Finset.one_le_card]
        cases ha : ε a <;> cases hb : ε b
        · simp [ha, hb] at hab
        · exact ⟨⟨b, by simp [hb]⟩, ⟨a, by simp [ha]⟩⟩
        · exact ⟨⟨a, by simp [ha]⟩, ⟨b, by simp [hb]⟩⟩
        · simp [ha, hb] at hab
      have : (1 : ℝ) ≤ ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) :=
        Real.one_le_rpow (by exact_mod_cast hq) (by norm_num)
      nlinarith
  · exact ⟨2 * n + 1, fun a b _ hne => absurd ⟨a, b, hne⟩ hex, by linarith⟩

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
  {S : Submodule ℂ H} [S.HasOrthogonalProjection]

theorem proj_comm (hσ : IsURepOn (Kset ε) σ) (hS : IsKStableOn ε σ S) {k : Mt} (hk : k ∈ Kset ε) (x : H) :
    S.starProjection (σ k x) = σ k (S.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hS k hk _ (S.starProjection_apply_mem x)) fun s hs => ?_
  rw [← map_sub, inner_rep_K hσ hk]
  exact Submodule.starProjection_inner_eq_zero x _ (hS _ (Kset_star ε hk) s hs)

theorem ps_entry {lam abelian₂ : Fin n → ℝ} {w : S} {τ : Mt → (S →L[ℂ] S)} (hτ : IsTau ε abelian₂ τ w)
    (hτσ : ∀ k ∈ Kset ε, ∀ v : S, (τ k v : H) = σ (k.map star) v) {z : Mt} (hz : z.map star ∈ U1 ε) (x y : H) :
    ⟪S.orthogonalProjectionOnto y, ps ε lam τ w (z.map star) (S.orthogonalProjectionOnto x)⟫_ℂ = (Module.finrank ℂ S : ℂ) *
      ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) *
        (⟪y, σ (toMK k) (w : H)⟫_ℂ * ⟪σ (toMK k) (w : H), x⟫_ℂ) ∂(muK ε) := by
  rw [inner_ps lam hτ _ _ hz, intK, ← integral_const_mul]
  simp only [pk]
  rw [← muConj n ε (fun k => Phi lam (k⁻¹ * z.map star * k) * ((Module.finrank ℂ S : ℂ) *
    (⟪τ k w, S.orthogonalProjectionOnto x⟫_ℂ * ⟪S.orthogonalProjectionOnto y, τ k w⟫_ℂ)))]
  congr 1
  funext k
  have hk : toMK k ∈ Kset ε := k.2
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    hτσ _ (K_star hk), map_star_star, K_inv (K_star hk), map_star_ct, ← map_star_mul, ← map_star_mul, ← K_inv hk]
  ring

def diffOp (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Mt → (H →L[ℂ] H)) (τ : Mt → (S →L[ℂ] S)) (w : S) (z : Mt) :
    H →L[ℂ] H :=
  S.starProjection.comp (σ z) - S.subtypeL.comp ((Psi ε lam τ w (z.map star)).comp S.orthogonalProjectionOnto)

theorem diffOp_apply (lam : Fin n → ℝ) (τ : Mt → (S →L[ℂ] S)) (w : S) (z : Mt) (x : H) :
    diffOp ε lam σ τ w z x =
      S.starProjection (σ z x) - (Psi ε lam τ w (z.map star) (S.orthogonalProjectionOnto x) : S) := rfl

theorem inner_diffOp (lam : Fin n → ℝ) (τ : Mt → (S →L[ℂ] S)) (w : S) (x y : H) :
    (fun z => ⟪y, diffOp ε lam σ τ w z x⟫_ℂ) = fun z => ⟪S.starProjection y, σ z x⟫_ℂ +
      (-1) * ⟪S.orthogonalProjectionOnto y, Psi ε lam τ w (z.map star) (S.orthogonalProjectionOnto x)⟫_ℂ := by
  funext z
  rw [diffOp_apply, inner_sub_right, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    Submodule.inner_starProjection_left_eq_right]
  ring

theorem diffOp_equiv {lam : Fin n → ℝ} (hlam : IsHCParam lam) (hσ : IsURepOn (UJset ε) σ) (hS : IsKStableOn ε σ S)
    {w : S} {τ : Mt → (S →L[ℂ] S)} (hτ : IsTau ε (lowK ε lam) τ w)
    (hτσ : ∀ k ∈ Kset ε, ∀ v : S, (τ k v : H) = σ (k.map star) v) {g k₁ k₂ : Mt} (hg : g ∈ UJset ε)
    (h₁ : k₁ ∈ Kset ε) (h₂ : k₂ ∈ Kset ε) (x : H) :
    diffOp ε lam σ τ w (k₁ * g * k₂) x = σ k₁ (diffOp ε lam σ τ w g (σ k₂ x)) := by
  have e : τ (k₂.map star) (S.orthogonalProjectionOnto x) = S.orthogonalProjectionOnto (σ k₂ x) := by
    apply Subtype.ext
    rw [hτσ _ (K_star h₂), map_star_star]
    exact (proj_comm (URep_K hσ) hS h₂ x).symm
  rw [diffOp_apply, diffOp_apply, map_sub, ← proj_comm (URep_K hσ) hS h₁, map_star_mul, map_star_mul,
    (psiPolar n ε lam S τ w hlam hτ).2.2 _ (K_star h₁) _ (K_star h₂) _ (UJ_star hg),
    hσ.1.2 _ (indefinite_unitary_mul_mem ε (K_UJ h₁) hg) _ (K_UJ h₂), hσ.1.2 _ (K_UJ h₁) _ hg]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hτσ _ (K_star h₁), map_star_star, e]

theorem psi_near_one {lam : Fin n → ℝ} (hlam : IsHCParam lam) {w : S} {τ : Mt → (S →L[ℂ] S)}
    (hτ : IsTau ε (lowK ε lam) τ w) (hτσ : ∀ k ∈ Kset ε, ∀ v : S, (τ k v : H) = σ (k.map star) v) :
    ∀ᶠ g : UJ ε in 𝓝 1, ∀ (a b : Fin n) (x y : H),
      Eab ε a b (fun z => ⟪S.orthogonalProjectionOnto y,
        Psi ε lam τ w (z.map star) (S.orthogonalProjectionOnto x)⟫_ℂ) (umat g) = (Module.finrank ℂ S : ℂ) *
      Eab ε a b (fun z => ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) *
        (⟪y, σ (toMK k) (w : H)⟫_ℂ * ⟪σ (toMK k) (w : H), x⟫_ℂ) ∂(muK ε)) (umat g) := by
  have h1 := eventually_UJ (p := fun z => z ∈ U1 ε ∧ Psi ε lam τ w z = ps ε lam τ w z) (psLocal n ε lam S τ w hlam hτ)
  have h2 : Tendsto (fun g : Mt => g.map star) (𝓝 1) (𝓝 1) := by
    have := (Continuous.matrix_map (continuous_id (X := Mt)) (continuous_star (R := ℂ))).tendsto 1
    simpa only [id, map_star_one] using this
  have h3 : Tendsto (fun g : UJ ε => umat g) (𝓝 1) (𝓝 1) := (isClosedEmbeddingMatrix n ε).1.continuous.tendsto 1
  filter_upwards [h3.eventually (h2.eventually h1).eventually_nhds] with g hg a b x y
  rw [← eab_const_mul]
  refine eab_local g.2 (hg.mono fun z hz hzJ => ?_) a b
  obtain ⟨hU, he⟩ := hz (UJ_star hzJ)
  rw [he, ps_entry hτ hτσ hU]

theorem formulaGap : StrictLow → FormulaGap := by
  intro hSL n ε lam H _ _ σ hlam hσ h hgap hh w hw X hX u hu v hv
  haveI := hσ.1
  have hU := hσ.2.2.1
  have hS := (hSL n ε lam hlam H σ hσ).1
  obtain ⟨V, E, hD, hSV⟩ := GlobalTheory.DerEx.exists_isDer_lowKSub n ε lam H σ hU hS
  have han := GlobalTheory.T.lowest_K_type_analytic n ε H σ V E lam hU hD hS hSV u hu X hX.1
  obtain ⟨hw1, hwS, hwt⟩ := hw
  generalize lowKSub ε lam σ = S at *
  haveI := hS.1
  haveI := FiniteDimensional.complete ℂ S
  obtain ⟨τ, hτ, hτσ⟩ := TauExt.tauExists n ε _ H σ S ⟨w, hwS⟩ (URep_K hU) hS hw1 hwt
  have hw0 : (⟨w, hSV hwS⟩ : V) ≠ 0 := fun h0 => by
    have : w = 0 := congrArg Subtype.val h0
    simp [this] at hw1
  obtain ⟨hK, hsp, hfd⟩ := (KType.kType_iff n ε H σ V E hU hD).2 _ S ⟨w, hSV hwS⟩ hS hSV hwS hw0 hwt
  obtain ⟨g₀, hg1, hg2⟩ := exists_gap hlam hgap hh
  have hA : ∀ x y : S, LocAn ε (fun z => ⟪y, Psi ε lam τ ⟨w, hwS⟩ (z.map star) x⟫_ℂ) := fun x y =>
    locAn_conj (f := fun z => ⟪y, Psi ε lam τ ⟨w, hwS⟩ z x⟫_ℂ) fun g hg => psiAnalytic n ε lam S τ _ hlam hτ y x g hg
  have hsm : ∀ (x : V) (y : H), SmoothOnG ε (fun z => ⟪y, diffOp ε lam σ τ ⟨w, hwS⟩ z x⟫_ℂ) := fun x y => by
    rw [inner_diffOp]
    exact Line.smooth_comb _ (hD.2.2.2 x _) (hA _ _).smooth
  have hjet := GlobalTheory.T.highest_weight_gap_bound n ε H σ V E lam g₀ ⟨w, hSV hwS⟩ hU hD hK hfd hg1 hg2
    (fun z => (diffOp ε lam σ τ ⟨w, hwS⟩ z : H →ₗ[ℂ] H)) ?_ ?_ ?_ ?_
  · rw [hsp] at hjet
    have h0 := Line.vanish_of_zero_jet n ε _ X (hsm ⟨u, hSV hu⟩ v) hX.1 (fun l => hjet l u hu v) (by
      intro t ht
      have e := inner_diffOp (ε := ε) (σ := σ) lam τ ⟨w, hwS⟩ u v
      simp only [congrFun e]
      exact (((innerSL ℂ (S.starProjection v)).restrictScalars ℝ).analyticAt _ |>.comp (han t ht)).add
        (analyticAt_const.mul (locAn_line (hA _ _) hX.1 t ht)))
    have hp := exp_posDef (P_star hX)
    have h1 := (psiPolar n ε lam S τ _ hlam hτ).1 1 (one_K ε) _ (P_star hX)
    rw [one_mul, hτ.2.1.1, ← exp_star] at h1
    rw [← exp_star] at hp
    have h2 := ps_entry (lam := lam) hτ hτσ (z := NormedSpace.exp X) (fun k hk => (phiPos n lam _ (by
      rw [K_inv hk]
      exact hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (K_KC hk).1))).1) u v
    rw [congrFun (inner_diffOp lam τ ⟨w, hwS⟩ u v), h1, Submodule.starProjection_eq_self_iff.2 hv, neg_one_mul,
      add_neg_eq_zero] at h0
    refine h0.trans (h2.trans ?_)
    congr 2
    funext k
    have hk : toMK k ∈ Kset ε := k.2
    have hpos : ((toMK k)⁻¹ * NormedSpace.exp X * toMK k).PosDef := by
      rw [K_inv hk]
      exact (exp_posDef hX).conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (K_KC hk).1)
    rw [Phi_star, (phiPos n lam _ hpos).2.1.le.isSelfAdjoint.star_eq]
  · rw [hsp]
    exact fun g hg x _ => ⟨S.sub_mem (S.starProjection_apply_mem _) (Subtype.prop _),
      fun k₁ h₁ k₂ h₂ => diffOp_equiv hlam hU hS.2.1 hτ hτσ hg h₁ h₂ x⟩
  · rw [hsp]
    exact fun x hx y => hsm ⟨x, hSV hx⟩ y
  · intro G hG y
    filter_upwards [psi_near_one hlam hτ hτσ, GlobalTheory.T.highest_weight_eventually_zero n ε H σ V E lam _ hU hD hK hfd G hG y] with g h1 h2
    have h3 : ∀ a b, Eab ε a b (fun z => ⟪y, diffOp ε lam σ τ ⟨w, hwS⟩ z (at1 G a b : V)⟫_ℂ) (umat g) =
        ⟪S.starProjection y, σ (umat g) (E a b (at1 G a b) : V)⟫_ℂ + (-1) * ((Module.finrank ℂ S : ℂ) *
          Eab ε a b (fun z => ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) *
            (⟪y, σ (toMK k) w⟫_ℂ * ⟪σ (toMK k) w, (at1 G a b : V)⟫_ℂ) ∂(muK ε)) (umat g)) := fun a b => by
      rw [inner_diffOp, ← h1 a b (at1 G a b : V) y]
      refine (Line.word_comb (-1) (hD.2.2.2 _ _) (hA _ _).smooth [(a, b)] _ g.2).trans ?_
      rw [(Coef.coef_flow n ε H σ V E hU hD).1 _ _ _ _ g.2]
      rfl
    have h4 := congrArg (fun x : V => ⟪S.starProjection y, σ (umat g) x⟫_ℂ)
      (GlobalTheory.T.highest_weight_derivative_sum_zero n ε H σ V E lam _ hlam hσ hD hK hfd G hG)
    simp only [Submodule.coe_sum, map_sum, inner_sum, Submodule.coe_zero, map_zero, inner_zero_right] at h4
    simp only [ContinuousLinearMap.coe_coe, h3, Finset.sum_add_distrib, ← Finset.mul_sum, h2, h4]
    simp
  · rw [hsp]
    intro x hx
    change diffOp ε lam σ τ ⟨w, hwS⟩ 1 x = 0
    rw [diffOp_apply, map_star_one, (psiPolar n ε lam S τ _ hlam hτ).2.1, hU.1.1]
    exact sub_self _

end GlobalTheory.Jet.FormGap
end
end

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.FormGapFree

open GlobalTheory.Jet.FormGap GlobalTheory.Dec.FormF GlobalTheory.Dec.PsiEig Filter Topology

theorem formulaGap : FormulaGap := by
  intro n ε lam H _ _ σ hlam hσ h hgap hh w hw X hX u hu v hv
  haveI := hσ.1
  have hU := hσ.2.2.1
  obtain ⟨g₀, hg1, hg2⟩ := exists_gap hlam hgap hh
  have hS := GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub n ε lam H σ hlam hσ fun a b hab => by
    rcases lt_trichotomy a b with hlt | heq | hlt
    · exact (hg2.trans_le (hg1 a b hlt hab)).trans_le (le_abs_self _)
    · exact absurd (congrArg ε heq) hab
    · rw [abs_sub_comm]
      exact (hg2.trans_le (hg1 b a hlt hab.symm)).trans_le (le_abs_self _)
  obtain ⟨V, E, hD, hSV⟩ := GlobalTheory.DerEx.exists_isDer_lowKSub n ε lam H σ hU hS
  have han := GlobalTheory.Jet.Anal.lowK_analytic n ε H σ V E lam hU hD hS hSV u hu X hX.1
  obtain ⟨hw1, hwS, hwt⟩ := hw
  generalize lowKSub ε lam σ = S at *
  haveI := hS.1
  haveI := FiniteDimensional.complete ℂ S
  obtain ⟨τ, hτ, hτσ⟩ := TauExt.tauExists n ε _ H σ S ⟨w, hwS⟩ (URep_K hU) hS hw1 hwt
  have hw0 : (⟨w, hSV hwS⟩ : V) ≠ 0 := fun h0 => by
    have : w = 0 := congrArg Subtype.val h0
    simp [this] at hw1
  obtain ⟨hK, hsp, hfd⟩ := (KType.kType_iff n ε H σ V E hU hD).2 _ S ⟨w, hSV hwS⟩ hS hSV hwS hw0 hwt
  have hA : ∀ x y : S, LocAn ε (fun z => ⟪y, Psi ε lam τ ⟨w, hwS⟩ (z.map star) x⟫_ℂ) := fun x y =>
    locAn_conj (f := fun z => ⟪y, Psi ε lam τ ⟨w, hwS⟩ z x⟫_ℂ) fun g hg => psiAnalytic n ε lam S τ _ hlam hτ y x g hg
  have hsm : ∀ (x : V) (y : H), SmoothOnG ε (fun z => ⟪y, diffOp ε lam σ τ ⟨w, hwS⟩ z x⟫_ℂ) := fun x y => by
    rw [inner_diffOp]
    exact Line.smooth_comb _ (hD.2.2.2 x _) (hA _ _).smooth
  have hjet := GlobalTheory.Jet.Germ.germ_jet_zero n ε H σ V E lam g₀ ⟨w, hSV hwS⟩ hU hD hK hfd hg1 hg2
    (fun z => (diffOp ε lam σ τ ⟨w, hwS⟩ z : H →ₗ[ℂ] H)) ?_ ?_ ?_ ?_
  · rw [hsp] at hjet
    have h0 := Line.vanish_of_zero_jet n ε _ X (hsm ⟨u, hSV hu⟩ v) hX.1 (fun l => hjet l u hu v) (by
      intro t ht
      have e := inner_diffOp (ε := ε) (σ := σ) lam τ ⟨w, hwS⟩ u v
      simp only [congrFun e]
      exact (((innerSL ℂ (S.starProjection v)).restrictScalars ℝ).analyticAt _ |>.comp (han t ht)).add
        (analyticAt_const.mul (locAn_line (hA _ _) hX.1 t ht)))
    have hp := exp_posDef (P_star hX)
    have h1 := (psiPolar n ε lam S τ _ hlam hτ).1 1 (one_K ε) _ (P_star hX)
    rw [one_mul, hτ.2.1.1, ← exp_star] at h1
    rw [← exp_star] at hp
    have h2 := ps_entry (lam := lam) hτ hτσ (z := NormedSpace.exp X) (fun k hk => (phiPos n lam _ (by
      rw [K_inv hk]
      exact hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (K_KC hk).1))).1) u v
    rw [congrFun (inner_diffOp lam τ ⟨w, hwS⟩ u v), h1, Submodule.starProjection_eq_self_iff.2 hv, neg_one_mul,
      add_neg_eq_zero] at h0
    refine h0.trans (h2.trans ?_)
    congr 2
    funext k
    have hk : toMK k ∈ Kset ε := k.2
    have hpos : ((toMK k)⁻¹ * NormedSpace.exp X * toMK k).PosDef := by
      rw [K_inv hk]
      exact (exp_posDef hX).conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (K_KC hk).1)
    rw [Phi_star, (phiPos n lam _ hpos).2.1.le.isSelfAdjoint.star_eq]
  · rw [hsp]
    exact fun g hg x _ => ⟨S.sub_mem (S.starProjection_apply_mem _) (Subtype.prop _),
      fun k₁ h₁ k₂ h₂ => diffOp_equiv hlam hU hS.2.1 hτ hτσ hg h₁ h₂ x⟩
  · rw [hsp]
    exact fun x hx y => hsm ⟨x, hSV hx⟩ y
  · intro G hG y
    filter_upwards [psi_near_one hlam hτ hτσ, GlobalTheory.Jet.SchmidIntegral.eab_integral_eq_zero n ε H σ V E lam _ hU hD hK hfd G hG y] with g h1 h2
    have h3 : ∀ a b, Eab ε a b (fun z => ⟪y, diffOp ε lam σ τ ⟨w, hwS⟩ z (at1 G a b : V)⟫_ℂ) (umat g) =
        ⟪S.starProjection y, σ (umat g) (E a b (at1 G a b) : V)⟫_ℂ + (-1) * ((Module.finrank ℂ S : ℂ) *
          Eab ε a b (fun z => ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) *
            (⟪y, σ (toMK k) w⟫_ℂ * ⟪σ (toMK k) w, (at1 G a b : V)⟫_ℂ) ∂(muK ε)) (umat g)) := fun a b => by
      rw [inner_diffOp, ← h1 a b (at1 G a b : V) y]
      refine (Line.word_comb (-1) (hD.2.2.2 _ _) (hA _ _).smooth [(a, b)] _ g.2).trans ?_
      rw [(Coef.coef_flow n ε H σ V E hU hD).1 _ _ _ _ g.2]
      rfl
    have h4 := congrArg (fun x : V => ⟪S.starProjection y, σ (umat g) x⟫_ℂ)
      (GlobalTheory.Jet.Schmid.mul_vminus_eq_zero n ε H σ V E lam _ hlam hσ hD hK hfd G hG)
    simp only [Submodule.coe_sum, map_sum, inner_sum, Submodule.coe_zero, map_zero, inner_zero_right] at h4
    simp only [ContinuousLinearMap.coe_coe, h3, Finset.sum_add_distrib, ← Finset.mul_sum, h2, h4]
    simp
  · rw [hsp]
    intro x hx
    change diffOp ε lam σ τ ⟨w, hwS⟩ 1 x = 0
    rw [diffOp_apply, map_star_one, (psiPolar n ε lam S τ _ hlam hτ).2.1, hU.1.1]
    exact sub_self _

end GlobalTheory.Jet.FormGapFree
end
end
