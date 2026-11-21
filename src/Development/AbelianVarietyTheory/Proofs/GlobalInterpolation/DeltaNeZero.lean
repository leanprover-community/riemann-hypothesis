import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoSelfDualAndPeriodLatticesAgree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MovedVacuumMemThetaFunctionsAndMoves
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.ThetaMove.Transport

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem opU_comp (e : V ≃ₗ[ℂ] V') {H : Sesq V} {H' : Sesq V'} (hH : ∀ x y, H' (e x) (e y) = H x y)
    (F : V' → ℂ) (x z : V) : opU H x (fun w => F (e w)) z = opU H' (e x) F (e z) := by
  simp only [opU, hH, map_add]

def subEquiv (e : V ≃ₗ[ℂ] V') {Λ : AddSubgroup V} {Λ' : AddSubgroup V'} (h : ∀ x, x ∈ Λ ↔ e x ∈ Λ') : Λ ≃+ Λ' where
  toFun x := ⟨e x, (h _).1 x.2⟩
  invFun y := ⟨e.symm y, (h _).2 (by simp)⟩
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by simp

def quotEquiv (e : V ≃ₗ[ℂ] V') {Λ₁ Λ₂ : AddSubgroup V} {Λ₁' Λ₂' : AddSubgroup V'} (h₁ : ∀ x, x ∈ Λ₁ ↔ e x ∈ Λ₁')
    (h₂ : ∀ x, x ∈ Λ₂ ↔ e x ∈ Λ₂') : (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ≃+ (Λ₂' ⧸ Λ₁'.addSubgroupOf Λ₂') :=
  QuotientAddGroup.congr _ _ (subEquiv e h₂) (by
    ext y
    obtain ⟨x, rfl⟩ := (subEquiv e h₂).surjective y
    exact (AddSubgroup.mem_map_iff_mem (f := (subEquiv e h₂ : Λ₂ →+ Λ₂')) (subEquiv e h₂).injective).trans (h₁ _))

theorem term_add {H : Sesq V} {α : V → ℂ} (hH : IsHerm H) {A₁ A₂ : AddSubgroup V} (hd : IsSelfDual H A₂)
    (hs : IsSemiChar H A₂ α) {F : V → ℂ} (hF : F ∈ fixedBy H α A₁) {a s : V} (ha : a ∈ A₂) (hs₂ : s ∈ A₂)
    (hs₁ : s ∈ A₁) (z : V) : α (a + s) * opU H (a + s) F z = α a * opU H a F z := by
  rw [GlobalTheory.ThetaInter.alpha_opU_add hH hd hs ha hs₂, ← GlobalTheory.ThetaInter.opU_mul]
  congr 2
  funext w
  exact hF s hs₁ w

theorem inter_transport : ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (e : V ≃ₗ[ℂ] V') (H : Sesq V) (H' : Sesq V') (α : V → ℂ) (α' : V' → ℂ) (Λ₁ Λ₂ : AddSubgroup V) (Λ₁' Λ₂' : AddSubgroup V') (θ' : V' → ℂ), (∀ x y, H' (e x) (e y) = H x y) → (∀ x, x ∈ Λ₁ ↔ e x ∈ Λ₁') → (∀ x, x ∈ Λ₂ ↔ e x ∈ Λ₂') → (∀ x ∈ Λ₂, α x = α' (e x)) → IsHerm H' → IsSelfDual H' Λ₂' → IsSemiChar H' Λ₂' α' → (IsSelfDual H Λ₂ ∧ IsSemiChar H Λ₂ α ∧ ∀ F' ∈ fixedBy H' α' Λ₂', (fun z => F' (e z)) ∈ fixedBy H α Λ₂) ∧ (θ' ∈ fixedBy H' α' Λ₁' → relIdx Λ₁' Λ₂' ≠ 0 → inter H α Λ₁ Λ₂ (fun z => θ' (e z)) = fun z => inter H' α' Λ₁' Λ₂' θ' (e z)) := by
  intro V V' _ _ _ _ e H H' α α' Λ₁ Λ₂ Λ₁' Λ₂' θ' hH h₁ h₂ hα hh hd hs
  have hE : ∀ x y, altE H x y = altE H' (e x) (e y) := fun x y => by simp only [altE, hH]
  refine ⟨⟨?_, ⟨fun x hx => ?_, fun x hx y hy => ?_⟩, fun F hF x hx z => ?_⟩, fun hθ _ => ?_⟩
  · ext x
    rw [h₂ x]
    conv_rhs => rw [← hd]
    constructor
    · intro h y hy
      obtain ⟨y, rfl⟩ := e.surjective y
      rw [← hE]
      exact h y ((h₂ y).2 hy)
    · intro h y hy
      rw [hE]
      exact h _ ((h₂ y).1 hy)
  · rw [hα x hx]; exact hs.1 _ ((h₂ x).1 hx)
  · rw [hα _ (Λ₂.add_mem hx hy), hα x hx, hα y hy, map_add, hE]
    exact hs.2 _ ((h₂ x).1 hx) _ ((h₂ y).1 hy)
  · rw [opU_comp e hH, hα x hx]
    exact hF _ ((h₂ x).1 hx) _
  · funext z
    have hc : relIdx Λ₁ Λ₂ = relIdx Λ₁' Λ₂' := Nat.card_congr (quotEquiv e h₁ h₂).toEquiv
    rw [inter, inter, hc, ← finsum_comp_equiv (quotEquiv e h₁ h₂).toEquiv]
    congr 1
    refine finsum_congr fun c => ?_
    rw [opU_comp e hH, hα _ (Quotient.out c).2]
    have hm : -(subEquiv e h₂ (Quotient.out c)) + Quotient.out ((quotEquiv e h₁ h₂).toEquiv c) ∈
        Λ₁'.addSubgroupOf Λ₂' := by
      rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
      conv_rhs => rw [← QuotientAddGroup.out_eq' c]
      rfl
    have := term_add hh hd hs hθ (subEquiv e h₂ (Quotient.out c)).2
      (-(subEquiv e h₂ (Quotient.out c)) + Quotient.out ((quotEquiv e h₁ h₂).toEquiv c)).2
      (AddSubgroup.mem_addSubgroupOf.1 hm) (e z)
    rw [← AddSubgroup.coe_add, add_neg_cancel_left] at this
    exact this.symm

end GlobalTheory.ThetaMove.Transport
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fieldIso_selfDual_and_periodLattices_agree : ∀ (X : Fields) (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), s.Ok → (∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), IsSdLat N → StandardLatticesGL3.SD D (s.lat N)) ∧ ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (z : VCx X.Tau a b), z ∈ lam (ambOf s B χ cD) N N' ↔ (fun τ => z (s.iT.symm τ)) ∈ TaylorLogMetric.La D B.tor (s.lat N) (s.lat N') := by
  first | exact @GlobalTheory.PeriodTransport.seam_lattices | exact GlobalTheory.PeriodTransport.seam_lattices | (intros; apply GlobalTheory.PeriodTransport.seam_lattices <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedVacuum_mem_thetaFunctions_and_moves : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (a b : ℕ), TaylorLogMetric.IsChi D χ → B.EqP χ → B.LatAll → B.ThZeroMem a b → Even a → Even b → (∀ L L', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Base.chiFac χ a b L L' ≠ 0 ∧ B.thMoved a b L L' ∈ Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) (TaylorLogMetric.La D B.tor L L')) ∧ (∀ L L' L'', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → StandardLatticesGL3.SD D L'' → B.thMoved a b L L'' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'') (B.thMoved a b L L')) ∧ ∀ L L₁ L', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L₁ → StandardLatticesGL3.SD D L' → B.thMoved a b L₁ L' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L') (B.thMoved a b L L') := by
  first | exact @GlobalTheory.ThetaMove.Moved.thMoved_mem_and_moves | exact GlobalTheory.ThetaMove.Moved.thMoved_mem_and_moves | (intros; apply GlobalTheory.ThetaMove.Moved.thMoved_mem_and_moves <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem int_mul_mem_lamOf (a : 𝓞 D.host.K) {w : ℂ} (hw : w ∈ TaylorLogMetric.lamOf D cc δ) :
    D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ TaylorLogMetric.lamOf D cc δ := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩
    push_cast
    rw [map_mul]
    ring
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [mul_neg]; exact AddSubgroup.neg_mem _ ha

theorem int_smul_mem_La (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (a : 𝓞 D.host.K) {x : TaylorLogMetric.VC D N N'} (hx : x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') :
    D.host.φ₀ (((a : D.host.K) : D.host.E)) • x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L' := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨w, hw, B, hB, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨_, int_mul_mem_lamOf a hw, B, hB, smul_smul _ _ _⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [smul_neg]; exact AddSubgroup.neg_mem _ ha

theorem qIntAll_of_latAll : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), B.LatAll → B.QIntAll := by
  intro D cc δ B h N N' L L' hA x hx
  have hsd := (h.1 N N' L L' hA).1
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hw := int_smul_mem_La L L' a hx
  rw [ha] at hw
  have hw' : StandardLatticesGL3.w0 D • x ∈ dualLat (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.La D B.tor L L') := by
    rw [hsd]; exact hw
  obtain ⟨m, hm⟩ := hw' x hx
  have him : (TaylorLogMetric.Hf D B.tor x x).im = 0 := by
    have : starRingEnd ℂ (TaylorLogMetric.Hf D B.tor x x) = TaylorLogMetric.Hf D B.tor x x := by
      simp only [TaylorLogMetric.Hf, map_div₀, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj, mul_comm]
    exact Complex.conj_eq_iff_im.1 this
  have h1 : (StandardLatticesGL3.w0 D).re = 1 / 2 := by simp [StandardLatticesGL3.w0]
  have h2 : (StandardLatticesGL3.w0 D).im = Real.sqrt D.host.d / 2 := by simp [StandardLatticesGL3.w0]
  have h3 : formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N' x x = TaylorLogMetric.Hf D B.tor x x := rfl
  refine ⟨m, ?_⟩
  rw [← hm, altE, LinearMap.map_smul₂, h3, smul_eq_mul, Complex.mul_im, h1, h2, him]
  ring

end GlobalTheory.ThetaMove
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticForm_integral_of_selfDual_periodLattices : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), B.LatAll → B.QIntAll := by
  first | exact @GlobalTheory.ThetaMove.qIntAll_of_latAll | exact GlobalTheory.ThetaMove.qIntAll_of_latAll | (intros; apply GlobalTheory.ThetaMove.qIntAll_of_latAll <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.ThetaMove.SeamMoves

variable {X : Fields} {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
  (cD : D.what₂.Tau → ℂ)

def reidx (a b : ℕ) : VCx X.Tau a b ≃ₗ[ℂ] TaylorLogMetric.VC D a b := LinearEquiv.funCongrLeft ℂ (Fin b → Fin a → ℂ) s.iT.symm

theorem form_reidx (A : ℝ) (a b : ℕ) (x y : VCx X.Tau a b) :
    formV A D.what₂.Tau a b (reidx s a b x) (reidx s a b y) = Formalism.L2.Ker.HV A⁻¹ x y := by
  change (∑ τ, ∑ i, ∑ j, x (s.iT.symm τ) i j * (starRingEnd ℂ) (y (s.iT.symm τ) i j)) / (A : ℂ) =
    ((A⁻¹ : ℝ) : ℂ) * ∑ τ, ∑ i, ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j)
  rw [Equiv.sum_comp s.iT.symm (fun τ => ∑ i, ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j)), Complex.ofReal_inv, div_eq_inv_mul]

theorem isHerm_formV (A : ℝ) (n : Type) [Fintype n] (a b : ℕ) : IsHerm (formV A n a b) := by
  intro x y
  simp [formV, map_sum, mul_comm]

theorem iop_eq {a b : ℕ} (Λ₁ Λ₂ : AddSubgroup (TaylorLogMetric.VC D a b)) (G : TaylorLogMetric.VC D a b → ℂ) :
    TaylorLogMetric.Iop D B.tor Λ₁ Λ₂ G = inter (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) Λ₁ Λ₂ G := rfl

theorem alV_eq {a b : ℕ} (x : VCx X.Tau a b) {m : ℤ}
    (hm : Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D B.tor (reidx s a b x) (reidx s a b x)).re = (m : ℝ)) :
    alV D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ x = TaylorLogMetric.al D B.tor (reidx s a b x) := by
  have h1 : TaylorLogMetric.Hf D B.tor (reidx s a b x) (reidx s a b x) = Formalism.L2.Ker.HV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ x x :=
    form_reidx s _ a b x x
  unfold TaylorLogMetric.al
  rw [hm, round_intCast]
  rw [h1] at hm
  unfold alV alphaQ Formalism.L2.Th1.H.qOf
  rw [hm, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

include B in
theorem delta_ne_zero : δ ≠ 0 := by
  rintro rfl
  have h1 : B.L.ω₁ ∈ B.L.lattice.toAddSubgroup := B.L.ω₁_mem_lattice
  have h2 : TaylorLogMetric.lamOf D cc 0 ≤ ⊥ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨c, -, rfl⟩
    simp
  rw [B.lat] at h1
  have h3 : B.L.ω₁ = 0 := AddSubgroup.mem_bot.1 (h2 h1)
  exact B.L.indep.ne_zero 0 h3

theorem aa_ne_bot (hcc : cc ≠ ⊥) : (ambOf s B χ cD).AA ≠ ⊥ := by
  intro h
  have h1 : ((Ideal.absNorm cc : ℕ) : X.E) ∈ (ambOf s B χ cD).AA := by
    refine Submodule.subset_span ⟨_, Ideal.absNorm_mem cc, 1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, ?_⟩
    simp
  rw [h, Submodule.mem_bot, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at h1
  exact hcc h1

theorem aa_fg : (ambOf s B χ cD).AA.FG := by
  let j : 𝓞 D.host.E →+* 𝓞 X.E := RingOfIntegers.mapRingHom (s.iE.symm : D.host.E →+* X.E)
  have hj : ∀ a : 𝓞 D.host.E, ((j a : 𝓞 X.E) : X.E) = s.iE.symm (a : D.host.E) := fun _ => rfl
  obtain ⟨z, hz, hden⟩ := D.host.AA0.isFractional
  have hz0 : j z ≠ 0 := fun h => nonZeroDivisors.ne_zero hz (by
    have h1 := hj z
    rw [h] at h1
    have h2 : (z : D.host.E) = 0 := s.iE.symm.injective (by rw [← h1]; simp)
    exact RingOfIntegers.coe_injective (by simpa using h2))
  have hfr : IsFractional (nonZeroDivisors (𝓞 X.E)) (ambOf s B χ cD).AA := by
    refine (FractionalIdeal.isFractional_span_iff).2 ⟨j z, mem_nonZeroDivisors_of_ne_zero hz0, ?_⟩
    rintro r ⟨c, -, t, ht, rfl⟩
    obtain ⟨w, hw⟩ := hden t ht
    refine ⟨j (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w), ?_⟩
    rw [Algebra.smul_def]
    change ((j _ : 𝓞 X.E) : X.E) = ((j z : 𝓞 X.E) : X.E) * _
    rw [hj, hj, ← map_mul]
    congr 1
    have e : ((algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w : 𝓞 D.host.E) : D.host.E) =
      ((c : D.host.K) : D.host.E) * (w : D.host.E) := rfl
    have hw' : (w : D.host.E) = (z : D.host.E) * t := by rw [Algebra.smul_def] at hw; exact hw
    rw [e, hw']
    ring
  exact FractionalIdeal.fg_of_isNoetherianRing le_rfl ⟨_, hfr⟩

theorem vac_eq {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (h : Base.chiFac χ a b (s.lat N) (s.lat N') ≠ 0) :
    vac (ambOf s B χ cD) N N' = fun z => B.thMoved a b (s.lat N) (s.lat N') (reidx s a b z) := by
  funext z
  exact inv_mul_cancel_left₀ h _

theorem moves_ambOf : ∀ (X : Fields) (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), X.Ok → s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsChi D χ → B.EqP χ → B.LatAll → B.ThZeroMem a b → Even a → Even b → Moves (ambOf s B χ cD) a b := by
  intro X D s cc δ B χ cD a b hX hs hcc hχ hE hL hZ ha hb
  obtain ⟨hsd, hlam⟩ := GlobalTheory.T.fieldIso_selfDual_and_periodLattices_agree X D s cc δ B χ cD hs
  obtain ⟨hth, hm1, hm2⟩ := GlobalTheory.T.movedVacuum_mem_thetaFunctions_and_moves D cc δ B χ a b hχ hE hL hZ ha hb
  have hq := GlobalTheory.T.quadraticForm_integral_of_selfDual_periodLattices D cc δ B hL
  have hadm : ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
      TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := fun N N' h h' => ⟨ha, hb, hsd _ _ h, hsd _ _ h'⟩
  have key := fun (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E a)) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b)) (h : IsSdLat N₂)
      (h' : IsSdLat N₂') (θ : TaylorLogMetric.VC D a b → ℂ) =>
    Transport.inter_transport _ _ (reidx s a b) (Formalism.L2.Ker.HV (ambOf s B χ cD).sc)
      (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (alV (ambOf s B χ cD).d (ambOf s B χ cD).sc) (TaylorLogMetric.al D B.tor)
      (lam (ambOf s B χ cD) N₁ N₁') (lam (ambOf s B χ cD) N₂ N₂') (TaylorLogMetric.La D B.tor (s.lat N₁) (s.lat N₁'))
      (TaylorLogMetric.La D B.tor (s.lat N₂) (s.lat N₂')) θ (form_reidx s _ a b) (hlam a b N₁ N₁') (hlam a b N₂ N₂')
      (fun x hx => by
        obtain ⟨m, hm⟩ := hq a b _ _ (hadm N₂ N₂' h h') (reidx s a b x) ((hlam a b N₂ N₂' x).1 hx)
        exact alV_eq s B x hm)
      (isHerm_formV _ _ _ _) (hL.1 a b _ _ (hadm N₂ N₂' h h')).1 (hL.1 a b _ _ (hadm N₂ N₂' h h')).2
  refine ⟨delta_ne_zero B, Fintype.card_pos_iff.1 hX.f_pos, aa_fg s B χ cD, aa_ne_bot s B χ cD hcc.1, ?_, ?_, ?_⟩
  · intro N N' h h'
    obtain ⟨hc, han, hfix⟩ := hth _ _ (hsd _ _ h) (hsd _ _ h')
    obtain ⟨h1, h2, h3⟩ := (key N N N' N' h h' 0).1
    refine ⟨hc, ?_, h1, h2⟩
    rw [vac_eq s B χ cD N N' hc]
    refine ⟨fun z _ => ?_, h3 _ hfix⟩
    exact (han _ (Set.mem_univ _)).comp ((reidx s a b).toLinearMap.toContinuousLinearMap.analyticAt z)
  · intro N N' N'' h h' h''
    obtain ⟨hc, -, hfix⟩ := hth _ _ (hsd _ _ h) (hsd _ _ h')
    rw [vac_eq s B χ cD N N' hc, vac_eq s B χ cD N N'' (hth _ _ (hsd _ _ h) (hsd _ _ h'')).1,
      (key N N N' N'' h h'' _).2 hfix (hL.2 a b _ _ _ _ (hadm N N' h h') (hadm N N'' h h'')).1,
      hm1 _ _ _ (hsd _ _ h) (hsd _ _ h') (hsd _ _ h''), iop_eq]
  · intro N N₁ N' h h₁ h'
    obtain ⟨hc, -, hfix⟩ := hth _ _ (hsd _ _ h) (hsd _ _ h')
    rw [vac_eq s B χ cD N N' hc, vac_eq s B χ cD N₁ N' (hth _ _ (hsd _ _ h₁) (hsd _ _ h')).1,
      (key N N₁ N' N' h₁ h' _).2 hfix (hL.2 a b _ _ _ _ (hadm N N' h h') (hadm N₁ N' h₁ h')).1,
      hm2 _ _ _ (hsd _ _ h) (hsd _ _ h₁) (hsd _ _ h'), iop_eq]

end GlobalTheory.ThetaMove.SeamMoves
end
end
