import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TraceEqAdd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OmAtComplZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHI
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdDual
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.LatBasOHolds

section
noncomputable section

namespace PI.OmLocU.Sd

open MeasureTheory PI.VolStabSW.SdUniqW Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

section Vol

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]

theorem vol_mul_vol_ann {μ : Measure V} {χ : V → V → ℂ} (hμ : SelfDual μ χ)
    (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (h0 : ∀ y, χ y 0 = 1) (L L' : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V))
    (hL'c : IsCompact (L' : Set V)) (hL'o : IsOpen (L' : Set V)) (hA : ann χ (L : Set V) = L') :
    μ.real (L : Set V) * μ.real (L' : Set V) = 1 := by
  classical
  have := hμ.1
  set c : ℝ := μ.real (L : Set V) with hc
  have hcl : IsClopen (L : Set V) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  set Φ : V → ℂ := (L : Set V).indicator (fun _ => (1 : ℂ)) with hΦ
  have hΦc : Continuous Φ := by
    rw [hΦ, ← Set.piecewise_eq_indicator]
    exact continuous_const.piecewise (by simp [hcl.frontier_eq]) continuous_const
  have hΦs : HasCompactSupport Φ :=
    HasCompactSupport.intro hLc fun x hx => Set.indicator_of_notMem hx _
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂μ = (L' : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) y := by
    intro y
    rw [hΦ, transform_indicator μ χ hχ L hLo y, hA]
  have hI : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ := by
    have e : (fun y => ∫ x, Φ x * χ x y ∂μ) = (L' : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) :=
      funext hT
    rw [e, integrable_indicator_iff hL'o.measurableSet]
    exact integrableOn_const hL'c.measure_lt_top.ne
  have h1 := hμ.2 Φ hΦc hΦs hI 0
  have e1 : (fun y => (∫ x, Φ x * χ x y ∂μ) * χ y 0) =
      (L' : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) := by
    funext y
    rw [hT y, h0, mul_one]
  rw [e1, integral_indicator_const _ hL'o.measurableSet, neg_zero, hΦ,
    Set.indicator_of_mem (SetLike.mem_coe.2 L.zero_mem)] at h1
  have h2 : μ.real (L' : Set V) * c = 1 := by
    rw [Complex.real_smul] at h1
    exact_mod_cast h1
  rw [mul_comm]
  exact h2

theorem vol_sq_mul_index {μ : Measure V} {χ : V → V → ℂ} (hμ : SelfDual μ χ)
    (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (h0 : ∀ y, χ y 0 = 1) (L L' : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V))
    (hL'c : IsCompact (L' : Set V)) (hL'o : IsOpen (L' : Set V)) (hA : ann χ (L : Set V) = L')
    (hle : L ≤ L') (hN : L.relIndex L' ≠ 0) :
    μ.real (L : Set V) ^ 2 * (L.relIndex L' : ℝ) = 1 := by
  have := hμ.1
  have h1 := vol_mul_vol_ann hμ hχ h0 L L' hLc hLo hL'c hL'o hA
  have h2 := PI.VolStabSW.measure_eq_relIndex_mul μ L L' hle hL'o.measurableSet
    hLo.measurableSet hN
  have h3 : μ.real (L' : Set V) = (L.relIndex L' : ℝ) * μ.real (L : Set V) := by
    rw [measureReal_def, measureReal_def, h2, ENNReal.toReal_mul]
    simp
  rw [h3] at h1
  linarith [h1]

end Vol

section Ann

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem ann_eq_cond {V : Type} (ψ0 : Fv F v → ℂ) (d : Fv F v) (B : V → V → Fv F v) (L : Set V)
    (hC : ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, ψ0 (s * t) = 1) ↔
      d * t ∈ v.adicCompletionIntegers F)
    (hs : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ L, ∃ x' ∈ L, ∀ y, B x' y = s * B x y) :
    ann (fun x y => ψ0 (B x y)) L = {y | ∀ x ∈ L, d * B x y ∈ v.adicCompletionIntegers F} := by
  ext y
  constructor
  · intro hy x hx
    rw [← hC]
    intro s hs'
    obtain ⟨x', hx', h⟩ := hs s hs' x hx
    rw [← h y]
    exact hy x' hx'
  · intro hy x hx
    have ht := (hC _).2 (hy x hx) 1 (one_mem _)
    simpa using ht

end Ann

end PI.OmLocU.Sd
end
end

section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.VolStabSW
  PI.VolStabSW.SdUniqW PI.VolStabSW.LatFactsW
open scoped TensorProduct

section Oev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem oev_add {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x + y ∈ OEv (E := E) v := Submodule.add_mem _ hx hy

theorem oev_zero : (0 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := Submodule.zero_mem _

theorem oev_neg {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) : -x ∈ OEv (E := E) v :=
  Submodule.neg_mem _ hx

theorem oev_smul {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E}
    (hx : x ∈ OEv (E := E) v) : s • x ∈ OEv (E := E) v :=
  Submodule.smul_mem _ (⟨s, hs⟩ : v.adicCompletionIntegers F) hx

theorem sdc_sc_mul (x : Fv F v) (c : Fv F v ⊗[F] E) : sc (E := E) v x * c = x • c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul y e => simp [sc, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul']
  | add p q hp hq => rw [mul_add, hp, hq, smul_add]

theorem dV_int : dV v ∈ v.adicCompletionIntegers F := by
  unfold dV
  split_ifs with h
  · obtain ⟨x, _, he⟩ := h.choose_spec.2.2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← he]
    rw [show algebraMap F (Fv F v) ((x : 𝓞 F) : F) = (((x : 𝓞 F) : F) : v.adicCompletion F) from rfl,
      v.valuedAdicCompletion_eq_valuation']
    exact v.valuation_le_one x
  · exact one_mem _

theorem dV_ne_zero : dV v ≠ 0 := by
  unfold dV
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

theorem psiV_zero (ψ : AddChar (AF F) ℂ) : psiV F ψ v 0 = 1 := by
  have hs : singleV F v (0 : Fv F v) = 0 := by
    have h := SdUniqW.singleV_add v (0 : Fv F v) 0
    rw [add_zero] at h
    simpa using h
  rw [psiV, hs]
  convert AddChar.map_zero_eq_one ψ
  rfl

theorem unif_ne_zero {ϖ : Fv F v} (h : IsUnif v ϖ) : ϖ ≠ 0 := by
  intro h0
  rw [IsUnif, h0, map_zero] at h
  exact WithZero.coe_ne_zero h.symm

theorem unif_int {ϖ : Fv F v} (h : IsUnif v ϖ) : ϖ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, h]
  exact le_of_lt (by decide)

end Oev

section HermO

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

def HO (a : ℕ) : AddSubgroup (HermR (Fv F v) σ a) where
  carrier := {S | ∀ i j, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OEv (E := E) v}
  add_mem' := fun {_ _} hx hy i j => oev_add v (hx i j) (hy i j)
  zero_mem' := fun _ _ => oev_zero v
  neg_mem' := fun {_} hx i j => oev_neg v (hx i j)

theorem mem_HO {a : ℕ} (S : HermR (Fv F v) σ a) :
    S ∈ HO σ v a ↔ ∀ i j, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OEv (E := E) v :=
  Iff.rfl

theorem smul_mem_HO {a : ℕ} {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F)
    {S : HermR (Fv F v) σ a} (hS : S ∈ HO σ v a) : s • S ∈ HO σ v a := by
  rw [mem_HO] at hS ⊢
  intro i j
  rw [coe_hermSMul, Matrix.smul_apply]
  exact oev_smul v hs (hS i j)

theorem hermitianDivisible_eq_smul {a : ℕ} {ϖ : Fv F v} (hϖ : ϖ ≠ 0) :
    HermP v σ a ϖ = (smulSub ϖ (HO σ v a) : Set (HermR (Fv F v) σ a)) := by
  ext S
  rw [SetLike.mem_coe, mem_smulSub]
  simp only [HermP, PO, Set.mem_ofPred_eq]
  constructor
  · intro hS
    refine ⟨ϖ⁻¹ • S, ?_, ?_⟩
    · rw [mem_HO]
      intro i j
      obtain ⟨c, hc, he⟩ := hS i j
      rw [coe_hermSMul, Matrix.smul_apply, he, sdc_sc_mul, smul_smul, inv_mul_cancel₀ hϖ, one_smul]
      exact hc
    · rw [smul_smul, mul_inv_cancel₀ hϖ, one_smul]
  · rintro ⟨p, hp, rfl⟩ i j
    refine ⟨(p : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j, hp i j, ?_⟩
    rw [coe_hermSMul, Matrix.smul_apply, sdc_sc_mul]

theorem pairHerm_smul_left {a : ℕ} (s : Fv F v) (S T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a (s • S) T = s * pairHerm (Fv F v) σ a S T := by
  simp only [pairHerm, coe_hermSMul, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul,
    smul_eq_mul]
  ring

theorem pairHerm_zero_right {a : ℕ} (S : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a S 0 = 0 := by
  simp [pairHerm]

end HermO

section Steps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def TopH (a : ℕ) : Prop :=
  IsCompact (HO σ v a : Set (HermR (Fv F v) σ a)) ∧ IsOpen (HO σ v a : Set (HermR (Fv F v) σ a))

def DualH (a : ℕ) : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v →
    {T : HermR (Fv F v) σ a | ∀ S ∈ HO σ v a,
      dV v * pairHerm (Fv F v) σ a S T ∈ v.adicCompletionIntegers F} =
      (smulSub (dV v)⁻¹ (HO σ v a) : Set (HermR (Fv F v) σ a))

def IdxHO (a : ℕ) : Prop :=
  UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ((HO σ v a).relIndex (smulSub (dV v)⁻¹ (HO σ v a)) : ℝ) = absV v (dV v) ^ (-((a : ℝ) ^ 2)) ∧
    ((smulSub ϖ (HO σ v a)).relIndex (HO σ v a) : ℝ) = qv v ^ (a ^ 2)

theorem sdVolH_of_top (a : ℕ) (hC : CondV σ J ψ v) (hT : TopH σ v a) (hD : DualH σ J ψ v a)
    (hI : IdxHO σ v a) : SdVolH σ J ψ v a := by
  intro hS hU hν ϖ hϖ
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hϖ0 := unif_ne_zero v hϖ
  have hd0 := dV_ne_zero v
  have hνsd : SdHerm F E σ (Fv F v) (psiV F ψ v) a (dT σ ψ v a) := by
    simp only [dT, dif_pos hν]
    exact hν.choose_spec
  have := hνsd.1
  set ν := dT σ ψ v a with hνdef
  set L := HO σ v a with hLdef
  set L' := smulSub (dV v)⁻¹ L with hL'def
  obtain ⟨hLc, hLo⟩ := hT
  have hL'c : IsCompact (L' : Set (HermR (Fv F v) σ a)) := isCompact_smulSub _ L hLc
  have hL'o : IsOpen (L' : Set (HermR (Fv F v) σ a)) := isOpen_smulSub _ (inv_ne_zero hd0) L hLo
  have hχ : ∀ x t y : HermR (Fv F v) σ a, psiV F ψ v (pairHerm (Fv F v) σ a (t + x) y) =
      psiV F ψ v (pairHerm (Fv F v) σ a t y) * psiV F ψ v (pairHerm (Fv F v) σ a x y) := by
    intro x t y
    rw [pairHerm_add, psiV_add]
  have h0 : ∀ y : HermR (Fv F v) σ a, psiV F ψ v (pairHerm (Fv F v) σ a y 0) = 1 := by
    intro y
    rw [pairHerm_zero_right, psiV_zero]
  have hA : ann (fun S T => psiV F ψ v (pairHerm (Fv F v) σ a S T)) (L : Set (HermR (Fv F v) σ a)) =
      L' := by
    rw [Sd.ann_eq_cond v (psiV F ψ v) (dV v) (pairHerm (Fv F v) σ a) _ (hC hS)]
    · exact hD hS hU
    · intro s hs x hx
      exact ⟨s • x, smul_mem_HO σ v hs hx, fun y => pairHerm_smul_left σ v s x y⟩
  have hle : L ≤ L' := by
    intro S hS'
    rw [hL'def, mem_smulSub]
    refine ⟨dV v • S, smul_mem_HO σ v (dV_int v) hS', ?_⟩
    rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
  obtain ⟨hN1, hN2⟩ := hI hU ϖ hϖ
  have hNz : L.relIndex L' ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hN1
    have := Real.rpow_pos_of_pos (absV_dV_pos v) (-((a : ℝ) ^ 2))
    linarith
  have key := Sd.vol_sq_mul_index hνsd hχ h0 L L' hLc hLo hL'c hL'o hA hle hNz
  rw [hN1] at key
  have hp := absV_dV_pos v
  have hvolL : ν.real (L : Set (HermR (Fv F v) σ a)) = absV v (dV v) ^ ((a : ℝ) ^ 2 / 2) := by
    have e1 : absV v (dV v) ^ (-((a : ℝ) ^ 2)) = (absV v (dV v) ^ ((a : ℝ) ^ 2))⁻¹ :=
      Real.rpow_neg hp.le _
    have e2 : (absV v (dV v) ^ ((a : ℝ) ^ 2 / 2)) ^ 2 = absV v (dV v) ^ ((a : ℝ) ^ 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
      norm_num
    have hA2 : 0 < absV v (dV v) ^ ((a : ℝ) ^ 2) := Real.rpow_pos_of_pos hp _
    rw [e1] at key
    have e3 : ν.real (L : Set (HermR (Fv F v) σ a)) ^ 2 = (absV v (dV v) ^ ((a : ℝ) ^ 2 / 2)) ^ 2 := by
      rw [e2]
      field_simp at key
      linarith
    exact (pow_left_inj₀ measureReal_nonneg (Real.rpow_pos_of_pos hp _).le two_ne_zero).1 e3
  have hle2 : smulSub ϖ L ≤ L := by
    intro S hS'
    rw [mem_smulSub] at hS'
    obtain ⟨p, hp', rfl⟩ := hS'
    exact smul_mem_HO σ v (unif_int v hϖ) hp'
  have hPo : IsOpen (smulSub ϖ L : Set (HermR (Fv F v) σ a)) := isOpen_smulSub _ hϖ0 L hLo
  have hPc : IsCompact (smulSub ϖ L : Set (HermR (Fv F v) σ a)) := isCompact_smulSub _ L hLc
  have hNz2 : (smulSub ϖ L).relIndex L ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hN2
    have := pow_pos (qv_pos v) (a ^ 2)
    linarith
  have h2 := PI.VolStabSW.measure_eq_relIndex_mul ν (smulSub ϖ L) L hle2 hLo.measurableSet
    hPo.measurableSet hNz2
  have h3 : ν.real (L : Set (HermR (Fv F v) σ a)) =
      ((smulSub ϖ L).relIndex L : ℝ) * ν.real (smulSub ϖ L : Set (HermR (Fv F v) σ a)) := by
    rw [measureReal_def, measureReal_def, h2, ENNReal.toReal_mul]
    simp
  rw [hN2, hvolL] at h3
  rw [hermitianDivisible_eq_smul σ v hϖ0, ← ENNReal.ofReal_toReal hPc.measure_lt_top.ne, ← measureReal_def]
  congr 1
  have hq := pow_pos (qv_pos v) (a ^ 2)
  have e4 : qv v ^ (-((a : ℤ) ^ 2)) = (qv v ^ (a ^ 2))⁻¹ := by
    rw [zpow_neg]
    congr 1
  rw [e4, h3]
  field_simp

end Steps

end PI.OmLocU
end
end

section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
  PI.VolStabSW PI.VolStabSW.SdUniqW
open scoped TensorProduct

section Steps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def LW (a : ℕ) : AddSubgroup (TupV (E := E) v n a) where
  carrier := LamT v Λ a
  add_mem' := fun {_ _} hx hy i => Submodule.add_mem _ (hx i) (hy i)
  zero_mem' := fun _ => Submodule.zero_mem _
  neg_mem' := fun {_} hx i => Submodule.neg_mem _ (hx i)

theorem coe_LW (a : ℕ) : (LW v Λ a : Set (TupV (E := E) v n a)) = LamT v Λ a := rfl

theorem smul_mem_LW {a : ℕ} {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F)
    {X : TupV (E := E) v n a} (hX : X ∈ LW v Λ a) : s • X ∈ LW v Λ a :=
  fun i => Submodule.smul_mem _ (⟨s, hs⟩ : v.adicCompletionIntegers F) (hX i)

def TopW (a : ℕ) : Prop :=
  (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsCompact (LamT (E := E) v Λ a) ∧ IsOpen (LamT (E := E) v Λ a)

def DualW (a : ℕ) : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v →
    {Y : TupV (E := E) v n a | ∀ X ∈ LamT v Λ a,
      dV v * BR (Fv F v) σ J X Y ∈ v.adicCompletionIntegers F} =
      (smulSub (dV v)⁻¹ (LW v Λ a) : Set (TupV (E := E) v n a))

def IdxW (a : ℕ) : Prop :=
  (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    UnramAt (E := E) v →
    ((LW v Λ a).relIndex (smulSub (dV v)⁻¹ (LW v Λ a)) : ℝ) = absV v (dV v) ^ (-(2 * ((n : ℝ) * a)))

theorem sdVolW_of_top (a : ℕ) (hC : CondV σ J ψ v) (hT : TopW v Λ a) (hD : DualW σ J ψ v Λ a)
    (hI : IdxW v Λ a) : SdVolW σ J ψ v Λ a := by
  intro hS hL hSD hU hμ
  have hd0 := dV_ne_zero v
  have hμsd : SdW F E σ n J (Fv F v) (psiV F ψ v) a (dX σ J ψ v a) := by
    simp only [dX, dif_pos hμ]
    exact hμ.choose_spec
  have := hμsd.1
  set μ := dX σ J ψ v a with hμdef
  set L := LW v Λ a with hLdef
  set L' := smulSub (dV v)⁻¹ L with hL'def
  obtain ⟨hLc, hLo⟩ := hT hL
  rw [← coe_LW] at hLc hLo
  have hL'c : IsCompact (L' : Set (TupV (E := E) v n a)) := isCompact_smulSub _ L hLc
  have hL'o : IsOpen (L' : Set (TupV (E := E) v n a)) := isOpen_smulSub _ (inv_ne_zero hd0) L hLo
  have hχ : ∀ x t y : TupV (E := E) v n a, psiV F ψ v (BR (Fv F v) σ J (t + x) y) =
      psiV F ψ v (BR (Fv F v) σ J t y) * psiV F ψ v (BR (Fv F v) σ J x y) := by
    intro x t y
    rw [BR_add, psiV_add]
  have h0 : ∀ y : TupV (E := E) v n a, psiV F ψ v (BR (Fv F v) σ J y 0) = 1 := by
    intro y
    have e := SdDualW.BR_smul_right v σ J 0 y y
    rw [zero_smul, zero_mul] at e
    rw [e, psiV_zero]
  have hA : ann (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y)) (L : Set (TupV (E := E) v n a)) = L' := by
    rw [Sd.ann_eq_cond v (psiV F ψ v) (dV v) (BR (Fv F v) σ J) _ (hC hS)]
    · exact hD hS hL hSD hU
    · intro s hs x hx
      exact ⟨s • x, smul_mem_LW v Λ hs hx, fun y => SdDualW.BR_smul_left v σ J s x y⟩
  have hle : L ≤ L' := by
    intro X hX
    rw [hL'def, mem_smulSub]
    refine ⟨dV v • X, smul_mem_LW v Λ (dV_int v) hX, ?_⟩
    rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have hN1 := hI hL hU
  have hNz : L.relIndex L' ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hN1
    have := Real.rpow_pos_of_pos (absV_dV_pos v) (-(2 * ((n : ℝ) * a)))
    linarith
  have key := Sd.vol_sq_mul_index hμsd hχ h0 L L' hLc hLo hL'c hL'o hA hle hNz
  rw [hN1] at key
  have hp := absV_dV_pos v
  have e1 : absV v (dV v) ^ (-(2 * ((n : ℝ) * a))) = (absV v (dV v) ^ (2 * ((n : ℝ) * a)))⁻¹ :=
    Real.rpow_neg hp.le _
  have e2 : (absV v (dV v) ^ ((n : ℝ) * a)) ^ 2 = absV v (dV v) ^ (2 * ((n : ℝ) * a)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
    ring_nf
  have hA2 : 0 < absV v (dV v) ^ (2 * ((n : ℝ) * a)) := Real.rpow_pos_of_pos hp _
  rw [e1] at key
  have e3 : μ.real (L : Set (TupV (E := E) v n a)) ^ 2 = (absV v (dV v) ^ ((n : ℝ) * a)) ^ 2 := by
    rw [e2]
    field_simp at key
    rw [key, mul_assoc]
  have hvol := (pow_left_inj₀ measureReal_nonneg (Real.rpow_pos_of_pos hp _).le two_ne_zero).1 e3
  rw [← coe_LW, ← ENNReal.ofReal_toReal hLc.measure_lt_top.ne, ← measureReal_def, hvol]

end Steps

end PI.OmLocU
end
end

section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.VolStabSW
  PI.VolStabSW.PositiveNearLattice PI.VolStabSW.SdDualW
open scoped TensorProduct

section Top

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def oevS : AddSubgroup (Fv F v ⊗[F] E) :=
  (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)).toAddSubgroup

theorem coe_oevS : (oevS (E := E) v : Set (Fv F v ⊗[F] E)) = OEv (E := E) v := rfl

theorem inclR_mem_oev (x : 𝓞 E) : inclR (F := F) (Fv F v) (x : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨x, Set.mem_univ _, rfl⟩

theorem exists_int_basis : ∃ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ k, IsIntegral ℤ (b k) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  classical
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image (Module.finBasis F E))
  have hyF : IsUnit ((y : F)) := by
    rw [isUnit_iff_ne_zero]
    exact_mod_cast hy
  refine ⟨_, (Module.finBasis F E).isUnitSMul (fun _ => hyF), fun k => ?_⟩
  rw [Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]
  exact hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))

theorem latA_le_oevS [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (hb : ∀ k, IsIntegral ℤ (b k)) : latA v b ≤ oevS (E := E) v := by
  intro z hz
  have hz' : ∀ k, crd b (Fv F v) z k ∈ v.adicCompletionIntegers F := hz
  rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply]
  have hm : inclR (F := F) (Fv F v) (((⟨b k, hb k⟩ : 𝓞 E)) : E) ∈ OEv (E := E) v :=
    inclR_mem_oev v (⟨b k, hb k⟩ : 𝓞 E)
  exact Submodule.smul_mem _ (⟨_, hz' k⟩ : v.adicCompletionIntegers F) hm

theorem isOpen_oev : IsOpen (OEv (E := E) v) := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨d, b, hb⟩ := exists_int_basis (F := F) (E := E)
  rw [← coe_oevS]
  exact AddSubgroup.isOpen_mono (latA_le_oevS v b hb) (isOpen_latA v b)

theorem isCompact_oev : IsCompact (OEv (E := E) v) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  set g : Fin m → Fv F v ⊗[F] E := fun i => inclR (F := F) (Fv F v) ((s i : 𝓞 E) : E) with hg
  have e : OEv (E := E) v = (fun c : Fin m → Fv F v => ∑ i, c i • g i) ''
      Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext z
    constructor
    · intro hz
      have h1 : z ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range g) := by
        refine (Submodule.span_le.2 ?_) hz
        rintro _ ⟨x, _, rfl⟩
        have hx : x ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; exact Submodule.mem_top
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact Submodule.subset_span ⟨i, rfl⟩
        | zero => simpa using Submodule.zero_mem _
        | add p q _ _ hp hq =>
          have e1 : inclR (F := F) (Fv F v) (((p + q : 𝓞 E)) : E) =
              inclR (F := F) (Fv F v) (p : E) + inclR (F := F) (Fv F v) (q : E) := by
            rw [← map_add]
            rfl
          show inclR (F := F) (Fv F v) (((p + q : 𝓞 E)) : E) ∈ _
          rw [e1]
          exact Submodule.add_mem _ (hp trivial) (hq trivial)
        | smul r p _ hp =>
          have e1 : inclR (F := F) (Fv F v) (((r • p : 𝓞 E)) : E) =
              r • inclR (F := F) (Fv F v) (p : E) := by
            rw [show ((r • p : 𝓞 E) : E) = r • (p : E) from map_zsmul (algebraMap (𝓞 E) E) r p,
              map_zsmul]
          show inclR (F := F) (Fv F v) (((r • p : 𝓞 E)) : E) ∈ _
          rw [e1]
          exact zsmul_mem (hp trivial) r
      rw [Submodule.mem_span_range_iff_exists_fun] at h1
      obtain ⟨c, rfl⟩ := h1
      exact ⟨fun i => (c i : Fv F v), fun i _ => (c i).2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ (⟨c i, hc i (Set.mem_univ _)⟩ : v.adicCompletionIntegers F)
          (inclR_mem_oev v (s i))
  rw [e]
  exact (isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image
    (continuous_finsetSum _ fun i _ => by fun_prop)

variable (σ : E →ₐ[F] E)

theorem coe_HO (a : ℕ) : (HO σ v a : Set (HermR (Fv F v) σ a)) =
    Subtype.val ⁻¹' (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a => OEv (E := E) v) := by
  ext S
  constructor
  · intro h
    rw [SetLike.mem_coe, mem_HO] at h
    exact fun i _ j _ => h i j
  · intro h
    rw [SetLike.mem_coe, mem_HO]
    exact fun i j => h i (Set.mem_univ _) j (Set.mem_univ _)

theorem topH_holds (a : ℕ) : TopH σ v a := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a => OEv (E := E) v) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_oev v
  have := locallyCompact_Fv F v
  refine ⟨?_, ?_⟩
  · rw [coe_HO]
    exact (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal.isCompact_preimage hK
  · rw [coe_HO]
    exact (isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => isOpen_oev v).preimage continuous_subtype_val

end Top

end PI.OmLocU
end
end

section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
  PI.VolStabSW PI.VolStabSW.PositiveNearLattice PI.VolStabSW.SdDualW
open scoped TensorProduct

section TopWs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem sdc_exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ y : ℤ, y ≠ 0 ∧ y • x ∈ L := by
  classical
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  obtain ⟨m, f, g, rfl⟩ := Submodule.mem_span_set'.1 hx
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image f)
  refine ⟨y, hy, ?_⟩
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : IsIntegral ℤ (y • f i) := hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  convert L.smul_mem (⟨y • f i, hi⟩ : 𝓞 E) (g i).2 using 1
  rw [← smul_assoc]
  rfl

theorem exists_int_smul_mem_all (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) {ι : Type} [Fintype ι] (w : ι → Fin n → E) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ j, y • w j ∈ L := by
  classical
  choose y hy hw using fun j => sdc_exists_int_smul_mem L hL (w j)
  refine ⟨∏ j, y j, Finset.prod_ne_zero_iff.2 fun j _ => hy j, fun j => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_smul]
  exact zsmul_mem (hw j) _

theorem ratV_single (i : Fin n) (e : E) :
    ratV (F := F) (Fv F v) (Pi.single i e : Fin n → E) =
      (Pi.single i (inclR (F := F) (Fv F v) e) : Fin n → Fv F v ⊗[F] E) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [ratV]
  · simp [ratV, Pi.single_eq_of_ne h]

theorem ratV_mem_latLoc {Λ : Set (Fin n → E)} {x : Fin n → E} (hx : x ∈ Λ) :
    ratV (F := F) (Fv F v) x ∈ latLoc (E := E) v Λ :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem sdc_isOpen_latLoc (Λ : Set (Fin n → E))
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    IsOpen (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨L, hLat, rfl⟩ := hL
  obtain ⟨d, b, hb⟩ := exists_int_basis (F := F) (E := E)
  obtain ⟨N, hN, hNw⟩ := exists_int_smul_mem_all L hLat.span_eq_top
    (fun p : Fin n × Fin d => (Pi.single p.1 (b p.2) : Fin n → E))
  have hNF : IsUnit ((N : F)) := by
    rw [isUnit_iff_ne_zero]
    exact_mod_cast hN
  set b2 := b.isUnitSMul (fun _ => hNF) with hb2
  have hb2L : ∀ i k, (Pi.single i (b2 k) : Fin n → E) ∈ L := by
    intro i k
    have e : (Pi.single i (b2 k) : Fin n → E) = N • (Pi.single i (b k) : Fin n → E) := by
      rw [hb2, Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]
      funext j
      by_cases h : j = i
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]
    rw [e]
    exact hNw (i, k)
  let H : AddSubgroup (Fin n → Fv F v ⊗[F] E) := AddSubgroup.pi Set.univ (fun _ => latA v b2)
  have hHo : IsOpen (H : Set (Fin n → Fv F v ⊗[F] E)) := by
    rw [AddSubgroup.coe_pi]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_latA v b2
  have hle : H ≤ (latLoc (E := E) v (L : Set (Fin n → E))).toAddSubgroup := by
    intro X hX
    rw [AddSubgroup.mem_pi] at hX
    rw [Submodule.mem_toAddSubgroup, ← Finset.univ_sum_single X]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hXi : ∀ k, crd b2 (Fv F v) (X i) k ∈ v.adicCompletionIntegers F := hX i (Set.mem_univ _)
    have e : Pi.single i (X i) = ∑ k, crd b2 (Fv F v) (X i) k •
        ratV (F := F) (Fv F v) (Pi.single i (b2 k) : Fin n → E) := by
      have hr := (Algebra.TensorProduct.basis (Fv F v) b2).sum_repr (X i)
      simp only [Algebra.TensorProduct.basis_apply] at hr
      funext j
      by_cases h : j = i
      · subst h
        simp only [ratV_single, Finset.sum_apply, Pi.smul_apply, Pi.single_eq_same]
        conv_lhs => rw [← hr]
        rfl
      · simp [ratV_single, Finset.sum_apply, Pi.single_eq_of_ne h]
    rw [e]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ (⟨_, hXi k⟩ : v.adicCompletionIntegers F) (ratV_mem_latLoc v (hb2L i k))
  exact AddSubgroup.isOpen_mono hle hHo

theorem sdc_isCompact_latLoc (Λ : Set (Fin n → E))
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    IsCompact (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨L, hLat, rfl⟩ := hL
  have : Module.Finite (𝓞 E) L := Submodule.IsLattice.finite (A := E) L
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := L)
  set g : Fin m → Fin n → Fv F v ⊗[F] E := fun i => ratV (F := F) (Fv F v) ((s i : L) : Fin n → E)
    with hg
  have hadd : ∀ p q : Fin n → E, ratV (F := F) (Fv F v) (p + q) =
      ratV (F := F) (Fv F v) p + ratV (F := F) (Fv F v) q := by
    intro p q
    funext j
    simp [ratV]
  have hzs : ∀ (r : ℤ) (p : Fin n → E), ratV (F := F) (Fv F v) (r • p) = r • ratV (F := F) (Fv F v) p := by
    intro r p
    funext j
    simp [ratV]
  have e : (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) =
      (fun c : Fin m → Fv F v => ∑ i, c i • g i) ''
        Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext z
    constructor
    · intro hz
      have h1 : z ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range g) := by
        refine (Submodule.span_le.2 ?_) hz
        rintro _ ⟨x, hx, rfl⟩
        have hx' : (⟨x, hx⟩ : L) ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; exact Submodule.mem_top
        have key : ∀ y : L, y ∈ Submodule.span ℤ (Set.range s) →
            ratV (F := F) (Fv F v) (y : Fin n → E) ∈
              Submodule.span (v.adicCompletionIntegers F) (Set.range g) := by
          intro y hy
          induction hy using Submodule.span_induction with
          | mem y hy =>
            obtain ⟨i, rfl⟩ := hy
            exact Submodule.subset_span ⟨i, rfl⟩
          | zero =>
            have : ratV (F := F) (Fv F v) (0 : Fin n → E) = 0 := by
              funext j
              simp [ratV]
            simpa [this] using Submodule.zero_mem _
          | add p q _ _ hp hq =>
            rw [Submodule.coe_add, hadd]
            exact Submodule.add_mem _ hp hq
          | smul r p _ hp =>
            rw [show ((r • p : L) : Fin n → E) = r • (p : Fin n → E) from rfl, hzs]
            exact zsmul_mem hp r
        exact key _ hx'
      rw [Submodule.mem_span_range_iff_exists_fun] at h1
      obtain ⟨c, rfl⟩ := h1
      exact ⟨fun i => (c i : Fv F v), fun i _ => (c i).2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ (⟨c i, hc i (Set.mem_univ _)⟩ : v.adicCompletionIntegers F)
          (ratV_mem_latLoc v (s i).2)
  rw [e]
  exact (isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image
    (continuous_finsetSum _ fun i _ => by fun_prop)

theorem topW_holds (Λ : Set (Fin n → E)) (a : ℕ) : TopW v Λ a := by
  intro hL
  have e : LamT (E := E) v Λ a =
      Set.pi Set.univ (fun _ : Fin a => (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E))) := by
    ext X
    simp [LamT, Set.mem_pi]
  rw [e]
  exact ⟨isCompact_univ_pi fun _ => sdc_isCompact_latLoc v Λ hL,
    isOpen_set_pi Set.finite_univ fun _ _ => sdc_isOpen_latLoc v Λ hL⟩

end TopWs

end PI.OmLocU
end
end

section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.VolStabSW

section Idx

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  {W : Type} [AddCommGroup W] [Module (Fv F v) W]

theorem sdc_unifEx_holds : UnifEx v := ⟨unifV v, by rw [IsUnif, unifV_val]; rfl⟩

theorem smulSub_smulSub (s t : Fv F v) (P : AddSubgroup W) :
    smulSub s (smulSub t P) = smulSub (s * t) P := by
  ext z
  simp only [mem_smulSub]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, by rw [smul_smul]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨t • p, ⟨p, hp, rfl⟩, by rw [smul_smul]⟩

theorem smulSub_one (P : AddSubgroup W) : smulSub (1 : Fv F v) P = P := by
  ext z
  simp [mem_smulSub]

theorem relIndex_smulSub {t : Fv F v} (ht : t ≠ 0) (H G : AddSubgroup W) :
    (smulSub t H).relIndex (smulSub t G) = H.relIndex G :=
  AddSubgroup.relIndex_map_map_of_injective H G (smul_right_injective W ht)

theorem smulSub_le {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F) (P : AddSubgroup W)
    (hP : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ P, s • x ∈ P) : smulSub s P ≤ P := by
  intro z hz
  rw [mem_smulSub] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  exact hP s hs p hp

theorem smulSub_unit {u : Fv F v} (hu : u ∈ v.adicCompletionIntegers F)
    (hu' : u⁻¹ ∈ v.adicCompletionIntegers F) (hu0 : u ≠ 0) (P : AddSubgroup W)
    (hP : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ P, s • x ∈ P) : smulSub u P = P := by
  apply le_antisymm (smulSub_le v hu P hP)
  intro z hz
  rw [mem_smulSub]
  exact ⟨u⁻¹ • z, hP _ hu' z hz, by rw [smul_smul, mul_inv_cancel₀ hu0, one_smul]⟩

theorem relIndex_pow {ϖ : Fv F v} (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ v.adicCompletionIntegers F)
    (P : AddSubgroup W) (hP : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ P, s • x ∈ P) (k : ℕ) :
    (smulSub (ϖ ^ k) P).relIndex P = ((smulSub ϖ P).relIndex P) ^ k := by
  induction k with
  | zero => simp [smulSub_one]
  | succ k ih =>
    have e : smulSub (ϖ ^ (k + 1)) P = smulSub (ϖ ^ k) (smulSub ϖ P) := by
      rw [smulSub_smulSub, pow_succ]
    have h2 : smulSub (ϖ ^ k) P ≤ P := smulSub_le v (pow_mem hϖ k) P hP
    have h1 : smulSub (ϖ ^ k) (smulSub ϖ P) ≤ smulSub (ϖ ^ k) P := by
      intro z hz
      rw [mem_smulSub] at hz ⊢
      obtain ⟨p, hp, rfl⟩ := hz
      exact ⟨p, smulSub_le v hϖ P hP hp, rfl⟩
    rw [e, ← AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2, relIndex_smulSub v (pow_ne_zero k hϖ0), ih]
    ring

theorem exists_unit_pow {ϖ : Fv F v} (hϖ : IsUnif v ϖ) {d : Fv F v} (hd0 : d ≠ 0)
    (hd : d ∈ v.adicCompletionIntegers F) :
    ∃ k : ℕ, ∃ u : Fv F v, u ∈ v.adicCompletionIntegers F ∧ u⁻¹ ∈ v.adicCompletionIntegers F ∧
      u ≠ 0 ∧ d = ϖ ^ k * u ∧ absV v d = qv v ^ (-(k : ℤ)) := by
  have hϖ0 := unif_ne_zero v hϖ
  have hv : Valued.v d ≠ 0 := (Valuation.ne_zero_iff _).2 hd0
  set m : ℤ := Multiplicative.toAdd (WithZero.unzero hv) with hmdef
  have hvm : Valued.v d = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    simp [m]
  have hm : m ≤ 0 := by
    have h1 : Valued.v d ≤ 1 := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hd
      exact hd
    rw [hvm] at h1
    have h2 : (Multiplicative.ofAdd m : Multiplicative ℤ) ≤ 1 := by exact_mod_cast h1
    rw [← ofAdd_zero] at h2
    exact Multiplicative.ofAdd_le.1 h2
  have hk : ((m.natAbs : ℕ) : ℤ) = -m := Int.ofNat_natAbs_of_nonpos hm
  have hvk : Valued.v (ϖ ^ m.natAbs) = Valued.v d := by
    rw [map_pow, hϖ, hvm, ← WithZero.coe_pow, ← ofAdd_nsmul]
    congr 2
    rw [nsmul_eq_mul, hk]
    ring
  have hϖk : ϖ ^ m.natAbs ≠ 0 := pow_ne_zero _ hϖ0
  have hu1 : Valued.v ((ϖ ^ m.natAbs)⁻¹ * d) = 1 := by
    rw [map_mul, map_inv₀, hvk, inv_mul_cancel₀ hv]
  refine ⟨m.natAbs, (ϖ ^ m.natAbs)⁻¹ * d, ?_, ?_, ?_, ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu1]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu1, inv_one]
  · exact mul_ne_zero (inv_ne_zero hϖk) hd0
  · rw [← mul_assoc, mul_inv_cancel₀ hϖk, one_mul]
  · unfold absV
    rw [dif_neg hv]
    unfold qv
    congr 1
    rw [hk]
    simp [m]

end Idx

section Steps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Set (Fin n → E))

def IdxPiW (a : ℕ) : Prop :=
  (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
      ((smulSub ϖ (LW v Λ a)).relIndex (LW v Λ a) : ℝ) = qv v ^ (2 * n * a)

def IdxPiH (a : ℕ) : Prop :=
  UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ((smulSub ϖ (HO σ v a)).relIndex (HO σ v a) : ℝ) = qv v ^ (a ^ 2)

theorem relIndex_dV {W : Type} [AddCommGroup W] [Module (Fv F v) W] (P : AddSubgroup W)
    (hP : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ P, s • x ∈ P) (N : ℕ) (e : ℝ)
    (hN : ∀ ϖ : Fv F v, IsUnif v ϖ → ((smulSub ϖ P).relIndex P : ℝ) = qv v ^ N)
    (he : e = -(N : ℝ)) :
    (P.relIndex (smulSub (dV v)⁻¹ P) : ℝ) = absV v (dV v) ^ e := by
  obtain ⟨ϖ, hϖ⟩ := sdc_unifEx_holds v
  have hd0 := dV_ne_zero v
  obtain ⟨k, u, hu, hu', hu0, hd, habs⟩ := exists_unit_pow v hϖ hd0 (dV_int v)
  have e1 : P.relIndex (smulSub (dV v)⁻¹ P) = (smulSub ϖ P).relIndex P ^ k := by
    rw [← relIndex_smulSub v hd0, smulSub_smulSub, mul_inv_cancel₀ hd0, smulSub_one, hd,
      ← smulSub_smulSub, smulSub_unit v hu hu' hu0 P hP,
      relIndex_pow v (unif_ne_zero v hϖ) (unif_int v hϖ) P hP]
  rw [e1, Nat.cast_pow, hN ϖ hϖ, habs, he]
  have hq := qv_pos v
  rw [← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← pow_mul, ← Real.rpow_natCast]
  congr 1
  push_cast
  ring

theorem idxW_of (a : ℕ) (h : IdxPiW v Λ a) : IdxW v Λ a := by
  intro hL hU
  exact relIndex_dV v (LW v Λ a) (fun s hs x hx => smul_mem_LW v Λ hs hx) (2 * n * a) _
    (fun ϖ hϖ => h hL hU ϖ hϖ) (by push_cast; ring)

theorem idxHO_of (a : ℕ) (h : IdxPiH σ v a) : IdxHO σ v a := by
  intro hU ϖ hϖ
  refine ⟨relIndex_dV v (HO σ v a) (fun s hs x hx => smul_mem_HO σ v hs hx) (a ^ 2) _
    (fun ϖ hϖ => h hU ϖ hϖ) (by push_cast; ring), h hU ϖ hϖ⟩

end Steps

end PI.OmLocU
end
end

section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem sdVolW_of (a : ℕ) (hC : CondV σ J ψ v) (hD : DualW σ J ψ v Λ a) (hI : IdxW v Λ a) :
    SdVolW σ J ψ v Λ a :=
  sdVolW_of_top σ J ψ v Λ a hC (topW_holds v Λ a) hD hI

theorem sdVolH_of (a : ℕ) (hC : CondV σ J ψ v) (hD : DualH σ J ψ v a) (hI : IdxHO σ v a) :
    SdVolH σ J ψ v a :=
  sdVolH_of_top σ J ψ v a hC (topH_holds v σ a) hD hI

theorem sdVolW_of_pi (a : ℕ) (hC : CondV σ J ψ v) (hD : DualW σ J ψ v Λ a) (hI : IdxPiW v Λ a) :
    SdVolW σ J ψ v Λ a :=
  sdVolW_of σ J ψ v Λ a hC hD (idxW_of v Λ a hI)

theorem sdVolH_of_pi (a : ℕ) (hC : CondV σ J ψ v) (hD : DualH σ J ψ v a) (hI : IdxPiH σ v a) :
    SdVolH σ J ψ v a :=
  sdVolH_of σ J ψ v a hC hD (idxHO_of σ v a hI)

end PI.OmLocU
end
end

section
noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

section Int

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem b_fg : (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)).FG := by
  let b := RingOfIntegers.basis E
  have h : Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) =
      Submodule.span (v.adicCompletionIntegers F)
        (Set.range fun i => inclR (F := F) (Fv F v) ((b i : 𝓞 E) : E)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, -, rfl⟩
      have hx : ((x : 𝓞 E) : E) = ∑ i, (b.repr x i) • ((b i : 𝓞 E) : E) := by
        have := congrArg (fun y : 𝓞 E => (y : E)) (b.sum_repr x)
        simpa using this.symm
      simp only
      rw [hx, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_zsmul]
      exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨_, Set.mem_univ _, rfl⟩
  rw [h]
  exact Submodule.fg_span (Set.finite_range _)

def bAlg : Subalgebra (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
  Submodule.toSubalgebra (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)) (b_one_mem (E := E) v)
    (fun _ _ hx hy => b_mul_mem v hx hy)

theorem b_int_of_sc {a : Fv F v} (ha : sc (E := E) v a ∈ OEv (E := E) v) : a ∈ v.adicCompletionIntegers F := by
  have hfg : (Subalgebra.toSubmodule (bAlg (E := E) v)).FG := b_fg v
  have hi : IsIntegral (v.adicCompletionIntegers F) (sc (E := E) v a) :=
    IsIntegral.of_mem_of_fg (bAlg (E := E) v) hfg _ ha
  let f : Fv F v →ₐ[v.adicCompletionIntegers F] Fv F v ⊗[F] E :=
    (Algebra.ofId (Fv F v) (Fv F v ⊗[F] E)).restrictScalars (v.adicCompletionIntegers F)
  have hfa : f a = sc (E := E) v a := by rw [b_sc_eq]; rfl
  rw [← hfa] at hi
  have hi' := (isIntegral_algHom_iff f (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective).1 hi
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi'
  rw [← hy]
  exact y.2

theorem b_sigR_mem (σ : E →ₐ[F] E) {z : Fv F v ⊗[F] E} (hz : z ∈ OEv (E := E) v) :
    sigR (Fv F v) σ z ∈ OEv (E := E) v := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, -, rfl⟩ := hx
    have hb : IsIntegral ℤ (σ (b : E)) := by
      simpa using (b.isIntegral_coe).map (σ.toRingHom.toIntAlgHom)
    have e : sigR (Fv F v) σ (inclR (F := F) (Fv F v) (b : E)) =
        inclR (F := F) (Fv F v) ((⟨σ (b : E), hb⟩ : 𝓞 E) : E) := by
      simp [sigR, inclR]
    rw [e]
    exact b_inclR_mem (F := F) (E := E) v ⟨σ (b : E), hb⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    have h1 : r • x = algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) * x := by
      rw [← Algebra.smul_def]; rfl
    have h2 : algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) * sigR (Fv F v) σ x =
        r • sigR (Fv F v) σ x := by
      rw [← Algebra.smul_def]; rfl
    have h3 : sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v)) =
        algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) := by
      simp [sigR, Algebra.TensorProduct.algebraMap_apply]
    rw [h1, map_mul, h3, h2]
    exact Submodule.smul_mem _ r hx

theorem b_tr_sc (s : Fv F v) (w : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (sc (E := E) v s * w) =
      s * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w := by
  rw [b_sc_eq, ← Algebra.smul_def, map_smul, smul_eq_mul]

end Int

section DualW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem b_hR_smul_right (x y : Fin n → Fv F v ⊗[F] E) (c : Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • y) = c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem b_hR_smul_left (c : Fv F v ⊗[F] E) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (c • x) y = sigR (Fv F v) σ c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem b_hR_zero_left (y : Fin n → Fv F v ⊗[F] E) : hR (Fv F v) σ J 0 y = 0 := by
  simp [hR, Formalism.UG.hform]

theorem b_smulF (s : Fv F v) (y : Fin n → Fv F v ⊗[F] E) : s • y = sc (E := E) v s • y := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Algebra.smul_def]
  rfl

theorem b_BR_smul_right {a : ℕ} (s : Fv F v) (X Y : TupV (E := E) v n a) :
    BR (Fv F v) σ J X (s • Y) = s * BR (Fv F v) σ J X Y := by
  simp only [BR, Pi.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [b_smulF v s (Y i), b_hR_smul_right, b_tr_sc]

theorem b_BR_single {a : ℕ} (i : Fin a) (u : Fin n → Fv F v ⊗[F] E) (Y : TupV (E := E) v n a) :
    BR (Fv F v) σ J (Pi.single i u) Y =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (hR (Fv F v) σ J u (Y i)) := by
  classical
  rw [BR, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, b_hR_zero_left, map_zero]
  · intro h; exact absurd (Finset.mem_univ i) h
theorem dualW_of_perf (a : ℕ) (hP : TrPerf σ J ψ v) : DualW σ J ψ v Λ a := by
  classical
  rintro hS ⟨L, hLat, rfl⟩ hSD hU
  have hd0 := dV_ne_zero v
  have hinv : ∀ y, σ (σ y) = y := b_sig_sig σ hS.1
  ext Y
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_smulSub]
  constructor
  · intro h
    refine ⟨dV v • Y, fun i => ?_, by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]⟩
    refine (hSD _).2 fun x hx => hP hS hU _ fun c hc => ?_
    have hcx : Pi.single i (sigR (Fv F v) σ c • x) ∈ LamT v (L : Set (Fin n → E)) a := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Pi.single_eq_same]
        exact b_lat_smul v L (b_sigR_mem v σ hc) hx
      · rw [Pi.single_eq_of_ne hj]
        exact Submodule.zero_mem _
    have h1 := h _ hcx
    rw [b_BR_single, b_hR_smul_left, sigR_sigR v σ hinv] at h1
    rw [Pi.smul_apply, b_smulF v, b_hR_smul_right, mul_left_comm, b_tr_sc]
    exact h1
  · rintro ⟨X', hX', rfl⟩ X hX
    rw [b_BR_smul_right, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
    exact sum_mem fun i _ => b_trace_mem v ((hSD _).1 (hX' i) _ (hX i))

end DualW

end PI.OmLocU.SdB
end
end

section
noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

section DualH

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem b_tr_sig (hcm : IsCMExt F E σ) (w : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (sigR (Fv F v) σ w) = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w := by
  have hinv := b_sig_sig σ hcm
  have hnt := b_sig_nt σ hcm
  have hfin : Module.finrank F E = 2 := hcm.2.2.1
  apply (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective
  rw [trace_v v σ hinv hnt hfin, trace_v v σ hinv hnt hfin, sigR_sigR v σ hinv, add_comm]

def hm {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (i j : Fin a) (c : Fv F v ⊗[F] E) : HermR (Fv F v) σ a :=
  ⟨Matrix.single i j c + Matrix.single j i (sigR (Fv F v) σ c), fun p q => by
    simp only [Matrix.add_apply, Matrix.single_apply]
    rw [map_add, apply_ite (sigR (Fv F v) σ), apply_ite (sigR (Fv F v) σ), map_zero, sigR_sigR v σ hinv, add_comm]
    congr 1 <;> exact if_congr and_comm rfl rfl⟩

theorem coe_hm {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (i j : Fin a) (c : Fv F v ⊗[F] E) :
    (hm σ v hinv i j c : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) =
      Matrix.single i j c + Matrix.single j i (sigR (Fv F v) σ c) := rfl

theorem hm_mem {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (i j : Fin a) {c : Fv F v ⊗[F] E}
    (hc : c ∈ OEv (E := E) v) : hm σ v hinv i j c ∈ HO σ v a := by
  intro p q
  rw [coe_hm, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
  refine Submodule.add_mem _ ?_ ?_
  · split_ifs
    · exact hc
    · exact Submodule.zero_mem _
  · split_ifs
    · exact b_sigR_mem v σ hc
    · exact Submodule.zero_mem _

theorem sum_eq_trace {a : ℕ} (M N : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :
    ∑ p, ∑ q, M p q * N q p = (M * N).trace := by
  rfl

theorem half_two : algebraMap F (Fv F v) (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul, one_div, inv_mul_cancel₀ two_ne_zero, map_one]

theorem half_mul (t : Fv F v) : algebraMap F (Fv F v) (1 / 2) * (t + t) = t := by
  rw [← two_mul, ← mul_assoc, half_two, one_mul]

theorem pair_hm (hcm : IsCMExt F E σ) {a : ℕ} (i j : Fin a) (c : Fv F v ⊗[F] E) (T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a (hm σ v (b_sig_sig σ hcm) i j c) T =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c * (T : Matrix (Fin a) (Fin a) _) j i) := by
  unfold pairHerm
  rw [sum_eq_trace, coe_hm, add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul,
    smul_eq_mul, smul_eq_mul, ← T.2 i j, ← map_mul (sigR (Fv F v) σ), map_add, b_tr_sig σ v hcm, half_mul]

theorem pairHerm_smul_right' {a : ℕ} (s : Fv F v) (S T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a S (s • T) = s * pairHerm (Fv F v) σ a S T := by
  simp only [pairHerm, coe_hermSMul, Matrix.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul,
    smul_eq_mul]
  ring

theorem pair_int (hcm : IsCMExt F E σ) {a : ℕ} {S T : HermR (Fv F v) σ a} (hS : S ∈ HO σ v a) (hT : T ∈ HO σ v a) :
    pairHerm (Fv F v) σ a S T ∈ v.adicCompletionIntegers F := by
  have hinv := b_sig_sig σ hcm
  have hnt := b_sig_nt σ hcm
  have hfin : Module.finrank F E = 2 := hcm.2.2.1
  set u := ∑ p, ∑ q, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) p q * (T : Matrix (Fin a) (Fin a) _) q p
    with hudef
  have hu : u ∈ OEv (E := E) v :=
    sum_mem fun p _ => sum_mem fun q _ => b_mul_mem v (hS p q) (hT q p)
  have hfix : sigR (Fv F v) σ u = u := by
    rw [hudef, map_sum]
    simp only [map_sum, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [← S.2 p q, ← T.2 q p]
  have hsc : sc (E := E) v (pairHerm (Fv F v) σ a S T) = u := by
    have htr : sc (E := E) v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) u) = u + u := by
      rw [b_sc_eq, trace_v v σ hinv hnt hfin, hfix]
    have h2 : sc (E := E) v (algebraMap F (Fv F v) (1 / 2)) * 2 = 1 := by
      have e2 : (2 : Fv F v ⊗[F] E) = sc (E := E) v 2 := by rw [b_sc_eq, map_ofNat]
      rw [e2, b_sc_eq, b_sc_eq, ← map_mul, half_two, map_one]
    have hm2 : ∀ x y : Fv F v, sc (E := E) v (x * y) = sc (E := E) v x * sc (E := E) v y := fun x y => by
      simp only [b_sc_eq, map_mul]
    unfold pairHerm
    rw [← hudef, hm2, htr, ← two_mul, ← mul_assoc, h2, one_mul]
  exact b_int_of_sc v (hsc ▸ hu)

theorem dualH_of_perf (a : ℕ) (hP : TrPerf σ J ψ v) : DualH σ J ψ v a := by
  intro hS hU
  have hcm := hS.1
  have hd0 := dV_ne_zero v
  ext T
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_smulSub]
  constructor
  · intro h
    refine ⟨dV v • T, fun i j => ?_, by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]⟩
    rw [coe_hermSMul, Matrix.smul_apply, Algebra.smul_def]
    refine hP hS hU _ fun c hc => ?_
    have h1 := h _ (hm_mem σ v (b_sig_sig σ hcm) j i hc)
    rw [pair_hm σ v hcm] at h1
    rw [mul_left_comm, ← b_sc_eq, b_tr_sc]
    exact h1
  · rintro ⟨T', hT', rfl⟩ S hS'
    rw [pairHerm_smul_right', ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
    exact pair_int σ v hcm hS' hT'

end DualH

end PI.OmLocU.SdB
end
end

section
noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem latIdx (b : Fin (2 * n) → Fin n → Fv F v ⊗[F] E) (hb : LinearIndependent (Fv F v) b)
    (hmem : ∀ x, x ∈ latLoc (E := E) v Λ ↔
      ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i)
    (hR : ResIdx v) (ϖ : Fv F v) (hϖ : IsUnif v ϖ) :
    (lattice₂ v Λ ϖ).relIndex (latA v Λ) = (Ideal.absNorm v.asIdeal) ^ (2 * n) := by
  let φ : (Fin (2 * n) → v.adicCompletionIntegers F) →+ latA v Λ :=
    { toFun := fun c => ⟨∑ i, (c i : Fv F v) • b i, (hmem _).2 ⟨c, rfl⟩⟩
      map_zero' := by ext1; simp
      map_add' := fun c d => by
        ext1
        simp [add_smul, Finset.sum_add_distrib] }
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := (hmem x).1 hx
    exact ⟨c, rfl⟩
  have key : ((lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)).comap φ =
      AddSubgroup.pi Set.univ (fun _ => unifO v ϖ) := by
    ext c
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    constructor
    · rintro ⟨z, hz, hze⟩ i _
      obtain ⟨d, rfl⟩ := (hmem z).1 hz
      refine ⟨d i, ?_⟩
      have e : ∑ i, (c i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
        have : (DistribMulAction.toAddMonoidHom (Fin n → Fv F v ⊗[F] E) (sc (E := E) v ϖ))
            (∑ i, (d i : Fv F v) • b i) = ∑ i, (ϖ * d i) • b i := by
          show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = _
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => sc_smul_smul v ϖ _ _
        rw [← this, hze]
        rfl
      have h0 := Fintype.linearIndependent_iff.1 hb (fun i => (c i : Fv F v) - ϖ * d i)
        (by simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self])
      exact sub_eq_zero.1 (h0 i)
    · intro h
      choose d hd using fun i => h i (Set.mem_univ i)
      refine ⟨∑ i, (d i : Fv F v) • b i, (hmem _).2 ⟨d, rfl⟩, ?_⟩
      show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = ∑ i, (c i : Fv F v) • b i
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sc_smul_smul, hd i]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφs, key, AddSubgroup.index_pi]
  simp only [hR ϖ hϖ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem lamIdx (a : ℕ) (b : Fin (2 * n) → Fin n → Fv F v ⊗[F] E) (hb : LinearIndependent (Fv F v) b)
    (hmem : ∀ x, x ∈ latLoc (E := E) v Λ ↔
      ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i)
    (hR : ResIdx v) (ϖ : Fv F v) (hϖ : IsUnif v ϖ) :
    (lamP v Λ a ϖ).relIndex (lamA v Λ a) = (Ideal.absNorm v.asIdeal) ^ (2 * n * a) := by
  have hV := latIdx v Λ b hb hmem hR ϖ hϖ
  rw [AddSubgroup.relIndex, ← redT_ker, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.2 (redT_surj v Λ a ϖ), AddSubgroup.card_top, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a),
    Fintype.card_fin]
  have hq : Nat.card (latA v Λ ⧸ (lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)) =
      (Ideal.absNorm v.asIdeal) ^ (2 * n) := by
    rw [← hV, AddSubgroup.relIndex, AddSubgroup.index]
  rw [hq, ← pow_mul]

theorem basis_of (hCM : IsCMExt F E σ) (L : Submodule (𝓞 E) (Fin n → E)) (hLat : Submodule.IsLattice E L) :
    ∃ b : Fin (2 * n) → (Fin n → Fv F v ⊗[F] E), LinearIndependent (Fv F v) b ∧
      ∀ x, x ∈ latLoc (E := E) v (L : Set (Fin n → E)) ↔
        ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  obtain ⟨m, b, hli, hmem, hsp⟩ := exists_basO v L hLat
  have hm : m = 2 * n := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_pi_fintype]
    simp only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  subst hm
  exact ⟨b, hli, hmem⟩

theorem smul_tup {a : ℕ} (ϖ : Fv F v) (p : TupV (E := E) v n a) : ϖ • p = sc (E := E) v ϖ • p := by
  funext i j
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Algebra.smul_def]
  rfl

theorem idxPiW_std (a : ℕ) (hS : StdHyp σ J ψ) : IdxPiW v Λ a := by
  rintro ⟨L, hLat, rfl⟩ _ ϖ hϖ
  obtain ⟨b, hb, hmem⟩ := basis_of σ v hS.1 L hLat
  have e : smulSub ϖ (LW v (L : Set (Fin n → E)) a) = lamP v (L : Set (Fin n → E)) a ϖ := by
    ext X
    rw [mem_smulSub, lamP, AddSubgroup.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, by rw [DistribMulAction.toAddMonoidHom_apply, smul_tup]⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, by rw [DistribMulAction.toAddMonoidHom_apply, smul_tup]⟩
  have e2 : LW v (L : Set (Fin n → E)) a = lamA v (L : Set (Fin n → E)) a := AddSubgroup.ext fun _ => Iff.rfl
  rw [e, e2, lamIdx v _ a b hb hmem (resIdx_holds v) ϖ hϖ, qv]
  push_cast
  ring

end PI.OmLocU.SdB
end
end

section
noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem genIdx {W : Type} [AddCommGroup W] [Module (Fv F v) W] {ι : Type} [Fintype ι] (M : AddSubgroup W)
    (b : ι → W) (hb : LinearIndependent (Fv F v) b)
    (hmem : ∀ x, x ∈ M ↔ ∃ c : ι → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i)
    (ϖ : Fv F v) (hϖ : IsUnif v ϖ) :
    (smulSub ϖ M).relIndex M = (Ideal.absNorm v.asIdeal) ^ (Fintype.card ι) := by
  classical
  let φ : (ι → v.adicCompletionIntegers F) →+ M :=
    { toFun := fun c => ⟨∑ i, (c i : Fv F v) • b i, (hmem _).2 ⟨c, rfl⟩⟩
      map_zero' := by ext1; simp
      map_add' := fun c d => by
        ext1
        simp [add_smul, Finset.sum_add_distrib] }
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := (hmem x).1 hx
    exact ⟨c, rfl⟩
  have hsm : ∀ d : ι → v.adicCompletionIntegers F,
      ϖ • ∑ i, (d i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
    intro d
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
  have key : ((smulSub ϖ M).addSubgroupOf M).comap φ =
      AddSubgroup.pi Set.univ (fun _ => unifO v ϖ) := by
    ext c
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    constructor
    · intro hc i _
      obtain ⟨z, hz, hze⟩ := (mem_smulSub ϖ M _).1 hc
      obtain ⟨d, rfl⟩ := (hmem z).1 hz
      refine ⟨d i, ?_⟩
      have e : ∑ i, (c i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
        rw [← hsm, hze]
        rfl
      have h0 := Fintype.linearIndependent_iff.1 hb (fun i => (c i : Fv F v) - ϖ * d i)
        (by simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self])
      exact sub_eq_zero.1 (h0 i)
    · intro h
      choose d hd using fun i => h i (Set.mem_univ i)
      refine (mem_smulSub ϖ M _).2 ⟨∑ i, (d i : Fv F v) • b i, (hmem _).2 ⟨d, rfl⟩, ?_⟩
      rw [hsm]
      show ∑ i, (ϖ * d i) • b i = ∑ i, (c i : Fv F v) • b i
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hd i]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφs, key, AddSubgroup.index_pi]
  simp only [resIdx_holds v ϖ hϖ, Finset.prod_const, Finset.card_univ]

theorem oEv_basis : ∃ β : Fin (Module.finrank F E) → Fv F v ⊗[F] E, LinearIndependent (Fv F v) β ∧
    ∀ x, x ∈ OEv (E := E) v ↔ ∃ c : Fin (Module.finrank F E) → v.adicCompletionIntegers F,
      x = ∑ i, (c i : Fv F v) • β i := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set M := Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) with hM
  have : Module.Finite (v.adicCompletionIntegers F) M := Module.Finite.iff_fg.2 (b_fg v)
  have : Module.IsTorsionFree (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
      have h' : (r : Fv F v) • x = 0 := h
      rcases smul_eq_zero.1 h' with h0 | h0
      · exact Or.inl (Subtype.ext h0)
      · exact Or.inr h0
  have : Module.Free (v.adicCompletionIntegers F) M := Module.free_of_finite_type_torsion_free'
  let bM := Module.finBasis (v.adicCompletionIntegers F) M
  let b0 : Fin (Module.finrank (v.adicCompletionIntegers F) M) → Fv F v ⊗[F] E := fun i => (bM i : _)
  have hli0 : LinearIndependent (v.adicCompletionIntegers F) b0 :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent (Fv F v) b0 :=
    (LinearIndependent.iff_fractionRing (v.adicCompletionIntegers F) (Fv F v)).1 hli0
  have hmem : ∀ x, x ∈ M ↔ ∃ c : Fin (Module.finrank (v.adicCompletionIntegers F) M) → v.adicCompletionIntegers F,
      x = ∑ i, (c i : Fv F v) • b0 i := by
    intro x
    constructor
    · intro hx
      refine ⟨fun i => bM.repr ⟨x, hx⟩ i, ?_⟩
      have h := congrArg Subtype.val (bM.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at h
      exact h.symm.trans (Finset.sum_congr rfl fun i _ => rfl)
    · rintro ⟨c, rfl⟩
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem M (c i) (bM i).2
  have hsp : ⊤ ≤ Submodule.span (Fv F v) (Set.range b0) := by
    have hM0 : ∀ x ∈ M, x ∈ Submodule.span (Fv F v) (Set.range b0) := by
      intro x hx
      obtain ⟨c, rfl⟩ := (hmem x).1 hx
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    intro x _
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul c e =>
      have hal : IsAlgebraic ℤ e := IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ e)
      obtain ⟨m, hm0, hI⟩ := hal.exists_integral_multiple
      have hmF : (m : Fv F v) ≠ 0 := by
        rw [← map_intCast (algebraMap F (Fv F v))]
        exact (map_ne_zero _).2 (Int.cast_ne_zero.2 hm0)
      have e2 : inclR (F := F) (Fv F v) (m • e) = (m : Fv F v) • inclR (F := F) (Fv F v) e := by
        rw [map_zsmul, Int.cast_smul_eq_zsmul]
      have e3 : c ⊗ₜ[F] e = c • inclR (F := F) (Fv F v) e := by
        simp [inclR, TensorProduct.smul_tmul']
      have e1 : c ⊗ₜ[F] e = (c * (m : Fv F v)⁻¹) • inclR (F := F) (Fv F v) ((⟨m • e, hI⟩ : 𝓞 E) : E) := by
        show _ = (c * (m : Fv F v)⁻¹) • inclR (F := F) (Fv F v) (m • e)
        rw [e2, smul_smul, mul_assoc, inv_mul_cancel₀ hmF, mul_one, e3]
      rw [e1]
      exact Submodule.smul_mem _ _ (hM0 _ (b_inclR_mem (F := F) (E := E) v ⟨m • e, hI⟩))
    | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  have hrk : Module.finrank (v.adicCompletionIntegers F) M = Module.finrank F E := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_baseChange]
  refine ⟨fun i => b0 (Fin.cast hrk.symm i), ?_, fun x => ?_⟩
  · exact hli.comp _ (Fin.cast_injective _)
  · rw [show x ∈ OEv (E := E) v ↔ x ∈ M from Iff.rfl, hmem]
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨fun i => c (Fin.cast hrk.symm i), ?_⟩
      exact (Fintype.sum_equiv (finCongr hrk) _ _ (fun i => rfl))
    · rintro ⟨c, rfl⟩
      refine ⟨fun i => c (Fin.cast hrk i), ?_⟩
      exact Fintype.sum_equiv (finCongr hrk.symm) _ _ (fun i => by simp)

end PI.OmLocU.SdB
end
end

section
noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def hd {a : ℕ} (i : Fin a) : HermR (Fv F v) σ a :=
  ⟨Matrix.single i i 1, fun p q => by
    rw [Matrix.single_apply, Matrix.single_apply, apply_ite (sigR (Fv F v) σ), map_one, map_zero]
    exact if_congr and_comm rfl rfl⟩

theorem hm_apply_ne {a : ℕ} (hinv : ∀ y, σ (σ y) = y) {k l i j : Fin a} (c : Fv F v ⊗[F] E)
    (h1 : ¬(k = i ∧ l = j)) (h2 : ¬(l = i ∧ k = j)) :
    (hm σ v hinv k l c : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0 := by
  show (Matrix.single k l c + Matrix.single l k (sigR (Fv F v) σ c)) i j = 0
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_neg h1, if_neg h2, add_zero]

theorem hd_apply_ne {a : ℕ} {k i j : Fin a} (h : ¬(k = i ∧ k = j)) :
    (hd σ v k : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0 := by
  show Matrix.single k k (1 : Fv F v ⊗[F] E) i j = 0
  rw [Matrix.single_apply, if_neg h]

def hb {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (p : Fin a × Fin a) : HermR (Fv F v) σ a :=
  if p.1 < p.2 then hm σ v hinv p.1 p.2 (β 0) else if p.2 < p.1 then hm σ v hinv p.2 p.1 (β 1) else hd σ v p.1

theorem hb_zero {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {p : Fin a × Fin a} {i j : Fin a}
    (hp1 : p ≠ (i, j)) (hp2 : p ≠ (j, i)) : (hb σ v hinv β p : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0 := by
  obtain ⟨k, l⟩ := p
  unfold hb
  dsimp only
  split_ifs with hkl hlk
  · exact hm_apply_ne σ v hinv _ (fun e => hp1 (Prod.ext e.1 e.2)) (fun e => hp2 (Prod.ext e.2 e.1))
  · exact hm_apply_ne σ v hinv _ (fun e => hp2 (Prod.ext e.2 e.1)) (fun e => hp1 (Prod.ext e.1 e.2))
  · have hkl' : k = l := le_antisymm (not_lt.1 hlk) (not_lt.1 hkl)
    subst hkl'
    exact hd_apply_ne σ v (fun e => hp1 (Prod.ext e.1 e.2))

theorem hermitian_basis_above_first {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {i j : Fin a} (h : i < j) :
    (hb σ v hinv β (i, j) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = β 0 := by
  unfold hb
  rw [if_pos h]
  show (Matrix.single i j (β 0) + Matrix.single j i (sigR (Fv F v) σ (β 0))) i j = β 0
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_pos ⟨rfl, rfl⟩,
    if_neg (fun e => h.ne e.2), add_zero]

theorem hermitian_basis_above_second {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {i j : Fin a} (h : i < j) :
    (hb σ v hinv β (j, i) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = β 1 := by
  unfold hb
  rw [if_neg (not_lt.2 h.le), if_pos h]
  show (Matrix.single i j (β 1) + Matrix.single j i (sigR (Fv F v) σ (β 1))) i j = β 1
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_pos ⟨rfl, rfl⟩,
    if_neg (fun e => h.ne e.2), add_zero]

theorem hermitian_basis_below_first {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {i j : Fin a} (h : j < i) :
    (hb σ v hinv β (i, j) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = sigR (Fv F v) σ (β 1) := by
  unfold hb
  rw [if_neg (not_lt.2 h.le), if_pos h]
  show (Matrix.single j i (β 1) + Matrix.single i j (sigR (Fv F v) σ (β 1))) i j = sigR (Fv F v) σ (β 1)
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_neg (fun e => h.ne e.1),
    if_pos ⟨rfl, rfl⟩, zero_add]

theorem hermitian_basis_below_second {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {i j : Fin a} (h : j < i) :
    (hb σ v hinv β (j, i) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = sigR (Fv F v) σ (β 0) := by
  unfold hb
  rw [if_pos h]
  show (Matrix.single j i (β 0) + Matrix.single i j (sigR (Fv F v) σ (β 0))) i j = sigR (Fv F v) σ (β 0)
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_neg (fun e => h.ne e.1),
    if_pos ⟨rfl, rfl⟩, zero_add]

theorem hb_eq {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (i : Fin a) :
    (hb σ v hinv β (i, i) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i i = 1 := by
  unfold hb
  rw [if_neg (lt_irrefl i), if_neg (lt_irrefl i)]
  show Matrix.single i i (1 : Fv F v ⊗[F] E) i i = 1
  rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩]

theorem coe_sum_hb {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (c : Fin a × Fin a → Fv F v)
    (i j : Fin a) :
    ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j =
      ∑ p, c p • (hb σ v hinv β p : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j := by
  rw [AddSubmonoidClass.coe_finset_sum, Matrix.sum_apply]
  rfl

theorem sum_lt {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (c : Fin a × Fin a → Fv F v)
    {i j : Fin a} (h : i < j) :
    ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j =
      c (i, j) • β 0 + c (j, i) • β 1 := by
  have hne : ((i, j) : Fin a × Fin a) ≠ (j, i) := fun e => h.ne (Prod.ext_iff.1 e).1
  rw [coe_sum_hb, Fintype.sum_eq_add (i, j) (j, i) hne
    (fun p hp => by rw [hb_zero σ v hinv β hp.1 hp.2, smul_zero]), hermitian_basis_above_first σ v hinv β h, hermitian_basis_above_second σ v hinv β h]

theorem sum_gt {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (c : Fin a × Fin a → Fv F v)
    {i j : Fin a} (h : j < i) :
    ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j =
      c (i, j) • sigR (Fv F v) σ (β 1) + c (j, i) • sigR (Fv F v) σ (β 0) := by
  have hne : ((i, j) : Fin a × Fin a) ≠ (j, i) := fun e => h.ne' (Prod.ext_iff.1 e).1
  rw [coe_sum_hb, Fintype.sum_eq_add (i, j) (j, i) hne
    (fun p hp => by rw [hb_zero σ v hinv β hp.1 hp.2, smul_zero]), hermitian_basis_below_first σ v hinv β h, hermitian_basis_below_second σ v hinv β h]

theorem sum_diag {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (c : Fin a × Fin a → Fv F v)
    (i : Fin a) :
    ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i i =
      sc (E := E) v (c (i, i)) := by
  rw [coe_sum_hb, Fintype.sum_eq_single (i, i) (fun p hp => by rw [hb_zero σ v hinv β hp hp, smul_zero]),
    hb_eq, sc, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end PI.OmLocU.SdB
end
end
