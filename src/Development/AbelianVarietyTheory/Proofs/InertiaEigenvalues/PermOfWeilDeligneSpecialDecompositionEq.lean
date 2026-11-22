module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemOfLpCharLpSpEqSumList
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DirectSumCancelRight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilDeligne.SpUnique

open SpSummand

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

section Rep

variable {V U U' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] [AddCommGroup U'] [Module ℂ U']
  [FiniteDimensional ℂ U'] {ρ : Representation ℂ (Weil h) V} {k : ℕ} {c : Weil h → ℂ}

theorem hasCopy_sum_left {b : WDRep h U} (b' : WDRep h U') (H : HasCopy ρ k c b) :
    HasCopy ρ k c (b.sum b') := by
  obtain ⟨f, g, hf, hc, rfl⟩ := H
  refine ⟨LinearMap.inl ℂ U U' ∘ₗ ((b.N ^ k) ∘ₗ g), LinearMap.inl ℂ U U' ∘ₗ g, ?_, fun σ v => ?_, ?_⟩
  · intro h0
    apply hf
    refine LinearMap.ext fun v => ?_
    have := congrArg Prod.fst (LinearMap.congr_fun h0 v)
    simpa using this
  · have := hc σ v
    refine Prod.ext ?_ ?_
    · simpa using this
    · simp
  · refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, sum_N_pow]
    refine Prod.ext ?_ ?_ <;> simp

theorem hasCopy_sum_right (b : WDRep h U) {b' : WDRep h U'} (H : HasCopy ρ k c b') :
    HasCopy ρ k c (b.sum b') := by
  obtain ⟨f, g, hf, hc, rfl⟩ := H
  refine ⟨LinearMap.inr ℂ U U' ∘ₗ ((b'.N ^ k) ∘ₗ g), LinearMap.inr ℂ U U' ∘ₗ g, ?_, fun σ v => ?_, ?_⟩
  · intro h0
    apply hf
    refine LinearMap.ext fun v => ?_
    have := congrArg Prod.snd (LinearMap.congr_fun h0 v)
    simpa using this
  · have := hc σ v
    refine Prod.ext ?_ ?_
    · simp
    · simpa using this
  · refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, sum_N_pow]
    refine Prod.ext ?_ ?_ <;> simp

theorem powZero_sum {b : WDRep h U} {b' : WDRep h U'} (H : PowZero k b) (H' : PowZero k b') :
    PowZero k (b.sum b') := by
  unfold PowZero at *
  rw [sum_N_pow, H, H', LinearMap.prodMap_zero]

theorem powZero_of_le (a : WDRep h U) (ha : a.ρ.IsIrreducible) {m : ℕ} (hmk : m ≤ k) :
    PowZero k (a.tensor (WDRep.sp h (m + 1))) := by
  unfold PowZero
  rw [tensor_sp_N_pow a (N_eq_zero_of_irr a ha), shiftEnd_pow_eq_zero (by omega),
    LinearMap.lTensor_zero]

theorem hasCopyW_lpSum_left (x y : WD h) (H : HasCopyW ρ k c x) : HasCopyW ρ k c (x.lpSum y) := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP n' b =>
      rw [WD.lpSum_mk, hasCopyW_mk]
      rw [hasCopyW_mk] at H
      exact hasCopy_sum_left b H

theorem hasCopyW_lpSum_right (x y : WD h) (H : HasCopyW ρ k c y) : HasCopyW ρ k c (x.lpSum y) := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP n' b =>
      rw [WD.lpSum_mk, hasCopyW_mk]
      rw [hasCopyW_mk] at H
      exact hasCopy_sum_right a H

theorem powZeroW_lpSum_of (x y : WD h) (H : PowZeroW k x) (H' : PowZeroW k y) :
    PowZeroW k (x.lpSum y) := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP n' b =>
      rw [WD.lpSum_mk, powZeroW_mk]
      rw [powZeroW_mk] at H H'
      exact powZero_sum H H'

theorem powZeroW_lpZero : PowZeroW k (WD.lpZero (h := h)) := by
  rw [WD.lpZero, powZeroW_mk]
  show (WDRep.diag h _).N ^ (k + 1) = 0
  rw [WDRep.diag_N, zero_pow (Nat.succ_ne_zero k)]

theorem hasCopyW_sumList {α : Type} (F : α → WD h) (l : List α) (p : α) (hp : p ∈ l)
    (H : HasCopyW ρ k c (F p)) : HasCopyW ρ k c (sumList (l.map F)) := by
  induction l with
  | nil => cases hp
  | cons q l ih =>
    change HasCopyW ρ k c ((F q).lpSum (sumList (l.map F)))
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hasCopyW_lpSum_left _ _ H
    · exact hasCopyW_lpSum_right _ _ (ih hp)

theorem powZeroW_sumList {α : Type} (F : α → WD h) (l : List α) (H : ∀ p ∈ l, PowZeroW k (F p)) :
    PowZeroW k (sumList (l.map F)) := by
  induction l with
  | nil => exact powZeroW_lpZero
  | cons q l ih =>
    change PowZeroW k ((F q).lpSum (sumList (l.map F)))
    exact powZeroW_lpSum_of _ _ (H q List.mem_cons_self) (ih fun p hp => H p (List.mem_cons_of_mem _ hp))

end Rep

theorem sumList_perm {l l' : List (WD h)} (hp : l.Perm l') : sumList l = sumList l' := by
  induction hp with
  | nil => rfl
  | cons x _ ih =>
    show WD.lpSum x (sumList _) = WD.lpSum x (sumList _)
    rw [ih]
  | swap x y l =>
    show WD.lpSum y (WD.lpSum x (sumList l)) = WD.lpSum x (WD.lpSum y (sumList l))
    rw [← WD.lpSum_assoc, ← WD.lpSum_assoc, WD.lpSum_comm x y]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

end GlobalTheory.WeilDeligne.SpUnique
