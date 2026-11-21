import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoldsFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne Polynomial TensorProduct Module
open GlobalTheory.Published.ParamAboveModel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published.CharWDTest

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

omit [NumberField E] [IsAlgClosure E Ω] in

theorem exists_prime_notMem (w : HeightOneSpectrum (𝓞 E)) : ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  by_cases h2 : ((2 : ℕ) : 𝓞 E) ∈ w.asIdeal
  · refine ⟨3, Nat.prime_three, fun h3 => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)⟩
    have := w.asIdeal.sub_mem h3 h2
    norm_num at this
    exact this
  · exact ⟨2, Nat.prime_two, h2⟩

theorem comp_eq {art : Ideles E →* Gab E Ω} (hart : IsGlobalArtin art) {χ : HChar E} {n : (E →+* ℂ) → ℤ}
    (hn : IsAlgPos χ n) {ξ : (w.adicCompletion E)ˣ →* ℂˣ} (hξ : GlobalTheory.NPin.IsComp χ w ξ)
    {a a' : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a) (ha' : IsLocalArtin h a') :
    ξ.comp a = ξ.comp a' := by
  obtain rfl := eq_loc hξ
  obtain ⟨p, hp, hw⟩ := exists_prime_notMem w
  have := Fact.mk hp
  obtain ⟨ι⟩ : Nonempty (Qbar p ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex p
  obtain ⟨r, -, hr⟩ := hart.exists_isLAdicOf ι hn
  ext σ
  have h1 := hr.loc_away (Or.inl hw) _ _ (ha.glob art hart σ)
  have h2 := hr.loc_away (Or.inl hw) _ _ (ha'.glob art hart σ)
  exact ι.symm.injective (h1.symm.trans h2)


variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (ι : Om l ≃+* ℂ)
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw)





omit [IsAlgClosure E Ω] in

theorem abs_ne_inv : (Model.absPow E (1 : ℕ)).loc w ≠ ((Model.absPow E (1 : ℕ)).loc w)⁻¹ := fun e => by
  have hval := (Model.absPow_isAbsPow E (1 : ℕ)).2.1 w
  have h1 : (Model.absPow E (1 : ℕ)).val w = ((Model.absPow E (1 : ℕ)).val w)⁻¹ :=
    DFunLike.congr_fun e (atFin w (unif w))
  have h2 := congrArg (fun u : ℂˣ => (u : ℂ)) h1
  simp only [Units.val_inv_eq_inv_val, hval] at h2
  have hq : 1 < Ideal.absNorm w.asIdeal := by
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using GlobalTheory.WeilDeligne.one_lt_normV w
  simp only [Nat.cast_one, Complex.ofReal_one, Complex.cpow_neg_one, inv_inv] at h2
  have h0 : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h3 := mul_inv_cancel₀ h0
  rw [h2] at h3
  have h4 : Ideal.absNorm w.asIdeal * Ideal.absNorm w.asIdeal = 1 := by exact_mod_cast h3
  nlinarith

end GlobalTheory.Published.CharWDTest

end
