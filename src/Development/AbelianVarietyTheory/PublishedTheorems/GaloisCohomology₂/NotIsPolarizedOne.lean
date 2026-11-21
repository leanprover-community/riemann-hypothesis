import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalOfCusp.Model

abbrev Qi : Type := CyclotomicField 4 ℚ

instance cmQi : IsCMField Qi := IsCyclotomicExtension.Rat.isCMField Qi (S := {4}) ⟨4, rfl, by norm_num⟩


variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E]
  {l : ℕ} [Fact l.Prime]




omit [IsCMField E] in

theorem isWDOf_one {w : HeightOneSpectrum (𝓞 E)} (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) (ι : Qbar l ≃+* ℂ) :
    IsWDOf ι (1 : G E Ω →* GL (Fin 1) (Qbar l)) (WD.mk (WDRep.diag h fun _ : Fin 1 => 1)) := by
  obtain ⟨x, hx⟩ := (exists_isWDOf_iff (h := h) (ι := ι) (r := (1 : G E Ω →* GL (Fin 1) (Qbar l))) hl
    (isTameChar_tameL h hl)).2 ⟨0, (isMonodromy_zero_iff (h := h)).2 (.of_trivial fun _ => rfl)⟩
  have e : wdOf h hl ι (1 : G E Ω →* GL (Fin 1) (Qbar l)) = WD.mk (WDRep.diag h fun _ : Fin 1 => 1) :=
    wdOf_eq_mk hl _ rfl fun g => LinearMap.ext fun v => funext fun i => by simp
  rwa [← e, hx.wdOf_eq hl]


omit [IsCMField E] in

theorem pure_cyc {w : HeightOneSpectrum (𝓞 E)} (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) (ι : Qbar l ≃+* ℂ) :
    ((wdOf h hl ι ((Matrix.GeneralLinearGroup.scalar (Fin 1)).comp (cyc E Ω l))).lpTw (((-2 : ℤ) : ℝ) / 2)).tempered := by
  rw [wdOf_cyc, WD.lpTw_add, show (1 : ℝ) + ((-2 : ℤ) : ℝ) / 2 = 0 by norm_num, WD.lpTw_zero]
  simp [WD.tempered_diag_iff]

end GlobalTheory.GalOfCusp.Model
