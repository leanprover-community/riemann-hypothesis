module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigEtaleModuleSheafMonoEpiIffSections

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections : ∀ (R : Type) [CommRing R] {F G : Shv R} (φ : F ⟶ G), (Mono φ ↔ ∀ U, Function.Injective (Sec.map φ (U := U))) ∧ (Mono φ ↔ ∀ U (a : Sec F U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0) ∧ (Epi φ ↔ ∀ U (b : Sec G U), Loc U fun V g => ∃ a : Sec F V, Sec.map φ a = Sec.res g b) ∧ (∀ ψ : F ⟶ G, (∀ U (a : Sec F U), Sec.map φ a = Sec.map ψ a) → φ = ψ) := by
  first | (exact @GlobalTheory.EtC.mono_epi_sections)
