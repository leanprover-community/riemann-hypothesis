module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.GalStepOfHyp

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F

namespace UpperTheory.V.Z.Tf.GOne

def CsdSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  GlobalTheory.ContraPair.DualIsConj π → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk π).HasSat w B ∧
    ∀ u, ConjPl w u → (CG.mk π).HasSat u (B.map (·⁻¹))

end UpperTheory.V.Z.Tf.GOne

end
