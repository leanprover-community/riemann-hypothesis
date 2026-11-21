import Development.WeilBound.CoreStatements.SatakeConjugation.CsdIff
import Formalism.LocalToGlobal.PlaceMapInjectivity.MapPlInjective

section
noncomputable section

open NumberField IsDedekindDomain

namespace PositivityTheory.NCmp

open GlobalTheory.CuspRep

def SatFlipLoc : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (w : HeightOneSpectrum (𝓞 L))
    (σ : SmIrr (GL (Fin a) (w.adicCompletion L))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
      GlobalTheory.LFun.HasSatGL (conjSrc (cc L) w) (σ.ρ.comp (ParLaws.flip (conjLoc (cc L) w) a)) (B.map (·⁻¹))

end PositivityTheory.NCmp
end
end

section
noncomputable section

open NumberField IsDedekindDomain

namespace PositivityTheory.NCmp

open GlobalTheory.CuspRep

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem mem_conjSrc_iff (v : HeightOneSpectrum (𝓞 L)) (x : 𝓞 L) :
    x ∈ (conjSrc (cc L) v).asIdeal ↔ IsCMField.ringOfIntegersComplexConj L x ∈ v.asIdeal := by
  have h := conjPl_conjSrc (cc L) v (x : L)
  rw [← (conjSrc (cc L) v).valuation_lt_one_iff_mem (K := L), ← v.valuation_lt_one_iff_mem (K := L)]
  have e : (((IsCMField.ringOfIntegersComplexConj L x : 𝓞 L) : L)) = cc L (x : L) := by
    simp [cc, IsCMField.coe_ringOfIntegersComplexConj]
  show (conjSrc (cc L) v).valuation L (x : L) < 1 ↔ v.valuation L ((IsCMField.ringOfIntegersComplexConj L x : 𝓞 L) : L) < 1
  rw [e, h]

end PositivityTheory.NCmp
end
end
