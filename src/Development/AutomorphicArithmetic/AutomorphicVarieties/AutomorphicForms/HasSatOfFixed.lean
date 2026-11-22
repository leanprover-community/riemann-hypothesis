module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HasFixedVector

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG

namespace UpperTheory.V.Af

variable {F : Type} [Field F] [NumberField F]

theorem LocIsotypic.hasFixed {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) (Af F)) V} {w : HeightOneSpectrum (𝓞 F)}
    {σ : SmIrr (GL (Fin n) (w.adicCompletion F))} (h : LocIsotypic ρ w σ)
    {U : Subgroup (GL (Fin n) (w.adicCompletion F))} (hU : IsCompact (U : Set (GL (Fin n) (w.adicCompletion F))))
    (hf : HasFixed (ρ.comp (locGL F n w)) U) : HasFixed σ.ρ U :=
  _root_.UpperTheory.Reformulated.B.HasFixedVector.hasFixed h hU hf

end UpperTheory.V.Af
