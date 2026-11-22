module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.FreeFlag

@[expose] public section

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

namespace UpperTheory.V.Th

def RigOver {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {n : ℕ} (r : G L Ω →* GL (Fin n) (Qbar l)) (ka : G L Ω →* (Qbar l)ˣ) : Prop :=
  ∃ (s : W.HidaSetting l L Ω) (V : s.Lev) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)),
    (∀ g, W.mat ρ (V.pr g) = (ka g : Qbar l) • W.mat r g) ∧
    (∀ g g' : G L Ω, W.resP L Ω g' = s.c * W.resP L Ω g * s.c⁻¹ → ka g * ka g' = cycBar L Ω l g ^ (1 - (n : ℤ))) ∧ AdZero V ρ

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}

end

end UpperTheory.V.Th

end
