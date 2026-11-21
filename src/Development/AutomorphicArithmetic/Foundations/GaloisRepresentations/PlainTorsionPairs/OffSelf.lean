import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.RedAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.PlaceFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DenseOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.NiceAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.FxTwflag
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.FixLe
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.IrrArithPointsAutomorphicAway

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J UpperTheory.V.Th
open private det_comap tw_flag unramified_at_base_place irr_of_mat pt_flag w_ne from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.NiceAt

namespace UpperTheory.Gal.projectedFormsSystemPart


section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
  {k : GalLink η Ψ σ g₁ B M L Φ} {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O}
  {ka : G L Ω →* (Qbar l)ˣ}

@[reducible] def setS (R : CReal k c₁ f 3 ka) (S : Fr.Space c₁.O (Φ.ext f) 3) : CReal k c₁ f 3 ka := { R with S := S }

def EndPt (R : CReal k c₁ f 3 ka) (ι : Qbar l ≃+* ℂ) (φ : R.B₀.B →ₐ[c₁.O] R.S.B) : Prop :=
  ∀ (h : R.s.Wt 3) (ξ : R.S.A →ₐ[c₁.O] Qbar l), VPt R.S ξ → R.S.u.TI (RingHom.ker ξ) →
    ∀ x : R.B₀.Pt, x = (ξ.comp R.S.inc).comp φ → x.Arith h → IsAutCsd ι ((R.K.tw (ptRep R.S ξ)).toHomUnits.comp R.V.pr)





end

def Red2 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f 3 ka), W.Large L c₁ → IsKa σ M ι 3 ka →
    ∀ φ, R.T.IsPhi φ → Function.Surjective φ → ∀ J, AllGood R.S (J.map φ) → R.T.DimT J → R.B₀.Dense J →
      EndPt R ι φ → ∀ ξ : R.S.A →ₐ[c₁.O] Qbar l, IntPt R.S ξ → R.S.u.TI (RingHom.ker ξ) →
      ∀ a ∈ J, ∃ s : R.S.A, ξ s ≠ 0 ∧ s * R.S.inc (φ a) = 0

end UpperTheory.Gal.projectedFormsSystemPart
