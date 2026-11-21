import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.NewtonThorneSym
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SelfTwGal
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SchurTwistHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Ad0IrrMulVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.QuadraticCharpolyCoeffDifference
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.CentChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.UOfSat

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Sd

private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

private theorem charEig_cyc_inv {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) :
    CharEig ι (cycBar F Ω l)⁻¹ w (normV w : ℂ) := by
  intro A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 : cycZ F Ω l s = 1 := Units.ext (PadicInt.ext_of_toZModPow.mp fun n => by
      rw [cycZ_toZModPow_eq hw hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
      simp)
    rw [MonoidHom.inv_apply, cycBar, MonoidHom.comp_apply, h1, map_one, inv_one]
  · have h2 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
      change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
      rw [cycZ_of_isFrob hw hA hσ, map_natCast, map_natCast]
    rw [MonoidHom.inv_apply, map_inv, inv_inv, h2, map_natCast]


