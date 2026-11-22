module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.X0OfStarCondition
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIntegralOpW
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotHasParamOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorSplitPlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CuspFormLimitTwoPlaces

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.RoadW GlobalTheory.CongL Polynomial

namespace GlobalTheory.RoadWGeo

def Lacunary (J : Finset ℤ) : Prop :=
  ∀ A B : Finset ℤ, A ⊆ J → B ⊆ J → Disjoint A B → A.Nonempty → B.Nonempty →
    (B.card : ℤ) * A.sum id ≠ (A.card : ℤ) * B.sum id

def wtJumps {a : ℕ} (lam : DomWeight a) : Finset ℤ :=
  Finset.univ.image fun k : Fin a => ((k : ℕ) : ℤ) - lam.w k

theorem strictMono_jump {a : ℕ} (lam : DomWeight a) : StrictMono fun k : Fin a => ((k : ℕ) : ℤ) - lam.w k := by
  intro i j hij
  have h1 := lam.anti hij.le
  have h2 : (i : ℕ) < j := hij
  simp only
  omega

theorem card_wtJumps {a : ℕ} (lam : DomWeight a) : (wtJumps lam).card = a := by
  rw [wtJumps, Finset.card_image_of_injective _ (strictMono_jump lam).injective]; simp

theorem wtJumps_val {a : ℕ} (lam : DomWeight a) :
    (wtJumps lam).val.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) := by
  rw [wtJumps, Finset.image_val_of_injOn (strictMono_jump lam).injective.injOn, infOfWeight, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun k _ => ?_
  simp only [Function.comp]
  push_cast
  ring

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime]

def ESAt {d : ℕ} (ι : Qbar l ≃+* ℂ) (ρ : G E Ω →* GL (Fin d) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂ) :
    Prop :=
  ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ s ∈ Ine (F := E) A, ρ s = 1) ∧
    ∀ σ : G E Ω, IsFrob A (normV w) σ →
      aeval (ρ σ⁻¹ : Matrix (Fin d) (Fin d) (Qbar l)) (((B.map fun b => X - C b).prod).map ι.symm.toRingHom) = 0

def LacWtAt {a : ℕ} (ι : Qbar l ≃+* ℂ) (v' : HeightOneSpectrum (𝓞 E)) (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∃ τ : E →+* ℂ, OverPl ι τ v' ∧ ∃ lam : DomWeight a, HasWeightAt U τ lam ∧ Lacunary (wtJumps lam)

end GlobalTheory.RoadWGeo

namespace GlobalTheory.Published

open GlobalTheory.RoadWGeo

end GlobalTheory.Published

end
