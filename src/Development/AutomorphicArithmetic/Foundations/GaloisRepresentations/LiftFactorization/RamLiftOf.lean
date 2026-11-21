import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ThreeApartOf
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.RamDefs
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp GlobalTheory.GalCut GlobalTheory.RealGal GlobalTheory.UnitaryBC UpperTheory.V.Published UpperTheory.Gal.UnramifiedFromSplittingCriterion UpperTheory.ConvolutionTheory.Sph

namespace UpperTheory.Gal.AbelianGaloisNormality

def FieldOK (l : ℕ) (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  (∃ x : E, ∃ d : ℕ, 0 < d ∧ x ^ 2 = -(d : E)) ∧ Even (Module.finrank ℚ (maximalRealSubfield E)) ∧
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) ∧
    (∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → IsSplitAt w) ∧
    ∃ w₁ w₂ w₃ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₁.asIdeal ∧ ((l : ℕ) : 𝓞 E) ∈ w₂.asIdeal ∧
      ((l : ℕ) : 𝓞 E) ∈ w₃.asIdeal ∧ GlobalTheory.Cong.Apart w₁ w₂ ∧ GlobalTheory.Cong.Apart w₁ w₃ ∧ GlobalTheory.Cong.Apart w₂ w₃

def Spl {E : Type} [Field E] [NumberField E] (Ω : Type) [Field Ω] [Algebra E Ω] (M : Type) [Field M] [Algebra M Ω]
    (T : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ t ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A t → ∀ g ∈ Dec (F := E) A, Fixes M g

def SplTop {E : Type} [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra E M]
    (T : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 E) ∈ T → IsSplitAt w

def Pol (c : Bool) {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (π : CuspSub E a) : Prop :=
  (CG.mk π).IsRegAlg ∧ ∃ χ : HChar (maximalRealSubfield E), GlobalTheory.ContraPair.PolarizedPair π χ ∧ (c = true → χ = quadChar E ^ a)

inductive Layers (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] :
    ∀ (M : Type) [Field M] [NumberField M] [Algebra M Ω] [Algebra E M], Prop
  | refl : Layers Ω E E
  | step (X Y : Type) [Field X] [NumberField X] [Algebra X Ω] [Algebra E X] [Field Y] [NumberField Y] [IsCMField Y] [Algebra Y Ω]
      [Algebra E Y] [Algebra X Y] [IsScalarTower E X Y] [IsScalarTower X Y Ω] :
      Layers Ω E X → IsGalois X Y → (Module.finrank X Y).Prime → Layers Ω E Y

def Disjoint' {E Ω : Type} (M : Type) [Field E] [Field M] [Field Ω] [Algebra E Ω] [Algebra M Ω] (N : Subgroup (G E Ω)) : Prop :=
  ∀ g : G E Ω, ∃ x n : G E Ω, Fixes M x ∧ n ∈ N ∧ g = x * n

def Reach (Ω : Type) [Field Ω] (l : ℕ) (c : Bool) {a : ℕ} :
    ℕ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω], CuspSub E a → Prop
  | 0 => fun E _ _ _ _ π => FieldOK l E ∧ GlobalTheory.GalCut.Good l π
  | k + 1 => fun E _ _ _ _ π => ∀ T : Set (HeightOneSpectrum (𝓞 E)), T.Finite →
      {Q : QCM E Ω | Spl Ω ↥Q.K T ∧ (k = 0 → SplTop ↥Q.K T) ∧ RamOff T Q ∧
        ∃ P : CuspSub ↥Q.K a, IsLiftUnr π P ∧ Pol c P ∧ Reach Ω l c k ↥Q.K P}.Infinite

def BCFam : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ), l.Prime →
    ∀ a : ℕ, 1 ≤ a → ∀ (c : Bool) (π : CuspSub E a), Pol c π → Reach Ω l c 3 E π

def BCGood : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ), l.Prime →
    ∀ a : ℕ, 1 ≤ a → ∀ (c : Bool) (π : CuspSub E a), Pol c π → ∀ S : Set (HeightOneSpectrum (𝓞 E)), S.Finite →
    ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) →
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω)
      (_ : Algebra E M) (_ : IsScalarTower E M Ω), Layers Ω E M ∧ Disjoint' M N ∧ Spl Ω M S ∧ SplTop M S ∧ FieldOK l M ∧
      ∃ P : CuspSub M a, IsLiftUnr π P ∧ Pol c P ∧ GlobalTheory.GalCut.Good l P

abbrev Rel (a : ℕ) : Type 1 :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M],
    CuspSub K a → CuspSub M a → Prop

structure Rel.Tower {a : ℕ} (R : Rel a) : Prop where
  refl : ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (π : CuspSub K a), R K K π π
  layer : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M]
    [IsGalois K M], (Module.finrank K M).Prime → ∀ (π : CuspSub K a) (P : CuspSub M a), IsLiftUnr π P → R K M π P
  trans : ∀ (K M L : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Field L] [NumberField L]
    [IsCMField L] [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L] (π : CuspSub K a) (P : CuspSub M a)
    (U : CuspSub L a), R K M π P → R M L P U → R K L π U

def TowerLift : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (S : Set (HeightOneSpectrum (𝓞 E))), (∀ u ∉ S, ∃ B, (CG.mk π).HasSat u B) →
    ∀ X : Fld E Ω, UnramifiedFromSplittingCriterion.Tower S X →
    ∃ P : CuspSub X.K a, IsLiftUnr π P ∧ (∀ c, Pol c π → Pol c P) ∧ ∀ R : Rel a, R.Tower → R E X.K π P

def BCLocal : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (ι : Type) [Finite ι]
    (v : ι → HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (A : ι → ValuationSubring Ω), Function.Injective v →
    (∀ i, IsPlaceOver (A i) (v i)) → ∀ V : ∀ i, Subgroup (Dec (F := maximalRealSubfield E) (A i)),
    (∀ i, IsOpen (V i : Set (Dec (F := maximalRealSubfield E) (A i)))) →
    (∀ i, commutator (Dec (F := maximalRealSubfield E) (A i)) ≤ V i) →
    ∀ T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), T.Finite → (∀ i, v i ∉ T) →
    ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) →
    ∃ X : Fld E Ω, GlobalTheory.AboveL.SolvDisj X.K N ∧
      (∀ i (g : Dec (F := maximalRealSubfield E) (A i)),
        Fixes (maximalRealSubfield X.K) (g : G (maximalRealSubfield E) Ω) ↔ g ∈ V i) ∧
      (∀ t ∈ T, ∀ B : ValuationSubring Ω, IsPlaceOver B t → ∀ g ∈ Dec (F := maximalRealSubfield E) B,
        Fixes (maximalRealSubfield X.K) g) ∧
      ∃ P : CuspSub X.K a, IsLiftUnr π P ∧ (∀ c, Pol c π → Pol c P) ∧ ∀ R : Rel a, R.Tower → R E X.K π P

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a l : ℕ} {π : CuspSub E a}

end

end UpperTheory.Gal.AbelianGaloisNormality
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp GlobalTheory.GalCut GlobalTheory.RealGal GlobalTheory.UnitaryBC UpperTheory.V.Published UpperTheory.Gal.UnramifiedFromSplittingCriterion UpperTheory.ConvolutionTheory.Sph

namespace UpperTheory.Gal.AbelianGaloisNormality

def LiftRefl : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (a : ℕ) (π : CuspSub K a), IsLiftUnr π π

def WeakTrans : Prop :=
  ∀ (K M L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Field L]
    [NumberField L] [IsTotallyComplex L] [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L] (a : ℕ)
    (π : CuspSub K a) (P : CuspSub M a) (U : CuspSub L a),
    WeakBC (CG.mk π).HasSat (CG.mk P).HasSat → WeakBC (CG.mk P).HasSat (CG.mk U).HasSat → WeakBC (CG.mk π).HasSat (CG.mk U).HasSat

def UnrFactor : Prop :=
  ∀ (K M L : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L] [Algebra K M] [Algebra M L]
    [Algebra K L] [IsScalarTower K M L] (w : HeightOneSpectrum (𝓞 L)), (w.under (𝓞 M)).under (𝓞 K) = w.under (𝓞 K) ∧
    (Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal →
      Algebra.IsUnramifiedAt (𝓞 M) w.asIdeal ∧ Algebra.IsUnramifiedAt (𝓞 K) (w.under (𝓞 M)).asIdeal)

def SplitFactor : Prop :=
  ∀ (K M L : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L] [Algebra K M] [Algebra M L]
    [Algebra K L] [IsScalarTower K M L] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (i : v.adicCompletion K ≃+* w.adicCompletion L), Continuous i →
    (∀ x : K, i (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) →
    ∃ (u : HeightOneSpectrum (𝓞 M)) (j : v.adicCompletion K ≃+* u.adicCompletion M) (k : u.adicCompletion M ≃+* w.adicCompletion L),
      Continuous j ∧ Continuous k ∧ (∀ x : K, j (algebraMap K _ x) = algebraMap M _ (algebraMap K M x)) ∧
      (∀ x : M, k (algebraMap M _ x) = algebraMap L _ (algebraMap M L x)) ∧ ∀ y, i y = k (j y)

def SplitTrans : Prop :=
  ∀ (K M L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Field L]
    [NumberField L] [IsTotallyComplex L] [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L] (a : ℕ)
    (π : CuspSub K a) (P : CuspSub M a) (U : CuspSub L a),
    UpperTheory.CBC.SplitLift (.cx π) (.cx P) → UpperTheory.CBC.SplitLift (.cx P) (.cx U) → UpperTheory.CBC.SplitLift (.cx π) (.cx U)

def LiftTrans : Prop :=
  ∀ (K M L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Field L]
    [NumberField L] [IsTotallyComplex L] [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L] (a : ℕ)
    (π : CuspSub K a) (P : CuspSub M a) (U : CuspSub L a), IsLiftUnr π P → IsLiftUnr P U → IsLiftUnr π U

def PolLift : Prop :=
  ∀ (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (P : CuspSub M a), WeakBC (CG.mk π).HasSat (CG.mk P).HasSat →
    (∀ τ : M →+* ℂ, (CG.mk P).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap E M))) → ∀ c, Pol c π → Pol c P

def FixLift : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω]
    [IsScalarTower K M Ω] (g : G K Ω),
    Fixes M g → ∃ g' : G M Ω, AlgEquiv.restrictScalarsHom K g' = g ∧
      ∀ A : ValuationSubring Ω, (g ∈ Dec (F := K) A ↔ g' ∈ Dec (F := M) A) ∧ (g ∈ Ine (F := K) A ↔ g' ∈ Ine (F := M) A)

def PlaceUp : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω]
    [IsScalarTower K M Ω] (A : ValuationSubring Ω),
    (∀ v : HeightOneSpectrum (𝓞 K), IsPlaceOver A v → ∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v ∧ IsPlaceOver A w) ∧
    ∀ w : HeightOneSpectrum (𝓞 M), IsPlaceOver A w → IsPlaceOver A (w.under (𝓞 K))

def SplTrans : Prop :=
  ∀ (K M L Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [Algebra L Ω] [IsScalarTower K M Ω] (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 M))),
    (∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) ∈ S → w ∈ T) → Spl Ω M S → Spl Ω L T → Spl Ω L S

def DisjTrans : Prop :=
  ∀ (K M L Ω : Type) [Field K] [Field M] [Field L] [Field Ω] [Algebra K M] [Algebra M L] [Algebra K Ω] [Algebra M Ω] [Algebra L Ω]
    [IsScalarTower K M Ω] [IsScalarTower M L Ω] (N : Subgroup (G K Ω)), Disjoint' M N →
    GlobalTheory.AboveL.SolvDisj L (N.comap (AlgEquiv.restrictScalarsHom K : G M Ω →* G K Ω)) → Disjoint' L N

def OpenComap : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω]
    [IsScalarTower K M Ω] [IsAlgClosure K Ω] (N : Subgroup (G K Ω)), IsOpen (N : Set (G K Ω)) →
    IsOpen (N.comap (AlgEquiv.restrictScalarsHom K : G M Ω →* G K Ω) : Set (G M Ω))

def RamLift : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Field Ω] [Algebra K M]
    [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsGalois K M], (Module.finrank K M).Prime →
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v → (∃ τ ∈ Ine (F := K) A, ¬ Fixes M τ) →
    ∀ a : ℕ, 1 ≤ a → ∀ (π : CuspSub K a) (B : Multiset ℂˣ), (CG.mk π).HasSat v B →
    ∃ P : CuspSub M a, IsLiftUnr π P ∧ ∀ c, Pol c π → Pol c P

def StrongOf : Prop := LiftUnr → RamSph → GlobalTheory.Published.ArthurClozelStrongTC

end UpperTheory.Gal.AbelianGaloisNormality
end
end
