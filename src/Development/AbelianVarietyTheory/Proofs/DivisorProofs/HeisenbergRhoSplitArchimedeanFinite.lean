module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilRepresentationExists
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.PrimesInProgressionNonempty
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BorelCasselman
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsIrrKSubOfIsKTypeOf
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesLowestKTypeOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KudlaSplittingSplitUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.PlaneFormNondegenerate
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ThetaRationalInvarianceHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.HeisSplit

theorem schr_add_of_orth {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a b : (κ → R) × (κ → R)) (h1 : a.1 ⬝ᵥ b.2 = 0) (h2 : b.1 ⬝ᵥ a.2 = 0) (φ : (κ → R) → ℂ) :
    schr ψ (a + b) φ = schr ψ a (schr ψ b φ) := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add, h1, h2]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  ring

theorem dot_eq_zero {R : Type} [CommRing R] {κ : Type} [Fintype κ] (e : R) (a c : κ → R) (h : e • a = 0) :
    a ⬝ᵥ (e • c) = 0 := by
  rw [dotProduct_smul, ← smul_dotProduct, h, zero_dotProduct]

section

variable (F : Type) [Field F] [NumberField F]

noncomputable def finAd (z : Af F) : AF F := ((0 : InfiniteAdeleRing F), z)

theorem finAd_mul (x : AF F) : finAd F x.2 * finAd F 1 = x * finAd F 1 := by
  refine Prod.ext ?_ ?_
  · show (0 : InfiniteAdeleRing F) * 0 = x.1 * 0
    simp
  · rfl

theorem finAd_idem : finAd F 1 * finAd F 1 = finAd F 1 := by
  refine Prod.ext ?_ ?_
  · show (0 : InfiniteAdeleRing F) * 0 = 0
    simp
  · show (1 : Af F) * 1 = 1
    simp

theorem evI_finAd : evI F (finAd F 1) = 0 := by
  exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem mul_finAd_of (t : AF F) (ht : evI F t = 0) : t * finAd F 1 = t := by
  have h : t.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 ht
  refine Prod.ext ?_ ?_
  · show t.1 * 0 = t.1
    simp [h]
  · show t.2 * 1 = t.2
    simp

theorem schr_pureA [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] (c : (κ → AF F) × (κ → AF F))
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (h : (κ → Af F) → ℂ) :
    schr ψ (finAd F 1 • c) (pureA F f h) =
      pureA F f (fun z => schr ψ (finAd F 1 • c) (fun x => h fun i => (x i).2) fun i => finAd F (z i)) := by
  funext x
  have e1 : (fun i => finAd F (x i).2) ⬝ᵥ (finAd F 1 • c).2 = x ⬝ᵥ (finAd F 1 • c).2 := by
    simp only [dotProduct, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, ← mul_assoc, finAd_mul]
  have e2 : ∀ i, ((x + (finAd F 1 • c).1) i).1 = (x i).1 := by
    intro i
    show (x i).1 + 0 * (c.1 i).1 = (x i).1
    simp
  have e3 : ∀ i, (((fun i => finAd F (x i).2) + (finAd F 1 • c).1) i).2 = ((x + (finAd F 1 • c).1) i).2 := fun i => rfl
  simp only [schr, pureA, e1, e2, e3]
  ring

end

theorem rho_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ),
    ∀ w : Matrix α β (AE F E),
    ∃ (u : Matrix α β (AE F E)) (H : ((κ → Af F) → ℂ) → (κ → Af F) → ℂ), At (evI F) u ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        ∀ (f f₁ : SInf F κ) (h : (κ → Af F) → ℂ),
          (∀ h' : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F f h') = pureA F f₁ h') →
            d.rho ψ (actB (cA σ) g w) (pureA F f h) = pureA F f₁ (H h) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d w
  have hu : finAd F 1 • (w - finAd F 1 • w) = 0 := by
    rw [smul_sub, smul_smul, finAd_idem, sub_self]
  refine ⟨w - finAd F 1 • w,
    fun h z => schr ψ (finAd F 1 • d.e w) (fun x => h fun i => (x i).2) fun i => finAd F (z i), ?_, ?_⟩
  · intro t ht
    rw [smul_sub, smul_smul, mul_finAd_of F t ht, sub_self]
  · intro g hg f f₁ h hyp
    have hg' := hg _ (evI_finAd F)
    rw [smul_sub, sub_eq_zero] at hg'
    have hv : actB (cA σ) g (finAd F 1 • w) = finAd F 1 • w := by
      unfold actB
      rw [Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.transpose_smul, hg', Matrix.transpose_smul, Matrix.transpose_one,
        Matrix.mul_smul, Matrix.mul_one]
    have hw : actB (cA σ) g w = actB (cA σ) g (w - finAd F 1 • w) + finAd F 1 • w := by
      have : actB (cA σ) g (w - finAd F 1 • w) = actB (cA σ) g w - actB (cA σ) g (finAd F 1 • w) := by
        unfold actB
        rw [Matrix.sub_mul]
      rw [this, hv, sub_add_cancel]
    have ha : finAd F 1 • d.e (actB (cA σ) g (w - finAd F 1 • w)) = 0 := by
      rw [← map_smul]
      unfold actB
      rw [← Matrix.smul_mul, hu, Matrix.zero_mul, map_zero]
    rw [← hyp, hw]
    unfold Darboux.rho
    rw [map_add (f := _), map_smul, schr_add_of_orth, schr_pureA]
    · exact dot_eq_zero _ _ _ (congrArg Prod.fst ha)
    · rw [dotProduct_comm]
      exact dot_eq_zero _ _ _ (congrArg Prod.snd ha)

end GlobalTheory.HeisSplit
