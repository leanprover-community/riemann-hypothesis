module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
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
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize

namespace GlobalTheory.ArchTens

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def placeSz {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (w : Pl D.host.E) : ℝ :=
  (cosExp G w : ℝ) * Real.log (Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal)

theorem placeSz_nonneg {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (w : Pl D.host.E) :
    0 ≤ placeSz G w :=
  mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C : ℝ)

def DatAt : Prop := ∀ (σ : D.what₂.LL →+* ℂ) Φ, ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ (w : locPl ch.G A.μ0) x y,
  AbsLe σ ((ch.S.term A.μ0 Φ β w).datum (ch.S.colAt A.μ0 w x) (ch.S.rowAt A.μ0 w y))
    (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w)

def FlipAt : Prop := ∀ (σ : D.what₂.LL →+* ℂ) Φ (w : locPl ch.G A.μ0) z,
  AbsLe σ (Tflip ch.W ch.S.B A.μ0 Φ w z) (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w)

def CoefAt : Prop := ∀ Φ, ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ w : locPl ch.G A.μ0,
  |((ch.S.term A.μ0 Φ β w).coef : ℝ)| ≤ Real.exp (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w)

end Claims

section Abs

variable {D : D7}

theorem absLe_mono {σ : D.what₂.LL →+* ℂ} {z : ℂ} {B B' : ℝ} (h : AbsLe σ z B) (hB : B ≤ B') : AbsLe σ z B' :=
  let ⟨y, e, h⟩ := h
  ⟨y, e, h.trans (Real.exp_le_exp.2 hB)⟩

theorem absLe_mul {σ : D.what₂.LL →+* ℂ} {z z' : ℂ} {B B' : ℝ} (h : AbsLe σ z B) (h' : AbsLe σ z' B') :
    AbsLe σ (z * z') (B + B') := by
  obtain ⟨y, e, hy⟩ := h
  obtain ⟨y', e', hy'⟩ := h'
  refine ⟨y * y', by rw [map_mul, e, e'], ?_⟩
  rw [map_mul, norm_mul, Real.exp_add]
  exact mul_le_mul hy hy' (norm_nonneg _) (Real.exp_pos _).le

theorem absLe_prod {ι : Type} (s : Finset ι) {σ : D.what₂.LL →+* ℂ} (z : ι → ℂ) (B : ι → ℝ) (h : ∀ i ∈ s, AbsLe σ (z i) (B i)) :
    AbsLe σ (∏ i ∈ s, z i) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, map_one _, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact absLe_mul (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem absLe_rat (σ : D.what₂.LL →+* ℂ) (q : ℚ) {B : ℝ} (h : |(q : ℝ)| ≤ Real.exp B) : AbsLe σ (q : ℂ) B := by
  refine ⟨(q : D.what₂.LL), map_ratCast _ _, ?_⟩
  rw [map_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  exact h

end Abs

theorem sum_placeSz_le {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) :
    ∑ w : locPl G t, placeSz G w ≤ sig G := by
  classical
  rw [Finset.sum_coe_sort (locPl G t) (placeSz G)]
  have h1 : ∑ w ∈ locPl G t, placeSz G w = ∑ w ∈ G.pl.W0, placeSz G w := by
    refine (Finset.sum_subset (Finset.subset_union_left) fun w _ hw => ?_).symm
    simp [placeSz, (depthAt_of_notMem G hw).1]
  rw [h1, sig]
  unfold Places.W0
  refine (Finset.sum_image_le_of_nonneg fun w _ => placeSz_nonneg G w).trans (le_of_eq (Finset.sum_congr rfl fun v hv => ?_))
  rw [placeSz, (depthAt_w G hv).1, G.pl.under_w hv]

end GlobalTheory.ArchTens

end
