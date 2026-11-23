module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexFormsFiniteDimensionalStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyFamOkStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyLawBasisStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawNormClassSumFockStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsOfOkStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesComplexFormsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesIntegralFormsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondRepresentationStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalLatticeSpanAtPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightLawGoodOfFieldEmbeddingStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2



theorem laws_all : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → ∀ (Q : PerIn I) (hQ : Q.Ok) (Pl : Rows.Places K), J.Laws emb σ hc ∧ FmLaws J Q emb σ hc Pl hI hQ := by
  intro E K ι _ _ _ _ _ _ _ R I J emb σ hc hF hI hJ Q hQ Pl
  have hd := GlobalTheory.T.levelPrimeDiamond_representation I J emb σ hc hF hI hJ
  have hfam : ∀ i, ((I.S i).fam emb (lamT hc i)).Ok := fun i => GlobalTheory.T.hermitianLatticeChartFamily_fam_ok (I.S i) emb σ (lamT hc i) hF (hI.step i)
  have hfamP : (Q.S'.fam emb Q.sgT).Ok := GlobalTheory.T.hermitianLatticeChartFamily_fam_ok Q.S' emb σ Q.sgT hF hQ.step
  refine ⟨⟨hd.1, hd.2, GlobalTheory.T.complexForms_finiteDimensional (I.S 0) emb σ (lamT hc 0) hF (hI.step 0), GlobalTheory.T.levelPrimeDiamond_preserves_complexForms I J emb σ hc hF hI hJ⟩, ?_⟩
  exact
    { fam := hfam
      famP := hfamP
      lev := fun i => GlobalTheory.T.tDat_laws_of_ok (J.A i) J.T (hI.step i) (hJ.lev i)
      good := fun i => GlobalTheory.T.weight_law_good_of_field_embedding (I.S i) emb σ (lamT hc i) hF (hI.step i) _
      basis := fun i => GlobalTheory.T.hermitianLatticeChartFamily_lawBasis (I.S i) emb σ (lamT hc i) hF (hI.step i) _
      norm := fun i => letI := I.clFin hI i; GlobalTheory.T.lawNorm_classSum_fock (I.S i) emb σ (lamT hc i) hF (hI.step i) _
      goodP := GlobalTheory.T.weight_law_good_of_field_embedding Q.S' emb σ Q.sgT hF hQ.step _
      basisP := GlobalTheory.T.hermitianLatticeChartFamily_lawBasis Q.S' emb σ Q.sgT hF hQ.step _
      normP := letI := Q.clFin hQ; GlobalTheory.T.lawNorm_classSum_fock Q.S' emb σ Q.sgT hF hQ.step _
      dia_lat := GlobalTheory.T.levelPrimeDiamond_preserves_integralForms I J emb σ hc hF hI hJ _
      B_span := fun i w P => GlobalTheory.T.local_lattice_span_at_place I J emb σ hc hF hI hJ Pl i _ w P }

end GlobalTheory.Mem.Col2
