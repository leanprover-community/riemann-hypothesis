module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAdelicFourierSeparatingCharsVanish
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwConjOfIsTest
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralTsumEnormNeTop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.UnfoldCut

section Group

variable {D G : Type} [Group D] [Group G]

end Group

section Measure

variable {D G : Type} [Group D] [Group G]

end Measure

section Main

variable {D G : Type} [Group D] [Countable D] [Group G] [MeasurableSpace G] [MeasurableMul G]

end Main

section Top

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem secondCountable_GA : SecondCountableTopology (GA E n) := by
  haveI := GlobalTheory.AdelicFourierUniq.secondCountable_inf E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  haveI : SecondCountableTopology (Ad E) :=
    inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem locallyCompact_GA : LocallyCompactSpace (GA E n) :=
  GroundTheory.Automorphic.AdelicGLn.locallyCompactSpace E n

theorem t2Space_adelicGL_cmField : T2Space (GA E n) := by
  haveI := GlobalTheory.AdelicFourierUniq.t2Space_infiniteAdeleRing_of_numberField E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  haveI : T2Space (Ad E) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))
  haveI : T2Space (Matrix (Fin n) (Fin n) (Ad E)) :=
    inferInstanceAs (T2Space (Fin n → Fin n → Ad E))
  haveI : T2Space (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.t2Space
  exact Units.isEmbedding_embedProduct.t2Space

theorem countable_GL : Countable (GL (Fin n) E) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  exact Units.val_injective.countable

end Top

end GlobalTheory.CompanionTheory.UnfoldCut

end
