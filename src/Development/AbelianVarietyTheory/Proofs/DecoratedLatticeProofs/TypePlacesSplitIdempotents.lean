module

public import Mathlib
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
public import Formalism.LocalToGlobal.IndefiniteReal.RealRec
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAMulMemIntAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverTypePrimeChosenAndConj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesOverSplitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.SumExtendByZeroLeSum

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelPlaces

theorem not_isConjPl_lev {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} (h : ¬ Formalism.BasicNotions.IsConjPl D.host P P) :
    ¬ Formalism.IndefR.Lev.IsConjPl (D := D) P P := by
  intro hl
  apply h
  intro x y hxy
  have hs : ∀ c c' : 𝓞 D.host.E, (c' : D.host.E) = star (c : D.host.E) → c' = GlobalTheory.IdemSupport.cO D c :=
    fun c c' e => RingOfIntegers.ext (by rw [e, GlobalTheory.IdemSupport.cO_coe])
  have hy : y = GlobalTheory.IdemSupport.cO D x := by
    apply RingOfIntegers.ext
    rw [hxy, GlobalTheory.IdemSupport.cO_coe]
    exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
  subst hy
  constructor
  · intro hx
    obtain ⟨c', hc', e⟩ := hl x hx
    rwa [hs _ _ e] at hc'
  · intro hx
    obtain ⟨c', hc', e⟩ := hl _ hx
    rwa [hs _ _ e, GlobalTheory.IdemSupport.cO_cO] at hc'

end GlobalTheory.LevelPlaces

namespace GlobalTheory.LevelPlaces

end GlobalTheory.LevelPlaces
