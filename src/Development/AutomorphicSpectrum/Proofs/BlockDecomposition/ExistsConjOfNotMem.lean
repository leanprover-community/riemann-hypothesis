module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilTensorLiftConclusion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsThetaPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.FieldNOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.EntZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.FinDiscNOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.JoinType
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical



open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B
open PositivityTheory.Rg.BcB.Desc
open PositivityTheory.Rg.BcB.F

namespace GlobalTheory.CompanionTheory.LFixDPf

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}



section Conj

open GlobalTheory.SplitPts GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws

end Conj

section Int

open GlobalTheory.SplitPts GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws

theorem mem_KGL_map_conj (u : Pl E) (g : GLw n (conjSrc (conjE E) u)) :
    GeneralLinearGroup.map (conjLoc (conjE E) u) g ∈ GlobalTheory.LFun.KGL u (n := n) ↔ g ∈ GlobalTheory.LFun.KGL (conjSrc (conjE E) u) (n := n) := by
  have hv : ∀ x : (conjSrc (conjE E) u).adicCompletion E,
      conjLoc (conjE E) u x ∈ u.adicCompletionIntegers E ↔ x ∈ (conjSrc (conjE E) u).adicCompletionIntegers E := fun x => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers, (conjLoc_spec (conjE E) u).2.2 x]
  rw [GlobalTheory.AdelicU.mem_GLint_iff, GlobalTheory.AdelicU.mem_GLint_iff]
  refine and_congr (forall₂_congr fun a b => hv _) (forall₂_congr fun a b => ?_)
  rw [← map_inv]
  exact hv _

end Int

section Int2

open GlobalTheory.SplitPts GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws

end Int2

section Main

open GlobalTheory.SplitPts GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws
open PositivityTheory.Rg.BcB.F.F5.Bo

variable {d : LocData E n}

end Main

section Core

open GlobalTheory.SplitPts GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws
open PositivityTheory.Rg.BcB.F.F5.Bo

end Core

end GlobalTheory.CompanionTheory.LFixDPf

end
