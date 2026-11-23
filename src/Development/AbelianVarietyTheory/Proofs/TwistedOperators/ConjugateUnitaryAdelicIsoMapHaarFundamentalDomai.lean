module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainConjugateUnitaryAdeli
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.HaarConjImage

theorem map_isHaarFD : ∀ (D : D7) (S : HSp D) (c : D.host.E) {J : Matrix (Fin S.rank) (Fin S.rank) D.host.E} (hJ : J = c • S.gram), c ≠ 0 →
    ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), IsHaarFD S ν 𝓕 →
      (ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ)).IsHaarMeasure ∧
      IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ '' 𝓕)
        (ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ)) := by
  intro D S c J hJ hc ν 𝓕 h
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig S.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig S.gram
  have : BorelSpace (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) := ⟨rfl⟩
  have c1 : Continuous (GlobalTheory.HaarConj.conjE S c hc hJ) := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU S c hJ
  have c2 : Continuous (GlobalTheory.HaarConj.conjE S c hc hJ).symm := GlobalTheory.HaarConj.continuous_conjInv S c hc hJ
  haveI := h.1
  exact ⟨MulEquiv.isHaarMeasure_map ν (GlobalTheory.HaarConj.conjE S c hc hJ) c1 c2,
    GlobalTheory.HaarConj.isFundamentalDomain_image (GlobalTheory.HaarConj.conjE S c hc hJ) c1.measurable c2.measurable (GQ S) _
      (GlobalTheory.HaarConj.mem_ratU_iff S c hc hJ) ν 𝓕 h.2⟩

end GlobalTheory.HaarConjImage

end
