module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsOfFinOrderHeckeCharacterValueCompletelySpliStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpIffHasInfQ
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterEquivalenceLocalData
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitValueAdelic

theorem not_isOfFinOrder_val : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ → (∀ τ : D.what₂.Tau, ∃ a : ℚ, a ≠ 0 ∧ HasInfExp D χ τ a) → ∀ p : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.LFun.UnrAt χ w → ¬ IsOfFinOrder (GlobalTheory.LFun.val (F := D.host.F) χ w) := by
  intro D χ hχ ha p hp w hw _
  obtain ⟨H, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D χ hχ
  choose a ha0 ha using ha
  have h1 := (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ D χ H a hH).1 ha
  rw [(GlobalTheory.ChrTie.unrAt_iff_and_val_eq D χ H hH w).2]
  exact GlobalTheory.T.not_isOfFinOrder_heckeCharacter_value_completelySplitPrime D H a p h1 ha0 hp w hw

end GlobalTheory.SplitValueAdelic
