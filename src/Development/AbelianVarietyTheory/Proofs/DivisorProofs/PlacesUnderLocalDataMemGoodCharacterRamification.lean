module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedAtLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharacterQuotientNotUnramifiedOverBaseP
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrModelOfIsLin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPairLat

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB alpha beta blk)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf HasExp SplitsFully)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.TripleSpaceW (conjSub)
open GlobalTheory.SkewLat (scLat pairLat)

namespace GlobalTheory.BigNZ.LocalPlaceUnderMembership

theorem under_locPl_mem : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (B : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (a a' : ℕ),
    X.α = alpha G t i j → X.β = beta G i j → X.IsGood B a a' →
    ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ∈ X.T := by
  classical
  intro D T L sc G μ₀ hL t i j B X a a' hα hβ hX w hw
  by_contra hn
  have hab : w ∉ GlobalTheory.LFun.above D.host.E (X.T : Set (HeightOneSpectrum (𝓞 D.host.F))) := fun h => hn h
  have hu : GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
    rw [← hα, ← hβ, div_eq_mul_inv]
    exact (hX.unrα w hab).mul (hX.unrβ w hab).inv
  by_cases hs : w.under (𝓞 D.host.F) ∈ G.pl.S0
  · rcases G.pl.mem_S0_of_sum_eq.1 hs with h | h
    · exact GlobalTheory.ThetaGridRamifiedOverBasePlace.thetaGridCharacterQuotient_not_unramified_over_basePlace hL t i j w h hu
    · exact GlobalTheory.FunObj.SqNum.not_unrAt_alpha_div_beta_over_S₁ hL t i j w h hu
  · rcases Finset.mem_union.1 hw with h | h
    · unfold Places.W0 at h
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      exact hs (by rw [G.pl.under_w hv]; exact hv)
    · exact GlobalTheory.TwistRam.not_unrAt_alpha_div_beta hL t i j w w h rfl hs hu

end GlobalTheory.BigNZ.LocalPlaceUnderMembership
