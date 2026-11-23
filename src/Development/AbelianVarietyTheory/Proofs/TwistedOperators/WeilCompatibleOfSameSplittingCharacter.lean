module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousWittTowerRestrictionWeilCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionWeilDataTwistCharacterTrivialSplitPlaStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionIntertwinesWeilUpToCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionWeilCharacterRationalEqOneStatement
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SameCharCompat

theorem compatibleOfSameChar : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.CompatibleOfSameChar D := by
  intro D V V' W r C B hs ψ χS χT χT' ω ω' hω hω' μ 𝓨 hμ h f hf
  obtain ⟨c, hc⟩ := GlobalTheory.T.wittTowerRestriction_intertwines_weil_upToCharacter D V V' W r C B hs ψ χS χT χS χT' ω ω' hω hω' μ 𝓨 hμ
  have h1 : ∀ g, c g = 1 := GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D W c
    (GlobalTheory.T.continuous_wittTowerRestriction_weilCharacter D V V' W r C B hs ψ χS χT χS χT' ω ω' hω hω' μ 𝓨 hμ c hc)
    (GlobalTheory.T.wittTowerRestriction_weilCharacter_rational_eq_one D V V' W r C B hs ψ χS χT χS χT' ω ω' hω hω' μ 𝓨 hμ c hc)
    (GlobalTheory.T.restriction_weilData_twistCharacter_trivial_splitPlaces D V V' W r C B hs ψ χS χT χT' ω ω' hω hω' μ 𝓨 hμ c hc)
  rw [hc h f hf, h1 h]
  simp

end GlobalTheory.SameCharCompat
