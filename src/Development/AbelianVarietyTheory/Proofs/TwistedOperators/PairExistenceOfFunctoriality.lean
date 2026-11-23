module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFockIntertwinerAdjointExchangedPairStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinerLargerSourceMirrorCase
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsItWOfGlobIt
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PairIt

open GlobalTheory.Chain GlobalTheory.Chain.RealIt

theorem exists_locIt_pair {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} {X : ProvA} (hX : ChosenSeries X)
    (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h2 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond X) (hB : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D)
    (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) {aS aT : ℚ}
    (hP : GlobalTheory.PairLift.PairPar (S τ) (S' τ) aS aT) :
    (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ aS aT A := by
  obtain ⟨t, P, P', hS, hS', hc⟩ := hP
  rcases hc with ⟨⟨al, be, ga, de, e1, ⟨hd, e2⟩ | ⟨hd, e2⟩⟩, -⟩ | ⟨al, be, ga, de, e1, ⟨hd, e2⟩ | ⟨hd, e2⟩⟩
  · exact exists_locIt hX h1 h2 hB M M' τ hd (hS.trans (congrArg dualPar e1)) (hS'.trans (congrArg dualPar e2))
  · obtain ⟨hr, A, hA⟩ := GlobalTheory.Chain.RealItLarge.exists_locIt_large hX h1 h2 hB M' M τ hd
      (hS'.trans (congrArg dualPar e2)) (hS.trans (congrArg dualPar e1))
    obtain ⟨A', hA'⟩ := GlobalTheory.T.localFockIntertwiner_adjoint_exchangedPair D W V _ _ M' M τ _ _ A hA
    exact ⟨⟨hr.2, hr.1⟩, A', hA'⟩
  · obtain ⟨hr, A, hA⟩ := exists_locIt hX h1 h2 hB M' M τ hd
      (hS'.trans (congrArg dualPar e1)) (hS.trans (congrArg dualPar e2))
    obtain ⟨A', hA'⟩ := GlobalTheory.T.localFockIntertwiner_adjoint_exchangedPair D W V _ _ M' M τ _ _ A hA
    exact ⟨⟨hr.2, hr.1⟩, A', hA'⟩
  · exact GlobalTheory.Chain.RealItLarge.exists_locIt_large hX h1 h2 hB M M' τ hd
      (hS.trans (congrArg dualPar e2)) (hS'.trans (congrArg dualPar e1))

end GlobalTheory.PairIt

end
