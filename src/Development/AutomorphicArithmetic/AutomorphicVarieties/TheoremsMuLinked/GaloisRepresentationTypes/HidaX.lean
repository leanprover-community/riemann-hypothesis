module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AbsH
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HdEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.JPT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.LevelX
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta

@[expose] public section

open UpperTheory.V UpperTheory.V.Th UpperTheory.V.Hi UpperTheory.V.Hi.CaseU

theorem UpperTheory.V.Th.hidaX :
    Af.HypothesesH → HidaX := by
  intro P l _ L Ω _ _ _ _ _ _ s V hS c n hn r B Λ ι
  obtain ⟨R⟩ := hdEx P l L Ω s n hn V (QData.empty V hS) c r ι Λ
  let K : (hset (QData.empty V hS) R.τ₀).Lev := ⟨fun q => Empty.elim q, fun q => Empty.elim q⟩
  obtain ⟨J, hJ⟩ := jEx P l L Ω s n hn V _ c r ι B Λ R K
  exact ⟨J, jPT P l L Ω s n hn V _ c r ι B Λ R K hS J hJ, Th.AnnihilatorQuotientFinite.levelX P l L Ω s n hn V _ c r ι B Λ R K hS J hJ⟩
