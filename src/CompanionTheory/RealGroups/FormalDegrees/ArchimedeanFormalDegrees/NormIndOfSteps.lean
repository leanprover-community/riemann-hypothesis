module

public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.HlamStable
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.MomB
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.DegreeNormalization.DegPsi
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.DegreeNormalization.GapNorm
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.FormalDegreeFormula.CKContinuous
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.MomentRecursion.MomStep
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.PositiveConjugation.DzSubMuNextNonneg
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.PositiveConjugation.HsOpOpMul
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.PositiveConjugation.PhiCont
import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.PositiveConjugation.PhiMul
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.SignDefiniteness.NormDef
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CKContinuous
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HsOpIntegralRankOne
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.ExplicitFunctionSquareIntegrable

@[expose] public section

noncomputable section

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS CompanionTheory.RgDs

theorem hsInt : HsInt := GlobalTheory.CompanionTheory.RgFd.hsInt GlobalTheory.CompanionTheory.HsPsProof.hsPs hsPol phiMul phiCont

theorem psiNorm_of (hI : NormInd) : PsiNorm := by
  intro n ε lam hl
  by_cases h : S7.q0 ε = 0
  · exact normDef n ε h lam hl
  · have h1 : 1 ≤ min (pOf ε) (qOf ε) := Nat.one_le_iff_ne_zero.2 h
    exact hI n ε (h1.trans (min_le_left _ _)) (h1.trans (min_le_right _ _)) lam hl

theorem normInd_of_steps (hP : CoefPow)
    (h : MomW → CoefPow → KNull → HsPol → PhiMul → PhiLe → PhiCont → HsInt → GapNorm → NormInd) : NormInd :=
  h momW hP (kNull_of momW hP) hsPol phiMul phiLe phiCont hsInt (gapNorm_of degPsi)

end CompanionTheory.RgFd
