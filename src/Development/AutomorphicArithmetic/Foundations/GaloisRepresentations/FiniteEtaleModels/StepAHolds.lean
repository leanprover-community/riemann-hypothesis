module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BaseOnto
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ABetaH
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ABetaLat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ADictP
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.AGalOfKer
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ALevRe
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ALevTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ANumSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ASysExt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrEtaK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrKer
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrPull
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrSame
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.CoreAOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.StepAOf
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.FiniteEtaleModels

theorem stepA_holds (h₁ : MultUnit) (h₂ : LatGen) (h₃ : ClsEx) (h₄ : TrEta) (h₅ : TrBack) (h₆ : QComp) : StepA :=
  stepA_of (dictP_holds h₁) sysExt_holds trEtaK_holds trKer_holds galOfKer_holds betaH_holds (betaLat_holds h₂) numSplit_holds
    (coreA_of trPull trSame_holds levTr_holds levRe_holds h₃) h₄ h₅ h₆

end UpperTheory.Gal.FiniteEtaleModels
