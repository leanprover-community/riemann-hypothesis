module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Elliptic
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.OnePole
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.PDeriv
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaAdd
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaOrder
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.ThreeTermNumEqTwistedGammaOfSigmaZero
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SigmaLogDeriv2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

@[expose] public section

namespace Formalism.L2.Th1.F

theorem ellipticEntire : EllipticEntire := elliptic_entire_const
theorem ellipticNoPole : EllipticNoPole := elliptic_no_pole_const
theorem ellipticOnePole : EllipticOnePole :=
  ellipticOnePole_of ellipticNoPole ellipticEntire zetaQuasi legendre
theorem sigmaOrder : SigmaOrder := sigmaOrder_of sigmaEntire sigmaZero sigmaSimple
theorem sigmaAdd : SigmaAdd :=
  sigmaAdd_of ellipticNoPole sigmaEntire sigmaOdd sigmaZero sigmaSimple sigmaQuasi sigmaOrder
theorem sgStarAdd : SgStarAdd := sgStarAdd_of sigmaAdd
theorem pInjective : PInjective := pInjective_of sigmaAdd sigmaZero
theorem sigmaDouble : SigmaDouble := sigmaDouble_of sigmaAdd sigmaEntire sigmaSimple
theorem pDerivZero : PDerivZero := pDerivZero_of sigmaDouble sigmaZero
theorem discNeZero : DiscNeZero := discNeZero_of pDerivZero pInjective
theorem zetaAdd : ZetaAdd := zetaAdd_of sigmaAdd sigmaLogDeriv sigmaZero
theorem sigmaThree : SigmaThree :=
  sigmaThree_of ellipticOnePole sigmaOrder sigmaQuasi sigmaZero sigmaEntire sigmaOdd sigmaSimple sigmaAdd
theorem sgStarThree : SgStarThree := sgStarThree_of sigmaThree
theorem thetaLine : ThetaLine := thetaLine_of ellipticOnePole sgStarQuasi sgStarBasic

end Formalism.L2.Th1.F
