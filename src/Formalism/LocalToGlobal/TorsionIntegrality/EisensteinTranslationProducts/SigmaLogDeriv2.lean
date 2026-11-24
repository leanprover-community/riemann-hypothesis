module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Legendre
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.AnalyticIdentityTheoremsZetaFacts
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.EtaEis
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Legendre
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaBasic
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaConv
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaLog
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaQuasi
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.ZetaQuasi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.L2.Th1.F

theorem zetaSummable : ZetaSummable := zeta_summable
theorem zetaHasDeriv : ZetaHasDeriv := zeta_has_deriv
theorem zetaOdd : ZetaOdd := zeta_odd
theorem zetaQuasi : ZetaQuasi := zetaQuasi_of zetaHasDeriv zetaOdd
theorem sigmaSummable : SigmaSummable := sigma_summable
theorem sigmaProdLU : SigmaProdLU := sigma_product_locally_uniform
theorem sigmaEntire : SigmaEntire := sigmaEntire_of sigmaProdLU
theorem sigmaOdd : SigmaOdd := sigma_odd
theorem sigmaZero : SigmaZero := sigmaZero_of sigmaSummable
theorem sigmaLogDeriv : SigmaLogDeriv := sigmaLogDeriv_of sigmaProdLU sigmaSummable zetaSummable
theorem sigmaQuasi : SigmaQuasi := sigmaQuasi_of zetaQuasi sigmaLogDeriv sigmaEntire sigmaOdd sigmaZero
theorem sigmaSimple : SigmaSimple := sigmaSimple_of sigmaQuasi sigmaEntire (sigmaDerivZero_of sigmaProdLU)
theorem etaEisenstein : EtaEisenstein := etaEisenstein_of zetaSummable zetaOdd
theorem legendre : Legendre := legendre_of etaEisenstein

end Formalism.L2.Th1.F
