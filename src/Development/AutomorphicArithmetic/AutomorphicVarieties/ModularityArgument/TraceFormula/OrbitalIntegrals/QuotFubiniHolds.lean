module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniOf
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.OrbProper
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace UpperTheory.V.Z.Tf.Orb

theorem orbProper_holds : OrbProper := UpperTheory.ConvolutionTheory.Loc.orbProper

theorem gLTop_holds : GLTop := gLTop_of

theorem extCont_holds : ExtCont := extCont_of

theorem centComm_holds : CentComm := centComm_of

theorem twCent_holds : TwCent := twCent_of

theorem haarComm_holds : HaarComm := haarComm_of

theorem quotIndep_holds : QuotIndep := quotIndep_of

theorem normEx_holds : NormEx := normEx_of

theorem quotInt_holds : QuotInt := quotInt_of

theorem untwist_holds : Untwist := untwist_of

theorem twOrbLin_holds : TwOrbLin := twOrbLin_of orbProper_holds

theorem orbLin_holds : OrbLin := orbLin_of orbProper_holds

theorem twOrbComm_holds : TwOrbComm := twOrbComm_of orbProper_holds

theorem orbComm_holds : OrbComm := orbComm_of orbProper_holds

end UpperTheory.V.Z.Tf.Orb
