module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.FibreSum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PDenseCoset
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PDenseOff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PDenseSub
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PESpan
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PExpand
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PExtract
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PFibre
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PFibreOff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PHomog
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PInterp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PInterpNF
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PMixDet
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.POffPow
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.POffRed
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PPairCount
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PPairSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PSpanE
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PSpanProd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PSpanTop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PVdmSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurDetOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYClrOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.Vdm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.WeylTieOf
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

noncomputable section

open Finset

namespace UpperTheory.Gal.Schur

theorem SchurYClr_holds : SchurYClr := (schurYClr_of tie mixDet).1
theorem SchurYOffClr_holds : SchurYOffClr := (schurYClr_of tie mixDet).2
theorem VdmSplit_holds : VdmSplit := vdmSplit_of pairSplit
theorem SchurY_holds : SchurY := schurY_of SchurYClr_holds VdmSplit_holds
theorem SchurYOff_holds : SchurYOff :=
  schurYOff_of (offClrRed_of (offClrPow_of SchurYOffClr_holds VdmSplit_holds (pairCount_of pairSplit)))
    VdmSplit_holds
theorem SchurHomog_holds : SchurHomog := schurHomog
theorem SchurDet_holds : SchurDet := schurDet_of tie
theorem WeylTie_holds : WeylTie := weylTie_of tie
theorem SpanE_holds : SpanE := spanE_of eSpanMul
theorem DenseCoset_holds : DenseCoset := denseCoset_of denseSub spanTop denseOff
theorem Interp_holds : Interp := interp_of (spanProd_of SpanE_holds) expand extract DenseCoset_holds
theorem InterpNF_holds : InterpNF := interpNF_of Interp_holds
theorem Fibre_holds : Fibre := fibre_of SchurY_holds schurHomog SchurDet_holds
theorem FibreOff_holds : FibreOff := fibreOff_of SchurYOff_holds schurHomog SchurDet_holds
theorem FibreSum_holds : FibreSum := fibreSum_of InterpNF_holds Fibre_holds FibreOff_holds

end UpperTheory.Gal.Schur
