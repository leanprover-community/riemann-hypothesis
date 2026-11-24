module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.ResClosed
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PClopenAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCycAll
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCycExt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCycRes
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PFibExt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PHensSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PResClosed
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PSecGen
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PValLiftB
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PWtVal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PullHQComp
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

@[expose] public section

namespace UpperTheory.Gal.Mod

theorem wtVal_holds : WtVal := by
  exact wtVal fibExt secGen (clopenAt resClosed hensSplit)

theorem cycAll_holds : CycAll := by
  exact cycAll resClosed valLiftB (cycRes wtVal_holds) (cycExt fibExt)

theorem esPt_holds : ESPt := esPt cycAll_holds

end UpperTheory.Gal.Mod
