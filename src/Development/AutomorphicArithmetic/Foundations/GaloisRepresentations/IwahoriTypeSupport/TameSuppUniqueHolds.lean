module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.HasTypeVecIff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.FinTri
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.GrpFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.JacOfType
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.JacProd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.LocHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.SuppOfTypeOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TypeToIw
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace UpperTheory.Gal.TypesAndIwahori

theorem suppOfType_holds : SuppOfType := suppOfType_of loc_holds (typeToIw finTri)

theorem topB_holds : TopB := topB_of (jacOfType loc_holds) grpFacts (jacProd loc_holds)

end UpperTheory.Gal.TypesAndIwahori
