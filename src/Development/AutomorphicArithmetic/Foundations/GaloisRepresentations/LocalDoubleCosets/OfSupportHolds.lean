module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.CellStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.DistInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.DistZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.EigZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.EtaEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.ExistsStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.FunInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.GLCells
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.GLFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.Imports
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.JacSemi
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.LocDescOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.MemCcMulRight
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.PrAuto
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.PrLeft
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.PrMem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.PrSurj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.StabSub
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.ToBorel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePowAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

namespace UpperTheory.Gal.LocD

theorem funInv_holds : FunInv := by
  have dist := distInv (distZero (cellStep stabSub))
  exact funInv (biInv dist) prMem prLeft prAuto prSurj etaEx

theorem scalar_holds : Scalar := by
  have fi := funInv_holds
  exact scalar_of (eig eigZero) toBorel jacSemi (core fi gLCells gLFacts)

theorem locDesc_holds : LocDesc := locDesc_of scalar_holds tracePow

theorem ofSupport_holds : OfSupport := ofSupport

end UpperTheory.Gal.LocD
