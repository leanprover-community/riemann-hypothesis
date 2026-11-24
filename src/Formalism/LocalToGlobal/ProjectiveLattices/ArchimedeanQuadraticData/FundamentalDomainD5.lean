module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoveringRadiusStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.DiscrMulIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.DotSelfEqSqNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ExistsBasisIn
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinrankCmType
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.LatticeZbasis
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ThetaDotSelf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinF
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.HQsmulRight
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.RhoDotSelf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmApproximationTransference

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField Matrix ComplexConjugate ReciprocityTheory.MultiplicativeHeights

theorem d5_translation : ReciprocityTheory.ChartRestriction.G.FD.CoveringRadiusStatement :=
  GlobalTheory.CMTransference.cmApproximation_transference

end Formalism.L2.Pj.FundamentalDomainD5
