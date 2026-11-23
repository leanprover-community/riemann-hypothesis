module

public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeDepthDataExistsAtPointsProofStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LargePrimeDepthDataExistsAtPointsProofStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PackagesExistFrobeniusComplexConjugationStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitPrimeDepthDataExistsAtPointsProofStatement
public import Development.AutomorphicArithmetic.OrbitLabellings.ExistsPkgCsOfDegreeBoundAtInertPrimes
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

theorem goodPrime_packages :
    (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) →
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
        (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgSt Xo c := by
  intro hU E _ _ _ H Dw lv Xo c _
  exact ⟨GlobalTheory.T.inertPrimeDepthDataExistsAtPoints_proof hU E H Dw lv Xo c, (GlobalTheory.T.packages_exist_frobeniusComplexConjugation hU E H Dw lv Xo c).1, GlobalTheory.T.splitPrimeDepthDataExistsAtPoints_proof hU E H Dw lv Xo c,
    GlobalTheory.T.largePrimeDepthDataExistsAtPoints_proof hU E H Dw lv Xo c, (GlobalTheory.T.packages_exist_frobeniusComplexConjugation hU E H Dw lv Xo c).2,
    (UpperTheory.exists_pkgCs_of_degree_bound_at_inert_primes hU E H Dw lv Xo c).1, (UpperTheory.exists_pkgCs_of_degree_bound_at_inert_primes hU E H Dw lv Xo c).2⟩

end GlobalTheory
