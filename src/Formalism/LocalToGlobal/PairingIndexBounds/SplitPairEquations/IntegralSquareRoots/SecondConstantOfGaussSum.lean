module

public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.MulIntegerMemBaseLattice
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.EqPOf
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.OneEntryMem
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.SecondConstantOfTrianglesData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.MainNotions Formalism.L2.PairingIndexBounds.Eq

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Ker.Base D cc δ}

theorem first_constant_of_gauss_sum (hS : B.StdOK) (hL : B.LatAll) (hTL : Tr0L D B.tor) (hG : GaussRow B) : J1 B :=
  first_constant_of_triangles_data hS hL hTL hG (fun N N' _ _ => lat0IsLat hS N N') (fun N N' _ _ => thZeroSpans hS N N')

theorem second_constant_of_gauss_sum (hS : B.StdOK) (hL : B.LatAll) (hTR : Tr0R D B.tor) (hG : GaussRow B) : J2 B :=
  second_constant_of_triangles_data hS hL hTR hG (fun N N' _ _ => lat0IsLat hS N N') (fun N N' _ _ => thZeroSpans hS N N')

theorem first_constant_of_pullback (hS : B.StdOK) (hL : B.LatAll) (hTL : Tr0L D B.tor) (hNeg : NegOneNorm D) : J1 B :=
  first_constant_of_gauss_sum hS hL hTL (gaussRow_of B hS hL hNeg)

theorem second_constant_of_pullback (hS : B.StdOK) (hL : B.LatAll) (hTR : Tr0R D B.tor) (hNeg : NegOneNorm D) : J2 B :=
  second_constant_of_gauss_sum hS hL hTR (gaussRow_of B hS hL hNeg)

theorem eqP_of_neg (B : Ker.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ)
    (hSq : SqP D B.tor) (hTL : Tr0L D B.tor) (hTR : Tr0R D B.tor) (hNeg : NegOneNorm D) : B.EqP χ :=
  eqP B hcc hδ hδ0 hS χ hχ hSq hTL hTR (first_constant_of_pullback hS (B.latAll hcc hδ hδ0) hTL hNeg) (second_constant_of_pullback hS (B.latAll hcc hδ hδ0) hTR hNeg)

end Formalism.L2.PairingIndexBounds.Eq.J
