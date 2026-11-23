module

import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LocalFormOfWeakForm
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETExSt
public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaValuationTest

open Formalism.MainNotions Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.ModuliIntegralCharts.H1

variable {D : Formalism.BasicNotions.D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem phiC_nonneg (X : WeightAlgebra.PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) : 0 ≤ X.phiC la y := by
  apply Formalism.MainNotions.Gaps.T0.phiC_nonneg <;> assumption

theorem mem_Mlat (X : WeightAlgebra.PJ D B P j) (i : ℕ) (η : B.Cusp j (Formalism.L2.Pj.wEt D j i)) (h : EtVal X i η) :
    η ∈ B.Mlat j _ := by
  refine (X.Mlat_eq _ η).2 fun la y => le_trans ?_ (h la y)
  exact EReal.coe_nonneg.2 (mul_nonneg (by positivity) (phiC_nonneg X la y))

end GlobalTheory.EtaValuationTest
