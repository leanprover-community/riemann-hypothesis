module

public import Mathlib.Basic.Complex.Basic
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemMoveLevUloc
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies
import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
import Formalism.LocalToGlobal.InertKernelTheory.TieSerPin
import Formalism.LocalToGlobal.KernelLattices.TopLawQ
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Imports
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CoeffProdRename

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem pullback_contraction_scalars : ∀ (m m' g g' k k' x x' A A' Δ Δ' : ℂ) (n n' c c' : ℤ), m ≠ 0 → m' ≠ 0 → g ≠ 0 → g' ≠ 0 → k ≠ 0 → k' ≠ 0 → x ≠ 0 → x' ≠ 0 → A ≠ 0 → A' ≠ 0 → Δ ≠ 0 → Δ' ≠ 0 → (g' * m' * k') * (g * m * k)⁻¹ * (Δ⁻¹ * A) ^ (-c) * (Δ'⁻¹ * A') ^ c' * ((Δ⁻¹ * A) ^ n' * (Δ'⁻¹ * A') ^ (-n))⁻¹ * (k * x' / (k' * x)) = (m⁻¹ * A ^ (-n')) * (m' * A' ^ n) * (x⁻¹ * g⁻¹ * Δ ^ (n' + c) * A ^ (-c)) * (x' * g' * Δ' ^ (-(n + c')) * A' ^ c') := by
  intro m m' g g' k k' x x' A A' Δ Δ' n n' c c' hm hm' hg hg' hk hk' hx hx' hA hA' hΔ hΔ'
  simp only [mul_zpow, inv_zpow', zpow_neg, zpow_add₀ hΔ, zpow_add₀ hΔ', zpow_add₀ hA, zpow_add₀ hA', neg_add, mul_inv, inv_inv, div_eq_mul_inv]
  field_simp

end GlobalTheory.TwV.DelB
