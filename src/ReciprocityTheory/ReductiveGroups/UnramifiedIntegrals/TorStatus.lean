module

public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CM4
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorDefs
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ExistsFinitePartOneIdeleSplitCongruenceQuotient
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ScaledTorsionPointNonsingular
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
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorBasic
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorMain

@[expose] public section

noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

theorem cmTorsion_of_point (hpt : TorPt) : CM4 := by
  intro d L _ _ _ l _ hl _ ι lam hlam m2 m3 n2 n3 hΔ z N hN0 hN hz hz0
  have hg : GoodPair l (lam ^ 4 * ι L.g₂) (lam ^ 6 * ι L.g₃) := ⟨hl, m2, m3, n2, n3, hΔ⟩
  obtain ⟨h, hNP⟩ := hpt l L ι lam hlam z N hz hz0
  have hP0 : (Affine.Point.some _ _ h) ≠ 0 := Affine.Point.some_ne_zero h
  obtain ⟨hx, hy⟩ := tor_kur hg _ N hN0 hN hNP hP0
  obtain ⟨-, ix, iy⟩ := integral_of_not_mem_formalGroup hg _ (torsion_not_mem_formalGroup hg _ N hN hNP hP0)
  have hx' : lam ^ 2 * ι (L.weierstrassP z) ∈ MaximalUnramifiedExtension l := hx
  have hy' : lam ^ 3 * ι (L.derivWeierstrassP z) / 2 ∈ MaximalUnramifiedExtension l := hy
  have ix' : ‖lam ^ 2 * ι (L.weierstrassP z)‖ ≤ 1 := ix
  have iy' : ‖lam ^ 3 * ι (L.derivWeierstrassP z) / 2‖ ≤ 1 := iy
  have e : lam ^ 3 * ι (L.derivWeierstrassP z) = 2 * (lam ^ 3 * ι (L.derivWeierstrassP z) / 2) := by
    ring
  have h2 : ‖(2 : ℂ_[l])‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_natCast_le_one ℂ_[l] 2
  refine ⟨hx', ?_, ix', ?_⟩
  · rw [e]
    exact mul_mem (by simp) hy'
  · rw [e, norm_mul]
    exact mul_le_one₀ h2 (norm_nonneg _) iy'

theorem torPt : TorPt := Formalism.L2.Th1.E.scaled_torsion_point_of_add Formalism.L2.Th1.E.PtOfAdd_of

theorem cm4 : CM4 := cmTorsion_of_point torPt

end ReciprocityTheory.ChartRestriction.L1
