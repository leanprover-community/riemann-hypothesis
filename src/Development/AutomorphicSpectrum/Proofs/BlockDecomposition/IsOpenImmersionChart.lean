module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeChart

attribute [local instance] MvPolynomial.gradedAlgebra

instance isOpenImmersion_chart (R : Type) [CommRing R] (N : ℕ) (j : Fin (N + 1)) :
    IsOpenImmersion (chart R N j) := by
  unfold chart
  infer_instance

theorem opensRange_fst {R : Type} [CommRing R] {X : Scheme.{0}} (N : ℕ)
    (i : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace R N) (j : Fin (N + 1)) :
    (pullback.fst i (chart R N j)).opensRange = i ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N j := by
  have hr : (chart R N j).opensRange = GlobalTheory.ProjSpace.chart R N j := Proj.opensRange_awayι _ _ _ _
  rw [← hr]
  ext x
  change x ∈ Set.range (pullback.fst i (chart R N j)) ↔ i x ∈ Set.range (chart R N j)
  rw [Scheme.Pullback.range_fst]
  rfl

theorem preimage_chart_mem {R : Type} [CommRing R] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ)
    (i : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace R N) (h : IsTautologicalLineAt D N i) (j : Fin (N + 1)) :
    i ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N j ∈ 𝒱D D := by
  obtain ⟨_, s, hs, _⟩ := h
  rw [← opensRange_fst]
  refine ⟨(pullback.fst i (chart R N j)).isoOpensRange.inv ≫ s j, ?_⟩
  rw [Category.assoc, hs, Iso.inv_comp_eq]
  exact (Scheme.Hom.isoOpensRange_hom_ι _).symm

end GlobalTheory.CompanionTheory.ConeChart
