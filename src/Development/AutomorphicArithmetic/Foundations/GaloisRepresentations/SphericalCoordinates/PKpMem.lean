module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFr
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PerCApply

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem mem_intK_iff {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (a : K) :
    a ∈ GlobalTheory.LKLoc.intK p K ↔ ‖(a : PadicAlgCl p)‖ ≤ 1 := by
  show (algebraMap K (PadicAlgCl p) a) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p ↔ _
  exact ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff

theorem UpperTheory.Gal.W2.kpMem_of :
    UpperTheory.Gal.W2.KpMem := by
  intro p _ G g
  rw [GlobalTheory.HeckeP.inclG_mem_KHT_iff]
  unfold UpperTheory.Gal.W2.IntPt
  have hunit : (‖(g.1 : ℚ_[p])‖ ≤ 1 ∧ ‖((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1) ↔ ‖(g.1 : ℚ_[p])‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv]
    have hpos : 0 < ‖(g.1 : ℚ_[p])‖ := norm_pos_iff.2 g.1.ne_zero
    constructor
    · rintro ⟨h1, h2⟩
      exact le_antisymm h1 (by simpa using (inv_le_one₀ hpos).1 h2)
    · intro h
      rw [h]
      simp
  rw [hunit]
  apply and_congr_right'
  apply forall_congr'
  intro w
  unfold GlobalTheory.LKLoc.KintK
  rw [GlobalTheory.HeckeP.mem_range_map_subtype]
  simp only [mem_intK_iff]
  rw [← forall_and]
  apply forall_congr'
  intro i
  rw [← forall_and]
