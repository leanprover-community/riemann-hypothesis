module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem isLogCanonicalMultiple_add_qWeil : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), ∀ (Δ : X → ℚ) (m m' : ℕ) (G D₀ : CartierDiv X), 0 < m → 0 < m' → IsLogCanonicalMultiple p n Δ m G → IsLogCanonicalMultiple p n (Δ + qWeil D₀ m') (m * m') (m' • G + m • D₀) := by
  intro X _ _ p n Δ m m' G D₀ hm hm' hG
  obtain ⟨η, hη, hG⟩ := hG
  refine ⟨η, hη, fun x g hg z hz E hE => ?_⟩
  obtain ⟨V, hV, hgV⟩ := hg.exists_nhds
  obtain ⟨a, ha⟩ := G.exists_isEqn z
  obtain ⟨d, hd⟩ := D₀.exists_isEqn z
  have h3 := ((hgV z (hz.mem_open V.isOpen hV)).mult_eq.symm.trans
    ((ha.nsmul m').add (hd.nsmul m)).mult_eq)
  rw [← hE.ord_eq, ← hE.ord_eq, E.ord_mul, E.ord_pow, E.ord_pow] at h3
  have h4 := hG z a ha z specializes_rfl E hE
  have hd' := hd.mult_eq
  rw [← hE.ord_eq] at hd'
  have h1 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have h2 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  rw [Pi.add_apply, qWeil, hd', h3]
  push_cast
  rw [← h4]
  field_simp
  ring

end GlobalTheory
