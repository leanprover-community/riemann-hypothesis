module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad

theorem natCast_mem_nonunits_of_induces (D : D7) (p : ℕ) [hp : Fact p.Prime] (la : PlL D p) (W : ValuationSubring ℂ)
    (h : ∀ x : D.what₂.LL, D.what₂.embLL x ∈ W ↔ la.1.valuation D.what₂.LL x ≤ 1) : (p : ℂ) ∈ W.nonunits := by
  have hlt : la.1.valuation D.what₂.LL (p : D.what₂.LL) < 1 := by
    have := (la.1.valuation_lt_one_iff_mem (K := D.what₂.LL) ((p : ℕ) : 𝓞 D.what₂.LL)).2 la.2
    simpa using this
  have hp0 : (p : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hv0 : 0 < la.1.valuation D.what₂.LL (p : D.what₂.LL) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hp0)
  have hnot : ((p : ℂ))⁻¹ ∉ W := by
    intro hm
    have h1 : D.what₂.embLL ((p : D.what₂.LL)⁻¹) ∈ W := by simpa using hm
    have h2 := (h _).1 h1
    rw [map_inv₀, inv_le_one₀ hv0] at h2
    exact absurd hlt (not_lt.2 h2)
  rw [ValuationSubring.mem_nonunits_iff]
  by_contra hc
  apply hnot
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀]
  exact inv_le_one_of_one_le₀ (not_lt.1 hc)

theorem placeW_spec (D : D7) (p : ℕ) [Fact p.Prime] (la : PlL D p) (jc : DV.KW p →+* ℂ) (h : JcPin D p la jc) :
    (∀ x : D.what₂.LL, D.what₂.embLL x ∈ placeW D p la jc ↔ la.1.valuation D.what₂.LL x ≤ 1) ∧
    ∀ a : DV.KW p, jc a ∈ placeW D p la jc ↔
      a ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range :=
  Classical.epsilon_spec h

theorem placeW_over : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (la : PlL D p) (jc : DV.KW p →+* ℂ), JcPin D p la jc → (p : ℂ) ∈ (placeW D p la jc).nonunits ∧ ∀ x : D.what₂.LL, D.what₂.embLL x ∈ placeW D p la jc ↔ la.1.valuation D.what₂.LL x ≤ 1 :=
  fun D p _ la jc h =>
    ⟨natCast_mem_nonunits_of_induces D p la _ (placeW_spec D p la jc h).1, (placeW_spec D p la jc h).1⟩

end GlobalTheory.ShFam.Pad
