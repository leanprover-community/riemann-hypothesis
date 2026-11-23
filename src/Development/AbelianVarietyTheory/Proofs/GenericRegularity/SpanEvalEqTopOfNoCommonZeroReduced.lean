module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NaturalRuleValueBaseChangeOfIsReducedStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem span_evR_eq_top_of_noCommonZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∀ (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S), Ideal.span (Set.range fun i => evR Xo c (ws i) y) = ⊤ := by
  intro E _ _ _ H Dw l Xo c hL a n m ws hws hnz S _ _ _ y
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  letI : Field (S ⧸ M) := Ideal.Quotient.field M
  let T : Type := AlgebraicClosure (S ⧸ M)
  let φ : S →ₐ[c.F] T := (IsScalarTower.toAlgHom c.F (S ⧸ M) T).comp (Ideal.Quotient.mkₐ c.F M)
  obtain ⟨z, hz⟩ := hL.bc S T φ y
  obtain ⟨i, hi⟩ := hnz T z
  apply hi
  rw [GlobalTheory.T.naturalRule_value_baseChange_of_isReduced E H Dw l Xo c hL a n (ws i) (hws i) S T φ y z hz]
  have hm : evR Xo c (ws i) y ∈ M := hle (Ideal.subset_span ⟨i, rfl⟩)
  have h0 : Ideal.Quotient.mkₐ c.F M (evR Xo c (ws i) y) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
  show (IsScalarTower.toAlgHom c.F (S ⧸ M) T) (Ideal.Quotient.mkₐ c.F M (evR Xo c (ws i) y)) = 0
  rw [h0, map_zero]

end GlobalTheory.Reg
