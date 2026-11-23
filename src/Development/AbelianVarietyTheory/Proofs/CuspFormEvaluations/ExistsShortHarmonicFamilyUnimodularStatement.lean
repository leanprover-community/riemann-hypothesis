module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyUnimodular
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_short_harmonic_family_unimodular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n), Λ.Unimod → Λ.La.FG → Dw.p + Dw.q ≤ n → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (L : ℝ), 2 ≤ L → Real.log (FD.rdE E) ≤ 2 * L → Real.log (FD.fdeg E) ≤ 2 * L → Real.log (1 + DF Dw a) ≤ 2 * L → Real.log n ≤ L → ∃ S : Finset (MvPolynomial (LtN Dw n) c.F), (∀ Q ∈ S, Q ∈ harmL c Λ a ∧ ∀ σ' : c.F →+* ℂ, Real.log (∑ m ∈ Q.support, ‖σ' (Q.coeff m)‖) ≤ 140 * (Dw.p + Dw.q : ℕ) * L * DF Dw a) ∧ (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), P ∈ Submodule.span c.F (S : Set (MvPolynomial (LtN Dw n) c.F))) ∧ S.card ≤ ((2 * (Dw.p + Dw.q) + 1) * DF Dw a + 1) ^ (2 * FD.fdeg E * n * (2 * Dw.p + Dw.q)) := by
  first | exact @GlobalTheory.Harm.exists_short_harmL_family | exact GlobalTheory.Harm.exists_short_harmL_family | (intros; apply GlobalTheory.Harm.exists_short_harmL_family <;> assumption)
