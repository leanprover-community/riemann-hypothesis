module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetMemSubring
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CauchyBinetSumPositionedMinors
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

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

theorem _root_.GlobalTheory.T.cauchyBinet_sum_positioned_minors : ∀ {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
    (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω)
    (hBC : ∀ s, B s * C s = 1) (t : StepIx Ψ p q) (I I' : Finset (Fin (p + q)))
    (hI : I.card = (t.2 : ℕ) + 1) (hI' : I'.card = (t.2 : ℕ) + 1)
    (hp : ∀ a ∈ I, ∃ l, posOf p q t.1 l = a) (hp' : ∀ a ∈ I', ∃ l, posOf p q t.1 l = a),
    ∑ J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1), sMin B t I J * cMin C t J I' = if I = I' then 1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.Inv.sum_sMin_mul_cMin | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.Inv.sum_sMin_mul_cMin | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.Inv.sum_sMin_mul_cMin <;> assumption)
