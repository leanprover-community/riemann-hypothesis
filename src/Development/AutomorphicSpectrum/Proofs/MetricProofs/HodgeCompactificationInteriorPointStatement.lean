module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCompactificationInteriorPoint
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries

@[expose] public section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.hodge_compactification_interior_point : ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (A : HodgeCpt Y S y) (Fl : A.Flag), Mono (spMap β) → ∀ (z : Sp ℂ ⟶ A.X), A.Interior z → ∀ s, ∃ (h : genPt A.ξ ⤳ centre z) (b : Fin (labelRk D s) → A.Li) (Γ : Matrix (Fin (labelRk D s)) (Fin (labelRk D s)) ℂ), (∀ k, flagStep Ω b k = flagStep Ω (Fl.b s) k) ∧ (A.V s).IsFrameAt b ⟨centre z, h⟩ ∧ A.M.GramAt A.t.PP.L z b Γ ∧ Γ.PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramFrame.main | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramFrame.main | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramFrame.main <;> assumption)
