module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSecReadingDecreasingIntegerExponents
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

theorem _root_.GlobalTheory.T.isSec_reading_decreasing_integer_exponents : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), Nonempty (KeySec Xo c) → GoodEmb c σ → IsUnf U → 1 ≤ Dw.p + Dw.q → ∀ G : WTZ E, Even G.2 → (∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → G.1 (τ, j) ≤ G.1 (τ, i)) → ∀ f ∈ secZ Xo c (exZ Dw G), ∀ k, (U.X k).IsSec (modelWt U G k) (rdU U f k) := by
  first | exact @GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU | exact GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU | (intros; apply GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU <;> assumption)
