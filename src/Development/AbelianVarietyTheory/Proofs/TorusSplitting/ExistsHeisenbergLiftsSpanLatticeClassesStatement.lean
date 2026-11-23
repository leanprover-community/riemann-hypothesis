module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsHeisenbergLiftsSpanLatticeClasses
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_heisenbergLifts_span_latticeClasses : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] (G : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) G), P.TorsionIso → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (N : ℕ), 1 ≤ N → ∀ (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (ev : M → (TFK (R := V) F ⟶ P.A.A)), (∀ a b, ev (a + b) = ev a * ev b) → (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ (letI := H.starRing; P.oA.act o : P.A.A ⟶ P.A.A)) → (∀ a, ev a ^ N = 1) → (∀ u, u ^ N = 1 → ∃ a, ev a = u) → ∃ pt : M → QkPt P.D.toPre F N, (∀ a, P.ToA F N (pt a) (ev a)) ∧ ∀ (n : ℕ) (z : Fin n → M), Submodule.span (𝓞 E) (Set.range z) = ⊤ → ∀ a : P.D.toPre.X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range fun b => (pt (z b)).y), ∃ t : P.D.toPre.X, a = u + N • t := by
  first | exact @GlobalTheory.EtaVal.exists_qkPt_span | exact GlobalTheory.EtaVal.exists_qkPt_span | (intros; apply GlobalTheory.EtaVal.exists_qkPt_span <;> assumption)
