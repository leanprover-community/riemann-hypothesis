module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NefOnFibresBlockXdegSumsOfRootLines
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.nefOnFibres_block_xdeg_sums_of_rootLines : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) [Fintype (CMType H)] (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → (∀ p ∈ S, HT.HTFree 𝔐 p) → (∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ discr E ∧ 4 * Fintype.card (CMType H) + 2 ≤ p ∧ 2 < p) → Fl.RootLines M.xdeg e → NefOnFibres (mCoordIdeal M.y) (∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin (D.p + D.q) => D.p ≤ (i : ℕ)), M.xdeg (τ, i)) ∧ NefOnFibres (mCoordIdeal M.y) (-∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin (D.p + D.q) => (i : ℕ) < D.p), M.xdeg (τ, i)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.nefOnFibres_block_xdeg_sums_of_rootLines | exact GlobalTheory.CompanionTheory.Relay.nefOnFibres_block_xdeg_sums_of_rootLines | (intros; apply GlobalTheory.CompanionTheory.Relay.nefOnFibres_block_xdeg_sums_of_rootLines <;> assumption)
