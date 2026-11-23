module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCoverPrimes
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.hodge_comp_cover_primes : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (dg : ℕ) [Fintype (CMType H)], 𝔐.IsCover dg → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → (∀ p ∈ S, HT.HTFree 𝔐 p) → ∃ (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐' : HodgeCpt Y S M.y) (Fl : 𝔐'.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω) (i : Ω →+* M.Ω) (g : 𝔐'.X ⟶ 𝔐.X) (bk : K → M.K) (bx : ∀ k, J k ≃ M.ι (bk k)) (j : 𝔐.Li →+ 𝔐'.Li), Function.Injective bk ∧ (∀ k x, M.y ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐'.ξ 𝔐.ξ g i ∧ (∀ p ∈ S, HT.HTFree 𝔐' p) ∧ Fl.RootLines M.xdeg e ∧ (∀ (a : Ω) v, j (a • v) = i a • j v) ∧ (∀ (n : ℕ) (v : Fin n → 𝔐.Li), LinearIndependent Ω v → LinearIndependent M.Ω fun k => j (v k)) ∧ ∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ g j := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_primes | exact GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_primes | (intros; apply GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_primes <;> assumption)
