module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentIntegralAtPrimeInS
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

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem _root_.GlobalTheory.T.hodge_component_integral_at_prime_in_S : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → ∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (w : Module.Dual Ω 𝔐.Li), (∀ q, InChart 𝔐.ξ (mseg y) s.1 q → InChart 𝔐.ξ (mseg y) t.1 q → OverZp 𝔐 p q → w ∈ 𝔐.M.omLat q) → ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • w ∈ (Dc t).om := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.pow_smul_mem_om_of_overlap | exact GlobalTheory.CompanionTheory.Ar.HT.pow_smul_mem_om_of_overlap | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.pow_smul_mem_om_of_overlap <;> assumption)
