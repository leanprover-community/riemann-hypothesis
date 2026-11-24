module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelMoveModuliUniqueUniversalTriple
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
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem _root_.GlobalTheory.T.levelMove_moduli_unique_universalTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (ρ ρ' : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ν' : SABMap Xo.univ.t Xo.univ.t ρ') (gM gM' gA gA' : Dw.La →ₗ[𝓞 E] Dw.La), 1 ≤ Dw.p + Dw.q → (∀ a, gM a - gM' a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ a, Dw.ModN l.A (gA a - gA' a)) → IsIso ρ → IsIso ρ' → IsLevMove ρ ν gM gA → IsLevMove ρ' ν' gM' gA' → (∃ g : Sim Dw, (∀ a, g.f l.M a - gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ (∀ a, Dw.ModN l.A (g.f l.A a - gA a)) ∧ (l.A : ℤ) ∣ g.ν l.A - 1) → ρ = ρ' ∧ ν.φ = ν'.φ := by
  first | exact @GlobalTheory.levMove_unique | exact GlobalTheory.levMove_unique | (intros; apply GlobalTheory.levMove_unique <;> assumption)
