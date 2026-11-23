module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.weil_pairing_pullback : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (n : ℕ) (e : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ), GenWeil G L ξ n e → FullTorsion G ξ n → ∀ (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → FullTorsion G' ξ' n → ∀ (L' : LB G'.left) (e' : (Over.mk ξ' ⟶ G') → (Over.mk ξ' ⟶ G') → Ω'ˣ), GenWeil G' L' ξ' n e' → ∀ (y : Over.mk ξ ⟶ G) (y' : Over.mk ξ' ⟶ G'), y ^ n = 1 → y' ^ n = 1 → (∀ (g : Over.mk ξ ⟶ G) (g' : Over.mk ξ' ⟶ G'), g ^ n = 1 → g' ^ n = 1 → g'.left ≫ φ = spMap i ≫ g.left → (e' y' g' : Ω') = i (e y g)) → (∀ (g : Over.mk ξ ⟶ G), g ^ n = 1 → ∃ g' : Over.mk ξ' ⟶ G', g' ^ n = 1 ∧ g'.left ≫ φ = spMap i ≫ g.left) → (∀ (g' : Over.mk ξ' ⟶ G'), g' ^ n = 1 → ∃ g : Over.mk ξ ⟶ G, g ^ n = 1 ∧ g'.left ≫ φ = spMap i ≫ g.left) → ∀ (W : G.left.Opens) (s : Γ(G.left, W)),
  (∀ (k : Type) [Field k] [IsAlgClosed k] (τ : Ω →+* k) (xk g : Over.mk (spMap τ ≫ ξ) ⟶ G) (c : kˣ) (h : ⊤ ≤ g.left ⁻¹ᵁ W), xk.left = spMap τ ≫ y.left → g ^ n = 1 → Out.WeilIs G L n xk g (unitOn c) → secVal (B := k) g.left W h s = c) →
  (∀ (k : Type) [Field k] [IsAlgClosed k] (τ : Ω' →+* k) (xk g : Over.mk (spMap τ ≫ ξ') ⟶ G') (c : kˣ) (h : ⊤ ≤ g.left ⁻¹ᵁ (φ ⁻¹ᵁ W)), xk.left = spMap τ ≫ y'.left → g ^ n = 1 → Out.WeilIs G' L' n xk g (unitOn c) → secVal (B := k) g.left (φ ⁻¹ᵁ W) h (φ.app W s) = c) := by
  exact @GlobalTheory.CompanionTheory.Ar.HtTorPull.torsion_clause
