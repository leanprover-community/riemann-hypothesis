module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealPullbackLocallyGenerated
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.ideal_pullback_locally_generated : ∀ (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₁] (t : Y₁ ⟶ Y₀) (I : Y₀.IdealSheafData) (y : Y₁) (U : Y₀.Opens) (hx : t y ∈ U) (n : ℕ) (b : Fin n → Γ(Y₀, U)), (∀ (k : Fin n) (W : Y₀.affineOpens) (h : W.1 ≤ U), resG Y₀ h (b k) ∈ I.ideal W) → (∀ (W : Y₀.affineOpens) (hxW : t y ∈ W.1) (a : Γ(Y₀, W.1)), a ∈ I.ideal W → Y₀.presheaf.germ W.1 (t y) hxW a ∈ Ideal.span (Set.range fun k => Y₀.presheaf.germ U (t y) hx (b k))) → ∀ (U' : Y₁.affineOpens) (f : Γ(Y₁, U'.1)) (hyU' : y ∈ U'.1), fnOf U'.1 (gen_mem hyU') f ≠ 0 → (I.comap t).ideal U' = Ideal.span {f} → ∀ (V : Y₁.Opens) (hV : V ≤ t ⁻¹ᵁ U) (hyV : y ∈ V), (∀ k, RegAt y (fnOf V (gen_mem hyV) (t.appLE U V hV (b k)) / fnOf U'.1 (gen_mem hyU') f)) ∧ ∃ k, UnitAt y (fnOf V (gen_mem hyV) (t.appLE U V hV (b k)) / fnOf U'.1 (gen_mem hyU') f) := by
  exact @_root_.GlobalTheory.IdealPull.regAt_and_unitAt_div_gen
