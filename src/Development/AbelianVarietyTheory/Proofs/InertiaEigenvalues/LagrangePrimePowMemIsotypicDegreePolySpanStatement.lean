module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImageStableDegreeBounds
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RepresentationBounds
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangePrimePowMemIsotypicDegreePolySpan
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.lagrange_prime_pow_mem_isotypicDegreePoly_span : ∀ (l e a : ℕ) [Fact l.Prime], 1 ≤ a → e + 1 = l ^ a → ∀ (Sig : Finset (ZMod e)) (c : ZMod e) (A' N : ℕ), Sig.card ≤ N → 2 * A' + 2 < l → ∃ α β : Polynomial ℤ_[l], Polynomial.C ((l : ℤ_[l]) ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N) = α * (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A').map (Int.castRingHom ℤ_[l]) + β * (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₂ Sig c A').map (Int.castRingHom ℤ_[l]) := by
  first | exact @GlobalTheory.lagrange_C_rho_eq_comb_degrees | exact GlobalTheory.lagrange_C_rho_eq_comb_degrees | (intros; apply GlobalTheory.lagrange_C_rho_eq_comb_degrees <;> assumption)
