module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantOrbitOfInvPowCharacter
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.isLocallyConstant_orbit_of_inv_pow_character' : ∀ {p : ℕ} {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ),
    (∀ N : ℕ, IsLocallyConstant (fun g : G => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g : Oˣ) : O))) →
    ∀ (e : ℕ) {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M),
    (∀ g m, ρ g m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) → ∀ (m : M) (N : ℕ), (p : O) ^ N • m = 0 →
    IsLocallyConstant (fun g => ρ g m) := by
  first | exact @GlobalTheory.ShapeNeg.isLocallyConstant_orbit_of_inv_pow_character | exact GlobalTheory.ShapeNeg.isLocallyConstant_orbit_of_inv_pow_character | (intros; apply GlobalTheory.ShapeNeg.isLocallyConstant_orbit_of_inv_pow_character <;> assumption)
