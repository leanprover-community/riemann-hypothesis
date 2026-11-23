module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupHodgeTateFirstMapNatural
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.pDivGroup_hodgeTateFirstMap_natural : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G H : PDivGroup p O) (f : G ⟶ H), HasDatum hε G → HasDatum hε H → ∀ (M : Type) [AddCommGroup M] [Module O M] (r : latt G →ₛₗ[WittVector.fontaineTheta O p] M) (M' : Type) [AddCommGroup M'] [Module O M'] (r' : latt H →ₛₗ[WittVector.fontaineTheta O p] M') (u : M' →ₗ[O] M) (ι : G.omega →ₗ[O] M) (ι' : H.omega →ₗ[O] M'), Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = xi ε • n) → (∀ y, u (r' y) = r (lattMap f y)) → (∀ (χ : G.dual.Tate) (y : latt G), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) → ι (dlog G χ) = r y) → (∀ (χ : H.dual.Tate) (y : latt H), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε H t χ)) → ι' (dlog H χ) = r' y) → ∀ w, u (ι' w) = ι (omegaMap G H f w) := by
  first | exact @GlobalTheory.PDivLat.iota_natural | exact GlobalTheory.PDivLat.iota_natural | (intros; apply GlobalTheory.PDivLat.iota_natural <;> assumption)
