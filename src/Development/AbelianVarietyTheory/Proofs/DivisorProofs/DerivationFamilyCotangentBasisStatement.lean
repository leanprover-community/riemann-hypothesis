module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationFamilyCotangentBasis
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.derivation_family_cotangent_basis : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra R A] (e : A →+* R), (∀ r, e (algebraMap R A r) = r) → Module.Free R (RingHom.ker e).Cotangent → Module.Finite R (RingHom.ker e).Cotangent → ∀ (n : ℕ) (dv : Fin n → A → R), (∀ a x y, dv a (x + y) = dv a x + dv a y) → (∀ a x y, dv a (x * y) = e x * dv a y + e y * dv a x) → (∀ a r, dv a (algebraMap R A r) = 0) → (∀ D : A → R, (∀ x y, D (x + y) = D x + D y) → (∀ x y, D (x * y) = e x * D y + e y * D x) → (∀ r, D (algebraMap R A r) = 0) → ∃! c : Fin n → R, ∀ x, D x = ∑ a, c a * dv a x) → ∃ z : Fin n → A, (∀ i, e (z i) = 0) ∧ (∀ a i, dv a (z i) = if a = i then 1 else 0) ∧ maximalIdeal A = (maximalIdeal R).map (algebraMap R A) ⊔ Ideal.span (Set.range z) := by
  first | exact @GlobalTheory.CoordsAlg.coords_of_derivation_basis | exact GlobalTheory.CoordsAlg.coords_of_derivation_basis | (intros; apply GlobalTheory.CoordsAlg.coords_of_derivation_basis <;> assumption)
