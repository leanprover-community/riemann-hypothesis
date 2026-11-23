module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOrthogonalIdempotentsHeckeSpanRep
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.exists_orthogonal_idempotents_heckeSpan_rep : ∀ (l : ℕ) [Fact l.Prime] {Γ X A : Type} [Group Γ] [Finite X] [CommRing A] [IsDomain A] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A] {n r t : ℕ} (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (π : X) (e : (Fin n → FractionRing A) ≃ₗ[FractionRing A] ((Fin r → FractionRing A) × (Fin t → FractionRing A))), 2 ≤ r → Submodule.span A (Set.range (mat ρ)) = ⊤ → IsDecomp (t := t) (rep π) ρ χ e → ∃ eB e1 : X → Matrix (Fin n) (Fin n) A, (InRing T rep eB ∧ InRing T rep e1 ∧ eB * eB = eB ∧ e1 * e1 = e1 ∧ eB * e1 = 0 ∧ e1 * eB = 0) ∧ (∀ u, e (((eB π).map (toFr A)).mulVec u) = (0, (e u).2)) ∧ ∃ ε : Matrix (Fin r) (Fin r) (FractionRing A), ε.rank = 1 ∧ ∀ u, e (((e1 π).map (toFr A)).mulVec u) = (ε.mulVec (e u).1, 0) := by
  first | exact @GlobalTheory.SpanIdem.exists_orthogonal_idempotents | exact GlobalTheory.SpanIdem.exists_orthogonal_idempotents | (intros; apply GlobalTheory.SpanIdem.exists_orthogonal_idempotents <;> assumption)
