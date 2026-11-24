module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBlockAction
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.exists_block_action_of_decomposition : ∀ {Γ X O : Type} [Group Γ] [CommRing O] [IsDomain O] {n r t : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)) (ρ : Γ →* GL (Fin r) O) (χ : ℕ → (Γ →* Oˣ)) (π : X) (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))), Submodule.span O (Set.range (mat ρ)) = ⊤ → IsDecomp (t := t) (rep π) ρ χ e → ∃ (ψρ : (X → Matrix (Fin n) (Fin n) O) → Matrix (Fin r) (Fin r) O) (ψχ : Fin t → (X → Matrix (Fin n) (Fin n) O) → O), (∀ a, InRing T rep a → ∀ u, e (((a π).map (toFr O)).mulVec u) = (((ψρ a).map (toFr O)).mulVec (e u).1, fun c : Fin t => toFr O (ψχ c a) * (e u).2 c)) ∧ ∀ P : Matrix (Fin r) (Fin r) O, ∃ a, InRing T rep a ∧ ψρ a = P := by
  first | exact @GlobalTheory.SpanBlockAction.exists_block_action | exact GlobalTheory.SpanBlockAction.exists_block_action | (intros; apply GlobalTheory.SpanBlockAction.exists_block_action <;> assumption)
