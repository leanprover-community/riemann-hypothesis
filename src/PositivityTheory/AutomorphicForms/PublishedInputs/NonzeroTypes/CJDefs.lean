module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

variable {n : ℕ} (G : Grp k n)

def HasEtaVec {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) W) :
    Prop :=
  ∃ y : W, y ≠ 0 ∧ ∀ m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a)), ρ m y = G.eta m • y

def JacquetModuleFiniteProp : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → IsSmooth (jacU G.e π) ∧ HasFiniteLength (jacU G.e π)

def SubquotientProp : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) W),
    IsSmooth ρ → HasFiniteLength ρ → G.HasEtaVec ρ →
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Module ℂ X) (σ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) X),
      IsSmooth σ ∧ σ.IsIrreducible ∧ IsSubquotient σ ρ ∧ G.HasEtaVec σ

def TensorProductProp : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) X),
    IsSmooth σ → σ.IsIrreducible → G.HasEtaVec σ →
    ∃ (Y : Fin G.s → Type) (_ : ∀ a, AddCommGroup (Y a)) (_ : ∀ a, Module ℂ (Y a))
      (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
      (∀ a, IsSmooth (τ a)) ∧ (∀ a, (τ a).IsIrreducible) ∧ (∀ a, HasDetVec (τ a) (G.μ a)) ∧
        Nonempty (σ.Equiv (piTensor τ))

def SupportOfProductProp : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible →
    ∀ (Y : Fin G.s → Type) [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
      (∀ a, IsSmooth (τ a)) → (∀ a, (τ a).IsIrreducible) → (∀ a, HasDetVec (τ a) (G.μ a)) →
      IsSubquotient (piTensor τ) (jacU G.e π) → IsTwSphProd π G.d G.hd G.μ

def ExistsGroupElementProp : Prop :=
  ∀ (n : ℕ) (χ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (χ i)) →
    ∃ (G : Grp k n) (σ : Equiv.Perm (Fin n)), ∀ i, res (χ (σ i)) = res (G.chi i)

end Grp

end UpperTheory.TNZ
