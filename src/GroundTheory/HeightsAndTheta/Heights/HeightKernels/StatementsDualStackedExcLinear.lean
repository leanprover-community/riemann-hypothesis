module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExc
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

def linPointMap {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k) :
    MRing (stackedBlocks T) →+* MvPolynomial (Option (Fin n)) k :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl _, t⟩ => C (α t) * X none
    | ⟨.inr _, t⟩ => ∑ j, C (M t j) * X (some j)

def linPrime {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k) :
    Ideal (MRing (stackedBlocks T)) :=
  RingHom.ker (linPointMap α M)

def LinFormsIndep {T : Type} {k : Type} [Field k] {n : ℕ} (M : T → Fin n → k) : Prop :=
  ∀ w : Fin n → k, (∀ t, ∑ j, M t j * w j = 0) → w = 0

def DualStackedExcLinear.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ E : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a E →
      ∃ (k : Type) (_ : Field k) (_ : Fintype k) (α : T → k) (M : T → Fin i → k),
        Submodule.span ℤ (Set.range α) = ⊤ ∧ LinFormsIndep M ∧ E = linPrime α M ∧
          Fintype.card k = F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup

def LinPrimeCut.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (k : Type) [Field k] (n : ℕ) (α : T → k) (M : T → Fin (n + 2) → k),
    Submodule.span ℤ (Set.range α) = ⊤ → LinFormsIndep M →
    ∀ c : T, graphSecond c ∉ linPrime α M →
      ∃ M' : T → Fin (n + 1) → k, LinFormsIndep M' ∧
        divSupp (linPrime α M) (graphSecond c) = {linPrime α M'} ∧
        multAt (linPrime α M ⊔ Ideal.span {graphSecond c}) (linPrime α M') = 1

def LinPrimeBase.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (k : Type) [Field k] (α : T → k) (M : T → Fin 1 → k),
    Submodule.span ℤ (Set.range α) = ⊤ → LinFormsIndep M →
    ∀ c : (κ : Unit ⊕ Unit) → stackedBlocks T κ,
      (∀ κ, (X ⟨κ, c κ⟩ : MRing (stackedBlocks T)) ∉ linPrime α M) →
      Nonempty ((MRing (stackedBlocks T) ⧸ (linPrime α M ⊔
        Ideal.span (Set.range fun κ => (X ⟨κ, c κ⟩ : MRing (stackedBlocks T)) - 1))) ≃+* k)

namespace LinPrimeExample

theorem linPointMap_first {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k)
    (t : T) : linPointMap α M (graphFirst t) = C (α t) * X none := by
  simp [linPointMap, graphFirst]

theorem linPointMap_second {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k)
    (t : T) : linPointMap α M (graphSecond t) = ∑ j, C (M t j) * X (some j) := by
  simp [linPointMap, graphSecond]

end LinPrimeExample

end

end GroundTheory.Heights₂.Heights
