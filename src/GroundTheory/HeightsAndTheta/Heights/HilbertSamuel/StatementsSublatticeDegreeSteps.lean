module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEuclideanSections
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
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

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def SublatticeExtension.Statement : Prop :=
  ∀ (E E' : Type) [AddCommGroup E] [AddCommGroup E'] (R R' : ℕ) (φ : E →+ EuclideanSpace ℝ (Fin R))
    (φ' : E' →+ EuclideanSpace ℝ (Fin R')) [DiscreteTopology (imageLattice φ)]
    [DiscreteTopology (imageLattice φ')] [IsZLattice ℝ (imageLattice φ')] (ψ : E' →+ E),
    Function.Injective φ → Function.Injective φ' → Function.Injective ψ → (∀ x, ‖φ (ψ x)‖ ≤ ‖φ' x‖) →
    ∃ Ψ : EuclideanSpace ℝ (Fin R') →ₗ[ℝ] EuclideanSpace ℝ (Fin R),
      (∀ x, Ψ (φ' x) = φ (ψ x)) ∧ (∀ y, ‖Ψ y‖ ≤ ‖y‖) ∧ Function.Injective Ψ

def SpanningExtension.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (ι : Type) [Fintype ι]
    (v : ι → V) (S : Set V), LinearIndependent ℝ v → Submodule.span ℝ S = ⊤ →
    ∃ w : Fin (Module.finrank ℝ V - Fintype.card ι) → V, (∀ j, w j ∈ S) ∧ LinearIndependent ℝ (Sum.elim v w)

def CovolumeLeGram.Statement : Prop :=
  ∀ (n : ℕ) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L]
    (ι : Type) [Fintype ι] [DecidableEq ι] (x : ι → EuclideanSpace ℝ (Fin n)), (∀ i, x i ∈ L) →
    LinearIndependent ℝ x → Fintype.card ι = n → ZLattice.covolume L ≤ Real.sqrt (Matrix.gram ℝ x).det

def GramContraction.Statement : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (Ψ : EuclideanSpace ℝ ι →ₗ[ℝ] V) (u : ι → EuclideanSpace ℝ ι) (w : κ → V),
    (∀ y, ‖Ψ y‖ ≤ ‖y‖) →
      (Matrix.gram ℝ (Sum.elim (Ψ ∘ u) w)).det ≤ (Matrix.gram ℝ u).det * ∏ j, ‖w j‖ ^ 2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
