module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChangeOfModel
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
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

section Objects

variable {K : Type} {ι : K → Type}

def oldV (N : ℕ) : (Σ k, ι k) → (Σ k, addIdx ι N k) := fun p => ⟨some p.1, p.2⟩

theorem isBlockMap_oldV (N : ℕ) :
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap (ι := ι) (ι' := addIdx ι N) some (oldV N) := by
  refine ⟨Option.some_injective K, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, i⟩ ⟨k', i'⟩ h
    have h1 : k = k' := Option.some_injective K (congrArg Sigma.fst h)
    subst h1
    have h2 : i = i' := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    rw [h2]
  · rintro ⟨_ | k, i⟩ ⟨k', hk'⟩
    · exact absurd hk' (Option.some_ne_none k')
    · exact ⟨⟨k, i⟩, rfl⟩

end Objects

def AddBlockIsometric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (m N : ℕ) (v : Fin N → Ω) (B L : HermLine (addIdx ι N)),
    IsArithVar (mCoordIdeal y) (D + 1) → 1 ≤ m →
    (∀ j, v j ∈ chartLat y A.a m) → KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v →
    B.a = unitDeg (none : Option K) →
    L.a = ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg some (fun k => (m : ℤ) * A.a k) →
    (∀ z, L.h z = A.h (basePart₂ z) ^ m) →
    (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin N,
      secNormAt y A m (v j) (basePart₂ z) * B.h z = ‖z ⟨none, j⟩‖) →
    IsIsometricOn (mCoordIdeal (addBlock y v)) B L

namespace PowerBlockProjectiveLine

open ProjLine

end PowerBlockProjectiveLine

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
