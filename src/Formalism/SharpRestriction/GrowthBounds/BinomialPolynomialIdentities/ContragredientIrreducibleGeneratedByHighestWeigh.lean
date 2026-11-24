module

public import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralEnvelopingPreservesSubmodule

@[expose] public section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

def lowWt {n : ℕ} (mu : Fin n → ℤ) : Fin n → ℤ := fun a => mu (Fin.rev a)

def ContragredientIrreducibleGeneratedByHighestWeight : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V) (v' : Module.Dual (KK O) V),
    IsIrrHW E mu v → IsHWV (dualOps E) (dualWt mu) v' → IsIrrHW (dualOps E) (dualWt mu) v'

def DualFunctionalInjectiveOnLowestWeightSpace : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V) (v' : Module.Dual (KK O) V),
    IsIrrHW E mu v → IsHWV (dualOps E) (dualWt mu) v' →
    (∀ x ∈ weightSp E (lowWt mu), v' x = 0 → x = 0) ∧ ∀ nu, nu ≠ lowWt mu → ∀ x ∈ weightSp E nu, v' x = 0

def LowestWeightExtremalVector : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V),
    IsIrrHW E mu v →
    ∃ w ∈ Delta (O := O) E v, w ∈ weightSp E (lowWt mu) ∧ ∃ u ∈ UZmon E, u w = v

def DeltaGeneratedByLowestWeightVector : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V) (v' : Module.Dual (KK O) V),
    IsIrrHW E mu v → IsHWV (dualOps E) (dualWt mu) v' →
    v' '' (Delta (O := O) E v : Set V) = Set.range (algebraMap O (KK O)) →
    ∃ x0 ∈ Delta (O := O) E v, x0 ∈ weightSp E (lowWt mu) ∧ v' x0 = 1 ∧
      Delta (O := O) E v = Submodule.span O {x | ∃ u ∈ UZmon E, x = u x0}

def DeltaFinitelyGenerated : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V) (v' : Module.Dual (KK O) V),
    IsIrrHW E mu v → IsHWV (dualOps E) (dualWt mu) v' →
    v' '' (Delta (O := O) E v : Set V) = Set.range (algebraMap O (KK O)) → (Delta (O := O) E v).FG

def NablaContragredientEqDualLatticeDelta : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V) (v' : Module.Dual (KK O) V),
    IsIrrHW E mu v → IsHWV (dualOps E) (dualWt mu) v' →
    v' '' (Delta (O := O) E v : Set V) = Set.range (algebraMap O (KK O)) →
    Nabla (O := O) (dualOps E) (dualWt mu) v' =
      {φ | ∀ x ∈ Delta (O := O) E v, φ x ∈ Set.range (algebraMap O (KK O))}

def LatticeBiduality : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (V : Type) [AddCommGroup V]
    [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V] (M : Submodule O V), M.FG →
    Submodule.span (KK O) (M : Set V) = ⊤ →
    (M : Set V) = {x | ∀ φ : Module.Dual (KK O) V, (∀ y ∈ M, φ y ∈ Set.range (algebraMap O (KK O))) →
      φ x ∈ Set.range (algebraMap O (KK O))}

end Formalism.MainNotions.G.ColumnFamilies
