module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.FractionRing
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

def TorsionFreeQuotientLength.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R], ringKrullDim R = 1 →
    ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] (r : ℕ),
      Module.rank R M = r → ∀ a : R, a ≠ 0 →
        Module.length R (M ⧸ (Ideal.span {a} • ⊤ : Submodule R M)) ≤
          (r : ℕ∞) * Module.length R (R ⧸ Ideal.span {a})

def KrullAkizukiQuotientLength.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R], ringKrullDim R = 1 →
    ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
      (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra R L]
      [IsScalarTower R K L] (S : Subalgebra R L) (b : R), b ≠ 0 →
        IsFiniteLength R (S ⧸ Ideal.span {algebraMap R S b})

end GroundTheory.Heights₂.Heights.Model
