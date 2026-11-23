module

public import Formalism.HermitianLattices.StatementLat
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
import Formalism.PeriodIntegrals.UJClassFin
import Formalism.PeriodIntegrals.UJClassMass

@[expose] public section

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def CofinStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (L N : Submodule (𝓞 E) V),
    Submodule.IsFullLattice E L → Submodule.IsFullLattice E N →
    ∃ D : ℤ, D ≠ 0 ∧ (∀ v ∈ L, (D : 𝓞 E) • v ∈ N) ∧ (∀ v ∈ N, (D : 𝓞 E) • v ∈ L)

def LocGmapStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (u : V ≃ₗ[E] V) (p : Ideal (𝓞 E)) (L : Submodule (𝓞 E) V),
    loc (K := E) p (gmap u L) = gmap u (loc (K := E) p L)

end PI.UnitaryGroupMassFormula.UJClassMass

end
