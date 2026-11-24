module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.IsCMUnram
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.IsUnimodular
public import Mathlib.Algebra.Module.Lattice.Basic
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

noncomputable section

namespace HcS.BasicNotions

open NumberField IsDedekindDomain
open scoped TensorProduct

structure CMData (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] : Prop where
  cmUnram : HcS.HermitianLatticesTheory.IsCMUnram E
  totReal : NumberField.IsTotallyReal F
  deg2 : Module.finrank F E = 2
  fixed : ∀ a : E, star a = a ↔ a ∈ (algebraMap F E).range

def CMData.sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : CMData F E) : E →ₐ[F] E :=
  { starRingEnd E with
    commutes' := fun a => (hc.fixed (algebraMap F E a)).2 ⟨a, rfl⟩ }

structure HSpace (E : Type) [Field E] [NumberField E] [StarRing E] where
  V : Type
  [acg : AddCommGroup V]
  [modE : Module E V]
  [modO : Module (𝓞 E) V]
  [tower : IsScalarTower (𝓞 E) E V]
  [fd : FiniteDimensional E V]

  hT : V →ₗ⋆[E] V →ₗ[E] E
  herm : hT.IsSymm
  nondeg : hT.Nondegenerate
  rank : ℕ
  rank_eq : Module.finrank E V = rank

  frame : Module.Basis (Fin rank) E V

  sig : (E →+* ℂ) → ℕ × ℕ

  L0 : Submodule (𝓞 E) V
  standardTuple_isLattice : Submodule.IsLattice E L0
  baseLattice_isUnimodular : HcS.HermitianLatticesTheory.IsUnimodular hT L0

attribute [instance] HSpace.acg HSpace.modE HSpace.modO HSpace.tower HSpace.fd

namespace HSpace

variable {E : Type} [Field E] [NumberField E] [StarRing E]

end HSpace

namespace Spaces

end Spaces

end HcS.BasicNotions

end
