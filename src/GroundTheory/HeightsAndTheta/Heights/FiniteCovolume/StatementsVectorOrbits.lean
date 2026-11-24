module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Examples

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

section Units

variable (E : Type*) [Field E] [NumberField E]

def congruenceUnits (N : ℕ) : Subgroup (𝓞 E)ˣ :=
  (Units.map (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 E)})).toMonoidHom).ker

omit [NumberField E] in
variable {E} in
theorem mem_congruenceUnits {N : ℕ} {ε : (𝓞 E)ˣ} :
    ε ∈ congruenceUnits E N ↔ (ε : 𝓞 E) - 1 ∈ Ideal.span {(N : 𝓞 E)} := by
  rw [congruenceUnits, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, ← map_one (Ideal.Quotient.mk _),
    Ideal.Quotient.eq]

def CongruenceUnitsFiniteIndex.Statement : Prop :=
  ∀ N : ℕ, 0 < N → (congruenceUnits E N).index ≠ 0

end Units

section Groups

def BoundedIndexSubgroupsFinite.Statement (G : Type*) [AddCommGroup G] : Prop :=
  ∀ A B : AddSubgroup G, B.FG → A ≤ B → ∀ C : ℕ,
    {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C}.Finite

end Groups

section Spaces

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def IsotropicScaling.Statement (h : HermitianForm F E W) : Prop :=
  ∀ (La : AddSubgroup W) (x₀ : W), IsLattice E La → IsIntegralOn h La → x₀ ∈ La → x₀ ≠ 0 →
    h.toSesq x₀ x₀ = 0 → ∃ N : ℕ, 0 < N ∧ ∀ ε ∈ congruenceUnits E N,
      ∃ γ ∈ latticeStab h La, γ • x₀ = ((ε : 𝓞 E) : E) • x₀

end Spaces

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
