module

public import Mathlib
public import GroundTheory.PAdicHodge.TiltMap
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

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

section Functor

variable {K L M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [IsUltrametricDist L] [NontriviallyNormedField M] [IsUltrametricDist M]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField L p]
  [IsPerfectoidField M p]
omit [IsUltrametricDist K] [IsUltrametricDist L] [IsUltrametricDist M] in
theorem norm_comp_eq {φ : K →+* L} (hφ : ∀ x, ‖φ x‖ = ‖x‖) {ψ : L →+* M}
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (x : K) : ‖(ψ.comp φ) x‖ = ‖x‖ := by
  rw [RingHom.comp_apply, hψ, hφ]

variable (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (ψ : L →+* M) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)

theorem preTiltMap_comp :
    preTiltMap (p := p) (ψ.comp φ) (norm_comp_eq hφ hψ) =
      (preTiltMap (p := p) ψ hψ).comp (preTiltMap (p := p) φ hφ) := by
  refine RingHom.ext fun x => Perfection.ext fun n => ?_
  rw [RingHom.comp_apply, coeff_preTiltMap, coeff_preTiltMap, coeff_preTiltMap]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (Perfection.coeff (ModP (normInteger K) p) p n x)
  rw [← ha, modPMap_mk, modPMap_mk, modPMap_mk]
  rfl

end Functor


variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]




variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]



variable {K C : Type*} [NontriviallyNormedField K] [NormedField C] [NormedAlgebra K C]



variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

variable (F : IntermediateField K C) [IsPerfectoidField F p]





end GroundTheory.PAdicHodge
