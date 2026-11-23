module

public import Mathlib.NumberTheory.NumberField.EquivReindex
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
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField NumberField.ComplexEmbedding GroundTheory.Heights₂.Heights.LowerBoundFree
  Module Matrix
open scoped Matrix ComplexConjugate Kronecker

section Tower

variable {Em : Type} [Field Em] [NumberField Em]

def towerZBasis {M : Type} [AddCommGroup M] [Module (𝓞 Em) M] {ρ : ℕ} {v : Fin ρ → M}
    (hv : LinearIndependent (𝓞 Em) v) :
    Basis (Fin ρ × (Em →+* ℂ)) ℤ (Submodule.span (𝓞 Em) (Set.range v)) :=
  ((RingOfIntegers.basis Em).smulTower' (Basis.span hv)).reindex
    (Equiv.prodCongr (Equiv.refl _) (equivReindex Em).symm)

theorem towerZBasis_apply {M : Type} [AddCommGroup M] [Module (𝓞 Em) M] {ρ : ℕ} {v : Fin ρ → M}
    (hv : LinearIndependent (𝓞 Em) v) (p : Fin ρ × (Em →+* ℂ)) :
    (towerZBasis hv p : M) = RingOfIntegers.basis Em (equivReindex Em p.2) • v p.1 := by
  simp [towerZBasis, Basis.smulTower'_apply, Basis.span_apply]


end Tower

namespace FullerData

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]
  (D : FullerData II Ψ K ι Ω E Em)



end FullerData

end GroundTheory.Heights₂.Heights.NineStatements
