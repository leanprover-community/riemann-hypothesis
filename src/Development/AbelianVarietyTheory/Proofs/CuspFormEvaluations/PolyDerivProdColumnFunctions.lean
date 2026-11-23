module

public import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PolyDerivMonomialOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndSt
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

open scoped ContDiff

theorem filter_col_toMultiset {T : Type} [Fintype T] {r : T → ℕ} {n : ℕ}
    (m : Formalism.L2.Pj.Letter T r n →₀ ℕ) (b : Fin n) :
    (Finsupp.toMultiset m).filter (fun ℓ => ℓ.2.2 = b) =
      (Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm
        fun ℓ : (Σ τ : T, Fin (r τ)) => m ⟨ℓ.1, ℓ.2, b⟩)).map
        (fun ℓ : (Σ τ : T, Fin (r τ)) => (⟨ℓ.1, ℓ.2, b⟩ : Formalism.L2.Pj.Letter T r n)) := by
  classical
  have hinj : Function.Injective
      (fun ℓ : (Σ τ : T, Fin (r τ)) => (⟨ℓ.1, ℓ.2, b⟩ : Formalism.L2.Pj.Letter T r n)) := by
    intro x y h
    exact congrArg (fun ℓ : Formalism.L2.Pj.Letter T r n => (⟨ℓ.1, ℓ.2.1⟩ : Σ τ : T, Fin (r τ))) h
  ext ⟨τ, i, c⟩
  rw [Multiset.count_filter]
  by_cases h : c = b
  · subst h
    rw [if_pos rfl]
    have := Multiset.count_map_eq_count' _ (Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm
        fun ℓ : (Σ τ : T, Fin (r τ)) => m ⟨ℓ.1, ℓ.2, c⟩)) hinj ⟨τ, i⟩
    rw [this]
    simp [Finsupp.count_toMultiset]
  · rw [if_neg h]
    symm
    rw [Multiset.count_eq_zero, Multiset.mem_map]
    rintro ⟨x, -, hx⟩
    exact h (congrArg (fun ℓ : Formalism.L2.Pj.Letter T r n => ℓ.2.2) hx).symm

theorem polyDeriv_prod_cols : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (T : Type) [Fintype T] (r : T → ℕ) (n : ℕ) (u : (Σ τ : T, Fin (r τ)) → V) (θ : Fin n → V → ℂ), (∀ b, Differentiable ℂ (θ b)) → ∀ P : MvPolynomial (Formalism.L2.Pj.Letter T r n) ℂ, I2.polyDeriv P (fun ℓ => (Pi.single ℓ.2.2 (u ⟨ℓ.1, ℓ.2.1⟩) : Fin n → V)) (fun z => ∏ b, θ b (z b)) 0 = ∑ m ∈ P.support, P.coeff m * ∏ b, I2.polyDeriv (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun ℓ : (Σ τ : T, Fin (r τ)) => m ⟨ℓ.1, ℓ.2, b⟩) (1 : ℂ)) u (θ b) 0 := by
  intro V _ _ _ T _ r n u θ hθ P
  classical
  have hω : ∀ b x, ContDiffAt ℂ ω (θ b) x := fun b x =>
    GlobalTheory.SCV.contDiffAt_of_differentiableOn (hθ b).differentiableOn Filter.univ_mem ω
  have hs : ∀ b, ContDiff ℂ (⊤ : ℕ∞) (θ b) := fun b =>
    contDiff_iff_contDiffAt.2 fun x => (hω b x).of_le le_top
  rw [I2.polyDeriv_eq_of_subset P _ _ _ (Finset.Subset.refl _)]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  rw [I2.pdTerm_eq_itD]
  have e : (Finsupp.toMultiset m).toList.map
      (fun ℓ : Formalism.L2.Pj.Letter T r n => (Pi.single ℓ.2.2 (u ⟨ℓ.1, ℓ.2.1⟩) : Fin n → V)) =
      ((Finsupp.toMultiset m).toList.map
        (fun ℓ : Formalism.L2.Pj.Letter T r n => ((ℓ.2.2, u ⟨ℓ.1, ℓ.2.1⟩) : Fin n × V))).map
        (fun p => Pi.single p.1 p.2) := by
    rw [List.map_map]; rfl
  rw [e, I2.itD_prod hs]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [I2.polyDeriv_monomial_one, I2.pdTerm_eq_itD]
  refine lD_perm (hω b 0) ?_
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe u, Multiset.coe_toList]
  have h := congrArg (Multiset.map fun ℓ : Formalism.L2.Pj.Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩)
    (filter_col_toMultiset m b)
  rw [Multiset.map_map] at h
  refine Eq.trans ?_ h
  conv_rhs => rw [← Multiset.coe_toList (Finsupp.toMultiset m)]
  rw [Multiset.filter_coe, Multiset.map_coe]
  unfold I2.colL
  rw [List.filter_map, List.map_map]
  rfl

end GlobalTheory.AnVal
