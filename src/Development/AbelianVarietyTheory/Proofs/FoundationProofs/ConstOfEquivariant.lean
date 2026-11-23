module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdxEqRelIndex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardMulCardOrth
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstOfGaussSign
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

noncomputable section

namespace GlobalTheory.EquivConst

theorem const_of_equivariant : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A A₁ : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → KLat D (tor0 D cc δ) A₁ → ∀ (u : VC D N N' ≃ₗ[ℂ] VC D N N'), (∀ z w, Hf D (tor0 D cc δ) (u z) (u w) = Hf D (tor0 D cc δ) z w) → (∀ x, x ∈ A ↔ u x ∈ A₁) → LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) ≠ 0 → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) → (∀ (b : 𝓞 D.host.E), ∀ x ∈ A, scal D N N' (b : D.host.E) x ∈ A) → (∀ (b : D.host.E) x, u (scal D N N' b x) = scal D N N' b (u x)) → ∀ th ∈ ThSp D (tor0 D cc δ) A, (fun z => th (u.symm z)) = (sgn D ((A.map (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')).toAddMonoidHom).relIndex A) * ((‖LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N'))‖ : ℂ) / LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')))) • Iop D (tor0 D cc δ) A A₁ th :=
  fun D => const_of_gaussSign D (GlobalTheory.HermGauss.gauss_sum_sign D)

end GlobalTheory.EquivConst
