module

public import Formalism.CoboundaryTransfers.Statement
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Formalism.CoboundaryTransfers.GammaStableTransfers.DiffOneSmulOfTower
public import Formalism.CoboundaryTransfers.GammaStableTransfers.TorsionKilledCriterionHolds
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

namespace Formalism.CoboundaryTransfers

theorem lift_wach (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (S : SES W₀ W₁ W₂)
    (e : ℕ) (hW : CokerKilled S e) (hQ : RatSurj S)
    (δ : D₀ →ₗ[O] D₀) (R : Polynomial O) (a k : ℕ) (u : O)
    (hk : B.PhiX k) (ha : M ≤ k * (a + 1))
    (hδ : ∀ y, B.X • δ y = W₀.γ y - y)
    (hR : ∀ y, W₀.QInv y → Polynomial.aeval δ (Polynomial.X * R) y ∈ W₀.N)
    (hZ : ∀ y, W₀.QInv y → (B.p : O) • y ∈ W₀.N → y ∈ W₀.N)
    (hZu : ∀ y, W₀.QInv y → (∏ i ∈ Finset.Icc 1 a, (1 - u ^ i)) • y ∈ W₀.N → y ∈ W₀.N)
    (hgr : ∀ i, 1 ≤ i → i ≤ a → ∀ n ∈ W₀.N, ∃ n' ∈ W₀.N,
      W₀.γ (B.X ^ i • n) = u ^ i • (B.X ^ i • n) + B.X ^ (i + 1) • n')
    (hφ : ∀ n ∈ W₀.N, ∃ z ∈ W₀.N,
      B.X ^ (a + 1) • n = B.X ^ (a + 1) • z - W₀.φ (B.X ^ (a + 1) • z)) :
    Lifts S ((B.p : O) ^ e * (R.eval 0 * ∏ i ∈ Finset.Icc 1 a, (1 - u ^ i))) :=
  cocycleLiftOfExact_holds O A B M D₀ D₁ D₂ W₀ W₁ W₂ S e _ hW hQ
    (torsionKilledCriterion_holds O A B M D₀ W₀ δ R a k _ hk ha hδ hR hZ hZu
      (gammaImageProduct_holds O A B M D₀ W₀ u a hgr) hφ)

end Formalism.CoboundaryTransfers
