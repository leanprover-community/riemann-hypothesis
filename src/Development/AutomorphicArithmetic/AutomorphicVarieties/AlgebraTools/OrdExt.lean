module

public import Mathlib.Algebra.MonoidAlgebra.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basis

@[expose] public section

open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.ord_ext :
    ∀ {R Γ E : Type} [CommRing R] [Monoid Γ] [Ring E] [Algebra R E] {n : ℕ} (r : Γ →* E) (ψ : Fin n → Γ →* R), (∀ g : Fin n → Γ, (List.ofFn fun i => r (g i) - algebraMap R E (ψ i (g i))).prod = 0) → ∀ z : Fin n → MonoidAlgebra R Γ, (List.ofFn fun i => MonoidAlgebra.lift R E Γ r (z i) - algebraMap R E (MonoidAlgebra.lift R R Γ (ψ i) (z i))).prod = 0 := by
  intro R Γ E _ _ _ _ n r ψ h z
  let φ : Fin n → (MonoidAlgebra R Γ →ₗ[R] E) := fun i =>
    (MonoidAlgebra.lift R E Γ r).toLinearMap -
      (Algebra.linearMap R E).comp (MonoidAlgebra.lift R R Γ (ψ i)).toLinearMap
  let F : (∀ _ : Fin n, MonoidAlgebra R Γ) →ₘₗ[R] E :=
    (MultilinearMap.mkPiAlgebraFin R n E).compLinearMap φ
  have hF : F = 0 := by
    refine Module.Basis.ext_multilinear (f := F) (g := 0)
      (fun _ => MonoidAlgebra.basis Γ R) ?_
    intro v
    simp only [F, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebraFin_apply,
      MultilinearMap.zero_apply, MonoidAlgebra.basis_apply]
    convert h v using 3
    funext i
    simp [φ, MonoidAlgebra.lift_single]
  have := congrArg (fun G => G z) hF
  simpa [F, φ] using this
