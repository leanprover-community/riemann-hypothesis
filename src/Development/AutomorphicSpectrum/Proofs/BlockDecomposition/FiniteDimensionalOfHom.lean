module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc

@[expose] public section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.HomTrace

theorem finiteDimensional_of_hom (W H : Type) [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] [Nontrivial W] [FiniteDimensional ℂ (W →ₗ[ℂ] H)] :
    FiniteDimensional ℂ H := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have hex : ∃ φ : Module.Dual ℂ W, φ w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).1 hcon)
  obtain ⟨φ, hφ⟩ := hex
  let j : H →ₗ[ℂ] (W →ₗ[ℂ] H) :=
    { toFun := fun h => φ.smulRight h
      map_add' := fun x y => by ext v; simp
      map_smul' := fun c x => by
        ext v
        simp only [LinearMap.smulRight_apply, LinearMap.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }
  have hj : Function.Injective j := by
    intro x y hxy
    have h1 : φ w • x = φ w • y := by
      simpa [j] using LinearMap.congr_fun hxy w
    exact smul_right_injective H hφ h1
  exact FiniteDimensional.of_injective j hj

noncomputable def sandwich {W H : Type} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] (a : H →ₗ[ℂ] H) (b : W →ₗ[ℂ] W) :
    (W →ₗ[ℂ] H) →ₗ[ℂ] (W →ₗ[ℂ] H) where
  toFun f := a ∘ₗ f ∘ₗ b
  map_add' f g := by ext v; simp
  map_smul' c f := by ext v; simp

theorem trace_sandwich {W H : Type} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] [FiniteDimensional ℂ W] [FiniteDimensional ℂ H]
    (a : H →ₗ[ℂ] H) (b : W →ₗ[ℂ] W) :
    LinearMap.trace ℂ (W →ₗ[ℂ] H) (sandwich a b) =
      LinearMap.trace ℂ W b * LinearMap.trace ℂ H a := by
  let e := dualTensorHomEquiv ℂ W H
  let M : (TensorProduct ℂ (Module.Dual ℂ W) H) →ₗ[ℂ] (TensorProduct ℂ (Module.Dual ℂ W) H) :=
    TensorProduct.map (Module.Dual.transpose (R := ℂ) b) a
  have hcomp : (e : _ →ₗ[ℂ] _) ∘ₗ M = sandwich a b ∘ₗ (e : _ →ₗ[ℂ] _) := by
    apply TensorProduct.ext'
    intro φ h
    ext v
    simp [e, M, sandwich, dualTensorHomEquiv, dualTensorHomEquivOfBasis_apply, dualTensorHom_apply,
      Module.Dual.transpose_apply]
  have hconj : e.conj M = sandwich a b := by
    rw [LinearEquiv.conj_apply]
    ext1 f
    have := LinearMap.congr_fun hcomp (e.symm f)
    simpa using this
  rw [← hconj, LinearMap.trace_conj', LinearMap.trace_tensorProduct', LinearMap.trace_transpose']

end GlobalTheory.CompanionTheory.HomTrace
