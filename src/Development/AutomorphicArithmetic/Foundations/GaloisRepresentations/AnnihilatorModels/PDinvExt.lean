module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DinvExact
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem mem_baseChange_iInf_ker_sub_id_of_baseChange_eq {F L X ι : Type} [Field F] [Field L] [Algebra F L]
    [AddCommGroup X] [Module F X] (A : ι → X →ₗ[F] X) (z : L ⊗[F] X)
    (hz : ∀ k, (A k).baseChange L z = z) :
    z ∈ (⨅ k, LinearMap.ker (A k - LinearMap.id)).baseChange L := by
  let b := Module.Free.chooseBasis F L
  let e : L ⊗[F] X ≃ₗ[F] (Module.Free.ChooseBasisIndex F L →₀ X) :=
    (TensorProduct.congr b.repr (LinearEquiv.refl F X)).trans (finsuppScalarLeft F X _)
  have nat : ∀ (f : X →ₗ[F] X) (w : L ⊗[F] X) j, e (f.baseChange L w) j = f (e w j) := by
    intro f w j
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [e, finsuppScalarLeft_apply_tmul_apply]
    | add u v hu hv => simp only [map_add (f := _), Finsupp.add_apply, hu, hv]
  have hmem : ∀ j, e z j ∈ ⨅ k, LinearMap.ker (A k - LinearMap.id) := by
    intro j
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    intro k
    have h := congrArg (fun w => e w j) (hz k)
    simpa only [nat] using h
  have hsingle : ∀ j (x : X), e.symm (Finsupp.single j x) = b j ⊗ₜ[F] x := by
    intro j x
    simp [e]
  have hz' : z = (e z).sum (fun j x => b j ⊗ₜ[F] x) := by
    conv_lhs => rw [← e.symm_apply_apply z, ← Finsupp.sum_single (e z)]

    simp only [Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => hsingle j _
  rw [hz']
  exact Submodule.sum_mem _ fun j _ => Submodule.tmul_mem_baseChange_of_mem _ (hmem j)

theorem UpperTheory.Gal.crystallineComparison.dinvExt_of :
    DinvExt := by
  unfold DinvExt
  intro F G B _ _ _ _ σ L _ _ V _ _ ρ
  let T : G → (V ⊗[F] B) →ₗ[F] (V ⊗[F] B) := fun g => AlgebraTensorModule.map (ρ g) (σ g)
  have hD : Dinv σ ρ = ⨅ g, LinearMap.ker (T g - LinearMap.id) := rfl
  have comm : ∀ g (w : (L ⊗[F] V) ⊗[F] B),
      AlgebraTensorModule.assoc F F L L V B (AlgebraTensorModule.map (extRep L ρ g) (σ g) w) =
        (T g).baseChange L (AlgebraTensorModule.assoc F F L L V B w) := by
    intro g w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul u c =>
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul a v => simp [T, extRep, AlgebraTensorModule.map_tmul]
      | add u₁ u₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add (f := _), h₁, h₂]
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
  ext z
  rw [Submodule.mem_map_equiv]
  constructor
  · intro hz
    rw [hD]
    apply mem_baseChange_iInf_ker_sub_id_of_baseChange_eq
    intro g
    have h : AlgebraTensorModule.map (extRep L ρ g) (σ g)
        ((AlgebraTensorModule.assoc F F L L V B).symm z) =
          (AlgebraTensorModule.assoc F F L L V B).symm z := by
      simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hz
      exact hz g
    have h2 := congrArg (AlgebraTensorModule.assoc F F L L V B) h
    rwa [comm, LinearEquiv.apply_symm_apply] at h2
  · intro hz
    simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro g
    apply (AlgebraTensorModule.assoc F F L L V B).injective
    rw [comm, LinearEquiv.apply_symm_apply]
    obtain ⟨w, rfl⟩ := hz
    have hfix : T g ∘ₗ (Dinv σ ρ).subtype = (Dinv σ ρ).subtype := by
      refine LinearMap.ext fun s => ?_
      have hs := s.2
      simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hs
      exact hs g
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hfix]
