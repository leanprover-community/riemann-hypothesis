module

public import Formalism.WeaklyAdmissibleFiltrations.Statement
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace UpperTheory.Reformulated.B.Qh15

theorem aux1 : ∀ {A : Type} [inst : CommRing A], SMulCommClass A A A := by
  intro A _
  infer_instance

theorem aux2 : ∀ {G A : Type} [inst : Group G] [inst_1 : CommRing A] (κ : G →* Aˣ),
  (↑(κ 1) : A) • (LinearMap.id : A →ₗ[A] A) = 1 := by
  intro G A _ _ κ
  ext
  simp

theorem aux3 : ∀ {G A : Type} [inst : Group G] [inst_1 : CommRing A] (κ : G →* Aˣ)
  (g h : G), (↑(κ (g * h)) : A) • (LinearMap.id : A →ₗ[A] A) =
    ((↑(κ g) : A) • LinearMap.id) * ((↑(κ h) : A) • LinearMap.id) := by
  intro G A _ _ κ g h
  ext
  simp [mul_comm]

noncomputable def chRep : {G A : Type} →
  [inst : Group G] → [inst_1 : CommRing A] → (G →* Aˣ) → Representation A G A :=
  fun {G A} [Group G] [CommRing A] κ =>
    { toFun := fun g => ↑(κ g) • LinearMap.id, map_one' := aux2 κ,
      map_mul' := aux3 κ }

theorem act_mul : ∀ {G : Type} [inst : Group G] {Qp K₀ K : Type} [inst_1 : Field Qp]
  [inst_2 : Field K₀] [inst_3 : Field K] [inst_4 : Algebra Qp K₀] [inst_5 : Algebra Qp K] [inst_6 : Algebra K₀ K]
  [inst_7 : IsScalarTower Qp K₀ K] {B BdR : Type} [inst_8 : CommRing B] [inst_9 : CommRing BdR] [inst_10 : Algebra Qp B]
  [inst_11 : Algebra K₀ B] [inst_12 : IsScalarTower Qp K₀ B] [inst_13 : Algebra Qp BdR] [inst_14 : Algebra K₀ BdR]
  [inst_15 : Algebra K BdR] [inst_16 : IsScalarTower Qp K BdR] [inst_17 : IsScalarTower K₀ K BdR]
  [inst_18 : IsScalarTower Qp K₀ BdR] (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {E : Type}
  [inst_19 : Field E] [inst_20 : Algebra Qp E] (κ : G →* Eˣ) (g : G) (x y : TensorProduct Qp E B),
  (Formalism.WeaklyAdmissibleFiltrations.actVB PD (chRep κ) g) x *
      (Formalism.WeaklyAdmissibleFiltrations.actVB PD (chRep κ⁻¹) g) y =
    (Formalism.WeaklyAdmissibleFiltrations.actVB PD (chRep 1) g) (x * y) := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD E _ _ κ g x y
  have hch : ∀ (μ : G →* Eˣ) (a : E), chRep μ g a = (μ g : E) * a :=
    fun μ a => rfl
  have hact : ∀ (μ : G →* Eˣ) (a : E) (b : B),
      Formalism.WeaklyAdmissibleFiltrations.actVB PD (chRep μ) g (a ⊗ₜ[Qp] b) =
        ((μ g : E) * a) ⊗ₜ[Qp] PD.actB g b := by
    intro μ a b
    rw [← hch]
    rfl
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, zero_mul]
  | add x₁ x₂ h₁ h₂ => simp only [map_add (f := _), add_mul, h₁, h₂]
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero]
    | add y₁ y₂ h₁ h₂ => simp only [map_add (f := _), mul_add, h₁, h₂]
    | tmul c d =>
      have hu : (κ g : E) * a * ((κ⁻¹ g : E) * c) = ((1 : G →* Eˣ) g : E) * (a * c) := by
        rw [mul_mul_mul_comm, ← Units.val_mul, MonoidHom.inv_apply, mul_inv_cancel,
          MonoidHom.one_apply]
      rw [Algebra.TensorProduct.tmul_mul_tmul, hact, hact, hact,
        Algebra.TensorProduct.tmul_mul_tmul, hu, map_mul]

end UpperTheory.Reformulated.B.Qh15
