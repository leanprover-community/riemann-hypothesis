module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.SplitGL
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Commensurated

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists.BrB

open Matrix PI.UnitaryGroupMassFormula.AdIndexEq

def piHom {K R : Type} [Field K] [CommRing R] (σ : R →+* R) (p1 : R →+* K) : R →+* K × K :=
  RingHom.prod p1 (p1.comp σ)

theorem piHom_bijective {K R : Type} [Field K] [CommRing R] [Algebra K R] [FiniteDimensional K R]
    (hdim : Module.finrank K R = 2) (σ : R →+* R) (p1 : R →+* K)
    (hσK : ∀ c, σ (algebraMap K R c) = algebraMap K R c) (hσσ : ∀ r, σ (σ r) = r)
    (hp1K : ∀ c, p1 (algebraMap K R c) = c) (ε : R) (h1 : p1 ε = 1) (h0 : p1 (σ ε) = 0) :
    Function.Bijective (piHom σ p1) := by
  let L : R →ₗ[K] K × K :=
    { toFun := piHom σ p1
      map_add' := fun a b => map_add _ a b
      map_smul' := fun c r => by
        rw [Algebra.smul_def, map_mul]
        ext <;> simp [piHom, hp1K, hσK] }
  have hsurj : Function.Surjective L := by
    rintro ⟨a, b⟩
    refine ⟨algebraMap K R a * ε + algebraMap K R b * σ ε, ?_⟩
    ext <;> simp [L, piHom, hp1K, hσK, hσσ, h1, h0]
  have hfr : Module.finrank K R = Module.finrank K (K × K) := by
    rw [hdim, Module.finrank_prod, Module.finrank_self]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).2 hsurj, hsurj⟩

def piEquiv {K R : Type} [Field K] [CommRing R] (σ : R →+* R) (p1 : R →+* K)
    (hb : Function.Bijective (piHom σ p1)) : R ≃+* K × K :=
  RingEquiv.ofBijective (piHom σ p1) hb

theorem piEquiv_sig {K R : Type} [Field K] [CommRing R] (σ : R →+* R) (p1 : R →+* K)
    (hσσ : ∀ r, σ (σ r) = r) (hb : Function.Bijective (piHom σ p1)) (r : R) :
    piEquiv σ p1 hb (σ r) = (piEquiv σ p1 hb r).swap := by
  ext <;> simp [piEquiv, piHom, hσσ]

theorem proj_coe {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]
    (σ : R →+* R) (π : R ≃+* k × k) (J : Matrix n n R) (y : Formalism.UG.UJ σ J) :
    ((SplitGL.proj σ π J y : GL n k) : Matrix n n k) = ((y : GL n R) : Matrix n n R).map (SplitGL.p1 π) := rfl

theorem isUnit_det_first_projection {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]
    (π : R ≃+* k × k) (J : Matrix n n R) (hdet : IsUnit J.det) : IsUnit (J.map (SplitGL.p1 π)).det := by
  show IsUnit ((SplitGL.p1 π).mapMatrix J).det
  rw [← RingHom.map_det]
  exact hdet.map _

theorem second_projection_mulVec_eq {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]
    (σ : R →+* R) (π : R ≃+* k × k) (hπ : ∀ r, π (σ r) = (π r).swap) (J : Matrix n n R)
    (hdet : IsUnit J.det) (y : Formalism.UG.UJ σ J) (β β' : n → k)
    (h : β' ᵥ* J.map (SplitGL.p1 π) =
      (β ᵥ* J.map (SplitGL.p1 π)) ᵥ* (((SplitGL.proj σ π J y)⁻¹ : GL n k) : Matrix n n k)) :
    ((y : GL n R) : Matrix n n R).map (SplitGL.p2 π) *ᵥ β = β' := by
  set P := J.map (SplitGL.p1 π) with hP
  set M2 := ((y : GL n R) : Matrix n n R).map (SplitGL.p2 π) with hM2
  set T := SplitGL.proj σ π J y with hT
  have hu : M2ᵀ * P * (T : Matrix n n k) = P := by
    rw [hT, proj_coe]
    exact ((SplitGL.unitary_iff σ π hπ J _).1 y.2).1
  have hTT : (T : Matrix n n k) * ((T⁻¹ : GL n k) : Matrix n n k) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key : M2ᵀ * P = P * ((T⁻¹ : GL n k) : Matrix n n k) := by
    calc M2ᵀ * P = M2ᵀ * P * ((T : Matrix n n k) * ((T⁻¹ : GL n k) : Matrix n n k)) := by
          rw [hTT, Matrix.mul_one]
      _ = P * ((T⁻¹ : GL n k) : Matrix n n k) := by rw [← Matrix.mul_assoc, hu]
  have h2 : (M2 *ᵥ β) ᵥ* P = β' ᵥ* P := by
    calc (M2 *ᵥ β) ᵥ* P = (β ᵥ* M2ᵀ) ᵥ* P := by rw [Matrix.vecMul_transpose]
      _ = β ᵥ* (M2ᵀ * P) := by rw [Matrix.vecMul_vecMul]
      _ = β ᵥ* (P * ((T⁻¹ : GL n k) : Matrix n n k)) := by rw [key]
      _ = (β ᵥ* P) ᵥ* ((T⁻¹ : GL n k) : Matrix n n k) := by rw [Matrix.vecMul_vecMul]
      _ = β' ᵥ* P := h.symm
  have hPu : IsUnit P.det := isUnit_det_first_projection π J hdet
  have h3 := congrArg (fun w => w ᵥ* P⁻¹) h2
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hPu, Matrix.vecMul_one] at h3
  exact h3

end PI.UnitaryGroupMassFormula.ScXuExists.BrB
