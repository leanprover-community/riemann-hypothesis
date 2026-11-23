module

public import Formalism.LocalToGlobal.GlobalTheory.CoefficientMapSurjective
import Formalism.LocalToGlobal.GlobalTheory.GL4.PColFin
import Formalism.LocalToGlobal.GlobalTheory.GL4.PColStd
public import Formalism.LocalToGlobal.GlobalTheory.MemIffOfLocBasisG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Alg

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem actAll_one (lam : ι → DomWeight n) (p : MvPolynomial (ι × Fin n × Fin n) K) :
    Formalism.MainNotions.flipTwoThree.actAll lam (fun _ => (1 : Matrix (Fin n) (Fin n) K)) p = p := by
  unfold Formalism.MainNotions.flipTwoThree.actAll
  simp only [Matrix.det_one, _root_.one_zpow, Finset.prod_const_one, one_smul]
  have e : (fun v : ι × Fin n × Fin n =>
      ∑ b, MvPolynomial.C ((1 : Matrix (Fin n) (Fin n) K) b v.2.1) * MvPolynomial.X (v.1, b, v.2.2)) = MvPolynomial.X := by
    funext v
    rw [Finset.sum_eq_single v.2.1]
    · simp
    · intro b _ hb; simp [Matrix.one_apply_ne hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [e, MvPolynomial.aeval_X_left_apply]

def actL (lam : ι → DomWeight n) (g : ι → Matrix (Fin n) (Fin n) K) :
    MvPolynomial (ι × Fin n × Fin n) K →ₗ[K] MvPolynomial (ι × Fin n × Fin n) K :=
  (∏ τ, (g τ).det ^ (lam τ).detShift) •
    (MvPolynomial.aeval (fun v : ι × Fin n × Fin n =>
      ∑ b, MvPolynomial.C (g v.1 b v.2.1) * MvPolynomial.X (v.1, b, v.2.2))).toLinearMap

theorem actAll_inv_cancel (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (p : MvPolynomial (ι × Fin n × Fin n) K) :
    Formalism.MainNotions.flipTwoThree.actAll lam (fun τ => (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (Formalism.MainNotions.flipTwoThree.actAll lam (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p) = p := by
  rw [actAll_comp]
  simp only [← Units.val_mul, inv_mul_cancel, Units.val_one]
  exact actAll_one lam p

theorem actAll_cancel_inv (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (p : MvPolynomial (ι × Fin n × Fin n) K) :
    Formalism.MainNotions.flipTwoThree.actAll lam (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (Formalism.MainNotions.flipTwoThree.actAll lam (fun τ => (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p) = p := by
  rw [actAll_comp]
  simp only [← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact actAll_one lam p

theorem actAll_mem_TSpan [CharZero K] (lam : ι → DomWeight n) (h : ι → GL (Fin n) K)
    {p : MvPolynomial (ι × Fin n × Fin n) K} (hp : p ∈ Formalism.MainNotions.flipTwoThree.TSpan K lam) :
    Formalism.MainNotions.flipTwoThree.actAll lam (fun τ => ((h τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p ∈ Formalism.MainNotions.flipTwoThree.TSpan K lam := by
  rw [Formalism.L2.GlobalTheoryTheory.TraceIntegrality.translate_span_eq] at hp ⊢
  have h1 := Formalism.L2.GlobalTheoryTheory.TraceIntegrality.rhoEquiv_symm_coe lam h⁻¹ ⟨p, hp⟩
  have e : (fun τ => (((h⁻¹ τ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)⁻¹) =
      fun τ => ((h τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    funext τ
    rw [Pi.inv_apply, Matrix.coe_units_inv, Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnits_det_units (h τ))]
  rw [e] at h1
  rw [← h1]
  exact Submodule.coe_mem _

end Alg

variable {D : D7} {u : D.what₂.Word} (T : Forms0 D u)

def coT (g : (D.mem u).C.cls 0 → D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL) :
    ((D.fm u).lat 0).V →ₗ[D.what₂.LL] ((D.mem u).C.cls 0 → Pol0 D) :=
  LinearMap.pi fun c => (actL ((D.fm u).lam 0) (fun τ => ((g c τ : GL (Fin (D.R.N 0)) D.what₂.LL) :
    Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL))).comp ((LinearMap.proj c).comp (co0 T))

theorem coT_apply (g : (D.mem u).C.cls 0 → D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL) (x : ((D.fm u).lat 0).V)
    (c : (D.mem u).C.cls 0) :
    coT T g x c = Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0)
      (fun τ => ((g c τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)) (co0 T x c) := rfl

theorem coT_injective (g : (D.mem u).C.cls 0 → D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL) :
    Function.Injective (coT T g) := by
  intro x y h
  apply coefficient_map_injective T
  funext c
  have h1 := congrArg (fun F => Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0)
    (fun τ => (((g c τ)⁻¹ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)) (F c)) h
  simp only [coT_apply, actAll_inv_cancel] at h1
  exact h1

theorem coT_range (hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c))
    (g : (D.mem u).C.cls 0 → D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL) (F : (D.mem u).C.cls 0 → Pol0 D) :
    (∃ x, coT T g x = F) ↔ ∀ c, F c ∈ Formalism.MainNotions.flipTwoThree.TSpan D.what₂.LL ((D.fm u).lam 0) := by
  constructor
  · rintro ⟨x, rfl⟩ c
    rw [coT_apply]
    exact actAll_mem_TSpan _ _ (coefficient_map_mem_span T x c)
  · intro hF
    obtain ⟨x, hx⟩ := coefficient_map_surjective T hst (fun c => Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0)
      (fun τ => (((g c τ)⁻¹ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)) (F c))
      (fun c => actAll_mem_TSpan _ (fun τ => (g c τ)⁻¹) (hF c))
    refine ⟨x, funext fun c => ?_⟩
    rw [coT_apply, hx]
    exact actAll_cancel_inv _ _ _

end Formalism.L2.GlobalTheoryTheory.ColValS
