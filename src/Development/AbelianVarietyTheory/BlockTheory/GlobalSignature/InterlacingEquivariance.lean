module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.LocalToGlobal.Columns.CoefColLemmas
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

def brOne (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    MvPolynomial (Fin N × Fin N) K →ₗ[K] MvPolynomial (Fin n × Fin n) K :=
  (rename (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n)).toLinearMap ∘ₗ
    (VV K fun _ : Unit => sg).subtype ∘ₗ
      Br.brStdP (K := K) hN (fun _ : Unit => lam) (fun _ : Unit => sg) ∘ₗ
        (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N))).toLinearMap

theorem brOne_rename (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n)
    (G : VV K fun _ : Unit => lam) :
    brOne K hN lam sg (rename Prod.snd (G : Pol K Unit N)) =
      rename Prod.snd ((Br.brStd hN (fun _ : Unit => lam) (fun _ : Unit => sg) G : VV K fun _ : Unit => sg) : Pol K Unit n) := by
  have h : rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N))
      (rename Prod.snd (G : Pol K Unit N)) = (G : Pol K Unit N) := by
    rw [rename_rename]
    exact rename_id_apply _
  simp only [brOne, Br.brStd, LinearMap.comp_apply, AlgHom.toLinearMap_apply, h, Submodule.subtype_apply]

theorem interlace_iff {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    Br.Interlace hN lam sg ↔ Formalism.MainNotions.PrimeDegreeVariant.Interlace hN.symm lam sg := by
  refine forall_congr' fun i => ?_
  simp only [Br.aBr, Br.bBr, Br.iS, Br.iC]
  omega

def OnePlace : Prop :=
  ∀ (N n : ℕ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n),
    Br.Interlace hN lam sg → Br.SameShift lam sg →
      Formalism.MainNotions.PrimeDegreeVariant.IsBr hN.symm lam sg (brOne ℂ hN lam sg)

def Equivariance : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) → Br.BrEquiv K hN lam sg

def Integrality : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n), Br.BrIntegral K hN lam sg

def Members : Prop :=
  ∀ (X : Fields) (Word : Type) (R : Ranks) (W : Wts X Word R), W.Ok → ∀ (u : Word) (τ : X.Tau),
    Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) ∧ Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ)

def Tensor : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) → (∀ τ, Br.SameShift (lam τ) (sg τ)) →
    ∀ (f : ι → MvPolynomial (Fin N × Fin N) K) (G : VV K lam), (∀ τ, f τ ∈ nablaSq K N (lam τ)) → (G : Pol K ι N) = ten f →
      ((Br.brStd hN lam sg G : VV K sg) : Pol K ι n) = ten fun τ => brOne K hN (lam τ) (sg τ) (f τ)

theorem members_sameShift {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (hW : W.Ok) (u : Word) (τ : X.Tau) :
    Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ) :=
  (lamTrue_sgTrue_detShift W hW u τ).symm

end GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance
