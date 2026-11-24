module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets

namespace UpperTheory.ConvolutionTheory.Loc

section Alg

variable {E : Type} [Field E] {n : ℕ}

def sg (σ : E ≃+* E) : GL (Fin n) E →* GL (Fin n) E := GeneralLinearGroup.map (σ : E →+* E)

def nrm (σ : E ≃+* E) (q : ℕ) (δ : GL (Fin n) E) : GL (Fin n) E := ((List.range q).map fun i => (sg σ)^[i] δ).prod

end Alg

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

def Isom (σ : E ≃+* E) : Prop := ∀ x, valuation E (σ x) = valuation E x

structure Cyc (σ : E ≃+* E) (q : ℕ) : Prop where
  isom : Isom σ
  pos : 0 < q
  ord : ∀ x, σ^[q] x = x

structure Unram (σ : E ≃+* E) (q : ℕ) : Prop extends Cyc σ q where
  res : ∀ j, 0 < j → j < q → ∃ x, valuation E x ≤ 1 ∧ valuation E (σ^[j] x - x) = 1

def ball (n : ℕ) (r : ValueGroupWithZero E) : Set (GL (Fin n) E) :=
  {g | ∀ i j, valuation E ((g : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤ r}

def Strict (t : Fin n → Eˣ) : Prop := ∀ i j, i < j → valuation E (t i : E) < valuation E (t j : E)

def howeSet (n : ℕ) (ϖ : Eˣ) (a c : ℤ) : Set (GL (Fin n) E) :=
  {g | ∀ i j : Fin n, valuation E ((g : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤
    valuation E ((ϖ ^ (a + c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) : Eˣ) : E)}

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def howeSpace (π : Representation ℂ (GL (Fin n) E) V) (ψ : AddChar E Circle) (S : Set (GL (Fin n) E)) : Submodule ℂ V where
  carrier := {v | ∀ x ∈ S, π x v = (ψ (GlobalTheory.Whittaker.superDiag x) : ℂ) • v}
  add_mem' := by
    intro a b ha hb x hx
    rw [map_add (f := _), ha x hx, hb x hx, smul_add]
  zero_mem' := by intro x _; simp
  smul_mem' := by
    intro c v hv x hx
    rw [map_smul, hv x hx, smul_comm]

end UpperTheory.ConvolutionTheory.Loc

end
