module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.InertUnitOrb

open GlobalTheory.UnitLemma

def intVec (K : UQ) (n : ℕ) : Submodule K.O (Fin n → K.E) where
  carrier := {v | ∀ i, v i ∈ (algebraMap K.O K.E).range}
  add_mem' := fun ha hb i => Subring.add_mem _ (ha i) (hb i)
  zero_mem' := fun _ => Subring.zero_mem _
  smul_mem' := fun c v hv i => by
    simp only [Pi.smul_apply, Algebra.smul_def]
    exact Subring.mul_mem _ ⟨c, rfl⟩ (hv i)

def modelLat {K : UQ} (B : InvAlg K) {n : ℕ} (ψ : B.A ≃ₗ[K.E] (Fin n → K.E))
    (P : Matrix (Fin n) (Fin n) K.E) : Submodule K.O B.A :=
  (intVec K n).comap ((Matrix.toLin' P).restrictScalars K.O ∘ₗ ψ.toLinearMap.restrictScalars K.O)

def unitLat {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E} {K : UQ}
    (e : K.E ≃+* w.adicCompletion E) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) (q : UL n w) :
    Submodule K.O B.A :=
  modelLat B ψ ((((q⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm)

end GlobalTheory.InertUnitOrb
