module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Defs

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

abbrev Big (n k : ℕ) (M : Type*) := PiLp 2 (fun _ : Fin k → Fin n × Fin n => M)

def coord (k : ℕ) (κ : Fin k → Fin n × Fin n) : Big n k M →ₗ[ℂ] M :=
  LinearMap.proj (R := ℂ) (φ := fun _ : Fin k → Fin n × Fin n => M) κ ∘ₗ
    (WithLp.linearEquiv 2 ℂ ((Fin k → Fin n × Fin n) → M)).toLinearMap

def ofCoords {X : Type*} [AddCommGroup X] [Module ℂ X] (k : ℕ)
    (f : (Fin k → Fin n × Fin n) → (X →ₗ[ℂ] M)) : X →ₗ[ℂ] Big n k M :=
  (WithLp.linearEquiv 2 ℂ ((Fin k → Fin n × Fin n) → M)).symm.toLinearMap ∘ₗ LinearMap.pi f

def mAct (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) (a b : Fin n) : Module.End ℂ (Big n k M) :=
  ofCoords k fun κ => E a b ∘ₗ coord k κ

def factorAd (k : ℕ) (i : Fin k) (a b : Fin n) : Module.End ℂ (Big n k M) :=
  ofCoords k fun κ =>
    (if (κ i).1 = a then coord k (Function.update κ i (b, (κ i).2)) else 0) -
      (if (κ i).2 = b then coord k (Function.update κ i ((κ i).1, a)) else 0)

def bAct (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) (a b : Fin n) : Module.End ℂ (Big n k M) :=
  mAct E k a b + ∑ i, factorAd k i a b

def factorCasimir (ε : Fin n → Bool) (k : ℕ) : Module.End ℂ (Big n k M) :=
  casimirK ε (fun a b => ∑ i, factorAd (M := M) k i a b)

def crossOp (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) (i : Fin k) :
    Module.End ℂ (Big n k M) :=
  ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), factorAd k i a b * mAct E k b a

def ncV (ε : Fin n → Bool) (V : Submodule ℂ M) (k : ℕ) : Submodule ℂ (Big n k M) :=
  ⨅ κ : Fin k → Fin n × Fin n,
    (if ∀ i, ε (κ i).1 ≠ ε (κ i).2 then V else ⊥).comap (coord k κ)

def word (E : Fin n → Fin n → Module.End ℂ M) {k : ℕ} (κ : Fin k → Fin n × Fin n) :
    Module.End ℂ M :=
  (List.ofFn fun i => E (κ i).1 (κ i).2).prod

def phi (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) : Big n k M →ₗ[ℂ] M :=
  ∑ κ, word E κ ∘ₗ coord k κ

def slice {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) (F : Big n k M) : Big n 1 M :=
  WithLp.toLp 2 (fun ι : Fin 1 → Fin n × Fin n => F (Function.update κ i (ι 0)))

def permute {k : ℕ} (σ : Equiv.Perm (Fin k)) (F : Big n k M) : Big n k M :=
  WithLp.toLp 2 (fun κ => F (κ ∘ σ))

def Wm (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) :
    Submodule ℂ (Big n 1 M) :=
  ⨆ (θ : ℝ) (_ : θ < 0), Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1

def Wp (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) :
    Submodule ℂ (Big n 1 M) :=
  ⨆ (θ : ℝ) (_ : 0 < θ), Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1

end Defs

end ReciprocityTheory.ChartRestriction.DS
