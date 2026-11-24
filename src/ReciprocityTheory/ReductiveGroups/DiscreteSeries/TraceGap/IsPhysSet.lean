module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrimeA
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

def IsPhys (ε : Fin n → Bool) (x : Fin n × Fin n) : Prop := ε x.1 = true ∧ ε x.2 = false

instance (ε : Fin n → Bool) : DecidablePred (IsPhys ε) := fun x =>
  inferInstanceAs (Decidable (ε x.1 = true ∧ ε x.2 = false))

def adMat (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ := fun x y =>
  if IsPhys ε x then (if IsPhys ε y then k x.1 y.1 * star (k x.2 y.2) else 0)
  else if x = y then 1 else 0

def adPhys (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) :
    (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ) :=
  Matrix.mulVecLin (adMat ε k)

def ff (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) : Fock n →ₐ[ℂ] Fock n :=
  ExteriorAlgebra.map (adPhys ε k)

def cpV (v : Fin n × Fin n → ℂ) : Module.End ℂ (Fock n) :=
  LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ v)

def dualV (v : Fin n × Fin n → ℂ) : Module.Dual ℂ (Fin n × Fin n → ℂ) :=
  ∑ x, star (v x) • LinearMap.proj (R := ℂ) (φ := fun _ : Fin n × Fin n => ℂ) x

def cmV (v : Fin n × Fin n → ℂ) : Module.End ℂ (Fock n) :=
  CliffordAlgebra.contractLeft (dualV v)

def ffMat (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Finset (Fin (n * n))) (Finset (Fin (n * n))) ℂ :=
  LinearMap.toMatrix (fockBasis n) (fockBasis n) (ff ε k).toLinearMap

def IsPhysSet (ε : Fin n → Bool) (S : Finset (Fin (n * n))) : Prop :=
  ∀ m ∈ S, IsPhys ε (finProdFinEquiv.symm m)

instance (ε : Fin n → Bool) : DecidablePred (IsPhysSet ε) := fun S =>
  inferInstanceAs (Decidable (∀ m ∈ S, IsPhys ε (finProdFinEquiv.symm m)))

def strPhys (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ S ∈ univ.filter (IsPhysSet ε), (-1 : ℂ) ^ S.card * ffMat ε k S S

def physDet (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  Matrix.det (fun x y : {x : Fin n × Fin n // IsPhys ε x} =>
    (if x = y then 1 else 0) - k x.1.1 y.1.1 * star (k x.1.2 y.1.2))

def modeChar (ε : Fin n → Bool) (s : Fin n → ℂ) (x : Fin n × Fin n) : ℂ :=
  if IsPhys ε x then s x.1 * star (s x.2) else 1

end ReciprocityTheory.ChartRestriction.DS.TRGap
