module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector
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

set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.GenCoef

variable (O : Type) [CommRing O] (N : ℕ)

def rowSubst (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) :
    MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (Fin N × Fin N) R :=
  aeval fun v => ∑ b : Fin N, C (Y v.1 b) * X (b, v.2)

def dwAlg (ν : Fin N → ℕ) : Subalgebra O (Module.End O (dualWeyl O N N ν)) :=
  Algebra.adjoin O (Set.range (fun g : GL (Fin N) O => Formalism.UG.dualWeylRep O N N ν g) ∪ Set.range (GlobalTheory.ExpFrame.rowProj O N ν))

def Expr (ν : Fin N → ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) : Prop :=
  ∃ (n : ℕ) (r : Fin n → R) (p : Fin n → Module.End O (dualWeyl O N N ν)), (∀ i, p i ∈ dwAlg O N ν) ∧
    ∀ f : dualWeyl O N N ν, rowSubst O N R Y (f : MvPolynomial (Fin N × Fin N) O) =
      ∑ i, r i • MvPolynomial.map (algebraMap O R) (p i f : MvPolynomial (Fin N × Fin N) O)

def lowGen : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  fun a b => if a = b then 1 else if b < a then X (a, b) else 0

def diagGen : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  Matrix.diagonal fun a => X (a, a)

def upGen : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  fun a b => if a = b then 1 else if a < b then X (a, b) else 0

def lduHom : MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (Fin N × Fin N) O :=
  aeval fun v => (lowGen O N * diagGen O N * upGen O N) v.1 v.2

end GlobalTheory.GenCoef

end
