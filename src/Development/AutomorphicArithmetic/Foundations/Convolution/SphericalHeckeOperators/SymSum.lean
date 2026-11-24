module

public import GroundTheory.AutomorphicForms.SatakeNormalized
public import GroundTheory.AutomorphicForms.AffineBruhat
public import GroundTheory.AutomorphicForms.MacdonaldAlternant
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

@[expose] public section

noncomputable section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa

namespace UpperTheory.ConvolutionTheory.H

section Laurent

variable {n : ℕ}


variable (n) in
def pairs : Finset (Fin n × Fin n) := Finset.univ.filter fun p => p.1 < p.2


variable (n) in
def dPol (t : ℂ) : LaurentRing n := ∏ p ∈ pairs n, (varL p.1 - t • varL p.2)

def symSum (y : LaurentRing n) : LaurentRing n := ∑ σ : Equiv.Perm (Fin n), permAct σ y

def Dom (r : LaurentRing n) : Prop := ∀ a ∈ r.coeff.support, Antitone a

def SDom (r : LaurentRing n) : Prop := ∀ a ∈ r.coeff.support, StrictAnti a

def Gap (m : ℕ) (a : Fin n → ℤ) : Prop := ∀ i j, i < j → a j + m ≤ a i

def bc (l : ℕ) : LaurentRing n →ₐ[ℂ] LaurentRing n :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (DistribSMul.toAddMonoidHom (Fin n → ℤ) (l : ℤ))

def eL (S : Finset (Fin n × Fin n)) : Fin n → ℤ := ∑ p ∈ S, Pi.single p.1 1

def eR (S : Finset (Fin n × Fin n)) : Fin n → ℤ := ∑ p ∈ pairs n \ S, Pi.single p.2 1

def sgS (S : Finset (Fin n × Fin n)) : ℂ := (-1) ^ (pairs n \ S).card

end Laurent

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

def dco (a : Fin n → ℤ) : Set (GL (Fin n) F) :=
  {g | ∃ x ∈ iwahori F n, ∃ y ∈ iwahori F n, g = x * torusPow F n a * y}

def uFn (a : Fin n → ℤ) : GL (Fin n) F → ℂ := (dco F a).indicator 1


variable (n) in
def oneK : GL (Fin n) F → ℂ := (integralGL F n : Set (GL (Fin n) F)).indicator 1

def BiI (φ : GL (Fin n) F → ℂ) : Prop := ∀ g, ∀ y ∈ iwahori F n, φ (y * g) = φ g ∧ φ (g * y) = φ g

def psI (z : Fin n → ℂˣ) : Submodule ℂ (GL (Fin n) F → ℂ) where
  carrier := {f | f ∈ principalSeriesSpace F n (paramChar F z) ∧ ∀ g, ∀ y ∈ iwahori F n, f (g * y) = f g}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, fun g y hy => by simp only [Pi.add_apply, ha.2 g y hy, hb.2 g y hy]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ _ => rfl⟩
  smul_mem' c _ h := ⟨Submodule.smul_mem _ c h.1, fun g y hy => by simp only [Pi.smul_apply, h.2 g y hy]⟩

variable {F} [MeasurableSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F))

def th (a : Fin n → ℤ) : GL (Fin n) F → ℂ :=
  (halfModulus F a / (μ.real (iwahori F n : Set (GL (Fin n) F)) : ℂ)) • uFn F a

def thP (r : LaurentRing n) : GL (Fin n) F → ℂ := r.coeff.sum fun a c => c • th μ a

def sand (ν₁ ν₂ : Fin n → ℤ) : GL (Fin n) F → ℂ :=
  ∑ S ∈ (pairs n).powerset, sgS S • groupConv μ (th μ (ν₁ + eL S)) (groupConv μ (oneK F n) (th μ (ν₂ + eR S)))

def comm : Submodule ℂ (GL (Fin n) F → ℂ) :=
  Submodule.span ℂ {x | ∃ a b, (a = oneK F n ∨ ∃ l, Antitone l ∧ a = uFn F l) ∧
    b ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ ∧ x = groupConv μ a b - groupConv μ b a}

end UpperTheory.ConvolutionTheory.H

end
