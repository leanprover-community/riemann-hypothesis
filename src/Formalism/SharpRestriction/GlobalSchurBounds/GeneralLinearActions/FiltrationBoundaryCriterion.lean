module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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

noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions

abbrev HH (D : D7) : Type := D.R.A

def hco (D : D7) (g : D.R.GG) : HH D := D.R.iotaInv g.2

def gOf (D : D7) (g₀ : G0) (h : HH D) : D.R.GG := (g₀, D.R.iota h)

def ordH {n : ℕ} (h : ZMod n) : ℕ := addOrderOf h

def rho (D : D7) (τ g : D.R.GG) : D.R.GG := D.R.cc * g * τ


open Classical in
def frob (D : D7) (p : ℕ) : D.R.GG :=
  if h : ∃ σ : D.host.E ≃ₐ[ℚ] D.host.E, ∃ P : Ideal (𝓞 D.host.E),
      P.IsPrime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧ IsArithFrobAt ℤ σ P
  then D.host.galE h.choose else 1

def hOf (e l : ℕ) : ZMod (2 ^ e) :=
  if h : Nat.Coprime l 2 then
    iotaHInv e (hcl e (ZMod.unitOfCoprime l (Nat.Coprime.pow_right (e + 2) h)))
  else 0

def sgc0 : G0 := ((-1 : ℤˣ), (1 : ℤˣ)) * c0

def PhiEmb (D : D7) : Set (D.host.E →+* ℂ) := D.host.emb '' (D.R.Psi : Set (D.R.GG))

def rdF (D : D7) : ℝ :=
  |(discr D.host.F : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ D.host.F : ℝ))

abbrev thick (D : D7) : Finset (D.R.GG) := D.host.thickPlaces

end Formalism.MainNotions.GlobalTheoryTheory

end
