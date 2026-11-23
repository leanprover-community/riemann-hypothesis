module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.EulerProductLocalFactors

noncomputable section

abbrev Place (K : Type) [Field K] [NumberField K] := HeightOneSpectrum (𝓞 K)

def normAt {K : Type} [Field K] [NumberField K] (w : Place K) : ℝ :=
  (Ideal.absNorm w.asIdeal : ℝ)

section Euler

variable {K : Type} [Field K] [NumberField K] {ι : Type}

def localFactor (I : Finset ι) (x : Place K → ι → ℂ) (w : Place K) : ℂ :=
  ∏ i ∈ I, (1 - x w i)⁻¹

def eulerProd (T : Set (Place K)) (I : Finset ι) (x : Place K → ι → ℂ) : ℂ :=
  ∏' w : {w : Place K // w ∉ T}, localFactor I x w.1

end Euler

def SatakeBound {E : Type} [Field E] [NumberField E] (T : Set (Place E)) (r : ℕ) (s : ℝ)
    (x : Place E → Fin r → ℂ) : Prop :=
  ∀ w, w ∉ T → ∀ i, ‖x w i‖ ≤ normAt w ^ (((r : ℝ) - 1) / 2 - s)

def twistTerm {F : Type} [Field F] [NumberField F] (ω : Place F → ℂ) (v : Place F) (i : ℕ) : ℂ :=
  ω v ^ i * ((normAt v : ℂ) ^ i)⁻¹

def dPart {F : Type} [Field F] [NumberField F] (S : Set (Place F)) (ω : Place F → ℂ)
    (r t : ℕ) : ℂ :=
  eulerProd S (Finset.Icc (t + 1) (r + t)) (twistTerm ω)

def placesOver {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E]
    [Algebra F E] (S : Set (Place F)) : Set (Place E) :=
  {w | ∃ v ∈ S, w.asIdeal.LiesOver v.asIdeal}


open Classical in
def quadSign {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E]
    [Algebra F E] (v : Place F) : ℂ :=
  by
    classical
    exact if (placesOver E ({v} : Set (Place F))).ncard = 2 then 1
      else if (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime then -1 else 0

end

end GlobalTheory.IndefiniteRowSideFullHecke.EulerProductLocalFactors
