module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
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

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def cr (c : ℝ) (k : Fin m × Fin n × Bool) : Module.End ℂ (PX m n) :=
  if k.2.2 then -((pderiv (R := ℂ) k).toLinearMap : Module.End ℂ (PX m n)) + (2 * c : ℂ) • LinearMap.mulLeft ℂ (X (k.1, k.2.1, false) : PX m n)
  else -((pderiv (R := ℂ) k).toLinearMap : Module.End ℂ (PX m n)) + (2 * c : ℂ) • LinearMap.mulLeft ℂ (X (k.1, k.2.1, true) : PX m n)

def fockMono (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : PX m n :=
  (((Finset.univ : Finset (Fin m × Fin n × Bool)).toList.map fun k => (cr c k) ^ (s k)).prod) 1

def fock (c : ℝ) (p : PX m n) : PX m n := ∑ s ∈ p.support, p.coeff s • fockMono c s

def Dop (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (p : PX m n) : PX m n :=
  if ε a = ε b then
    ∑ i, (X (b, i, true) * pderiv (a, i, true) p - X (a, i, false) * pderiv (b, i, false) p)
  else
    ∑ i, ((2 * c : ℂ) • pderiv (b, i, false) (pderiv (a, i, true) p) - (1 / (2 * c) : ℂ) • (X (a, i, false) * X (b, i, true) * p))

def contr (c : ℝ) (p : PX m n) : ℂ :=
  ∑ s ∈ p.support, if ∀ a i, s (a, i, false) = s (a, i, true) then
    p.coeff s * ∏ a, ∏ i, (((s (a, i, false)).factorial : ℂ) * (2 * c : ℂ) ^ (s (a, i, false))) else 0

def KopL (ε : Fin m → Bool) (i j : Fin n) : Module.End ℂ (PX m n) :=
  ∑ a ∈ Finset.univ.filter (fun a => ε a = true), LinearMap.mulLeft ℂ (X (a, i, false) : PX m n) ∘ₗ (pderiv (R := ℂ) (a, j, false)).toLinearMap -
    ∑ a ∈ Finset.univ.filter (fun a => ε a = false), LinearMap.mulLeft ℂ (X (a, j, true) : PX m n) ∘ₗ (pderiv (R := ℂ) (a, i, true)).toLinearMap

def mulQ (ε : Fin m → Bool) (i j : Fin n) (P : PX m n) : PX m n := Qp ε i j * P

def lapS (ε : Fin m → Bool) (c : ℝ) (i j : Fin n) (P : PX m n) : PX m n :=
  ∑ a, C (sgn ε a) * (pderiv (a, i, false) (pderiv (a, j, true) P - C (c : ℂ) * X (a, j, false) * P) -
    C (c : ℂ) * X (a, i, true) * (pderiv (a, j, true) P - C (c : ℂ) * X (a, j, false) * P))

def eulH (c : ℝ) (i j : Fin n) (P : PX m n) : PX m n :=
  ∑ a, X (a, j, false) * (pderiv (a, i, false) P - C (c : ℂ) * X (a, i, true) * P)

def eulA (c : ℝ) (i j : Fin n) (P : PX m n) : PX m n :=
  ∑ a, X (a, i, true) * (pderiv (a, j, true) P - C (c : ℂ) * X (a, j, false) * P)

def kAlg (ε : Fin m → Bool) : Subalgebra ℂ (Module.End ℂ (PX m n)) :=
  Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => KopL ε ij.1 ij.2)

end PositivityTheory.Rg.Sw.LC
