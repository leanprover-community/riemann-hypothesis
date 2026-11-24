module

public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty
public import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure PreX (B : Pre) where
  piG : Fin 2 → 𝓞 B.host.E
  piG_K : ∀ i, (piG i : B.host.E) ∈ B.host.K
  piG_norm : ∀ i, (piG i : B.host.E) * B.host.conj (piG i : B.host.E) = (B.host.g i : B.host.E)
  piG_cong : ∀ i, ((B.host.QS * B.host.q * B.host.d : ℕ) : 𝓞 B.host.E) ∣ piG i - 1
  piT : B.Word → 𝓞 B.host.E
  piT_K : ∀ u, (piT u : B.host.E) ∈ B.host.K
  piT_norm : ∀ u, (piT u : B.host.E) * B.host.conj (piT u : B.host.E) = (B.T u : B.host.E)
  piT_cong : ∀ u, ((B.host.QS * B.host.q * B.host.d * (B.host.g 0 * B.host.g 1) ^ 2 : ℕ) : 𝓞 B.host.E) ∣ piT u - 1
  pde_split : (Ideal.primesOver (Ideal.span {(B.host.pde : ℤ)}) (𝓞 B.host.E)).ncard = Module.finrank ℚ B.host.E ∧
    (Ideal.primesOver (Ideal.span {(B.host.pde' : ℤ)}) (𝓞 B.host.E)).ncard = Module.finrank ℚ B.host.E
  ccK_top : B.host.ccK = ⊤
  e_even : ∀ j : Fin B.R.m, UpperTheory.MUQ (fun τ : Tau B.R => B.host.emb (τ : B.R.GG)) (fun τ => (B.hc τ).e j)

  hcW_inj : Function.Injective B.hcW

  a : ℝ
  g_big : ∀ i, 2 * B.R.f * B.R.k < B.host.g i - 1
  T_gt : ∀ u, 4 * a < (B.T u : ℝ)
  a_gt : ((2 * B.R.f * B.R.N B.R.m + 1 : ℕ) : ℝ) < 4 * a
  spread_le : ∀ u j, j ≤ B.R.m → ∀ τ, ((Formalism.BasicNotions.Examples₂.lamOf (B.hcW u τ) j).spread : ℝ) ≤ 2 * a

def Base.tauLL (B : Base) (τ : Tau B.R) : B.host.E →+* B.LL :=
  B.embE.comp (B.host.sigmaOf (τ : B.R.GG) : B.host.E →+* B.host.E)

end GlobalTheory.Mem

end
