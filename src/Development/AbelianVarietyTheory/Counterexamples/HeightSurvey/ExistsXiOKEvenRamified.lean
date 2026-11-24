module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.PowClassNumberIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

noncomputable section

namespace GlobalTheory.XiCounterexample

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.FinalJoin
open GlobalTheory.NormOneChar
open scoped TensorProduct

theorem conj_emb (D : D7) (φ : D.host.E →+* ℂ) (y : D.host.E) :
    φ (GlobalTheory.Member.cF D y) = starRingEnd ℂ (φ y) :=
  @IsCMField.complexEmbedding_complexConj D.host.E _ _
    (D.host.isCMField_hostE) _ φ y

theorem conj_conj (D : D7) (y : D.host.E) : GlobalTheory.Member.cF D (GlobalTheory.Member.cF D y) = y :=
  D.host.φ₀.injective (by rw [conj_emb, conj_emb, Complex.conj_conj])

theorem mem_congOne (D : D7) (N : ℕ) (x : (AfE D)ˣ) :
    x ∈ congOne (GlobalTheory.Member.cF D) N ↔ CongOne N x ∧ NormOne x := by
  unfold CongOne
  simp only [GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers, nsmul_eq_mul]
  exact Iff.rfl

theorem fin_of_rat_tame (D : D7) (N : ℕ) (hN : 0 < N) (xi : (AfE D)ˣ →* ℂˣ)
    (h1 : ∀ (x : (AfE D)ˣ) (a : D.host.E), (x : AfE D) = 1 ⊗ₜ a → NormOne x → xi x = 1)
    (h2 : ∀ x, NormOne x → CongOne N x → xi x = 1) : ∃ m : ℕ, 0 < m ∧ ∀ x, NormOne x → xi x ^ m = 1 := by
  obtain ⟨m, hm, hexp⟩ := exists_exponent (GlobalTheory.Member.cF D) (conj_conj D) N hN
  refine ⟨m, hm, fun x hn => ?_⟩
  rw [← map_pow]
  obtain ⟨r, ⟨⟨a, ha⟩, hr⟩, k, hk, e⟩ := Subgroup.mem_sup.1 (hexp x hn)
  rw [← e, map_mul, h1 r a ha hr, h2 k ((mem_congOne D _ _).1 hk).2 ((mem_congOne D _ _).1 hk).1, mul_one]

end GlobalTheory.XiCounterexample
