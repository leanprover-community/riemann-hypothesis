module

public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem eisensteinTameWeightSecond_eq_character_sum :
    ∀ (N : ℕ) (s : ℂ), 0 < N → ∀ B : ℤ,
      tw2 N s B = ((N.totient : ℂ))⁻¹ * ∑ ν : DirichletCharacter ℂ N, (1 - s * ν (-1)) * ch ν B := by
  intro N s hN B
  haveI : NeZero N := ⟨hN.ne'⟩
  have hφ : ((N.totient : ℂ)) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hN).ne'
  have h1 := DirichletCharacter.sum_characters_eq ℂ (B : ZMod N)
  have h2 := DirichletCharacter.sum_characters_eq ℂ (-(B : ZMod N))
  have h3 : ∑ ν : DirichletCharacter ℂ N, ν (-1) * ν (B : ZMod N)
      = ∑ ν : DirichletCharacter ℂ N, ν (-(B : ZMod N)) := by
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← map_mul, neg_one_mul]
  have h4 : (-(B : ZMod N) = 1) ↔ ((B : ZMod N) = -1) := neg_eq_iff_eq_neg
  have hsum : ∑ ν : DirichletCharacter ℂ N, (1 - s * ν (-1)) * ch ν B
      = ∑ ν : DirichletCharacter ℂ N, ν (B : ZMod N)
        - s * ∑ ν : DirichletCharacter ℂ N, ν (-1) * ν (B : ZMod N) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp only [ch]
    ring
  rw [hsum, h3, h1, h2]
  simp only [tw2, h4]
  field_simp
  split_ifs <;> ring

end GlobalTheory.EisM
