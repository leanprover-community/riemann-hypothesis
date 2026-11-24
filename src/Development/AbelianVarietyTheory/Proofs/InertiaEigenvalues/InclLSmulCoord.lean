module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
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

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.BKGal

variable {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G] [TopologicalSpace G]

theorem inclL_smul_coord (P : PhiMod O K l e a ι) (m : OA l O) (c : ι → OA l O) :
    inclL t ϖ P (fun i => m * c i) = inclO l O m • inclL t ϖ P c := by
  rw [inclL_apply, inclL_apply]
  have h : (fun i => inclO l O (m * c i)) = inclO l O m • fun i => inclO l O (c i) :=
    funext fun i => by simp only [map_mul, Pi.smul_apply, smul_eq_mul]
  rw [h, Matrix.mulVec_smul]

theorem IsCrisVal.sub {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}
    {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T} {w w' : ι → OW l O} {b b' : TW (OB l O) T}
    (h : IsCrisVal t ϖ P jB w b) (h' : IsCrisVal t ϖ P jB w' b') : IsCrisVal t ϖ P jB (w - w') (b - b') := by
  obtain ⟨m, c, hu, hc, hb⟩ := h
  obtain ⟨m', c', hu', hc', hb'⟩ := h'
  refine ⟨m * m', fun i => m' * c i - m * c' i, by rw [map_mul]; exact hu.mul hu', ?_, ?_⟩
  · have e1 : (fun i => m' * c i - m * c' i) = (fun i => m' * c i) - (fun i => m * c' i) := rfl
    rw [e1, map_sub, inclL_smul_coord, inclL_smul_coord, ← hc, ← hc', smul_sub, smul_smul, smul_smul, map_mul,
      mul_comm (inclO l O m')]
  · have e2 : (fun i => toB l O (m' * c i - m * c' i)) =
        toB l O m' • (fun i => toB l O (c i)) - toB l O m • (fun i => toB l O (c' i)) :=
      funext fun i => by simp only [map_sub, map_mul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [e2, map_sub, map_smul, map_smul, ← hb, ← hb', smul_sub, smul_smul, smul_smul, map_mul,
      mul_comm (toB l O m')]

end GlobalTheory.BKGal
