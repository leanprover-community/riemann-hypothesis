module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulStrictMono
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Grampd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.RealVec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Realsurj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Hermitian
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.rypos :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ), Ry L N ⊆ Pos L N := by
  intro L _ _ _ N h hh w
  classical
  obtain ⟨hH, hq, hr, hb⟩ := gramq L N h
  have h0 : intVec (0 : Fin N × BI L → ℤ) = (0 : Lat L N) := by
    ext a; simp [intVec]
  have hpd : (gram h).PosDef := (grampd _ (gram h) hH fun c hc => by
    rw [hq, hr]
    exact hh _ fun e => hc (hb.1 (e.trans h0.symm))).1
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (mat_herm h w) fun z hz => ?_
  obtain ⟨x, hx⟩ := realsurj L N (Pi.single w z)
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hz
    have := congrFun hx w
    rw [Pi.single_eq_same] at this
    rw [← this]
    ext a; simp [realVec]
  have h1 := hpd.dotProduct_mulVec_pos hx0
  rw [star_trivial, hq, hx, qR, Finset.sum_eq_single w] at h1
  · rw [Pi.single_eq_same] at h1
    rw [Complex.lt_def]
    refine ⟨by simpa using h1, ?_⟩
    simpa using ((mat_herm h w).im_star_dotProduct_mulVec_self z).symm
  · intro v _ hv
    simp [Pi.single_eq_of_ne hv]
  · simp
