module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem ker_localizedTheta_eq_span_of_dvd (l : ℕ) [Fact l.Prime] (x : Per.Ainf l)
    (hx : ∀ a : Per.Ainf l, Per.θ l a = 0 ↔ x ∣ a) :
    Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) x} := by
  refine le_antisymm (fun y hy => ?_) ?_
  · obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) y
    have hy' : Per.θP l y = 0 := GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l y (by rwa [pow_one])
    have h0 : Per.θ l a = 0 := by
      have h1 := GlobalTheory.RingIface.fontaineTheta_algebraMap (l := l) a
      rw [← ha, map_mul, hy', zero_mul] at h1
      exact Subtype.ext h1.symm
    obtain ⟨c, rfl⟩ := (hx a).1 h0
    have hu : IsUnit (algebraMap (Per.Ainf l) (Per.AinfP l) ((l : ℕ) : Per.Ainf l) ^ n) :=
      (IsLocalization.Away.algebraMap_isUnit (S := Per.AinfP l) ((l : ℕ) : Per.Ainf l)).pow n
    rw [← Ideal.mul_unit_mem_iff_mem _ hu, ha, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_singleton_le_iff_mem]
    exact GlobalTheory.RingIface.alg_mem_kerP (l := l) ((hx x).2 dvd_rfl)

theorem ker_localizedTheta_eq_span_xi : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e →
    Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)} :=
  fun l _ e he => ker_localizedTheta_eq_span_of_dvd l (xi e) (theta_eq_zero_iff_xi_dvd l e he)

end GlobalTheory.MemLoc
