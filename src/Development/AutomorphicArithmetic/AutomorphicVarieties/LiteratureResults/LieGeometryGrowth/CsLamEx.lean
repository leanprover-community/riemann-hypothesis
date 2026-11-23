module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullRetrFacts
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo.Cs

namespace UpperTheory.V.Lit.Geo.Cs

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private noncomputable def lam0 (g : GA E a) : ℝ :=
  Real.log (Reduction.detModule E a g).1 / (a * Module.finrank ℚ E)

private theorem deg_pos (ha : 1 ≤ a) : (0 : ℝ) < a * Module.finrank ℚ E :=
  mul_pos (Nat.cast_pos.2 ha) (Nat.cast_pos.2 Module.finrank_pos)

private theorem central_log_mul (g h : GA E a) : lam0 (g * h) = lam0 g + lam0 h := by
  unfold lam0
  rw [map_mul, ← add_div, ← Real.log_mul (Reduction.detModule E a g).2.ne' (Reduction.detModule E a h).2.ne']
  rfl

private theorem central_split_mul_retract (ha : 1 ≤ a) (g : GA E a) :
    splitCentre E a (lam0 g) * (retractOne g : KernelIndexFullLattice.G1 E a).1 = g := by
  have e : splitCentre E a (lam0 g) = Reduction.centralSection E a (Reduction.detModule E a g) := by
    rw [KernelIndexFullLattice.splitEq_holds E a]
    refine congrArg (Reduction.centralSection E a) (Subtype.ext ?_)
    change Real.exp _ = _
    rw [lam0, mul_div_cancel₀ _ (deg_pos ha).ne', Real.exp_log (Reduction.detModule E a g).2]
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, e, coe_retractOne, inv_mul_cancel_right]

private theorem central_log_eq_zero_on_norm_one (x : KernelIndexFullLattice.G1 E a) : lam0 (x.1 : GA E a) = 0 := by
  rw [lam0, (Reduction.mem_normOneGL_iff_detModule).1 x.2]
  simp

private theorem central_log_split (ha : 1 ≤ a) (t : ℝ) : lam0 (splitCentre E a t) = t := by
  rw [lam0, KernelIndexFullLattice.splitEq_holds E a, Reduction.detModule_centralSection (by omega)]
  change Real.log (Real.exp _) / _ = _
  rw [Real.log_exp, mul_div_cancel_left₀ _ (deg_pos ha).ne']

end UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.lamEx :
    LamEx := by
  intro E _ _ _ a ha
  refine ⟨lam0, central_log_mul, central_split_mul_retract ha, fun c => ?_⟩
  obtain ⟨T, hT⟩ := (UpperTheory.V.Lit.Geo.retrFacts E a).2.2 c
  refine ⟨T, fun h hh => ?_⟩
  obtain ⟨t, ht, e⟩ := hT 1 h hh.1 hh.2
  have e' := congrArg lam0 e
  rw [central_log_mul, central_log_mul, central_log_eq_zero_on_norm_one, central_log_eq_zero_on_norm_one, central_log_split ha, zero_add, add_zero] at e'
  rwa [e']
