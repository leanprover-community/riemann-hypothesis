module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Formalism.SatakeDualWeyl.StatementE
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun Formalism.UG GlobalTheory.PRep

namespace DiscreteGroups.T1.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem absC_loc (u : ℂ) (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) (n : ℤ)
    (hx : Valued.v (x : w.adicCompletion E) = WithZero.exp (-n)) :
    (((Model.absC E u).loc w x : ℂˣ) : ℂ) = Complex.exp (u * (-(n * Real.log (Ideal.absNorm w.asIdeal : ℕ)) : ℝ)) := by
  change Complex.exp (u * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E w x)) = _
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local w x n hx]

theorem absC_unrAt (u : ℂ) (w : HeightOneSpectrum (𝓞 E)) : (Model.absC E u).UnrAt w := by
  intro x hx
  apply Units.ext
  rw [absC_loc u w x 0 (by rw [hx]; simp)]
  simp

theorem absC_val (u : ℂ) (w : HeightOneSpectrum (𝓞 E)) :
    (((Model.absC E u).val w : ℂˣ) : ℂ) = ((qV E w : ℕ) : ℂ) ^ (-u) := by
  have hu : Valued.v ((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = WithZero.exp (-(1 : ℤ)) :=
    unif_spec w
  have h := absC_loc u w (atFin w (unif w)) 1 hu
  change (((Model.absC E u).loc w (atFin w (unif w)) : ℂˣ) : ℂ) = _
  rw [h, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.2 (qV_ne_zero w))]
  have e : Complex.log ((qV E w : ℕ) : ℂ) = ((Real.log (Ideal.absNorm w.asIdeal : ℕ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg _), Complex.ofReal_natCast]; rfl
  rw [e]
  congr 1
  push_cast
  ring

end DiscreteGroups.T1.G

end
