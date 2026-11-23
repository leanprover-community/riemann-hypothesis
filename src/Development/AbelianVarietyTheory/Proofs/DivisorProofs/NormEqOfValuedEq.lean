module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaPair
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups

@[expose] public section

open NumberField IsDedekindDomain Matrix GroundTheory.Global GroundTheory.Automorphic.GJMatrix GlobalTheory.HenQ
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc)
open scoped nonZeroDivisors

noncomputable section
namespace GlobalTheory.HenQ
variable {K : Type} [Field K] [NumberField K]

theorem valued_det_of_KGL {w : HeightOneSpectrum (𝓞 K)} {n : ℕ} {g : GL (Fin n) (w.adicCompletion K)}
    (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) : Valued.v g.val.det = 1 := by
  obtain ⟨g0, rfl⟩ := hg
  set O := (w.adicCompletionIntegers K).toSubring
  have hd : ∀ h : GL (Fin n) O, ((Formalism.UG.bc O.subtype h).val.det) = ((h.val.det : O) : w.adicCompletion K) := by
    intro h
    exact (RingHom.map_det O.subtype h.val).symm
  have h1 : Valued.v ((g0.val.det : O) : w.adicCompletion K) ≤ 1 := (g0.val.det).2
  have h2 : Valued.v (((g0⁻¹).val.det : O) : w.adicCompletion K) ≤ 1 := ((g0⁻¹).val.det).2
  have h3 : ((g0.val.det : O) : w.adicCompletion K) * (((g0⁻¹).val.det : O) : w.adicCompletion K) = 1 := by
    rw [← Subring.coe_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    rfl
  have h4 := congrArg Valued.v h3
  rw [map_mul, map_one] at h4
  rw [hd]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := h4.symm
    _ ≤ Valued.v ((g0.val.det : O) : w.adicCompletion K) * 1 := mul_le_mul' le_rfl h2
    _ = _ := mul_one _

end GlobalTheory.HenQ
