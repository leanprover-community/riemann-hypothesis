module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecDegreeLe
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Assembly
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.AssemblyPartial
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowNormFormGeneric
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowSecDegree
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormEval
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem SecDegreeLe.proof : SecDegreeLe.Statement := by
  intro k E _ _ _ n e δ Q g y hQ hg hδ hfin hdom hsep hne
  classical
  set QE := Q.map (MvPolynomial.map (algebraMap k E))
  set A := Vertical.SecAlg QE y
  have : Module.Finite E A := hfin
  have : IsDomain A := hdom
  have : Algebra.IsSeparable E A := hsep
  have : Module.Free E A := Module.Free.of_divisionRing E A
  set N := Vertical.normForm (R := E) A (Vertical.secCoord QE y)
  set G := Vertical.specRest (algebraMap k E) g y

  have hirr : Irreducible N := Vertical.NormFormIrreducible.full E A n (Vertical.secCoord QE y)
    (fun j => y (.inr j)) (Vertical.secCoord_adjoin _ _) (Vertical.secCoord_chart _ _)
  obtain ⟨m, -, hm⟩ := Vertical.ChowSecDvd.full k E n e Q g y hQ hg
  have hd := Vertical.NormFormDvd.full E A n (Vertical.secCoord QE y) (G ^ m) (by rwa [map_pow])
  rw [← pow_mul] at hd
  have hNG : N ∣ G := hirr.prime.dvd_of_dvd_pow hd

  let b := Module.Free.chooseBasis E A
  have hN : N.IsHomogeneous (Module.finrank E A) := by
    show (Vertical.normForm (R := E) A (Vertical.secCoord QE y)).IsHomogeneous _
    rw [Vertical.normForm_eq_det b, Module.finrank_eq_card_chooseBasisIndex]
    refine Vertical.isHomogeneous_det_linear _ fun i k' => ?_
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    exact IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (isHomogeneous_X E j).mul (isHomogeneous_C (Fin n) _)
  have hN0 : N ≠ 0 := by
    intro h0
    have hv := Vertical.NormFormEval.full E A n (Vertical.secCoord QE y) (fun j => y (.inr j))
    change eval (fun j => y (.inr j)) N = _ at hv
    rw [h0, map_zero, Vertical.secCoord_chart, map_one] at hv
    exact zero_ne_one hv

  have hG : G.IsHomogeneous δ := Vertical.isHomogeneous_specRest _ hδ y
  rw [← hN.totalDegree hN0, ← hG.totalDegree hne]
  exact totalDegree_le_of_dvd_of_isDomain hNG hne

end

end GroundTheory.Heights₂.Heights
