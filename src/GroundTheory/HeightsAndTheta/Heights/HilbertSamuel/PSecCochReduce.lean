module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecCochReduce
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem SecCochReduce.map_map_int {K : Type} {ι : K → Type} (p : ℕ) (f : MRing ι) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (MvPolynomial.map (Int.castRingHom ℤ) f) =
      MvPolynomial.map (Int.castRingHom (ZMod p)) f := by
  rw [MvPolynomial.map_map]
  congr 1

theorem SecCochReduce.proof : SecCochReduce.Statement := by
  intro K _ _ ι _ _ Ω _ y p a s hs
  funext J
  rw [FibreReduction.redCoch_apply]
  by_cases hz : ∃ k, y ⟨k, GenOnFibres.cellChart J k⟩ = 0
  · obtain ⟨k, h0⟩ := hz
    have := GenOnFibres.subsingleton_loc (S := ZMod p) (GenOnFibres.cellChart_mem J k) h0
    exact Subsingleton.elim _ _
  · push Not at hz
    obtain ⟨e, F, hF, _, heq⟩ := GenOnFibres.secCoch_spec (S := ℤ) hs J hz
    have hrep : GenOnFibres.IsRep y (ZMod p) (KH.cellMon (ZMod p) J.1)
        (FibreReduction.redLoc y p J.1 (GenOnFibres.secCoch y ℤ s a J)) (GenOnFibres.cellChart J) s a := by
      refine ⟨e, F, hF, GenOnFibres.cmon_mem (ZMod p) (GenOnFibres.cellChart_mem J) e, ?_⟩
      rw [heq, FibreReduction.redLoc_mk, FibreReduction.redRing_mk, SecCochReduce.map_map_int]
      congr 1
      exact Subtype.ext (SecCochReduce.map_map_int p _)
    exact hrep.unique (GenOnFibres.secCoch_spec hs J hz)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
