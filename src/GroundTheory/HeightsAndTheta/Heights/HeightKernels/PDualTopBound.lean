module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ScaledExample
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

namespace TopDualBound

theorem grassConst_lines {i : ℕ} (hi : 1 ≤ i) : grassConst 1 1 (i - 1) = 1 / 2 * Real.log i := by
  have h : (1 : ℝ) + ((i - 1 : ℕ) : ℝ) = i := by
    rw [Nat.cast_sub hi]; push_cast; ring
  simp only [grassConst, h]
  norm_num

theorem dim_lines {i : ℕ} (hi : 1 ≤ i) : ((1 * 1 * (i - 1) + 1 : ℕ) : ℝ) = i := by
  congr 1; omega

end TopDualBound

theorem DualTopBound.proof (hBasis : DualLatticeBasisExists.Statement)
    (hBij : DualEmbBijective.Statement) (hMetric : DualTopMetricChange.Statement)
    (hLattice : DualTopLatticeChange.Statement) (hStd : DualTopStandard.Statement)
    (hDeg : DualGeomDegStandard.Statement) (hGrass : GrassHeightBound.Statement) :
    DualTopBound.Statement := by
  intro hZ2 K _ _ i F T _ _ b hb II hi hII
  obtain ⟨T', _, _, ⟨b'⟩⟩ := hBasis K i (HermLattice.standard K i)
  have hb' := hBij K i (HermLattice.standard K i) T' b'
  set g := geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))
  set d : ℝ := (Module.finrank ℚ K : ℝ) with hd
  have hA := hMetric K i F T b hb II hi hII
  have hB := hLattice K i F T T' b hb b' hb' II hi hII
  have hC := hStd K i T' b' hb' II hi hII
  have hG := hDeg K i F T b hb hi
  have hH := hGrass hZ2 1 1 (i - 1) le_rfl II hII
  rw [TopDualBound.dim_lines hi, TopDualBound.grassConst_lines hi] at hH
  rw [hA, hB, hC, hG]
  have hd0 : 0 < d := by rw [hd]; exact_mod_cast Module.finrank_pos
  have hi0 : (0 : ℝ) < i := by exact_mod_cast hi
  have hslope : (i : ℝ) * (-F.slope + 1 / 2 * Real.log i) * (d * g) =
      -F.degree * g + d * ((i : ℝ) * (1 / 2 * Real.log i) * g) := by
    simp only [HermLattice.slope, normalise]
    rw [← hd]
    field_simp
  rw [hslope]
  have := mul_le_mul_of_nonneg_left hH hd0.le
  linarith

end GroundTheory.Heights₂.Heights
