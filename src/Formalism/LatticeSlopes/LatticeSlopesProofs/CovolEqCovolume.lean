module

public import Formalism.LatticeSlopes.Statement
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

open Module Submodule MeasureTheory

noncomputable section

namespace Formalism.F

theorem covol_eq_covolume' : CovolEqCovolume := by
  intro E _ _ _ _ _ L _ _
  classical
  rw [covol, dite_eq_left (inferInstance : DiscreteTopology L)]
  set b := Module.finBasis ℤ L with hb
  set bR : Basis (Fin (Module.finrank ℤ L)) ℝ E := b.ofZLatticeBasis ℝ L with hbR
  have hrank : Module.finrank ℝ E = Module.finrank ℤ L := (ZLattice.rank ℝ L).symm
  set o : OrthonormalBasis (Fin (Module.finrank ℤ L)) ℝ E := (stdOrthonormalBasis ℝ E).reindex (finCongr hrank)
  set A := o.toBasis.toMatrix bR with hA

  have hgo : Matrix.gram ℝ (fun i => o.toBasis i) = 1 := by
    ext i j
    simp [Matrix.gram, Matrix.one_apply, orthonormal_iff_ite.mp o.orthonormal]
  have hv : (fun i => ((b i : L) : E)) = fun j => ∑ i, A i j • o.toBasis i := by
    funext j
    rw [hA, o.toBasis.sum_toMatrix_smul_self]
    exact (Basis.ofZLatticeBasis_apply ℝ L b j).symm
  have hg : Matrix.gram ℝ (fun i => ((b i : L) : E)) = A.transpose * A := by
    rw [hv, gram_sum_smul_eq_transpose_mul, hgo, Matrix.mul_one]
  have hdet : (Matrix.gram ℝ (fun i => ((b i : L) : E))).det = (o.toBasis.det bR) ^ 2 := by
    rw [hg, Matrix.det_mul, Matrix.det_transpose, Basis.det_apply, sq]

  have h1 : ZLattice.covolume L = (MeasureTheory.volume (ZSpan.fundamentalDomain bR)).toReal := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L MeasureTheory.volume
      (ZLattice.isAddFundamentalDomain b MeasureTheory.volume)]
    rfl
  have h2 := ZSpan.measure_fundamentalDomain bR MeasureTheory.volume o.toBasis
  have h3 : MeasureTheory.volume (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [MeasureTheory.measure_congr
      (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis MeasureTheory.volume),
      OrthonormalBasis.coe_toBasis, o.volume_parallelepiped]
  rw [hdet, Real.sqrt_sq_eq_abs, h1, h2, h3, mul_one, ENNReal.toReal_ofReal (abs_nonneg _)]

end Formalism.F
