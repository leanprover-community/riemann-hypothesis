module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.RelAlg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfdualMeasureHermitianAdelesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfdualMeasureHermitianTuplesStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PositivityTheory.SiegelWeilFormula.KWhit

theorem sdEx : SdEx := by
  intro F E _ _ _ _ _ σ hcm M J hJ ψ hψ n
  exact ⟨GlobalTheory.T.exists_selfdual_measure_hermitian_tuples F E σ hcm M J hJ ψ hψ n, GlobalTheory.T.exists_selfdual_measure_hermitian_adeles F E σ hcm ψ hψ n⟩

end PositivityTheory.SiegelWeilFormula.KWhit
