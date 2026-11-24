module

public import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EulerProductOfDensities
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealPlaceMeasures
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticeDensity
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Unfolding
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitVectorPerp
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolIndep
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeRatioOfUnfolding
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

namespace GlobalTheory.VolRatioFromSecondClause

theorem volumeRatio : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J → Formalism.MainNotions.StandardLattice.SW1b2 F E σ M J) → ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.RT.MassRatioUnderVolume D :=
  fun hSW D =>
    GlobalTheory.VolRatioUnfold.volumeRatio_of_unfolding GlobalTheory.LatticeDensityClosed.selfDualLatticeDensity
      GlobalTheory.RealPlaceMeasuresProof.realPlaceMeasures GlobalTheory.DensityProductClosed.eulerProductOfDensities
      GlobalTheory.VolIndepClosed.volIndep GlobalTheory.UnitPerpObj.unitVectorPerp GlobalTheory.UnfoldingObj.unfolding hSW D

end GlobalTheory.VolRatioFromSecondClause
