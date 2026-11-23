module

public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoubleCosetsMassLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdAll
public import Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.RankVolume

theorem definiteSpaceVolume_eq_mass_of_volumeComparison (hU : ∀ D : D7, StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D) :
    ∀ D : D7, Formalism.L2.Theta.RealTied D → StandardLattice.volY0 D = StandardLattice.massI D D.R.r := fun D h =>
  have hT : StandardLattice.VolTie D := Formalism.L2.Theta.VolTieG.volTie h.vol
  StandardLattice.volume_eq_mass_at_rank D (StandardLattice.volume_eq_mass_of_definite D (StandardLattice.volumeMass_of_unfolding D (hU D hT))
    (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.mass_volume_identity_of_class_decomp D hT (GlobalTheory.genusMassStd_all D)
      (GlobalTheory.DefiniteDecompObj.doubleCosets_mass D)))

end GlobalTheory.RankVolume
