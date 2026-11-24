module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.ProjectiveBundleFormulaTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeZeroSectionClassPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistUnitClassRootClassSpecStatement
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
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.Di
open scoped TensorProduct

theorem UpperTheory.Gal.KunnethLefschetz.Di.rootNat_holds :
    UpperTheory.Gal.KunnethLefschetz.Di.RootNat := by
  intro q _ i V U g ζ
  have hroot := (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.2.2
  have hnat := (GlobalTheory.T.degreeZeroSectionClass_properties (ZMod q) (tw q i) U).2.2.2.1 g (twGen i ζ)
  have hres := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 V U g ζ
  rw [hroot i U ζ, hroot i V (ζ.map g.appTop.hom), ← hres]
  exact hnat
