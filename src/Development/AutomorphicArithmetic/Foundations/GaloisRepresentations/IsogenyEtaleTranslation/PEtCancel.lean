module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open AlgebraicGeometry in
theorem UpperTheory.Gal.FixZ.etCancel_of :
    UpperTheory.Gal.FixZ.EtCancel := by
  intro A B C E f g f' hg hfin1 het1 hfin2 het2
  have h1 : AlgebraicGeometry.IsSeparated (CategoryTheory.CategoryStruct.comp g f') :=
    inferInstance
  have h2 : AlgebraicGeometry.IsSeparated g := AlgebraicGeometry.IsSeparated.of_comp g f'
  have h3 : AlgebraicGeometry.FormallyUnramified g :=
    AlgebraicGeometry.FormallyUnramified.of_comp g f'
  exact ⟨AlgebraicGeometry.IsFinite.of_comp f g, AlgebraicGeometry.Etale.of_comp f g⟩
