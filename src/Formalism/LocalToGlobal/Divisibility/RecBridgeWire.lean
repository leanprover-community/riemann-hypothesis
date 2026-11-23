module

public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.Divisibility.ClosedSizeLink.DivisionAdmissibleFamilyOfData
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
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
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.MirabolicMackeyTheory.StatementT
import Formalism.QuotientMetricDivisors.Statement
import Formalism.SharpRestriction.Divisibility.HookProducts.RBTieFrame

@[expose] public section

noncomputable section

namespace Formalism.L2.DIV.Wire

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.DIV

variable {eps : ℝ} {Fm : Formalism.MainNotions.FamP eps}

theorem la_of (Fm : Formalism.MainNotions.FamP eps) : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, 0 ≤ (Fm.L x i).La :=
  ⟨Fm.x1 + 1, fun x hx i => Formalism.MainNotions.DIV.La_nonneg (Fm.L x i) (Fm.sizes x (by linarith) i).2.2.2.2.2.2.1⟩

theorem za_of (Fm : Formalism.MainNotions.FamP eps) : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.L x i).ZeroAbove :=
  ⟨Fm.x1 + 1, fun x hx i => Formalism.MainNotions.WeightDegreeSizes.zero_gain_above_family Fm x (by linarith) i⟩

end Formalism.L2.DIV.Wire

end
