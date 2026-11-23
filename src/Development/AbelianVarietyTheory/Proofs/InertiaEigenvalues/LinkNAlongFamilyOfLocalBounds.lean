module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Formalism.SharpRestriction.GlobalTheoremInputs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmittedStatementsOfLocalBoundsConclusionStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.ExportBoundOfAdmissible
public import Formalism.SharpRestriction.LevelLetterCocycles.ThetaScalarFamilyOfEigenvalue
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

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.LinkFam

theorem main : ∀ {eps : ℝ} (Fm : FamP eps), ConclF Fm → Formalism.MainNotions.LinkN Fm := by
  intro eps Fm hC
  obtain ⟨C, x0, h⟩ := hC
  have hA : Formalism.MainNotions.TwistedPlaces.AdmF Fm := ⟨C, x0, fun x hx hx1 i hS => by
    obtain ⟨X, hX⟩ := h x hx hx1 i hS
    exact GlobalTheory.T.admittedStatements_of_localBoundsConclusion_alt _ _ _ X C hX⟩
  exact Formalism.MainNotions.N.linkN_of Fm hA (Formalism.MainNotions.TwistedPlaces.stmtF_holds Fm)

end GlobalTheory.LinkFam
