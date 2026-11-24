module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.AdmissibleOfCrystalline
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsInvariantSectionMemBasicOpenIff
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

open CategoryTheory AlgebraicGeometry Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct Module Matrix
open scoped Formalism.Per
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.affFin_of :
    AffFinProj := by
  intro R _ Y f hf s
  haveI : GlobalTheory.FiniteSubsetsInAffineOpens Y := GlobalTheory.FiniteSubsetsInAffineOpens.of_isProjOver hf
  obtain ⟨U, hU, hsub⟩ :=
    GlobalTheory.FiniteSubsetsInAffineOpens.exists_isAffineOpen (X := Y) (s : Set Y) s.finite_toSet
  exact ⟨U, hU, fun x hx => hsub (Finset.mem_coe.mpr hx)⟩
