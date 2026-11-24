module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CommonModel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detBasis_of :
    BasisIn := by
  intro C W X _ _ _ _ a mk hspan hfin
  obtain ⟨t, hts, hst, hli⟩ := exists_linearIndependent C (Set.range mk)
  have htop : ⊤ ≤ Submodule.span C (Set.range ((↑) : t → W)) := by
    rw [Subtype.range_coe, hst, hspan]
  let b₀ : Basis t C W := Basis.mk hli htop
  haveI : Finite t := Module.Finite.finite_basis b₀
  haveI : Fintype t := Fintype.ofFinite t
  have hcard : Fintype.card t = a := by
    rw [← hfin, Module.finrank_eq_card_basis b₀]
  let e : t ≃ Fin a := Fintype.equivFinOfCardEq hcard
  have hx : ∀ k : Fin a, ∃ x : X, mk x = ((e.symm k : t) : W) := fun k => hts (e.symm k).2
  choose x hx using hx
  refine ⟨x, b₀.reindex e, fun k => ?_⟩
  rw [Basis.reindex_apply, Basis.mk_apply, hx k]
