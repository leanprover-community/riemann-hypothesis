module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.valPts_of :
    ValPts := by
  intro R S V _ _ _ _ _ _ _ _
  have hinj : Function.Injective (IsScalarTower.toAlgHom R V (FractionRing V)) :=
    IsFractionRing.injective V (FractionRing V)
  constructor
  · intro z z' h
    ext s
    apply hinj
    simpa only [AlgHom.comp_apply] using AlgHom.congr_fun h s
  · intro φ
    have hmem : ∀ s, φ s ∈ (IsScalarTower.toAlgHom R V (FractionRing V)).range := by
      intro s
      have h1 : IsIntegral R (φ s) := (Algebra.IsIntegral.isIntegral s).map φ
      have h2 : IsIntegral V (φ s) := h1.tower_top
      obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
      exact (AlgHom.mem_range _).2 ⟨v, hv⟩
    let e := AlgEquiv.ofInjective (IsScalarTower.toAlgHom R V (FractionRing V)) hinj
    refine ⟨e.symm.toAlgHom.comp (φ.codRestrict _ hmem), ?_⟩
    ext s
    have h := e.apply_symm_apply ⟨φ s, hmem s⟩
    exact congrArg Subtype.val h
