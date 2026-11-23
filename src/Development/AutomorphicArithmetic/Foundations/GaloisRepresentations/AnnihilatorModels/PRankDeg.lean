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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.rankDeg_of :
    SplitsField → RankOfDeg := by
  intro hSF A S _ _ _ _ _ d hd
  funext p
  letI : Algebra A (AlgebraicClosure p.asIdeal.ResidueField) :=
    ((algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp
      (algebraMap A p.asIdeal.ResidueField)).toAlgebra
  let q : PrimeSpectrum (AlgebraicClosure p.asIdeal.ResidueField) := ⟨⊥, Ideal.isPrime_bot⟩
  have hq : PrimeSpectrum.comap (algebraMap A (AlgebraicClosure p.asIdeal.ResidueField)) q = p := by
    ext x
    change algebraMap A (AlgebraicClosure p.asIdeal.ResidueField) x ∈ (⊥ : Ideal _) ↔ x ∈ p.asIdeal
    rw [Ideal.mem_bot]
    change algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)
      (algebraMap A p.asIdeal.ResidueField x) = 0 ↔ x ∈ p.asIdeal
    rw [map_eq_zero_iff _ (algebraMap p.asIdeal.ResidueField _).injective,
      Ideal.algebraMap_residueField_eq_zero]
  rw [← hq, ← Module.rankAtStalk_baseChange q, Module.rankAtStalk_eq_finrank_of_free]
  obtain ⟨hfin, hsp⟩ := hSF A S (AlgebraicClosure p.asIdeal.ResidueField) inferInstance
  haveI := Fintype.ofFinite (S →ₐ[A] AlgebraicClosure p.asIdeal.ResidueField)
  have e := AlgEquiv.ofBijective (splitMap fun z => z) hsp
  have h1 := e.toLinearEquiv.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card,
    hd (AlgebraicClosure p.asIdeal.ResidueField)] at h1
  simp [h1]
