module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.WeightsConj
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeD
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.GalN UpperTheory.GalN.V
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem isRoot_map_equiv {k : Type} [Field k] (ι : k ≃+* ℂ) (p : Polynomial k) (x : k) :
    (p.map ι.toRingHom).IsRoot (ι x) ↔ p.IsRoot x := by
  have h : (p.map ι.toRingHom).eval (ι x) = ι (p.eval x) := by
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply ι.toRingHom x
  rw [Polynomial.IsRoot.def, Polynomial.IsRoot.def, h]
  exact map_eq_zero_iff ι ι.injective

private theorem isRoot_charpoly_smul {k : Type} [Field k] {n : ℕ} (c : k) (hc : c ≠ 0)
    (M : Matrix (Fin n) (Fin n) k) (x : k) :
    (c • M).charpoly.IsRoot (c * x) ↔ M.charpoly.IsRoot x := by
  have h : Matrix.scalar (Fin n) (c * x) - c • M = c • (Matrix.scalar (Fin n) x - M) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij, mul_sub]
  rw [Polynomial.IsRoot.def, Polynomial.IsRoot.def, Matrix.eval_charpoly, Matrix.eval_charpoly, h,
    Matrix.det_smul]
  simp [hc]

private theorem ratio_smul {k : Type} [Field k] {n : ℕ} (ι : k ≃+* ℂ) (c : k) (hc0 : c ≠ 0)
    (M : Matrix (Fin n) (Fin n) k) (q : ℂ)
    (h : ∀ α : ℂ, (M.charpoly.map ι.toRingHom).IsRoot α →
      ¬ (M.charpoly.map ι.toRingHom).IsRoot (q * α)) :
    ∀ α : ℂ, ((c • M).charpoly.map ι.toRingHom).IsRoot α →
      ¬ ((c • M).charpoly.map ι.toRingHom).IsRoot (q * α) := by
  have key : ∀ y : ℂ, ((c • M).charpoly.map ι.toRingHom).IsRoot (ι c * y) ↔
      (M.charpoly.map ι.toRingHom).IsRoot y := by
    intro y
    obtain ⟨x, rfl⟩ := ι.surjective y
    rw [← map_mul, isRoot_map_equiv, isRoot_map_equiv, isRoot_charpoly_smul c hc0]
  intro α hα hβ
  have hιc : ι c ≠ 0 := (map_ne_zero_iff ι ι.injective).2 hc0
  have hα' : ι c * ((ι c)⁻¹ * α) = α := by field_simp
  have h1 : (M.charpoly.map ι.toRingHom).IsRoot ((ι c)⁻¹ * α) := by
    rw [← key, hα']
    exact hα
  refine h _ h1 ?_
  rw [← key]
  have h2 : ι c * (q * ((ι c)⁻¹ * α)) = q * α := by
    field_simp
  rw [h2]
  exact hβ
