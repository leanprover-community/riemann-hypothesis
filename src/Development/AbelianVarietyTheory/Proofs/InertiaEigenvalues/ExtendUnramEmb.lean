module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

theorem GlobalTheory.UseLoc.extendUnramEmb : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), K.1 ≤ MaximalUnramifiedExtension l → ∀ e : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1, ∃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = e ∧ ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, τ'.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = e → τ' = τ := by
  intro l _ K LL hK e
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) := by
    intro y
    refine ⟨⟨y.1, ⟨y.2, hK y.2⟩⟩, ?_⟩
    apply Subtype.ext
    rfl
  let φ : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥K.1 :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)
      ⟨(IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1).toRingHom.injective, hsurj⟩
  refine ⟨e.comp φ.symm.toAlgHom, ?_, ?_⟩
  · ext x
    have : φ.symm (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 x) = x := φ.symm_apply_apply x
    simp only [AlgHom.comp_apply]
    exact congrArg (fun z => ((e z : ↥LL.1) : Om l)) this
  · intro τ' hτ'
    ext y
    obtain ⟨x, rfl⟩ := hsurj y
    have h1 := congrArg (fun f : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1 => f x) hτ'
    simp only [AlgHom.comp_apply] at h1
    rw [h1]
    simp only [AlgHom.comp_apply]
    have : φ.symm (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 x) = x := φ.symm_apply_apply x
    exact (congrArg (fun z => ((e z : ↥LL.1) : Om l)) this).symm
