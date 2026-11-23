module

public import Development.EtaleCohomology.EtaleTrace.LCoverCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

theorem finrank_frac_of_stdSmooth (k R K : Type) [Field k] [CommRing R] [IsDomain R] [Field K]
    [Algebra k R] [Algebra R K] [Algebra k K] [IsScalarTower k R K] [IsFractionRing R K] (d : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension d k R] :
    Module.finrank K Ω[K⁄k] = d := by
  have : Algebra.FormallyEtale R K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  have : Algebra.IsStandardSmooth k R := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  have : Module.Free R Ω[R⁄k] := Algebra.IsStandardSmooth.free_kaehlerDifferential
  have hr : Module.rank R Ω[R⁄k] = d := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential d
  have hf : Module.finrank R Ω[R⁄k] = d := Module.finrank_eq_of_rank_eq hr
  rw [← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R K).finrank_eq, Module.finrank_baseChange, hf]

theorem FieldDim_of : FieldDim := by
  intro k _ d X _ p hp
  letI := (kHom p).toAlgebra
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := hp.exists_isStandardSmoothOfRelativeDimension (genericPoint X)
  have hUtop : U = ⊤ := by
    have hs : Subsingleton (PrimeSpectrum k) := inferInstance
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have hy : p.base (genericPoint X) ∈ U := e hx
    exact (show y = p.base (genericPoint X) from hs.elim _ _) ▸ hy
  subst hUtop
  have : Nonempty V := ⟨⟨_, hx⟩⟩
  let ψ : CommRingCat.of k ⟶ Γ(X, V) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V e
  have hψ : ψ.hom.IsStandardSmoothOfRelativeDimension d := by
    have := hf.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)
    exact this
  letI : Algebra k Γ(X, V) := ψ.hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension d k Γ(X, V) := hψ
  haveI : IsScalarTower k Γ(X, V) X.functionField := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    have key : Scheme.Hom.appTop p ≫ X.presheaf.germ ⊤ (genericPoint X) trivial =
        Scheme.Hom.appLE p ⊤ V e ≫ X.germToFunctionField V := by
      rw [Scheme.Hom.appLE, Category.assoc]
      exact (congrArg (Scheme.Hom.app p ⊤ ≫ ·) (X.presheaf.germ_res (homOfLE le_top) (genericPoint X) hx)).symm
    simp only [RingHom.algebraMap_toAlgebra, kHom, ψ]
    have H : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial =
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V e) ≫ X.germToFunctionField V := by
      rw [Category.assoc, ← key]
    exact congrArg (fun f => CommRingCat.Hom.hom f c) H
  haveI := functionField_isFractionRing_of_isAffineOpen X V hV
  exact finrank_frac_of_stdSmooth k Γ(X, V) X.functionField d

end LateralTheory.EtaleTrace.Cov
