module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitarisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfNodupSumMultisetOfEq
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicWeightOfAutomorphicDefiniteUnitar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotientsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh

namespace GlobalTheory.BcSpehProof

theorem hasInfCharGL_unique {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} (hV : V ≠ ⊥) {τ : E →+* ℂ} {m m' : Multiset ℂ} (h : HasInfCharGL V τ m)
    (h' : HasInfCharGL V τ m') : m = m' := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV
  have e : ((m.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod =
      ((m'.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod := by
    refine Polynomial.funext fun u => ?_
    have := smul_left_injective ℂ h0 ((h.2 u φ hφ).symm.trans (h'.2 u φ hφ))
    simpa [Polynomial.eval_multiset_prod, Multiset.map_map] using this
  have e2 := congrArg Polynomial.roots e
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e2
  exact Multiset.map_injective neg_injective e2

theorem spehInf_eq (d : ℕ) (m : Multiset ℂ) : GlobalTheory.SphGal.spehInf d m = GlobalTheory.DefiniteBC.spehInf d m := by
  unfold GlobalTheory.SphGal.spehInf GlobalTheory.DefiniteBC.spehInf
  rw [← List.sum_ofFn, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

end GlobalTheory.BcSpehProof

namespace GlobalTheory.BcSpehProof

theorem isUnitarisable_of_equiv' {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : π.Equiv σ) (h : IsUnitarisable π) : IsUnitarisable σ := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨(B ∘ₗ φ.symm.toLinearEquiv.toLinearMap).compl₂ φ.symm.toLinearEquiv.toLinearMap, fun v w => h1 _ _,
    fun v hv => h2 _ (φ.symm.toLinearEquiv.map_ne_zero_iff.2 hv), fun g v w => ?_⟩
  have e : ∀ v, φ.symm.toLinearEquiv (σ g v) = π g (φ.symm.toLinearEquiv v) := fun v =>
    φ.symm.toIntertwiningMap.isIntertwining _ _ g v
  show B (φ.symm.toLinearEquiv (σ g v)) (φ.symm.toLinearEquiv (σ g w)) = _
  rw [e, e, h3]
  rfl

theorem hasInfChar_eq_of_sigma {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a b : ℕ} {P : CuspSub E a}
    {Q : CuspSub E b} (h : (⟨a, CG.mk P⟩ : Σ c, CG E c) = ⟨b, CG.mk Q⟩) {τ : E →+* ℂ} {m m' : Multiset ℂ}
    (hm : P.HasInfChar τ m) (hm' : Q.HasInfChar τ m') : m = m' := by
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h
  exact (CuspSub.Iso.hasInfChar (Quotient.exact (eq_of_heq h2)) hm).unique hm'

end GlobalTheory.BcSpehProof
