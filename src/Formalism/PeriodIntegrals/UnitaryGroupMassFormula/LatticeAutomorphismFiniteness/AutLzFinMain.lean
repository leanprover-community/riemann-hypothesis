module

public import Formalism.PeriodIntegrals.AutLzFinite
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismFiniteness.IndSetFinite
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismFiniteness.MulVecMapInjective
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodularSpan

@[expose] public section

noncomputable section

namespace PI.AutLzFinite.SlopeTestRemainingChoices

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem autLzFin_main (D : D7) : PI.AutLzFinite.AutLzFin D := by
  intro hsig Tn hTn F0 Λ hΛ
  obtain ⟨-, hfix, -⟩ := hΛ
  obtain ⟨hlat, hunimod, hlift, -⟩ := hfix
  have hstar : ∀ (τ : D.host.E →+* ℂ) (a : D.host.E), τ (star a) = starRingEnd ℂ (τ a) := by
    haveI := D.host.isCMField_hostE
    intro τ a
    exact NumberField.IsCMField.complexEmbedding_complexConj _ τ a
  have hPX : ∀ x ∈ F0.X, ∀ y ∈ perpS (VS D) F0.X, (VS D).hT x y = 0 := fun x hx y hy => hy x hx
  have hzX : ∀ x ∈ F0.X, (VS D).hT x F0.z = 0 := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, rfl⟩
      exact F0.z_orth a
    · simp
    · intro u v _ _ hu hv
      simp [hu, hv]
    · intro c u _ hu
      simp [hu]
  have hzP : F0.z ∈ perpS (VS D) F0.X := fun x hx => hzX x hx
  have hzz : ∀ τ : D.host.E →+* ℂ, (τ ((VS D).hT F0.z F0.z)).re < 0 := by
    intro τ
    rw [F0.z_norm, map_neg, map_natCast, Complex.neg_re, Complex.natCast_re]
    exact neg_neg_of_pos (by exact_mod_cast hTn)
  have hpos : ∀ τ : D.host.E →+* ℂ, ∀ y ∈ perpS (VS D) F0.X, (VS D).hT F0.z y = 0 → y ∉ F0.X →
      0 < (τ ((VS D).hT y y)).re := by
    intro τ y hy hzy hyX
    have hq : ((VS D).sig τ).2 ≤ D.R.rS + 1 := by
      have e : (VS D).sig τ = D.R.sigY0 := D.sp.baseSpace_signature_eq τ
      rw [e]
      simp [Formalism.BasicNotions.Ranks.sigY0]
    exact pos_perp (S := VS D) hstar τ (hsig τ) hq F0.e F0.e_indep F0.e_iso F0.z F0.z_orth (hzz τ) y
      (fun a => hy _ (Submodule.subset_span ⟨a, rfl⟩)) hzy hyX
  have hspan : Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ :=
    Formalism.HermitianLatticesTheory.IsUnimodular.span_eq_top hunimod (VS D).herm hlat.fg
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((VS D).hT x y) := by
    intro x hx y hy
    have hd : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hunimod
    have h1 : y ∈ Formalism.E.hdual (VS D).hT Λ := by
      have h2 : y ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by rw [hd]; exact hy
      exact h2
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 (h1 x hx)
    have ho' : (VS D).hT x y = algebraMap (𝓞 D.host.E) D.host.E o := ho.symm
    rw [ho']
    exact o.isIntegral_coe
  have hzΛ : F0.z ∈ Λ := hlift.1
  have hfin := indSet_finite (S := VS D) hstar F0.X (perpS (VS D) F0.X) hPX F0.z hzP hzz hpos Λ hspan hint hzΛ
  refine hfin.subset ?_
  rintro φ ⟨γ, hγ, hgΛ, hφ⟩
  obtain ⟨hiso, hXa, hz⟩ := hγ
  have hiso' : ∀ x y, (VS D).hT (γ x) (γ y) = (VS D).hT x y := hiso
  have hXr : F0.Xa D.R.rS = F0.X := by
    simp [FlagG.Xa, FlagG.X, Fin.is_lt, Set.setOf_true, Set.image_univ]
  refine ⟨γ, hiso', hz, ?_, ?_, hφ⟩
  · intro x hx
    have h3 : γ x ∈ Formalism.HermitianLatticesTheory.gmap γ Λ := ⟨x, hx, rfl⟩
    rwa [hgΛ] at h3
  · intro x hxP y hyX
    have hX : F0.X.map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X := by
      rw [← hXr]
      exact hXa D.R.rS
    rw [← hX] at hyX
    obtain ⟨y', hy', rfl⟩ := hyX
    show (VS D).hT (γ y') (γ x) = 0
    rw [hiso']
    exact hxP y' hy'

end PI.AutLzFinite.SlopeTestRemainingChoices
