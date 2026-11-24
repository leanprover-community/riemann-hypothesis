module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Zero
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf

namespace GlobalTheory.WeilDeligne

theorem eq_zero_of_commute_of_separable {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {f N : Module.End ℂ V} (hf : f.charpoly.Separable)
    (hc : Commute f N) (hN : IsNilpotent N) : N = 0 := by
  obtain ⟨k, hk⟩ := hN

  have hline : ∀ μ : ℂ, ∀ v ∈ f.maxGenEigenspace μ, N v = 0 := by
    intro μ
    have hdim : Module.finrank ℂ (f.maxGenEigenspace μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq]
      exact Polynomial.rootMultiplicity_le_one_of_separable hf μ
    obtain ⟨v₀, hv₀⟩ := finrank_le_one_iff.mp hdim
    have hgen : ∀ v ∈ f.maxGenEigenspace μ, ∃ c : ℂ, v = c • (v₀ : V) := by
      intro v hv
      obtain ⟨c, hcv⟩ := hv₀ ⟨v, hv⟩
      exact ⟨c, (congrArg Subtype.val hcv).symm⟩
    obtain ⟨c, hNv⟩ := hgen _ (Module.End.mapsTo_maxGenEigenspace_of_comm hc μ v₀.2)
    have hpow : ∀ m : ℕ, (N ^ m) (v₀ : V) = c ^ m • (v₀ : V) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hNv, smul_smul, ← pow_succ]
    have h0 : N (v₀ : V) = 0 := by
      have hz := hpow k
      rw [hk, LinearMap.zero_apply] at hz
      rcases smul_eq_zero.mp hz.symm with h | h
      · rw [hNv, (pow_eq_zero_iff'.mp h).1, zero_smul]
      · rw [h, map_zero]
    intro v hv
    obtain ⟨a, rfl⟩ := hgen v hv
    rw [map_smul, h0, smul_zero]
  ext v
  have hv : v ∈ ⨆ μ, f.maxGenEigenspace μ := by
    rw [Module.End.iSup_maxGenEigenspace_eq_top]; trivial
  exact Submodule.iSup_induction _ (motive := fun v => N v = 0) hv hline (map_zero N)
    (fun x y hx hy => by rw [map_add (f := _), hx, hy, add_zero])

end GlobalTheory.WeilDeligne

theorem GlobalTheory.WeilDeligne.WD.noMonodromy_of_inertia_separable_charpoly (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : GlobalTheory.WeilDeligne.WD h) :
    ∀ σ ∈ Ine (F := E) A, (x.inePol σ).Separable → x.mono0 := by
  intro σ hσ
  induction x using Quotient.inductionOn with
  | h a =>
    obtain ⟨n, a⟩ := a
    have hw : σ ∈ Weil h := Ine_le_Weil h hσ

    have hcomm : Commute (a.ρ ⟨σ, hw⟩) a.N := by
      have hc := a.comm ⟨σ, hw⟩
      rw [deg_eq_zero_iff.mpr hσ, zpow_zero, one_smul] at hc
      exact hc
    simp only [WD.mono0, WD.inePol, WD.charPol, dif_pos hw, Quotient.lift_mk, WDRep.Mono0]
    intro hs
    exact eq_zero_of_commute_of_separable hs hcomm a.nilpotent

end
