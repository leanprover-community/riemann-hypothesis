module

public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem eq_one_of_dvd {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hf : f.IsSemisimple) {n : ℕ} (hd : f.charpoly ∣ (X - C 1) ^ n) : f = 1 := by
  obtain ⟨q, hq⟩ := hd
  have h0 := congrArg (Polynomial.aeval f) hq
  rw [map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X,
    Polynomial.aeval_C] at h0
  have hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hf
  have := sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)
  rwa [map_one] at this

section

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem link {n m : ℕ} (b : WDRep h (Fin m → ℂ)) (μ : Fin n → Weil h →* ℂˣ)
    (hp : ∀ s, (b.ρ s).charpoly = ∏ i, (X - C (μ i s : ℂ))) (hN : b.N ≠ 0) :
    ∃ i j, (μ i (frob h) : ℂ) = ((normV w : ℕ) : ℂ) * μ j (frob h) := by
  have hs := b.semisimple (frob h)
  have htop : ⨆ c, Module.End.eigenspace (b.ρ (frob h)) c = ⊤ := by
    have h1 := Module.End.iSup_maxGenEigenspace_eq_top (b.ρ (frob h))
    simpa only [hs.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] using h1
  obtain ⟨c, v, hv, hNv⟩ : ∃ c v, v ∈ Module.End.eigenspace (b.ρ (frob h)) c ∧ b.N v ≠ 0 := by
    by_contra hc
    push_neg at hc
    refine hN (LinearMap.ker_eq_top.1 (top_le_iff.1 ?_))
    rw [← htop]
    exact iSup_le fun c v hv => hc c v hv
  have hfv : b.ρ (frob h) v = c • v := Module.End.mem_eigenspace_iff.1 hv
  have hv0 : v ≠ 0 := fun e => hNv (by rw [e, map_zero])
  have root : ∀ z u, u ≠ 0 → b.ρ (frob h) u = z • u → ∃ i, z = (μ i (frob h) : ℂ) := fun z u hu e => by
    have h1 : Module.End.HasEigenvalue (b.ρ (frob h)) z :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 e, hu⟩
    have h2 := Module.End.hasEigenvalue_iff_isRoot_charpoly _ _ |>.1 h1
    rw [hp, Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h2
    obtain ⟨i, -, hi⟩ := h2
    exact ⟨i, by simpa [sub_eq_zero] using hi⟩
  have hc2 : b.ρ (frob h) (b.N v) = (((normV w : ℕ) : ℂ) * c) • b.N v := by
    rw [b.comm_apply, deg_frob, zpow_one, hfv, map_smul, smul_smul]
  obtain ⟨j, hj⟩ := root _ _ hv0 hfv
  obtain ⟨i, hi⟩ := root _ _ hNv hc2
  exact ⟨i, j, by rw [← hi, ← hj]⟩

private theorem link_all {n : ℕ} (μ : Fin n → Weil h →* ℂˣ) (hu : ∀ i (s : Ine (F := E) A), μ i (ineIncl h s) = 1)
    {i j : Fin n} (e : (μ i (frob h) : ℂ) = ((normV w : ℕ) : ℂ) * μ j (frob h)) (s : Weil h) :
    (μ i s : ℂ) = ((normV w : ℕ) : ℂ) ^ deg s * μ j s := by
  obtain ⟨t, ht⟩ := exists_eq_zpow_mul (deg_frob (h := h)) s
  have hv : ∀ k, (μ k s : ℂ) = (μ k (frob h) : ℂ) ^ deg s := fun k => by
    conv_lhs => rw [ht]
    rw [map_mul, map_zpow, hu, mul_one, Units.val_zpow_eq_zpow_val]
  rw [hv, hv, e, mul_zpow]

end
