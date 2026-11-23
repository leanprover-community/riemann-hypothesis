module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproximateGermMemCartierIdealModMaxPowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChevalleyExistsLeSupMaximalIdealPowOfAntitoneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMapFibreDivisibilityIdealCompletionLimitStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

theorem GlobalTheory.FibreCorr.exists_correction : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens) (D : EffCartierData M.Z), (U : Set M.Z).Nonempty → (∀ x ∈ D.idealSheaf.support, x ∉ U) → ∀ (z : M₁.Z), IsClosed ({z} : Set M₁.Z) → ∀ k : ℕ, ∃ e : ℕ, ∀ F : M₁.O z, (∀ (q : ℕ) [Fact q.Prime] (y : Sp (OO q) ⟶ M.Z), π (y (cPt q)) = z → Set.range (gPt q ≫ y) ⊆ U → ∀ f, EqAt M D (y (cPt q)) f → ‖M.val (gPt q ≫ y) F‖ ≤ ‖M.val (gPt q ≫ y) f‖ ∨ ∃ h, NonUnitAt M₁ z h ∧ ‖M.val (gPt q ≫ y) F‖ ≤ ‖M.val (gPt q ≫ y) h‖ ^ e) → ∃ G b : M₁.O z, (F : Ω) = G + b ∧ (∀ x' : M.Z, π x' = z → ∀ f', EqAt M D x' f' → (G : Ω) / f' ∈ M.O x') ∧ b ∈ Ideal.span {c : M₁.O z | ¬ IsUnit c} ^ k := by
  intro o Ω _ _ _ _ M₁ M π hπ hprop hn₁ hn U D hU _ z hz k
  haveI := GlobalTheory.FibreCorr.isNoetherianRing_O M₁ z
  have key : ∀ k, ∃ e, GlobalTheory.FibreCorr.approxIdeal hπ U D z e ≤
      GlobalTheory.FibreCorr.fibreIdeal hπ D z ⊔ maximalIdeal (M₁.O z) ^ k := by
    refine GlobalTheory.T.chevalley_exists_le_sup_maximalIdeal_pow_of_antitone (M₁.O z) (GlobalTheory.FibreCorr.approxIdeal hπ U D z) (GlobalTheory.FibreCorr.fibreIdeal hπ D z)
      (GlobalTheory.FibreCorr.approxIdeal_antitone U D z) (GlobalTheory.FibreCorr.pow_le_approxIdeal U D z) ?_
    intro F a ha hK
    have ha' : ∀ n, F - algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z)) (a n) ∈
        (maximalIdeal (M₁.O z)).map (algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z))) ^ n := by
      intro n
      rw [← AdicCompletion.maximalIdeal_eq_map]
      exact ha n
    refine GlobalTheory.T.mem_map_fibreDivisibilityIdeal_completion_limit o Ω M₁ M π hπ hprop hn₁ hn D z hz F a ha' ?_
    intro x' hx' hc f' hf' e
    obtain ⟨N, hN⟩ := GlobalTheory.T.approximate_germ_mem_cartier_ideal_mod_max_pow o Ω M₁ M π hπ hn U D hU z x' hx' hc f' hf' e
    exact ⟨N, fun n hn => hN n hn (a n) (hK n)⟩
  obtain ⟨e, he⟩ := key k
  refine ⟨e, fun F hF => ?_⟩
  have hF' : F ∈ GlobalTheory.FibreCorr.approxIdeal hπ U D z e := hF
  obtain ⟨G, hG, b, hb, hGb⟩ := Submodule.mem_sup.1 (he hF')
  refine ⟨G, b, ?_, fun x' hx' f' hf' => hG x' hx' f' hf', ?_⟩
  · rw [← hGb]; simp
  · have hm : Ideal.span {c : M₁.O z | ¬ IsUnit c} = maximalIdeal (M₁.O z) :=
      Ideal.span_eq (maximalIdeal (M₁.O z))
    rw [hm]
    exact hb
