module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.cyclotomicChar_eq_locPow_of_localArtin_unit :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (σ : Weil h),
    valuation (w.adicCompletion F) (a σ : w.adicCompletion F) = 1 →
    ((cycBar F Ω p σ : (Qbar p)ˣ) : Qbar p) = GlobalTheory.HeckeGal.locPow ι (fun _ => 1) w (a σ : w.adicCompletion F) := by
  intro hG F Ω _ _ _ _ _ w A h a ha p _ ι σ hv
  obtain ⟨art, hart⟩ := hG F Ω
  obtain ⟨μ, hμ, hL⟩ := hart.exists_isLAdicOf ι (GlobalTheory.Published.CharAboveModel.absPow_isAlgPos F 1)
  have e := GlobalTheory.Published.CharAboveModel.eq_cyc_pow hart hμ hL
  have h1 := hL.loc (a σ) σ (ha.glob art hart σ)
  have : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion F))
    (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))
  have hu : Valued.v (a σ : w.adicCompletion F) = 1 := he.eq_one_iff_eq_one.1 hv
  have h2 : (GlobalTheory.HeckeGal.Model.absPow F ((1 : ℕ) : ℝ)).loc w (a σ) = 1 :=
    (GlobalTheory.HeckeGal.Model.absPow_isAbsPow F ((1 : ℕ) : ℝ)).1 w _ hu
  rw [h2, e, pow_one, cyc_eq_map_cycZ] at h1
  simp only [Units.val_one, map_one, one_mul, Nat.cast_one] at h1
  exact h1
