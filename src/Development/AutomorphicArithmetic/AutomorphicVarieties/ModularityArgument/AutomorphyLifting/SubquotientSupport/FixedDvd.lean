module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IrreducibleWeilDeligneTameLevelEqCharacter
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.V.Z.Win.T2.eq_one_of_charpoly_dvd {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hf : f.IsSemisimple) {n : ℕ} (hd : f.charpoly ∣ (Polynomial.X - 1) ^ n) : f = 1 := by
  obtain ⟨q, hq⟩ := hd
  have h0 := congrArg (Polynomial.aeval f) hq
  rw [map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X,
    map_one] at h0
  have hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hf
  rw [map_one] at hs
  exact sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)

private theorem UpperTheory.V.Z.Win.T2.char_of_dvd {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (M n : ℕ) (hM : 1 ≤ M) (x z : WD h)
    (hx : ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) →
      x.charPol (ineIncl h s) = (Polynomial.X - 1) ^ n)
    (hz : IsIrrWD z) (hd : ∀ σ, z.charPol σ ∣ x.charPol σ) :
    ∃ (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ), z = WD.lpOfChar h ξ hξ ∧
      ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) → ξ (ineIncl h s) = 1 := by
  obtain ⟨m, b, rfl, hb⟩ := hz
  have key : ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) →
      b.ρ (ineIncl h s) = 1 := by
    intro s hs
    have h2 := hd (ineIncl h s)
    rw [hx s hs, WD.charPol_mk] at h2
    exact UpperTheory.V.Z.Win.T2.eq_one_of_charpoly_dvd _ (b.semisimple _) h2
  obtain ⟨ξ, hξ, h1, h2⟩ := UpperTheory.irreducible_weilDeligne_tame_level_eq_character F Ω w A h M hM m b hb key
  exact ⟨ξ, hξ, h1, fun s hs => h2 _ (key s hs)⟩

private theorem UpperTheory.V.Z.Win.T2.val_lt_one {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {M : ℕ}
    (hw : (M : 𝓞 F) ∈ w.asIdeal) : valuation (w.adicCompletion F) (M : w.adicCompletion F) < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [(isEquiv (valuation (w.adicCompletion F))
    (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one]
  have h : Valued.v (((algebraMap (𝓞 F) F (M : 𝓞 F) : F)) : w.adicCompletion F) =
      w.valuation F (algebraMap (𝓞 F) F (M : 𝓞 F)) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have h2 : w.valuation F (algebraMap (𝓞 F) F (M : 𝓞 F)) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w _).mpr hw
  rw [← h] at h2
  have e : (((algebraMap (𝓞 F) F (M : 𝓞 F) : F)) : w.adicCompletion F) = ((M : ℕ) : w.adicCompletion F) := by
    rw [map_natCast]
    exact map_natCast (algebraMap F (w.adicCompletion F)) M
  rwa [e] at h2

private theorem UpperTheory.V.Z.Win.T2.good_ofChar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ) (hχ : GlobalTheory.SmGL.IsSmoothChar χ) :
    UpperTheory.Zero.LLC.Good (IrrGL.ofChar χ hχ) :=
  ⟨{IrrGL.ofChar χ hχ}, hasSupport_self (IrrGL.isCusp_ofChar χ hχ), fun y hy => by
    rw [Multiset.mem_singleton.1 hy]
    exact Or.inl rfl⟩
