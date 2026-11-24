module

public import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NotMemOfCoprime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCoprimeMulIsIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section

namespace GlobalTheory.BetaInvIntegral

theorem betaH_inv_integral : ∀ (D : D7) (T : Full D), LawsFull T → ∀ (j : ℕ), InR D j → ∀ {n : ℕ} (Λ : GenLat D.host.E n) (σ : T.Q.c.F →+* ℂ) (p : ℕ), p.Prime → Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt p → ∃ m : ℕ, Nat.Coprime m p ∧ IsIntegral ℤ ((m : ℂ) * (σ (betaH (Dw := T.Q.Dw j) T.Q.c Λ))⁻¹) := by
  intro D T hF j hj n Λ σ p hp hU hT hTp
  have hβ : betaH (Dw := T.Q.Dw j) T.Q.c Λ ≠ 0 := by
    unfold betaH
    split_ifs with h
    · exact h.choose_spec.1
    · exact one_ne_zero
  obtain ⟨M, hM, hint⟩ := GlobalTheory.KerTie.MuqUnit.exists_coprime_mul_isIntegral hp
    (betaH (Dw := T.Q.Dw j) T.Q.c Λ)⁻¹ (fun w hw => by
      obtain ⟨k, hk, h1, h2⟩ := hTp
      have hA : ReciprocityTheory.ChartRestriction.G.PullbackSections.AdaptAt Λ w :=
        ⟨k, GlobalTheory.ShortUnits.not_mem_of_coprime' w hk.symm hw, h1, h2⟩
      have hv := GlobalTheory.ShortUnits.vLa_betaH T hF j hj Λ w hU hT hA
      have hne : w.valuation T.Q.c.F (betaH (Dw := T.Q.Dw j) T.Q.c Λ) ≠ 0 := by simpa using hβ
      have h1' : w.valuation T.Q.c.F (betaH (Dw := T.Q.Dw j) T.Q.c Λ) = 1 := by
        rw [← WithZero.exp_log hne]
        simp only [vLa, neg_eq_zero] at hv
        rw [hv]; rfl
      rw [map_inv₀, h1', inv_one])
  refine ⟨M, hM, ?_⟩
  have := map_isIntegral_int σ hint
  simpa [map_mul, map_inv₀, map_natCast] using this

end GlobalTheory.BetaInvIntegral
