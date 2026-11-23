module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDefs
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.PlaneCoeffOneTTens
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MemSupportSumMonomial
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.TypeBd
public import Formalism.SharpRestriction.GrowthBounds.PolynomialLevels.LevNMonomial
public import Formalism.SharpRestriction.GrowthBounds.PolynomialLevels.LowestWeightNonposOffSet
public import Formalism.SharpRestriction.GrowthBounds.PolynomialLevels.MemSpanList
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.JointEIntList
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.NormalSetCounting

theorem compD_eq_homComp {ι : Type} {s : ℕ} {Kf : Type} [Field Kf] (d : ι → ℕ) (H : MvPolynomial (ι × Fin s) Kf) :
    compD d H = homComp d H := rfl

theorem restN (D : Formalism.BasicNotions.D7) : RestN := by
  intro p _ n' r K m _ _ _ O _ _ _ _ S hR hk Fr L₁ N₁ hV _ J _ Dt hT G hG dNo ka e he hne j u hu M
  obtain ⟨hJ, hnL, hsgn, -, -, -⟩ := hT
  have hY := levN_zNo p O hk Fr L₁ N₁ hV Dt.nL hJ hnL (fun i hi x hx hW => tl_surj' hV hJ hnL i hi x hx hW) G hG
  rw [hY] at hne
  have key : ∀ (u' : ℕ) (hu' : u' < Dt.nL j + r + 1) (Sz : Set ℤ),
      (∀ s, (⟨j, s⟩ : TL J Dt.nL r) ∈ NSet Dt.nL j u' ↔ posTL Fr (⟨j, s⟩ : TL J Dt.nL r) ∈ Sz) →
      lam1S LZ Sz (G (segZ j)) ≤ ((M : ℤ) : WithBot ℤ) → ka j u' 0 ≤ M := by
    intro u' hu' Sz hS hM
    have h1 := jproj_ne (normE p K Dt) (eeN D K Dt) (fun i => (eeN_spec D K Dt i).1) (fun i => (eeN_spec D K Dt i).2)
      (eeN_comm D K Dt S hR) (fun i => ka i.1 i.2.val) e he _ hne ⟨j, ⟨u', hu'⟩⟩
    have h2 := (typeBound_proved D (KK O) (TL J Dt.nL r) Dt.trueLet K (NSet Dt.nL j u') (eeN D K Dt ⟨j, ⟨u', hu'⟩⟩)
      (eeN_spec D K Dt ⟨j, ⟨u', hu'⟩⟩).1 (eeN_spec D K Dt ⟨j, ⟨u', hu'⟩⟩).2 _ _ h1).1 M
    apply h2
    rw [compD_eq_homComp]
    refine le_trans (valComp (KK O) (TL J Dt.nL r) K Dt.trueLet (NSet Dt.nL j u') _ dNo).2 ?_
    exact le_trans (lam_prod_le Dt hV hJ hnL hsgn G hG j _ Sz (fun t ht => mem_NSet_fst ht) hS) hM
  exact ⟨key u (by omega) _ fun s => NSet_lt hV hnL j u hu s, key (u + 1) (by omega) _ fun s => NSet_le hV hnL j u hu s⟩

end Formalism.MainNotions.PairMembershipBlocks
