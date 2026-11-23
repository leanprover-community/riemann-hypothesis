module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CongruenceAtTypePrimes
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibility
public import Formalism.SharpRestriction.LevelLetterCocycles.CongruenceSingleEndomorphism
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatPowSubOneLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff

@[expose] public section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
namespace GlobalTheory.TypePrimeEta
end GlobalTheory.TypePrimeEta
namespace GlobalTheory
theorem typePrimeBound_of_etaBound_alt : ∀ (D : D7) (C : ℝ) (CT : ℕ), 8 * (CT : ℝ) ≤ C →
    _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT (EtaBound CT) → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT := by
  intro D C CT hC hQ i k k' hkk hl r ρ hr hadm eta s S sg U h1 h2 h3 h4 h5 h7 h8
  obtain ⟨c, hη, hL⟩ := hQ i k k' hkk hl r ρ hr hadm eta s S sg U h1 h2 h3 h4 h5 h7 h8
  have hv : (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ) ≤ 2 * D.R.f * (D.R.r : ℝ) ^ 2 := by
    exact_mod_cast TypePrimeEta.val_cardG0g_le D k k' hkk h2
  have key : ∀ π ∈ D.nd.Zgood i,
      (c π : ℝ) + (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ) ≤ rhs C eta i ρ π := by
    intro π hπ
    obtain ⟨N, r', hN2, hN, hr1, hr4, hc⟩ := hL π hπ
    have hA := TypePrimeEta.first_le D.R.f D.R.r D.R.t CT N r' eta D.R.nV C hC hN2 hN hr4 rfl
    unfold rhs eT
    linarith
  have hη' : (D.nd.etaLoc i : ℝ) ≤ ∑ π ∈ D.nd.Zgood i,
      (D.nd.mult i π : ℝ) * ((c π : ℝ) + (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ)) := by
    exact_mod_cast hη
  exact hη'.trans (Finset.sum_le_sum fun π hπ => mul_le_mul_of_nonneg_left (key π hπ) (Nat.cast_nonneg _))
end GlobalTheory
end
