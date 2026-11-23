module

public import GroundTheory.LocalFields.MaximalUnramified
public import GroundTheory.ProfiniteCohomology.CupProducts
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.InvariantSplit
public import GroundTheory.ProfiniteCohomology.PoincareDuality.Torsion
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KummerCharacterTameFormula
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

theorem _root_.GlobalTheory.T.kummer_character_tame_formula : ∀ (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] (n : ℕ) [NeZero n] (ζ y : Ωˣ) (a : Kˣ), ζ ^ n = 1 → ord (a : K) = 1 → (y : Ω) ^ n = algebraMap K Ω a → ∀ (κ χ : Gal(Ω/K) → ZMod n), (∀ g : Gal(Ω/K), g (y : Ω) = (ζ : Ω) ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → Continuous χ → (∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1) → ∀ x : cocycles (galUnits.{0} K Ω) 2, (∀ s : Fin 2 → Gal(Ω/K), cochainOf _ (cocycleι _ 2 x) s = Additive.ofMul (ζ ^ (κ (s 0) * χ (s 1)).val)) → brauerInv K Ω (cohomologyπ _ 2 x) = - zmodToQZ n 1 := by
  first | exact @GlobalTheory.CompanionTheory.KummerCupInv.inv_kummerCup | exact GlobalTheory.CompanionTheory.KummerCupInv.inv_kummerCup | (intros; apply GlobalTheory.CompanionTheory.KummerCupInv.inv_kummerCup <;> assumption)
