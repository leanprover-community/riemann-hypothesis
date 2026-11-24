module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertTwistedLatticeJetsModularFamily
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

theorem _root_.GlobalTheory.T.hilbertTwistedLattice_jets_modular_family : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι) (α : ι → Matrix (Fin 2) (Fin 2) (ZMod N)) (Ch : ι → ℍ → ℂ) (κ : Emb F → ℕ), (∀ i γ, α (act i γ) = α i * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)) → (∀ i (γ : SL(2, ℤ)) (τ : ℍ), Ch i (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * Ch (act i γ) τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I)) → IsFam act (wt (2 * s) κ : ℕ) (fun i ↦ hfun (2 * s) (twist N L (α i)) κ (Ch i)) := by
  first | exact @GlobalTheory.HilbFam.isFam_hfun_twist | exact GlobalTheory.HilbFam.isFam_hfun_twist | (intros; apply GlobalTheory.HilbFam.isFam_hfun_twist <;> assumption)
