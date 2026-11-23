module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.CoverCone

theorem inCone_of_kTypesAbove : GlobalTheory.Dec.KTypesAbove → ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (P : SignedPar n) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e P.sgn → Factors R.U e σ → IsDSPar P σ → ∀ (μ : Ix p q → ℚ) v, IsHW R.HK.act μ v → InCone (blockPar P e) μ := by
  intro KTA p q n e P T R σ hb hσ hds μ v hv
  obtain ⟨S, hS⟩ := GlobalTheory.RealPar.isKTypeOf_of_isHW R hb hσ μ ⟨v, hv⟩
  obtain ⟨c, hc, hμ⟩ := KTA n P.sgn P.lam R.U.H σ P.hc hds _ S hS
  refine ⟨fun a b => c (e a) (e b), fun a b hab => ?_, ?_⟩
  · have h2 := P.hc.1 (hc _ _ hab)
    rw [← GlobalTheory.RealPar.ratEntry_cast, ← GlobalTheory.RealPar.ratEntry_cast] at h2
    exact_mod_cast h2
  · funext x
    apply Rat.cast_injective (α := ℝ)
    have hx := congrFun hμ (e x)
    simp only [Equiv.symm_apply_apply] at hx
    push_cast
    rw [hx, GlobalTheory.RealPar.blattner_eq P hb (lam := GlobalTheory.RealPar.blockPar P e) (fun a => GlobalTheory.RealPar.ratEntry_cast P (e a)) x]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    congr 1
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GlobalTheory.RealPar.root_apply]
    split_ifs <;> simp

end GlobalTheory.CoverCone
