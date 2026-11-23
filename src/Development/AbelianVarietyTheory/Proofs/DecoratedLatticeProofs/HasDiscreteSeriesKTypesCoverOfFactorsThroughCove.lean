module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CasimirEqGelfandValueOfInfinitesimalCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HighestWeightLineOfKTypeMultiplicityOneStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InConeOfKTypesAbove
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondGelfandInvariantValueEqStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.CoverDS

theorem hasTypes_of_factors : GlobalTheory.Dec.LowKMultOne → GlobalTheory.Dec.KTypesAbove → GlobalTheory.Dec.DSInfChar →
    ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (P : SignedPar n) (T : GrpData p q) (R : DSRep T)
      (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)),
      BlockOrd e P.sgn → Factors R.U e σ → IsDSPar P σ → HasTypes R (blockPar P e) := by
  intro h1 h2 h3 p q n e P T R σ hb hf hd
  have hc : ∀ a, ((blockPar P e a : ℚ) : ℝ) = P.lam (e a) := fun a => ratEntry_cast P (e a)
  have hlow : (fun i => ((blattner (blockPar P e) (e.symm i) : ℚ) : ℝ)) = Formalism.QuantumDeterminants.lowK P.sgn P.lam := by
    funext i
    rw [blattner_eq P hb hc, e.apply_symm_apply]
    rfl
  have hn : p + q = n := by simpa using Fintype.card_congr e
  refine ⟨?_, fun v => ?_, GlobalTheory.CoverCone.inCone_of_kTypesAbove h2 p q n e P T R σ hb hf hd⟩
  · refine GlobalTheory.T.highestWeightLine_of_kTypeMultiplicityOne p q n e P.sgn T R σ hb hf _ ?_ ?_
    · rw [hlow]
      exact hd.2.2.2.2.2.1
    · rw [hlow]
      exact h1 n P.sgn P.lam _ σ P.hc hd
  · rw [GlobalTheory.T.casimir_eq_gelfandValue_of_infinitesimalCharacter p q n e P.sgn T R σ hb hf _ (h3 n P.sgn P.lam _ σ P.hc hd) v, GlobalTheory.T.secondGelfandInvariant_value_eq, hn]
    congr 1
    have hc' : ∀ a, ((blockPar P e a : ℚ) : ℂ) = ((P.lam (e a) : ℝ) : ℂ) := fun a => by
      rw [← hc a]; simp
    rw [normSq]
    push_cast
    simp only [hc']
    rw [Equiv.sum_comp e (fun a => ((P.lam a : ℝ) : ℂ) ^ 2)]

end GlobalTheory.CoverDS
