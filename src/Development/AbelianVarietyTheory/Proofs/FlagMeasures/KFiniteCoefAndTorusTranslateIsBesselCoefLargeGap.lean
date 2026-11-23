module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JEqOrbInt
public import Formalism.SharpRestriction.CuspSpanNormBounds.ContinuousCjIT
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliKFiniteCoefficient
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
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

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

noncomputable section

namespace GlobalTheory.AmpTKGap

theorem isCoef_kfin_and_torus_translate : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) (κ τ : ℝ), 0 < κ → 0 < τ → ∀ f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp), Formalism.MainNotions.S.IsKFinCoefH L.σ f → (∃ s : ℂ, BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' f s) ∧ ∃ s : ℂ, BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' (fun x => f (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ x)) s := by
  intro H k r L l l' κ τ hκ hτ f hf
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  have hDS : (GlobalTheory.AmpTK.rep L).IsDS L.ε L.lam := ⟨L.hlam, hσ⟩
  have hmain := (GlobalTheory.isCoef_of_translate_smul_exists H.1.1.2.2.1 k r L.ε L.lam (GlobalTheory.AmpTK.rep L) L.Wp L.Wq l l' hDS).1
  have hd := Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mem_UH (k := k) (r := r) hκ hτ
  have hdi := Formalism.MainNotions.FrameBoundFromBesselTorus.dMi_mem_UH (k := k) (r := r) hκ hτ
  have h1 : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ BranchingSupport.GG k r := by
    have := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hd hdi
    rwa [Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mul_dMi hκ hτ] at this
  obtain ⟨P, Q, hQ, hP, h⟩ := hf
  refine ⟨hmain f ⟨1, h1, 1, h1, P, Q, hQ, hP, fun g => ?_⟩, hmain _ ⟨_, hd, _, hdi, P, Q, hQ, hP, fun g => ?_⟩⟩
  · exact (congrArg f (by simp : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * g * 1 = g)).trans (h g)
  · exact (congrArg f (Formalism.MainNotions.FrameBoundFromBesselTorus.cj_cjI hκ hτ g)).trans (h g)

end GlobalTheory.AmpTKGap

end
