module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcCompFinAwayPtOfNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockScaledIntegralOfLocal
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExtensionEmbeddingEvInfRealAd
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.ThetaLifts.LatticeBasics.EulerA

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP

private theorem evInf_realAd_one {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) :
    evInf F w (realAd F 1) = 1 := by
  apply (InfinitePlace.Completion.extensionEmbedding w).injective
  rw [GlobalTheory.CompanionTheory.RealAdeleComponent.extensionEmbedding_evInf_realAd, map_one]
  simp

theorem UpperTheory.unitaryLocalGroup_le_offPlaces_empty :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {X : Spc F E n} (v : Pl (F := F)), locGrp σ X v ≤ gOff σ X ∅ := by
  intro F E _ _ _ _ _ σ n X v
  refine (Subgroup.closure_le _).2 fun g hg => Subgroup.subset_closure ⟨fun w => ?_, by simp⟩
  have h0 : realAd F 1 • (mat g - 1) = 0 := hg _ (GlobalTheory.ThKTorus.IntegralOfAdic.evFin_realAd F v 1)
  ext i j
  have e := congrArg (fun M : Matrix (Fin n) (Fin n) (AE F E) => compInf F E w (M i j)) h0
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, map_zero] at e
  rw [GlobalTheory.AwayFix.Chart.compInf_smul_away, evInf_realAd_one, one_smul, map_sub, sub_eq_zero] at e
  rw [Matrix.map_apply, e, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp
