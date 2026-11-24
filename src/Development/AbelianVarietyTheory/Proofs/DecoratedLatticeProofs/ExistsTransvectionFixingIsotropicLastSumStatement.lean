module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTransvectionFixingIsotropicLastSum
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.exists_transvection_fixing_isotropic_last_sum : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (z : Fin V₀.rank → D.host.E), star z ⬝ᵥ V₀.gram *ᵥ z ≠ 0 → ∀ (j : Fin ρ) (a : Fin ρ → D.host.E), a j = 1 → (∀ i, j < i → a i = 0) → j.1 + 1 = ρ → ∀ s : AE D, ∃ v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧ (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (Pi.single k 1)) v * GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a i = 0) ∧ ∀ u : GA D V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → (∀ i : {i : Fin ρ // i ≤ j}, u ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => i.1)) ∧ simpleSum d z u = s := by
  first | exact @GlobalTheory.TransvLast.exists_transv_simpleSum_last | exact GlobalTheory.TransvLast.exists_transv_simpleSum_last | (intros; apply GlobalTheory.TransvLast.exists_transv_simpleSum_last <;> assumption)
