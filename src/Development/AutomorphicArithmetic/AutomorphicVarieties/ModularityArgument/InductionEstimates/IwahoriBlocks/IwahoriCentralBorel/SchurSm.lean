module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import GroundTheory.AutomorphicForms.CompactFormulaCountable
public import GroundTheory.AutomorphicForms.SmoothRepSchur
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.schurSm :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) (w : Pl K) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Gw n w) V), GlobalTheory.PRep.IsSmooth ρ → ρ.IsIrreducible → Schur ρ := by
  intro K _ _ n w V _ _ ρ hs hi T hT
  haveI := hi
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (w.adicCompletion K)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → w.adicCompletion K))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (w.adicCompletion K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (Gw n w) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  have hsm : GroundTheory.Automorphic.IsSmooth ρ := fun v => hs v
  let φ : Representation.IntertwiningMap ρ ρ :=
    { toLinearMap := T, isIntertwining' := fun g => LinearMap.ext fun v => hT g v }
  obtain ⟨c, hc⟩ := (algebraMap_intertwiningMap_bijective_of_isSmooth hsm).2 φ
  exact ⟨c, fun v => (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) hc).symm⟩
