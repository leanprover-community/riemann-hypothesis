module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepInverseCharacterLocalComponentChainTame
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.QTw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.step_inverse_character_local_component_chain_tame : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (P : BadPr I a), P.1 ∉ (B.primes X).vGs → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt (D := I.rec7 l Z) q.e P.1 → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt P.1 x) → DenseRange (ofSplit q).pr → ∀ (i : ℕ) (hi : i < B.R.m) (χ : (AE (I.rec7 l Z))ˣ →* Circle), ChrEq (D := I.rec7 l Z) χ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → ∀ μ : kˣ →* ℂˣ, (ofSplit q).IsComp χ⁻¹ μ → (∀ (x : B.fields.E) (u : kˣ), (u : k) = (ofSplit q).pr x → (μ u : ℂ) = B.embLL (Formalism.L2.Col.muAt I.Ch I.sel (I.tup a) (I.cst a) i P x)) ∧ IsTame μ := by
  first | exact @GlobalTheory.QTw.StepChar.comp_eq_muAt_and_tame | exact GlobalTheory.QTw.StepChar.comp_eq_muAt_and_tame | (intros; apply GlobalTheory.QTw.StepChar.comp_eq_muAt_and_tame <;> assumption)
