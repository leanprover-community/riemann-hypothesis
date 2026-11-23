module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIdentityAtEveryTuple
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaKernelIdentity_at_every_tuple : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) ψ θ x vac c₀ kom dd w Ram rd cK, PinX I l Z ψ θ x vac c₀ → PinColL A ι ψ θ x vac c₀ kom dd w Ram rd cK → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (s : ℂ), (∀ f, IsHol θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) ψ f → ∀ P, pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 = jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s (ColDat.xiS θ i hi f) P) → ∀ α γ (c : {c // A.chOf i c = ι i α}) (c' : {c // A.chOf (i + 1) c = ι (i + 1) γ}) P, (volLev (x i).vol (A.U i (ι i α)) : ℂ) * thetaKO (kom i) (A.h i _ c) (A.h (i + 1) _ c') (pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (comb ψ _ _ (dd i α γ) (vac i)) P) = cK i * A.abelian₂ i c.1 c'.1 (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) := by
  first | exact @GlobalTheory.KerTup.kernel_identity_tuple | exact GlobalTheory.KerTup.kernel_identity_tuple | (intros; apply GlobalTheory.KerTup.kernel_identity_tuple <;> assumption)
