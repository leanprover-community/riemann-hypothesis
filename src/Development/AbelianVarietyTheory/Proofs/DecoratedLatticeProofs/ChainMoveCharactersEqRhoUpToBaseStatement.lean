module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainMoveCharactersEqRhoUpToBase
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.chainMove_characters_eq_rho_up_to_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (c : {c // A.chOf i c = α}) (c' : {c // A.chOf (i + 1) c = γ}) x y, IsDetRoot _ (A.h i α c) x → IsDetRoot _ (A.h (i + 1) γ c') y → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) = (A.chr (i + 1) (A.xr i α) : ℂ) * (A.chr (i + 1) (A.xr (i + 1) γ) : ℂ)⁻¹ * ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) * I.A.chiF (B.R.N i) (B.R.N (i + 1)) ((I.stp u a i).rep c.1).1.1.deco.1.N ((I.stp u a (i + 1)).rep c'.1).1.1.deco.1.N := by
  first | exact @GlobalTheory.AdForm.TwDat.chr_moves_eq_rho_base | exact GlobalTheory.AdForm.TwDat.chr_moves_eq_rho_base | (intros; apply GlobalTheory.AdForm.TwDat.chr_moves_eq_rho_base <;> assumption)
