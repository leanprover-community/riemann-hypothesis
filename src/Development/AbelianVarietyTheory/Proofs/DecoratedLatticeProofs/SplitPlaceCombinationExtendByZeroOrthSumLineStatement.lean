module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCombinationExtendByZeroOrthSumLine
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)

theorem _root_.GlobalTheory.T.splitPlace_combination_extendByZero_orthSum_line : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∀ (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛA : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC T LT → α.IsLat LA ΛA → α₀.IsLat LS (lastKer ΛA) → β.IsLat LT ΛT → (∀ (Ψ : Matrix n n' k → ℂ) (c : WO A T →₀ ℂ), CombAt (· = p.v) c → (∀ f₀, Vac ψ A T LA LT (· = p.v) f₀ → Over ψ α β LA LT f₀ Ψ (comb ψ A T c f₀)) → ∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ → Over ψ α₀ β LS LT f₀ (tensCol Ψ (vecInd ΛT)) (comb ψ S T (extS o T c) f₀)) ∧ ∀ (Ψ : Matrix n' n k → ℂ) (c : WO T A →₀ ℂ), CombAt (· = p.v) c → (∀ f₀, Vac ψ T A LT LA (· = p.v) f₀ → Over ψ β α LT LA f₀ Ψ (comb ψ T A c f₀)) → ∀ f₀, Vac ψ T S LT LS (· = p.v) f₀ → Over ψ β α₀ LT LS f₀ (tensRow Ψ (dualInd ΛT)) (comb ψ T S (extT o T c) f₀) := by
  first | exact @GlobalTheory.FinPl.ExtZero.ext_zero | exact GlobalTheory.FinPl.ExtZero.ext_zero | (intros; apply GlobalTheory.FinPl.ExtZero.ext_zero <;> assumption)
