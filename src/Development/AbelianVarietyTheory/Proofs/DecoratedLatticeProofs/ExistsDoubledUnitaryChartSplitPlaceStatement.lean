module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubledUnitaryChartSplitPlace
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)


theorem _root_.GlobalTheory.T.exists_doubled_unitary_chart_split_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L], ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E), IsSplitChart σ J L h e → ∃ f : GLoc σ Q v ≃* GL (Fin (n + n)) (w.adicCompletion E), (∀ g, g ∈ KFin σ Q L v ↔ f g ∈ KGL w (n := (n + n))) ∧ (∀ y y', f (ioH _ σ hQ (y, y')) = blkGL finSumFinEquiv (e y, e y')) ∧ (∀ g, g ∈ siegelH (Fv F v) σ Q ↔ KeepsDiag finSumFinEquiv (f g).1) ∧ ∀ p : siegelH (Fv F v) σ Q, toCompl h (aH _ σ Q p).1 = (leviMat finSumFinEquiv (f p).1).det ∧ ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → ordL (toCompl h' (aH _ σ Q p).1) = -ordL (quotMat finSumFinEquiv (f p).1).det := by
  first | exact @GlobalTheory.LFun.DblSplit.exists_dbl_chart | exact GlobalTheory.LFun.DblSplit.exists_dbl_chart | (intros; apply GlobalTheory.LFun.DblSplit.exists_dbl_chart <;> assumption)
