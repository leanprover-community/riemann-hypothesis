module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdxAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLatticeIndexCartanDecompositionEqNormPow
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU


theorem _root_.GlobalTheory.T.localLatticeIndex_cartanDecomposition_eq_normPow : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (a : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.LFun.IsFrameAt w (frameLat T) a → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := T.rank), ∀ k₂ ∈ KGL w (n := T.rank), ∀ g : GlobalTheory.FinZeta.Gv T v, GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g = a * (k₁ * t * k₂) * a⁻¹ → GlobalTheory.LocKerMod.idxAt T w h g = qV D.host.E w ^ (∑ i, max (d i) 0).toNat := by
  first | exact @GlobalTheory.LocKerMod.FrameIdx.idxAt_eq_pow | exact GlobalTheory.LocKerMod.FrameIdx.idxAt_eq_pow | (intros; apply GlobalTheory.LocKerMod.FrameIdx.idxAt_eq_pow <;> assumption)
