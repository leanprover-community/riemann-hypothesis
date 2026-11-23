module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SandwichedFlipRouteThroughSmallEqInvConstRouteBi
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise


theorem _root_.GlobalTheory.T.sandwichedFlip_routeThroughSmall_eq_inv_const_routeBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (M : Vol G) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : ℕ) (hi : i < D.R.m) (hj : j < D.R.m) (c : ℂ), c ≠ 0 → CommutesWith W B ρ t ⟨i, hi⟩ ⟨j, hj⟩ c → M.Is t → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ (A : Path T (.grid 0 D.R.m) (.grid i (j + 1))) (Bp : Path T (.grid (i + 1) j) (.grid D.R.m 0)), GlobalTheory.FlipRun.OnGrid D.R.m t A → GlobalTheory.FlipRun.OnGrid D.R.m t Bp → ∀ (e : AE D), IsIdemSum e (locPl G t) → ∀ (α : PureT G A) (β : PureT G Bp) (φA : PureT G A) (φB : PureT G Bp), GlobalTheory.FlipRun.VecAll ρ e A φA α → GlobalTheory.FlipRun.VecAll ρ e Bp φB β → ∀ (σs : TotT G (routeSmall t i j)) (σb : TotT G (routeBig t i j)) (Φ : ∀ w, Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ), (∀ w ∈ locPl G t, GlobalTheory.SplitFlip.IsNatDatum (unifAt w) (depthAt G w) (Φ w)) → HasFlip B t ρ ⟨i, hi⟩ ⟨j, hj⟩ (depthAt G) Φ σb σs → ∀ F : Fn G (.grid 0 D.R.m), GlobalTheory.FlipRun.IsCuspListed W.θ _ F → ∀ Q : GlobalTheory.FlipRun.PolE G →₀ ℂ, liftT W M _ (GlobalTheory.FlipRun.tensE W _ Q (((σs).sum fun d c => Finsupp.single (((α).append d).append (β)) c) : TotT G ((A.comp (routeSmall t i j)).comp Bp))) F = c⁻¹ • liftT W M _ (GlobalTheory.FlipRun.tensE W _ (GlobalTheory.FlipRun.flipPolE ρ i j Q) (((σb).sum fun d c => Finsupp.single (((α).append d).append (β)) c) : TotT G ((A.comp (routeBig t i j)).comp Bp))) F := by
  first | exact @GlobalTheory.FlipRun.oneFlip_sandwich | exact GlobalTheory.FlipRun.oneFlip_sandwich | (intros; apply GlobalTheory.FlipRun.oneFlip_sandwich <;> assumption)
