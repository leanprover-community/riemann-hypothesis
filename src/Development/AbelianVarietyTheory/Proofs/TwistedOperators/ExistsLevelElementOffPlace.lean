module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramedCongruenceElementMemPrincipalCongruenceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitLocalFrameDiagonalStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceTuplesOneOrbitModUniformizerPowerStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.CosetFJ

theorem besselOrbit_at_badPlace_eq_congruenceTranslate : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ g ∈ grpAt (G.V (.grid (2 * σ + 2) 0)) (· = v), ∀ (u : UX D (σ + 1)), ∀ a ∈ (pcFB W F σ h h').A₁, MxOff (· = v) (mt (G.V (.grid (2 * σ + 2) 0)) g⁻¹ ⬝ (xFB F σ h' ⬝ u.1.1) - xFB F σ h' - a) → ∃ k ∈ lev G (.grid (2 * σ + 2) 0), k ∈ grpAt (G.V (.grid (2 * σ + 2) 0)) (· = v) ∧ MxOff (· = v) (mt (G.V (.grid (2 * σ + 2) 0)) k ⬝ xFB F σ h' - mt (G.V (.grid (2 * σ + 2) 0)) g⁻¹ ⬝ (xFB F σ h' ⬝ u.1.1)) := by
  intro D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv g hg u a ha hoff
  obtain ⟨k, _, _, _, _, p, β, ι, ι', s, t, hpv, hidem, hlat, hι, hι', hιι, hX, hΦ, hA⟩ :=
    GlobalTheory.T.split_local_frame_diagonal D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv
  obtain ⟨ha1, ha2⟩ := hA a ha
  subst hpv
  obtain ⟨k₀, hk₀, hoff'⟩ := GlobalTheory.T.splitPlace_tuples_one_orbit_mod_uniformizer_power D k p _ σ β (xFB F σ h') ι ι' s t (G.pl.depth sc p.v) (G.pl.depth_pos sc _) hι hι' hιι
    hX hΦ g hg u a ha1 ha2 hoff
  have hsd : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.sp.V_is (2 * σ + 2) 0 (by omega) h' (Nat.zero_le _)).sd
  refine ⟨β.gl _, GlobalTheory.T.framedCongruenceElement_mem_principalCongruence D hQ T L μ0 hL sc G W M hM (.grid (2 * σ + 2) 0) hsd p.v hv k p rfl hidem _ β hlat k₀ hk₀, ?_, hoff'⟩
  exact ((GlobalTheory.FrameAt.frame_facts D k p _ _ β).1 _).2 ⟨_, rfl⟩

end GlobalTheory.CosetFJ
