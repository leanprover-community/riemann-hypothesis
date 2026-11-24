module

public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.NatCastEqZeroOfNotDvd

@[expose] public section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

def GenUnitsC : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (s : ℕ) (u : ℤ_[l]ˣ),
    ((u : ℤ_[l]) - 1 ∈ Ideal.span {(l : ℤ_[l])}) → ((u : ℤ_[l]) - 1 ∉ Ideal.span {(l : ℤ_[l]) ^ 2}) →
      Subgroup.closure (insert (redU l s u) (Set.range fun d : DeltaT l => redU l s d.1)) = ⊤


variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

structure LevBasics (W : LocWach PD LL O v n) (a : ZMod n) (s : ℕ) where
  F : Type
  fF : Field F
  algOF : Algebra O F
  inj : Function.Injective (algebraMap O F)
  hp : ((PD.p : ℕ) : F) ≠ 0
  root : ∃ ζ : F, IsPrimitiveRoot ζ (PD.p ^ (s + 1))
  ev : Rs F PD.p s → LetA O n →+* F
  ev_O : ∀ (ζ : Rs F PD.p s) (x : O), ev ζ (algebraMap O (LetA O n) x) = algebraMap O F x
  ev_letE : ∀ ζ : Rs F PD.p s, ev ζ (letE a) = 1
  ev_π : ∀ ζ : Rs F PD.p s, ev ζ letπ = (ζ : F) - 1
  ev_ps : ∀ ζ : Rs F PD.p s, ev ζ (ps W s) = 0
  ev_pt : ∀ t, t ≠ s → ∀ ζ : Rs F PD.p s, ev ζ (ps W t) ≠ 0
  σ : W.Gam → (ZMod (PD.p ^ (s + 1)))ˣ
  ev_γ : ∀ g (ζ : Rs F PD.p s) x, ev ζ (W.γA g x) = ev (powR F PD.p s (σ g) ζ) x
  gen : Subgroup.closure (insert (σ W.gam) (σ '' (W.DelF : Set W.Gam))) = ⊤


end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
