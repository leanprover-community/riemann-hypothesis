module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

def Layer.pull {l : ℕ} [Fact l.Prime] {Γ Δ : Type} [Group Γ] [Group Δ] (j : Δ →* Γ) {a d' : ℕ} {L₀ : FinExt l}
    {Cl : Set (Γ →* GL (Fin a) (Om l))} {ρ' : Γ →* GL (Fin d') ℤ_[l]} (Y : Layer L₀ Cl ρ') :
    Layer L₀ ((fun ρ => ρ.comp j) '' Cl) (ρ'.comp j) where
  m := Y.m
  rep k := (Y.rep k).comp j
  mem k := ⟨Y.rep k, Y.mem k, rfl⟩
  L := Y.L
  le := Y.le
  rep_mem k g := Y.rep_mem k (j g)
  b := Y.b
  b_mem := Y.b_mem
  indep := Y.indep
  span := Y.span
  e := Y.e
  reads k := ⟨fun g => (Y.reads k).equi (j g), (Y.reads k).one⟩
  c := Y.c

def Tower.pull {l : ℕ} [Fact l.Prime] {Γ Δ : Type} [Group Γ] [Group Δ] (j : Δ →* Γ) {d : ℕ}
    {ρ : Γ →* GL (Fin d) ℤ_[l]} (T : Tower ρ) : Tower (ρ.comp j) where
  d' := T.d'
  ρ' n := (T.ρ' n).comp j
  Pi := T.Pi
  onto n := ⟨fun g => (T.onto n).equi (j g), (T.onto n).surj⟩
  f := T.f
  f_equi n g := T.f_equi n (j g)
  f_Pi := T.f_Pi

def Cover.pull {l : ℕ} [Fact l.Prime] {Γ Δ : Type} [Group Γ] [TopologicalSpace Γ] [Group Δ] [TopologicalSpace Δ]
    (j : Δ →* Γ) (hj : Continuous j) {a : ℕ} {L₀ : FinExt l} {r : Γ →* GL (Fin a) (Om l)}
    {Cl : Set (Γ →* GL (Fin a) (Om l))} (C : Cover L₀ r Cl) :
    Cover L₀ (r.comp j) ((fun ρ => ρ.comp j) '' Cl) where
  d := C.d
  ρ := C.ρ.comp j
  cont := C.cont.comp hj
  b := C.b
  e := C.e
  reads := ⟨fun g => C.reads.equi (j g), C.reads.one⟩
  tw := C.tw.pull j
  cont' n := (C.cont' n).comp hj
  lay n := (C.lay n).pull j
  unit := C.unit
  trace := C.trace

theorem cover_pull : ∀ (l : ℕ) [Fact l.Prime] (Γ Δ : Type) [Group Γ] [TopologicalSpace Γ] [Group Δ] [TopologicalSpace Δ] (j : Δ →* Γ), Continuous j → ∀ (a : ℕ) (L₀ : FinExt l) (r : Γ →* GL (Fin a) (Om l)) (Cl : Set (Γ →* GL (Fin a) (Om l))), Cover L₀ r Cl → Nonempty (Cover L₀ (r.comp j) ((fun ρ => ρ.comp j) '' Cl)) :=
  by
  intro _ _ _ _ _ _ _ _ j hj _ _ _ _ C
  exact ⟨C.pull j hj⟩

end GlobalTheory.BKLim
