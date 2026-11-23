module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticePrescribedSplitPlaceStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLat

theorem exists_selfDual_frames : ∀ (D : D7) (S : HSp D) (L₀ : GlobalTheory.FinPl.Lat S), IsSelfDualC S L₀ → ∀ (I : Type) [Finite I] (K : I → Type) [∀ i, Field (K i)] [∀ i, ValuativeRel (K i)] [∀ i, TopologicalSpace (K i)] [∀ i, IsNonarchimedeanLocalField (K i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (K i)) (Y : I → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] (F : ∀ i, GlobalTheory.LocMod.Frame (K i) S.rank (Y i)), (∀ i i', (q i).v = (q i').v → i = i') → ∃ L : GlobalTheory.FinPl.Lat S, IsSelfDualC S L ∧ ∀ i, IntIn (q i) S (F i) L := by
  intro D S L₀ hL₀ I _ K _ _ _ _ q Y _ _ F hinj
  have key : ∀ s : Finset I, ∃ L : GlobalTheory.FinPl.Lat S, IsSelfDualC S L ∧ ∀ i ∈ s, IntIn (q i) S (F i) L := by
    intro s
    refine Finset.induction_on s ⟨L₀, hL₀, by simp⟩ ?_
    intro j s hj ih
    obtain ⟨L, hL, hs⟩ := ih
    obtain ⟨L', hL', hother, hq⟩ := GlobalTheory.T.exists_selfDualLattice_prescribed_splitPlace D (K j) (q j) S (Y j) (F j) L hL
    refine ⟨L', hL', ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact hq
    · have hne : (q i).v ≠ (q j).v := fun h => hj (by obtain rfl := hinj i j h; exact hi')
      have h1 := hs i hi'
      unfold IntIn at h1 ⊢
      rw [hother _ hne]
      exact h1
  haveI := Fintype.ofFinite I
  obtain ⟨L, hL, h⟩ := key Finset.univ
  exact ⟨L, hL, fun i => h i (Finset.mem_univ i)⟩

end GlobalTheory.SplitLat
