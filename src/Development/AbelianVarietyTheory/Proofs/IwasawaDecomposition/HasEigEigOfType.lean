module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows

noncomputable section

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def eigOfType (R : RealDat3 D A3 Ks) (F : Face3 D A3) {X0 : BaseLevelRowSide D} (Y : Read (A3 := A3) R.toRealDat F.lv2 X0)
    (π : D.what₂.FT) : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ :=
  principalLevelFrame.cOfT (Y.PW ⟨0, Y.hm⟩)
    (levS _ (R.βW ⟨0, Y.hm⟩) (R.datWp ⟨0, Y.hm⟩ (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))
    (levChi _ (R.βW ⟨0, Y.hm⟩) (R.datWp ⟨0, Y.hm⟩ (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))
    (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) (principalLevelFrame.rowRepR R.θ (Y.eFT π))

def HasEig (R : RealDat3 D A3 Ks) (F : Face3 D A3) {X0 : BaseLevelRowSide D} (Y : Read (A3 := A3) R.toRealDat F.lv2 X0)
    (π : D.what₂.FT) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Prop :=
  principalLevelFrame.IsEigOf (Y.PW ⟨0, Y.hm⟩)
    (levS _ (R.βW ⟨0, Y.hm⟩) (R.datWp ⟨0, Y.hm⟩ (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))
    (levChi _ (R.βW ⟨0, Y.hm⟩) (R.datWp ⟨0, Y.hm⟩ (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))
    (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) (principalLevelFrame.rowRepR R.θ (Y.eFT π)) c

theorem hasEig_eigOfType {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
    {Y : Read (A3 := A3) R.toRealDat F.lv2 X0} {π : D.what₂.FT} (h : ∃ c, HasEig R F Y π c) :
    HasEig R F Y π (eigOfType R F Y π) := by
  unfold eigOfType principalLevelFrame.cOfT
  unfold HasEig at h ⊢
  rw [dite_eq_left h]
  exact h.choose_spec

end GlobalTheory.Mem.R3

end
