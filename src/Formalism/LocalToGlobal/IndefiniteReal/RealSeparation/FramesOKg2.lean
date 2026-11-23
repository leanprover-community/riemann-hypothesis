module

public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.FramesOKg
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

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def l0X (V : HSp D) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  V.L0.comap ((V.frame.equivFun.symm.toLinearMap).restrictScalars (𝓞 D.host.E))

def IsXCol (j : ℕ) (col : Fin (D.sp.Y j).rank) (l : Fin (D.sp.X j).rank) : Prop :=
  (col.val < D.R.k ∧ l.val = col.val) ∨ (D.R.k + (D.R.m - 1 - j) ≤ col.val ∧ l.val = col.val - (D.R.m - 1 - j))

def XBasesAtG (Rl : RealDat3 D A3 Ks) : Prop :=
  ∀ j : ℕ, j < D.R.m → ∃ βX : GL (Fin (D.sp.X j).rank) (EAf D), Formalism.L2.DIV.IsFrame βX (l0X (D.sp.X j)) ∧
    ∀ PP ∈ Rl.Pg, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP →
      ∀ (col : Fin (D.sp.Y j).rank) (l : Fin (D.sp.X j).rank), IsXCol (D := D) j col l →
        ∀ r : Fin (D.sp.Y j).rank, toEAf D ei * (betaY Rl j).val r col =
          toEAf D ei * (xMat (D := D) j).mulVec (fun i => βX.val i l) r

def FramesOKg2 (Rl : RealDat3 D A3 Ks) : Prop := FramesOKg Rl ∧ XBasesAtG Rl

end Formalism.IndefR.Mi

end
