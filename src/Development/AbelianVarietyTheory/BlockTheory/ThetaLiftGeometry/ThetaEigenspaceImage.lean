module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceImage

open Formalism.BasicNotions Formalism.MainNotions.N

def ThetaTMapsIntoEig {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
    x ∈ ZgoodN N A i → HasParamX N A i x Sig →
      ∀ f ∈ MjSig N A i Sig, what₂.thetaT (N.mu i) (N.j i) f ∈ eigC N A i x

def MjSigOut {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    (i : N.Loc) (Sig : List (Part A.CG)) : Submodule ℂ (what₂.Mj (N.j i)) :=
  ⨆ σ ∈ {σ | ∀ w, SplitOut N i w → isoLoc N A Sig w = A.locW i σ w}, what₂.isot (N.j i) σ

def ThetaTMapsIntoEigOut {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
    x ∈ ZgoodN N A i → HasParamX N A i x Sig →
      ∀ f ∈ MjSigOut N A i Sig, what₂.thetaT (N.mu i) (N.j i) f ∈ eigC N A i x

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem mjSig_le_mjSigOut (i : N.Loc) (Sig : List (Part A.CG)) :
    MjSig N A i Sig ≤ MjSigOut N A i Sig := by
  unfold MjSig MjSigOut
  exact biSup_mono fun σ hσ w hw => hσ.2.2 w hw.1

theorem thetaTMapsIntoEig_of_out (h : ThetaTMapsIntoEigOut N A) : ThetaTMapsIntoEig N A :=
  fun i x Sig hx hp f hf => h i x Sig hx hp f (mjSig_le_mjSigOut N A i Sig hf)

theorem thetaTMapsIntoEig_iff_map_le : ThetaTMapsIntoEig N A ↔
    ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
      x ∈ ZgoodN N A i → HasParamX N A i x Sig →
        (MjSig N A i Sig).map (what₂.thetaT (N.mu i) (N.j i)) ≤ eigC N A i x := by
  unfold ThetaTMapsIntoEig
  simp only [Submodule.map_le_iff_le_comap]
  rfl

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceImage
