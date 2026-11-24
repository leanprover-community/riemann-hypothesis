module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OmLocU
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

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

def scl (v : PlX X) : Fin (D.R.rS + 1 + D.R.rS) → Fv X.B.I.F v :=
  Fin.append (alp v D.R.rS) (fun b : Fin D.R.rS => (alp v D.R.rS b.castSucc)⁻¹)

def yTup (v : PlX X) : TupV (E := X.B.I.E) v X.B.I.n (D.R.rS + 1 + D.R.rS) :=
  fun i => sc (E := X.B.I.E) v (scl X v i) • ratTup (Fv X.B.I.F v) (tupH (frameOf X u')) i

def localGramMatrixFrame (v : PlX X) : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) :=
  (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v))

abbrev abelian₂ : Set (Fin X.B.I.n → X.B.I.E) := (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

def OmVStd : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → StdHyp X.B.I.cm.sig X.B.I.J ψ

def OmVLat : Prop :=
  ∃ L : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E), Submodule.IsLattice X.B.I.E L ∧ (L : Set (Fin X.B.I.n → X.B.I.E)) = abelian₂ X

def OmVSD : Prop := ∀ v : PlX X, IsSDLoc X.B.I.cm.sig X.B.I.J v (abelian₂ X)

def OmVPrim : Prop := ∀ v : PlX X, IsPrim v (abelian₂ X) (yTup X u' v)

def OmVGram : Prop := ∀ v : PlX X, gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v) = localGramMatrixFrame X u' v

def OmVDet : Prop :=
  ∀ v : PlX X, ¬ (((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) →
    ∃ w ∈ OEv (E := X.B.I.E) v, (localGramMatrixFrame X u' v).det ∈ OEv (E := X.B.I.E) v ∧ (localGramMatrixFrame X u' v).det * w = 1

def OmVScale : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X,
    omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
        {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))} =
      omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
        {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • yTup X u' v}

def OmVBadT : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
    IsSDLoc X.B.I.cm.sig X.B.I.J v (abelian₂ X) → UnramAt (E := X.B.I.E) v → IsPrim v (abelian₂ X) (yTup X u' v) →
    omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
        {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • yTup X u' v} =
      ENNReal.ofReal (absV v (dV v) ^ ((X.B.I.n : ℝ) * (D.R.rS + 1 + D.R.rS : ℕ) - ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2) *
        ∏ j ∈ Finset.Icc (X.B.I.n - (D.R.rS + 1 + D.R.rS)) X.B.I.n,
          (1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))))

def OmVLocU : Prop :=
  ∀ (v : PlX X) (a : ℕ) (Y : TupV (E := X.B.I.E) v X.B.I.n a),
    Formalism.L2.SG.Pf.NcLoc.OmLocU X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) a Y

end Formalism.L2.SG.Pf.NcVal.OmVSt
