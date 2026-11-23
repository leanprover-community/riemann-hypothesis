module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ArchimedeanSignatureMatchingOfTrivialBranchingSymm
public import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
public import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def ClassMapInjective : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (_ : FormsTiedSym D u Ch chOf),
    Function.Injective (D.fm u).til

def StabiliserMapBijective : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (_ : FormsTiedSym D u Ch chOf),
    ∀ c, Function.Bijective ((D.fm u).stabMap c)

def FormsCarriedToComplement : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
    Formalism.L2.Rows.LowerMapTieS Tf → ∀ φ ∈ (D.fm u).Fi D.R.m, Pt D u φ ∈ (D.fm u).ptC

def NormBoundAtInfinity : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
    Formalism.L2.Rows.LowerMapTieS Tf → Formalism.L2.Ker.BeOnTie D u →
    ∀ (h : (D.fm u).PRat) (v : NumberField.InfinitePlace D.what₂.LL) (x : Vl D u D.R.m),
      (Formalism.HermitianLatticesTheory.majAt (D.fm u).ptLat.b (D.fm u).ptLat.X v ((D.fm u).PtL h x) ((D.fm u).PtL h x)).re ≤
        ptB D u * (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat D.R.m).b ((D.fm u).lat D.R.m).X v x x).re

def ClassMapPropertiesOfSymmetricForms : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
    Formalism.L2.Rows.LowerMapTieS Tf → Formalism.L2.Ker.BeOnTie D u → ClassMapInjectiveBijectiveNorms D u

theorem symmetric_clauses_of_four (h1 : ClassMapInjective) (h2 : StabiliserMapBijective) (h3 : FormsCarriedToComplement) (h4 : NormBoundAtInfinity) : ClassMapPropertiesOfSymmetricForms :=
  fun D u Ch chOf Tf hL hB =>
    ⟨h1 D u Ch chOf Tf, h2 D u Ch chOf Tf, h3 D u Ch chOf Tf hL, h4 D u Ch chOf Tf hL hB⟩

theorem lowerMapTieSym_of (Tf : FormsTiedSym D u Ch chOf) (h : Formalism.L2.Rows.LowerMapTieS Tf) : LowerMapTieSym Tf := h

end Formalism.L2.GlobalTheoryTheory.Br
