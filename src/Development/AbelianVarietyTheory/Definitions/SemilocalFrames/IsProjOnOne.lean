module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.Deep

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

def frame (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) : Matrix (Fin I.n) (Fin I.n) ℂ :=
  I.P v * uMat (x.1 v)

def crd (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) (y : Fin I.n → I.E) : EuclideanSpace ℂ (Fin I.n) :=
  WithLp.toLp 2 ((frame I x v)⁻¹ *ᵥ fun i => I.φ v (y i))

def SatX (I : AutInst) (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Prop :=
  Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) S

def SizesGe (I : AutInst) (x : I.GA) (B B' : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo : ℝ) : Prop :=
  ∀ N : Submodule (𝓞 I.E) (Fin I.n → I.E), B' < N → N ≤ B → lo ≤ Formalism.HN.sizeQ (bas I) (frm I x) N B'

def SizesLe (I : AutInst) (x : I.GA) (A A' : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hi : ℝ) : Prop :=
  ∀ N : Submodule (𝓞 I.E) (Fin I.n → I.E), A' ≤ N →
    Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) A N → N ≠ A →
      Formalism.HN.sizeQ (bas I) (frm I x) A N ≤ hi

def omega (I : AutInst) (x : I.GA) (W : Submodule I.E (Fin I.n → I.E)) (ρ : ℝ) : Set I.GA :=
  {y | y.2 = x.2 ∧ ∃ A Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ,
    (∀ v, Formalism.REAL.inG (I.ε v) (A v) ∧ Formalism.REAL.inG (I.ε v) (Z v)) ∧
    Real.sqrt (∑ v, Formalism.REAL.hs (A v)) + Real.sqrt (∑ v, Formalism.REAL.hs (Z v)) ≤ ρ ∧
    (∀ v, uMat (y.1 v) = uMat (x.1 v) * NormedSpace.exp (A v) * NormedSpace.exp (Z v)) ∧
    ∀ s t : ℝ, ∃ m : I.Ginf, ((m, 1) : I.GA) ∈ I.NA W ∧
      ∀ v, uMat (m v) * uMat (x.1 v) =
        uMat (x.1 v) * NormedSpace.exp ((s : ℂ) • A v) * NormedSpace.exp ((t : ℂ) • Z v)}

def IsReps (B : RowsAut) (T : B.Hs →L[ℂ] B.I.L2 B.μf B.fund) (Fr : B.Hs → B.I.GA → ℂ) : Prop :=
  ∀ P : ℕ, ∀ u ∈ VP B P, GlobalTheory.Dec.IsContRep B (T u) (Fr u) ∧
    (∀ k ∈ B.I.Kg B.g, ∀ y, Fr u (y * (1, k)) = Fr u y) ∧
    ∀ (E : gInf B) (y : B.I.GA),
      HasDerivAt (fun t : ℝ => Fr u (y * ((fun v => expU (t • E v)), 1))) (Fr (dAct B E u) y) 0

def vv (B : RowsAut) {D : ℕ} (Fr : Fin D → B.Hs → B.I.GA → ℂ) (u : B.Hs) (y : B.I.GA) :
    EuclideanSpace ℂ (Fin D) :=
  WithLp.toLp 2 fun i => Fr i u y

end GlobalTheory.Deep
