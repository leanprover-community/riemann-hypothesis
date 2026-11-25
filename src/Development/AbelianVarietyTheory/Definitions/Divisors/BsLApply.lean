module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
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

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.ChernCalc
open GlobalTheory.FlagFibre (Low)
open scoped Matrix

namespace GlobalTheory.FlagCell2

variable {ι : Type} {m : ι → ℕ} {n d : ℕ}

abbrev Cell (m : ι → ℕ) : Type := Σ τ, Low (m τ)

def upU {K : Type} [Zero K] [One K] {s : ℕ} (y : Low s → K) : Matrix (Fin s) (Fin s) K :=
  Matrix.of fun a b => if h : a < b then y ⟨(b, a), h⟩ else if a = b then 1 else 0

def upM {K : Type} [Zero K] [One K] (y : Cell m → K) : Mat m K := fun τ => upU fun s => y ⟨τ, s⟩

def Cell.root (j : Cell m) : Root m := ⟨j.1, j.2.1.2⟩

def bsL {J : Type} (ε : Fin n ≃ Fin d ⊕ J) : V n →L[ℂ] V d :=
  (EuclideanSpace.equiv (Fin d) ℂ).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun a => EuclideanSpace.proj (ε.symm (.inl a))

def fb {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (w : V n) (j : J) : ℂ := w (ε.symm (.inr j))

def pt {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (v : V d) (y : J → ℂ) : V n := WithLp.toLp 2 fun a => Sum.elim (fun b => v b) y (ε a)

def cellPot (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (x : Root m) (w : V n) : ℝ :=
  -Real.log (grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2)

variable [Fintype ι]

def cellFib (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) : Ev n :=
  MvPolynomial.aeval (fun x => ofValues (ddc (cellPot ε G x) w)) ((fibrePoint m).map (algebraMap ℝ ℂ))

def cellForm (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (a : V d → Alt d) (w : V n) : Alt n :=
  pull (bsL ε) (a (bsL ε w)) * (cellFib ε G w : Alt n)

def fibDens (G : Mat m ℂ) (y : Cell m → ℂ) : ℝ :=
  ∏ τ, GlobalTheory.TrueCx.flagConst (m τ) * (G τ).det.re ^ ((m τ : ℤ) - 1) * GlobalTheory.FlagFibre.dens (G τ)ᵀ fun s => y ⟨τ, s⟩


omit [Fintype ι] in
theorem upU_eq {s : ℕ} (y : Low s → ℂ) : upU y = (GlobalTheory.FlagFibre.uni y)ᵀ := by
  ext a b
  simp only [upU, GlobalTheory.FlagFibre.uni, Matrix.of_apply, Matrix.transpose_apply, eq_comm]


omit [Fintype ι] in
theorem bsL_apply {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (w : V n) (a : Fin d) : bsL ε w a = w (ε.symm (.inl a)) := rfl


omit [Fintype ι] in
theorem bsL_pt {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (v : V d) (y : J → ℂ) : bsL ε (pt ε v y) = v := by
  ext a
  simp [bsL_apply, pt]


omit [Fintype ι] in
theorem fb_pt {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (v : V d) (y : J → ℂ) : fb ε (pt ε v y) = y := by
  funext j
  simp [fb, pt]

section Variety

variable {F : Type} [Field F] {X Y : Var F} {σ : F →+* ℂ}

def InCell (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (A : Mat m X.Fn)
    (u : Cell m → Y.Fn) (y : Y.X) : Prop :=
  A ∈ E.S (f y) ∧ upM u * A.map φ ∈ E'.S y

def cellMap (ε : Fin n ≃ Fin X.dim ⊕ Cell m) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str) (c : AlgChart X.str σ X.dim)
    (u : Cell m → Y.Fn) (y : CxPts Y.str σ) : V n :=
  pt ε (c.e (ptMap σ f hf y)) fun j => ratVal (u j) y

def cellSet (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X)
    (hf : f ≫ X.str = Y.str) (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn) : Set (CxPts Y.str σ) :=
  {y | InCell E E' φ f A u (under y) ∧ ptMap σ f hf y ∈ c.e.source}

end Variety

end GlobalTheory.FlagCell2
