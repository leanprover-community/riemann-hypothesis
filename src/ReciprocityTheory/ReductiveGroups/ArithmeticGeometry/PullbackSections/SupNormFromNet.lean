module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def netNorm (U : Unf Xo c σ r) (la : ∀ k, Wt (U.X k).Ψ r) (NN : Finset (FPt U.X)) (P : FDSec U.X) : ℝ :=
  Real.sqrt ((NN.card : ℝ)⁻¹ * ∑ p ∈ NN, ((U.X p.1).pnorm (la p.1) (P p.1) p.2) ^ 2)

def NnOf (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (NN : Finset (FPt U.X)) (f : Rul Xo c) : ℝ :=
  dmet n (Module.finrank ℚ E / 2) r * netNorm U (laU U a n) NN (rdU U f)

def IsNet (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (NN : Finset (FPt U.X)) : Prop :=
  NN.Nonempty ∧ ∀ P ∈ holSub U.X (laU U a n),
    supN U.X (laU U a n) P ≤ 4 * Real.sqrt NN.card * netNorm U (laU U a n) NN P

def NetExistsSt : Prop :=
  ∃ Cn : ℝ, ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j)
    (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → SupBoundPageRows D large₂ ka →
    ∃ NN : Finset (FPt (T.U j σ).X), IsNet (T.U j σ) (wtA ka) ka.n NN ∧
      Real.log (16 * NN.card) ≤ Cn * Zb D large₂ ^ 3

set_option synthInstance.maxHeartbeats 400000 in
def AlgInjAtSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ),
    GoodEmb T.Q.c σ → ∀ (m : ℕ) (f : Fin m → T.C j ka),
      LinearIndependent T.Q.c.F f → LinearIndependent ℂ (fun i => rdU (T.U j σ) (f i : T.R j))

end ReciprocityTheory.ChartRestriction.G.PullbackSections
