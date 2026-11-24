module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.TwoBlockModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

section Cycle

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
def vertCycleNum (P : Ideal (MRing ι)) (s : MRing ι) {n : ℕ} (e : Fin n → K → ℤ) : ℝ :=
  ∑ᶠ W ∈ divSupp P s, (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
    (if IsHorizontal W then 0 else (geoNum n W e : ℝ) * Real.log (charOf W))

theorem vertR_eq_vertCycleNum (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) :
    ReciprocityTheory.ChartRestriction.G.AI.I2.vertR P L s = vertCycleNum P s (fun j => (L j).a) :=
  rfl

end Cycle

section TwoBlock

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def twoBlockDen (c : κ) : MRing (FinTwoTypeFamily κ) :=
  X ⟨0, c⟩

def twoBlockNum (l : Ix κ → ℤ) : MRing (FinTwoTypeFamily κ) :=
  ∑ j : Ix κ, MvPolynomial.C (l j) * X ⟨1, j.2⟩

def twoBlockVert (x x' : Ix κ → Ω) (c : κ) (l : Ix κ → ℤ) {n : ℕ} (e : Fin n → Fin 2 → ℤ) : ℝ :=
  vertCycleNum (twoBlockIdeal x x') (twoBlockNum l) e - vertCycleNum (twoBlockIdeal x x') (twoBlockDen c) e

def twoBlockDegList (D i : ℕ) : Fin D → Fin 2 → ℤ :=
  fun j => if (j : ℕ) < i then Pi.single 0 1 else Pi.single 1 1

theorem twoBlockDegList_eq (m m' : ConeMetric ℂ (Ix κ)) (D i : ℕ) (j : Fin D) :
    twoBlockDegList D i j = (twoBlockList m m' D i (if (j : ℕ) < i then j.castSucc else j.succ)).a := by
  unfold twoBlockDegList twoBlockList
  split_ifs with h1 h2 h2 <;> simp_all [blockLine]
  omega

end TwoBlock

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
