module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.HasCoverByOne
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section FS

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


variable (ι) in
def fsHerm (a : K → ℤ) : HermLine ι where
  a := a
  h := refNorm a
  pos _ hz := refNorm_pos a hz
  smul c z _ := refNorm_smul a c z

theorem fsHerm_h (a : K → ℤ) (z : (Σ k, ι k) → ℂ) : (fsHerm ι a).h z = refNorm a z := rfl

end FS

section Flag

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

abbrev FlBlock : Type := Ψ × Fin (N - 1)

abbrev FlIdx : FlBlock Ψ N → Type := fun q => PlueckerData.Incr ((q.2 : ℕ) + 1) N

open Classical in
noncomputable instance instFintypeFlIdx (q : FlBlock Ψ N) : Fintype (FlIdx Ψ N q) := by
  unfold FlIdx PlueckerData.Incr; infer_instance

abbrev ΩFl : Type := FractionRing (MvPolynomial (Ψ × Fin N × Fin N) ℚ)

def yFl : (Σ q : FlBlock Ψ N, FlIdx Ψ N q) → ΩFl Ψ N := fun p =>
  algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N)
    (Matrix.det (Matrix.of fun a b : Fin ((p.1.2 : ℕ) + 1) =>
      (X (p.1.1, Fin.castLE (step_le p.1.2) a, p.2.1 b) : MvPolynomial (Ψ × Fin N × Fin N) ℚ)))

def PFl : Ideal (MRing (FlIdx Ψ N)) := mCoordIdeal (yFl Ψ N)

def dimFl : ℕ := Fintype.card Ψ * (N * (N - 1) / 2)

def xDeg (p : Ψ × Fin N) : FlBlock Ψ N → ℤ := fun q =>
  if q.1 = p.1 then (if (q.2 : ℕ) = p.2 then 1 else 0) - (if (q.2 : ℕ) + 1 = p.2 then 1 else 0) else 0

def xLine (p : Ψ × Fin N) : HermLine (FlIdx Ψ N) := fsHerm (FlIdx Ψ N) (xDeg Ψ N p)

def monoLines (m : (Ψ × Fin N) →₀ ℕ) (d : ℕ) : Fin d → HermLine (FlIdx Ψ N) := fun k =>
  if h : (k : ℕ) < (Finsupp.toMultiset m).toList.length then
    xLine Ψ N ((Finsupp.toMultiset m).toList.get ⟨k, h⟩)
  else fsHerm (FlIdx Ψ N) 0

def hFlMono (II : IntersectionSystem) (m : (Ψ × Fin N) →₀ ℕ) : ℝ :=
  if m.degree = dimFl Ψ N + 1 then
    II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (dimFl Ψ N + 1) (monoLines Ψ N m (dimFl Ψ N + 1))
  else 0

def hFl (II : IntersectionSystem) (F : RootPoly Ψ N) : ℝ :=
  ∑ m ∈ F.support, ((AddMonoidAlgebra.coeff F m : ℚ) : ℝ) * hFlMono Ψ N II m

end Flag

end GroundTheory.Heights₂.Heights.LowerBoundFree
