module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def curveRing (y : (Σ k, ι k) → Ω) : Subring Ω :=
  ⨅ (c : ∀ k, ι k) (_ : ∀ k, y ⟨k, c k⟩ ≠ 0), (chartRingZ y c).toSubring

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_curveRing {y : (Σ k, ι k) → Ω} {b : Ω} :
    b ∈ curveRing y ↔ ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → b ∈ chartRingZ y c := by
  simp [curveRing, Subring.mem_iInf]

def curveMul (y : (Σ k, ι k) → Ω) (x : Ω) : AddSubgroup Ω :=
  (curveRing y).toAddSubgroup.map (AddMonoidHom.mulLeft x)

end Objects

def CurveCharts.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K'),
    IsArithVar (mCoordIdeal y) 1 →
      Module.Finite ℤ (curveRing y) ∧
      Module.finrank ℤ (curveRing y) = Module.finrank ℚ (blockFnField y) ∧
      ∀ m : Ideal (curveRing y), m.IsMaximal → ∃ t : T, y ⟨(), t⟩ ≠ 0 ∧
        ∀ u : T, ∃ a b : curveRing y, b ∉ m ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a

def VertRIndex.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → HermLine (fun _ : Unit => T)) s =
        Real.log (genIndex (chartLat y (fun _ => 1) 1) (curveMul y (aeval y s)))

def SectionIndexNorm.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      (Module.finrank (blockFnField y) K' : ℝ) *
          Real.log (genIndex (chartLat y (fun _ => 1) 1) (curveMul y (aeval y s))) =
        Real.log |(Algebra.norm ℚ (aeval y s) : ℝ)| +
          Real.log (genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup
            (1 : Submodule (𝓞 K') K').toAddSubgroup)

end

end GroundTheory.Heights₂.Heights
