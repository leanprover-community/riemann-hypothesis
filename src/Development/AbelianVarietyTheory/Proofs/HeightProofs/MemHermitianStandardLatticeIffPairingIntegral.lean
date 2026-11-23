module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ShiftMapsUpDown
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.WeilUnramifiedCompare

section Lattice

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem hT_coord (V : HSpace E) (x y : Fin V.rank → E) :
    V.hT (∑ i, x i • V.frame i) (∑ k, y k • V.frame k) = ∑ i, ∑ k, star (x i) * V.gram i k * y k := by

  rw [map_sum V.hT, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_

  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, HSpace.gram, starRingEnd_apply]
  ring

theorem mem_hermitianStandardLattice_iff_pairing_integral (V : HSpace E) (x : V.V) : x ∈ V.L0 ↔ ∀ y ∈ V.L0, ∃ o : 𝓞 E, (o : E) = V.hT y x := by
  have h : Formalism.E.hdual V.hT V.L0 = V.L0 := V.baseLattice_isUnimodular
  conv_lhs => rw [← h]
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one, LinearMap.restrictScalars_apply]

end Lattice

open GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown (offS homInt homLat latFin latFinAA mapUp mapDown locPart gramFin AEf vacSign vacSignOf theta0
  HyperspecialFixesVacuum HomLatSelfDual mapUp_add mapUp_neg mapUp_zero)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Adeles

variable (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))



variable {F} in
theorem intAf_mul {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a * b ∈ intAf F := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)


end Adeles

variable {X : ThetaX D} {T : ThetaTied D X}

end GlobalTheory.WeilUnramifiedCompare

end
