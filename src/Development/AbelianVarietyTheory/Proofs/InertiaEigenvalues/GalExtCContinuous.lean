module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.InertiaEigenvalues

variable {l : ℕ} [Fact l.Prime]

theorem norm_galAlgCl (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv g x).symm

theorem isometry_galAlgCl (g : GQ l) : Isometry (g : Om l → Om l) :=
  AddMonoidHomClass.isometry_of_norm g (norm_galAlgCl g)

noncomputable def galExtC (g : GQ l) : PadicComplex l ≃+* PadicComplex l :=
  UniformSpace.Completion.mapRingEquiv g.toRingEquiv (isometry_galAlgCl g).continuous
    (isometry_galAlgCl g.symm).continuous

theorem galExtC_coe (g : GQ l) (x : Om l) :
    galExtC g (x : PadicComplex l) = ((g x : Om l) : PadicComplex l) :=
  UniformSpace.Completion.map_coe (isometry_galAlgCl g).uniformContinuous x

theorem galExtC_continuous (g : GQ l) : Continuous (galExtC g) :=
  UniformSpace.Completion.continuous_map

theorem norm_galExtC (g : GQ l) (y : PadicComplex l) : ‖galExtC g y‖ = ‖y‖ := by
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (galExtC_continuous g).norm continuous_norm
  | ih x => rw [galExtC_coe, PadicComplex.norm_extends, PadicComplex.norm_extends, norm_galAlgCl]

theorem galExtC_mul (g h : GQ l) : galExtC (g * h) = galExtC g * galExtC h := by
  ext y
  change galExtC (g * h) y = galExtC g (galExtC h y)
  induction y using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (galExtC_continuous _) ((galExtC_continuous g).comp (galExtC_continuous h))
  | ih x => rw [galExtC_coe, galExtC_coe, galExtC_coe, AlgEquiv.mul_apply]

noncomputable def galActC (l : ℕ) [Fact l.Prime] : GQ l →* (PadicComplex l ≃+* PadicComplex l) :=
  MonoidHom.mk' galExtC galExtC_mul

theorem isActC_galActC (l : ℕ) [Fact l.Prime] : IsActC (galActC l) :=
  ⟨galExtC_coe, norm_galExtC⟩

end GlobalTheory.InertiaEigenvalues
