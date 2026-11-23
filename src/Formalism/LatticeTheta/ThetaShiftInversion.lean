module

public import Formalism.LatticeTheta.Statement
public import Formalism.LatticeTheta.LatticeThetaProofs.Assembly
public import Formalism.LatticeTheta.LatticeThetaProofs.CovolumeDual
public import Formalism.LatticeTheta.LatticeThetaProofs.DualLattice
public import Formalism.LatticeTheta.LatticeThetaProofs.GaussSchwartz
public import Formalism.LatticeTheta.LatticeThetaProofs.LatticeFourierSeries
public import Formalism.LatticeTheta.LatticeThetaProofs.LatticeSummableDecay
public import Formalism.LatticeTheta.LatticeThetaProofs.Periodization
public import Formalism.LatticeTheta.LatticeThetaProofs.UnfoldCoeff
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.H

section
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem dualIsLattice : DualIsLattice (V := V) := by
  intro Λ _ _
  obtain ⟨ι, _, _, e, he⟩ := exists_basis_span_eq Λ
  refine isLattice_of_eq_span (LinearMap.BilinForm.dualBasis (innerₗ V)
    dualLattice_innerₗ_nondegenerate e) (dual Λ) ?_
  rw [← he, dualLattice_dual_span_eq e]

theorem dualDual : DualDual (V := V) := by
  intro Λ _ _
  obtain ⟨ι, _, _, e, he⟩ := exists_basis_span_eq Λ
  rw [← he, dualLattice_dual_span_eq e, dualLattice_dual_span_eq,
    LinearMap.BilinForm.dualBasis_dualBasis _ innerₗ_isSymm]

variable [MeasurableSpace V] [BorelSpace V]

theorem covolumeDual : CovolumeDual (V := V) := by
  intro Λ _ _ _ _
  obtain ⟨ι, _, _, e, he⟩ := exists_basis_span_eq Λ
  subst he
  have h := covolDual_det_mul
    ((stdOrthonormalBasis ℝ V).reindex ((stdOrthonormalBasis ℝ V).toBasis.indexEquiv e)) e
  set o := (stdOrthonormalBasis ℝ V).reindex ((stdOrthonormalBasis ℝ V).toBasis.indexEquiv e)
  set eD := LinearMap.BilinForm.dualBasis (innerₗ V) covolDual_nondegenerate e with heD
  have hli : LinearIndependent ℤ e := e.linearIndependent.restrict_scalars' ℤ
  have hliD : LinearIndependent ℤ eD := eD.linearIndependent.restrict_scalars' ℤ
  have heq : Submodule.span ℤ (Set.range eD) = dual (Submodule.span ℤ (Set.range e)) :=
    (dualLattice_dual_span_eq e).symm
  have hb : ((↑) : Submodule.span ℤ (Set.range e) → V) ∘ Module.Basis.span hli = e :=
    funext fun i => congrArg Subtype.val (Module.Basis.span_apply hli i)
  have hbD : ((↑) : dual (Submodule.span ℤ (Set.range e)) → V) ∘
      (Module.Basis.span hliD).map (LinearEquiv.ofEq _ _ heq) = eD :=
    funext fun i => by simp [Module.Basis.span_apply]
  rw [ZLattice.covolume_eq_det_mul_measureReal _ MeasureTheory.volume
      ((Module.Basis.span hliD).map (LinearEquiv.ofEq _ _ heq)) o.toBasis,
    ZLattice.covolume_eq_det_mul_measureReal _ MeasureTheory.volume (Module.Basis.span hli) o.toBasis, hb, hbD,
    covolDual_vol_fd, mul_one, mul_one, ← abs_inv]
  exact congrArg abs (eq_inv_of_mul_eq_one_left h)

theorem poissonDecay : PoissonDecay (V := V) := poissonDecay_of (dualIsLattice V) (lattice_summable_decay V) (poisson_periodization V)
  (unfolding_fourier_coefficient V) (lattice_fourier_series V)

theorem poissonSchwartz : PoissonSchwartz (V := V) := poissonSchwartz_of (poissonDecay V) (schwartz_decay_gaussian V)

end

end Formalism.H
