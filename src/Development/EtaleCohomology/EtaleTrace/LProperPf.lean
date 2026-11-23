module

public import Development.EtaleCohomology.EtaleTrace.LPdCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
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
import Mathlib.RingTheory.TotallySplit
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
open CategoryTheory AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.LProperPf

open LateralTheory.EtaleTrace

theorem bij (k : Type) [Field k] (N : ℕ) :
    Function.Bijective (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)) := by
  constructor
  · intro a b h
    have := congrArg Subtype.val h
    simpa using this
  · rintro ⟨p, hp⟩
    refine ⟨p.coeff 0, Subtype.ext ?_⟩
    have hp2 := hp
    rw [MvPolynomial.mem_homogeneousSubmodule, ← MvPolynomial.totalDegree_zero_iff_isHomogeneous,
      MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hp2
    change _ = p
    conv_rhs => rw [hp2]
    rfl

instance tower (k : Type) [Field k] (N : ℕ) :
    IsScalarTower k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0) (MvPolynomial (Fin (N + 1)) k) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

instance ft (k : Type) [Field k] (N : ℕ) :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0) (MvPolynomial (Fin (N + 1)) k) :=
  Algebra.FiniteType.of_restrictScalars_finiteType k _ _

theorem LProper_of : LPdCut.LProper := by
  intro k _ N
  have hi : IsIso (CommRingCat.ofHom (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bij k N)
  unfold PNto
  infer_instance

end LateralTheory.EtaleTrace.LProperPf
