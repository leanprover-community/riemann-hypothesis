module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeL2InnerProduct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

open NumberField MeasureTheory Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.GLFin

noncomputable section

namespace GlobalTheory.GLFin

theorem expGL_image_ball_mem_nhds : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ ε : ℝ, 0 < ε →
    (fun X : Lie E a => GlobalTheory.ExpDeriv.expGL X 1) '' {X | ‖X‖ < ε} ∈ nhds (1 : GL (Fin a) (Cinf E)) := by
  intro E _ _ _ a ε hε
  letI : NormedRing (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  have hd : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin a) (Fin a) (Cinf E) → _)
      ((ContinuousLinearEquiv.refl ℝ (Matrix (Fin a) (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] _)) 0 :=
    hasStrictFDerivAt_exp_zero
  have hmap0 := hd.map_nhds_eq_of_equiv
  rw [NormedSpace.exp_zero] at hmap0
  have hmap : Filter.map (NormedSpace.exp : Matrix (Fin a) (Fin a) (Cinf E) → _) (nhds 0) =
      nhds (1 : Matrix (Fin a) (Fin a) (Cinf E)) := hmap0
  have hopen : IsOpen {X : Matrix (Fin a) (Fin a) (Cinf E) | ‖(Matrix.of.symm X : Lie E a)‖ < ε} :=
    isOpen_lt (continuous_norm.comp (continuous_id : Continuous fun X : Lie E a => X)) continuous_const
  have hball : {X : Matrix (Fin a) (Fin a) (Cinf E) | ‖(Matrix.of.symm X : Lie E a)‖ < ε} ∈
      nhds (0 : Matrix (Fin a) (Fin a) (Cinf E)) := hopen.mem_nhds (by simpa using hε)
  have himg : (NormedSpace.exp : Matrix (Fin a) (Fin a) (Cinf E) → _) ''
      {X : Matrix (Fin a) (Fin a) (Cinf E) | ‖(Matrix.of.symm X : Lie E a)‖ < ε} ∈
      nhds (1 : Matrix (Fin a) (Fin a) (Cinf E)) := hmap ▸ Filter.image_mem_map hball
  have hpre := Units.continuous_val.continuousAt.preimage_mem_nhds (x := (1 : GL (Fin a) (Cinf E))) himg
  refine Filter.mem_of_superset hpre ?_
  rintro u ⟨X, hX, hXu⟩
  refine ⟨Matrix.of.symm X, hX, Units.ext ?_⟩
  rw [GlobalTheory.ExpDeriv.expGL_val, one_smul]
  exact hXu

end GlobalTheory.GLFin

end
