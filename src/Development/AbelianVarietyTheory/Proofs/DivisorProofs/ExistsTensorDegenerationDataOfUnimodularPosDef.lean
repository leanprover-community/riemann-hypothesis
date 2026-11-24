module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorPreDataRigidificationInvPsiZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiIsEvenStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataTauBimultiplicativeStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TensExist

theorem exists_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ D' : DegData R (maximalIdeal R), Nonempty (Tens D.toPre D'.toPre W) := by
  intro R _ _ _ hA D r W hpos hdet
  obtain ⟨D', T, hrig⟩ := GlobalTheory.T.exists_tensorPreData_rigidification_inv_psi_zero R hA D W hpos hdet
  obtain ⟨hp, ht⟩ := GlobalTheory.T.tensorData_psi_mem_maximalIdeal_tendsto_zero R hA D D' W hpos T
  exact ⟨⟨D', GlobalTheory.T.tensorData_psi_isEven R hA D D' W T, GlobalTheory.T.tensorData_tau_bimultiplicative R hA D D' W T hrig, hp, ht⟩, ⟨T⟩⟩

end GlobalTheory.Mum.TensExist
