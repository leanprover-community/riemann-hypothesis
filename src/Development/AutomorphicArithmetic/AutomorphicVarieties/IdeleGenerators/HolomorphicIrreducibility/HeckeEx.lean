module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TwoNeZeroNat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open CongruenceSubgroup UpperHalfPlane ModularForm UpperTheory.V.Af
open scoped MatrixGroups ModularForm Manifold

namespace UpperTheory.V.Sd

private def hM (p : ℕ) : Option (Fin p) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(p : ℤ), 0; 0, 1]
  | some u => !![1, ((u : ℕ) : ℤ); 0, (p : ℤ)]

private theorem hM_det (p : ℕ) (x : Option (Fin p)) : (hM p x).det = p := by
  cases x <;> simp [hM, Matrix.det_fin_two_of]

private def hG {p : ℕ} (hp : p.Prime) (x : Option (Fin p)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((Int.castRingHom ℝ).mapMatrix (hM p x)) (by
    rw [← RingHom.map_det, hM_det]; simpa using hp.ne_zero)

private def hT {p : ℕ} (hp : p.Prime) (k : ℕ) {N : ℕ} (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ x : Option (Fin p), χ ((hM p x 0 0 : ℤ) : ZMod N) • f ∣[(k : ℤ)] hG hp x

end UpperTheory.V.Sd

theorem UpperTheory.V.Sd.heckeEx :
    UpperTheory.V.Sd.HeckeEx :=
  _root_.UpperTheory.Reformulated.B.hecke_existence.heckeEx
