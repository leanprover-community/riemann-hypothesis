module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.TjcosetsFF
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta IsDedekindDomain NumberField Formalism.UG.P

namespace GlobalTheory.MeasTupleEq

theorem map_residue_surjective (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue O)) := by
  intro g
  classical
  let M : Matrix (Fin n) (Fin n) O := fun a b =>
    Function.surjInv (IsLocalRing.residue_surjective (R := O)) ((g : Matrix (Fin n) (Fin n) _) a b)
  have hM : M.map (IsLocalRing.residue O) = (g : Matrix (Fin n) (Fin n) _) := by
    ext a b
    simp only [M]
    exact Function.surjInv_eq _ _
  have hdet : IsUnit M.det := by
    have h1 : IsUnit (IsLocalRing.residue O M.det) := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using (Matrix.GeneralLinearGroup.det g).isUnit
    exact (isUnit_map_iff (IsLocalRing.residue O) _).1 h1
  refine ⟨Matrix.GeneralLinearGroup.mk'' M hdet, Units.ext ?_⟩
  exact hM

variable {D : D7} {X : ThetaX D}

end GlobalTheory.MeasTupleEq

end
