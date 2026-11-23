module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

theorem exists_linearEquiv_map_eq_of_finrank_eq {k V : Type} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (W W' : Submodule k V)
    (h : Module.finrank k W = Module.finrank k W') :
    ∃ e : V ≃ₗ[k] V, W.map e.toLinearMap = W' := by
  obtain ⟨U, hU⟩ := W.exists_isCompl
  obtain ⟨U', hU'⟩ := W'.exists_isCompl
  have h1 := Submodule.finrank_add_eq_of_isCompl hU
  have h2 := Submodule.finrank_add_eq_of_isCompl hU'
  have h3 : Module.finrank k U = Module.finrank k U' := by omega
  let a : W ≃ₗ[k] W' := LinearEquiv.ofFinrankEq _ _ h
  let b : U ≃ₗ[k] U' := LinearEquiv.ofFinrankEq _ _ h3
  let e : V ≃ₗ[k] V := (Submodule.prodEquivOfIsCompl W U hU).symm ≪≫ₗ (a.prodCongr b) ≪≫ₗ
    Submodule.prodEquivOfIsCompl W' U' hU'
  have he : ∀ w : W, e w = a w := by
    intro w
    simp [e]
  refine ⟨e, ?_⟩
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    have := he ⟨w, hw⟩
    change e w ∈ W'
    simp only at this
    rw [this]
    exact (a ⟨w, hw⟩).2
  · intro w hw
    refine ⟨a.symm ⟨w, hw⟩, (a.symm ⟨w, hw⟩).2, ?_⟩
    change e _ = w
    rw [he]
    simp

theorem exists_gl_map_residue_eq (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ)
    (W W' : Submodule (IsLocalRing.ResidueField O) (Fin n → IsLocalRing.ResidueField O))
    (h : Module.finrank (IsLocalRing.ResidueField O) W =
      Module.finrank (IsLocalRing.ResidueField O) W') :
    ∃ g : GL (Fin n) O, W.map (g.1.map (IsLocalRing.residue O)).mulVecLin = W' := by
  obtain ⟨e, he⟩ := exists_linearEquiv_map_eq_of_finrank_eq W W' h
  let M : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O) := LinearMap.toMatrix' e.toLinearMap
  choose A hA using fun i j => IsLocalRing.residue_surjective (R := O) (M i j)
  have hAM : (Matrix.of A).map (IsLocalRing.residue O) = M := by
    ext i j
    exact hA i j
  have hM : M.det ≠ 0 := by
    have : M.det = LinearMap.det e.toLinearMap := LinearMap.det_toMatrix' _
    rw [this]
    exact (LinearEquiv.isUnit_det' e).ne_zero
  have hu : IsUnit (Matrix.of A).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    change ((Matrix.of A).map (IsLocalRing.residue O)).det ≠ 0
    rw [hAM]
    exact hM
  obtain ⟨g, hg⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hu
  refine ⟨g, ?_⟩
  rw [hg, hAM, ← he]
  congr 1
  exact Matrix.toLin'_toMatrix' e.toLinearMap

end GlobalTheory.SplitHecke
