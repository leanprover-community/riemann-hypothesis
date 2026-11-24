module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

@[expose] public section

open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem EtNbhd.trans_isLocalHom_injective (R : Type) [CommRing R] [IsLocalRing R] (i j : EtNbhd R)
    (h : i ≤ j) : IsLocalHom (EtNbhd.trans h) ∧ Function.Injective (EtNbhd.trans h) := by
  have hloc : IsLocalHom (EtNbhd.trans h) := by
    unfold EtNbhd.trans
    exact Localization.isLocalHom_localRingHom _ _ _ _
  refine ⟨hloc, ?_⟩
  set f : i.A →ₐ[R] j.A := h.choose with hfdef
  letI : Algebra i.A j.A := (f : i.A →+* j.A).toAlgebra
  haveI : IsScalarTower R i.A j.A := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  haveI : Algebra.Etale i.A j.A := Algebra.Etale.of_restrictScalars R i.A j.A
  have hflat : (f : i.A →+* j.A).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hB : (EtNbhd.trans h).Flat := RingHom.Flat.localRingHom hflat j.q i.q _
  letI : Algebra i.B j.B := (EtNbhd.trans h).toAlgebra
  haveI : Module.Flat i.B j.B := RingHom.flat_algebraMap_iff.mp hB
  haveI : IsLocalHom (algebraMap i.B j.B) := hloc
  haveI hff : Module.FaithfullyFlat i.B j.B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact RingHom.FaithfullyFlat.injective hff

end GlobalTheory.Henselisation
