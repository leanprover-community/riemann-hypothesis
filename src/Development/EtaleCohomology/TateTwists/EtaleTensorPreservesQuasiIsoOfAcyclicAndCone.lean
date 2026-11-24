module

public import Development.EtaleCohomology.TateTwists.EtaleTensorPairQuasiIsoOfFlatQuasiIso
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.tqis

def acyc : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T),
    τ.IsTensor → (∀ t, FlatS (J.X t)) → C.Acyclic → T.Acyclic

def cone : Prop :=
  ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T'),
    τ.IsTensor → τ'.IsTensor → τ.Compat τ' f (𝟙 J) u → ∃ σ : Pair (mappingCone f) J (mappingCone u), σ.IsTensor

end LateralTheory.EtaleFoundations.tqis

theorem qis_iff_cone {R : Type} [CommRing R] {K L : Cx R} (f : K ⟶ L) : QuasiIso f ↔ (mappingCone f).Acyclic := by
  have h : HomotopyCategory.quasiIso (Shv R) (ComplexShape.up ℤ) ((HomotopyCategory.quotient _ _).map f) ↔ (HomotopyCategory.subcategoryAcyclic (Shv R)).trW ((HomotopyCategory.quotient _ _).map f) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff] at h
  change HomologicalComplex.quasiIso (Shv R) (ComplexShape.up ℤ) f ↔ _
  exact h.trans ((ObjectProperty.trW_iff_of_distinguished (HomotopyCategory.subcategoryAcyclic (Shv R)) _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _))

theorem cone_ge {R : Type} [CommRing R] {I I' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] (f : I ⟶ I') :
    (mappingCone f).IsStrictlyGE (-1) :=
  CochainComplex.isStrictlyGE_mappingCone f 0 0 (-1)

theorem LateralTheory.EtaleFoundations.etale_tensor_preserves_quasiIso_of_acyclic_and_cone (hA : LateralTheory.EtaleFoundations.tqis.acyc) (hC : LateralTheory.EtaleFoundations.tqis.cone) :
    LateralTheory.EtaleFoundations.EtaleTensorPairQuasiIsoOfFlatQuasiIso := by
  intro R _ I I' J T T' _ _ _ τ τ' hτ hτ' hJ f _ u hc
  obtain ⟨σ, hσ⟩ := hC R τ τ' f u hτ hτ' hc
  have := cone_ge f
  rw [qis_iff_cone]
  exact hA R (-1) 0 σ hσ hJ ((qis_iff_cone f).1 inferInstance)
