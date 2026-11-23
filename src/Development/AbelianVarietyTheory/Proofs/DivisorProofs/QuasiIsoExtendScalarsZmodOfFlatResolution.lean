module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodSemilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcyclicExtendScalarsZmodOfFlatBoundedBelowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafComplexMappingConeAcyclicOfQuasiIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFlatEtaleSheafBiprodStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFlatEtaleSheafIsoAndZeroStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedQis

theorem quasiIso_of_cone_acyclic {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {K L : CochainComplex 𝒜 ℤ} (u : K ⟶ L) (h : (CochainComplex.mappingCone u).Acyclic) : QuasiIso u := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at h
  have hu : HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map u) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished u)).2 h
  rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hu

theorem flatS_cone {R : Type} [CommRing R] (F : Shv R) (hF : FlatS F) (T : Cx R) (hT : ∀ t, FlatS (T.X t))
    (ε : sgl F ⟶ T) (n : ℤ) : FlatS ((mappingCone ε).X n) := by
  obtain ⟨hiso, hzero⟩ := GlobalTheory.T.isLocallyFlatEtaleSheaf_iso_and_zero R
  refine hiso (HomologicalComplex.homotopyCofiber.XIsoBiprod ε n (n + 1) rfl).symm
    (GlobalTheory.T.isLocallyFlatEtaleSheaf_biprod _ _ _ ?_ (hT n))
  by_cases h : n + 1 = 0
  · exact hiso (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 F (n + 1) h).symm hF
  · exact hzero _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)

theorem quasiIso_extCx_of_flat : ∀ (Q q : ℕ) [NeZero Q] (h : q ∣ Q) (F : Shv (ZMod Q)) (T : Cx (ZMod Q))
    [T.IsStrictlyGE 0], FlatS F → (∀ t, FlatS (T.X t)) → ∀ ε : sgl F ⟶ T, QuasiIso ε →
    QuasiIso ((GlobalTheory.EtC.ScalarExt.extCx (ZMod.castHom h (ZMod q))).map ε) := by
  intro Q q _ h F T _ hF hT ε hε
  have hK : (mappingCone ε).Acyclic := GlobalTheory.mappingCone_acyclic_of_quasiIso _
  have hNeg : (-1 : ℤ) < 0 := neg_one_lt_zero
  have hBound := CochainComplex.isStrictlyGE_mappingCone ε 0 0 (-1) hNeg (Int.le_of_lt hNeg)
  have hE := @GlobalTheory.T.acyclic_extendScalars_zmod_of_flat_boundedBelow Q q _ h
    (mappingCone ε) (-1) hBound (flatS_cone F hF T hT ε) hK
  have hC : (mappingCone (((extSh (ZMod.castHom h (ZMod q))).mapHomologicalComplex _).map ε)).Acyclic := fun n =>
    (hE n).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso ε (extSh (ZMod.castHom h (ZMod q))))
  exact quasiIso_of_cone_acyclic _ hC

end GlobalTheory.EtC.RedQis

end
