module

public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

noncomputable section

namespace GlobalTheory.Survey.CrystallineCyclotomic

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]


include PD in
theorem nontrivial_B : Nontrivial B := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply PD.not_mem_filtration_two
  rw [Subsingleton.elim PD.t 0, map_zero]
  exact zero_mem _

theorem dcris_trivial [FiniteDimensional Qp LL] :
    Dcris PD (Representation.trivial LL G LL) =
      LinearMap.range (AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL)
        (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) := by
  ext x
  rw [mem_Dcris]
  constructor
  · intro hx
    let e := Module.finBasis Qp LL
    let c : Fin (finrank Qp LL) → LL ⊗[Qp] B →ₗ[Qp] B := fun i =>
      (TensorProduct.lid Qp B).toLinearMap ∘ₗ (LinearMap.rTensor B (e.coord i))
    have hsum : ∀ y : LL ⊗[Qp] B, y = ∑ i, e i ⊗ₜ[Qp] c i y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b =>
        conv_lhs => rw [← e.sum_repr v, TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [c, TensorProduct.smul_tmul]
      | add a b ha hb =>
        simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib, ← ha, ← hb]
    have hc : ∀ i g y, c i (actVB PD (Representation.trivial LL G LL) g y) = PD.actB g (c i y) := by
      intro i g y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b =>
        have := ((PD.actB g).toAlgHom.toLinearMap.restrictScalars Qp).map_smul (e.coord i v) b
        have h2 : PD.actB g (e.coord i v • b) = e.coord i v • PD.actB g b := this
        simp only [c, actVB, LinearMap.comp_apply, AlgebraTensorModule.map_tmul,
          LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, h2]
        simp
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
    rw [hsum x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨k, hk⟩ := PD.invB (c i x) fun g => by rw [← hc, hx]
    exact ⟨e i ⊗ₜ k, by simp [hk]⟩
  · rintro ⟨y, rfl⟩ g
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem isCrys_trivial [FiniteDimensional Qp LL] : IsCrys PD (Representation.trivial LL G LL) := by
  haveI := nontrivial_B PD
  haveI := PD.finK₀
  unfold IsCrys
  rw [dcris_trivial, LinearMap.finrank_range_of_inj]
  · simp
  · exact Module.Flat.lTensor_preserves_injective_linearMap (M := LL)
      (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap (algebraMap K₀ B).injective

end GlobalTheory.Survey.CrystallineCyclotomic
