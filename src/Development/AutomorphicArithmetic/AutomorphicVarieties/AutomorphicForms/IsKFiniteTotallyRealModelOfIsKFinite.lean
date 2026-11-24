module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.MemArchMaxCompactIffOrthogonalAtInfinitePlaces
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Translation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

theorem UpperTheory.isKFinite_totallyRealModel_of_isKFinite :
    UpperTheory.V.Fb.KFinTo := by
  intro E _ _ _ a φ hopen hfin
  let Kf := AdelicGLn.integralFiniteGL E a
  let V : Subgroup Kf :=
    { carrier := {v | TR.finRep E a v.1 φ = φ}
      one_mem' := by
        show TR.finRep E a 1 φ = φ
        rw [map_one]; rfl
      mul_mem' := fun {v w} hv hw => by
        have hv' : TR.finRep E a v.1 φ = φ := hv
        have hw' : TR.finRep E a w.1 φ = φ := hw
        show TR.finRep E a (v.1 * w.1) φ = φ
        rw [map_mul, Module.End.mul_apply, hw', hv']
      inv_mem' := fun {v} hv => by
        have hv' : TR.finRep E a v.1 φ = φ := hv
        show TR.finRep E a (v.1⁻¹) φ = φ
        conv_lhs => rw [← hv']
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
  have hV : IsOpen (V : Set Kf) := hopen.preimage continuous_subtype_val
  haveI : CompactSpace Kf := isCompact_iff_compactSpace.1 (AdelicGLn.isCompact_integralFiniteGL E a)
  haveI : Finite (Kf ⧸ V) := Subgroup.quotient_finite_of_isOpen V hV
  unfold IsKFinite
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ q : Kf ⧸ V,
    ((Submodule.span ℂ (Set.range fun k => TR.cptRep E a k φ)).map (TR.finRep E a q.out.1)).map
      (TR.Sm E a).subtype) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  let kf : Kf := ⟨finPart k.1, finPart_mem_integralFiniteGL k.2⟩
  obtain ⟨y, hy⟩ := (grpEq E a).surjective (archPart k.1)
  have hyu : y.val ∈ Matrix.unitaryGroup (Fin a) (TR.Rinf E) :=
    (UpperTheory.mem_archMaxCompact_iff_orthogonal_at_infinitePlaces E a y).1 (hy ▸ archPart_mem_archCompact k.2)
  have hu : Unitary.toUnits (⟨y.val, hyu⟩ : TR.Kinf E a) = y := Units.ext rfl
  obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V kf
  have hv2 : TR.finRep E a v.1.1 φ = φ := v.2
  have hk : TR.infGL E a y * finGL E a kf.1 = k.1 := by
    rw [← infEmb_grpEq, hy, ← finEmb_eq]
    exact infEmb_archPart_mul_finEmb_finPart k.1
  refine Submodule.mem_iSup_of_mem (QuotientGroup.mk kf)
    ⟨_, ⟨_, Submodule.subset_span ⟨⟨y.val, hyu⟩, rfl⟩, rfl⟩, ?_⟩
  rw [hv]
  funext g
  show φ.1 (g * finGL E a (kf.1 * v.1.1) * TR.infGL E a (Unitary.toUnits (⟨y.val, hyu⟩ : TR.Kinf E a))) = φ.1 (g * k.1)
  have h3 : φ.1 (g * k.1 * finGL E a v.1.1) = φ.1 (g * k.1) := congrFun (congrArg Subtype.val hv2) (g * k.1)
  rw [hu, ← h3, ← hk, mul_assoc g, ← TR.infGL_comm, map_mul]
  simp only [mul_assoc]
