module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassMapPropertiesOfSymmetricForms
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassInjectiveOfSelfDual
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClsCrdEqGlob
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.SelfDualPHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain



theorem fvStab_holds {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (Tf : FormsTiedSym D u Ch chOf) : FvStab Tf := by
  intro c γ hγ v x hx
  have hF := Tf.fv D.R.m le_rfl (Or.inr rfl)
  have hγ' := ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI_range _ γ).1 hγ
  obtain ⟨κ, hκ, hκe⟩ := Subgroup.mem_map.mp hγ'
  have hbc : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 =
      ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1 * κ *
        ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1⁻¹ := by
    rw [← hκe]; rfl
  have hκv := ((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U_eq κ).1 hκ |>.2 (Tf.atT.eV v).1
  rw [(Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.UlocAlt (Tf.atT.eV v).1 (Tf.atT.eV v).2] at hκv
  obtain ⟨_, hfix⟩ := (Subgroup.mem_inf.mp hκv).2
  have hzx := dualLoc_of (Tf.cls D.R.m le_rfl (Or.inr rfl)) (Tf.atT.eV v).1 ((D.fm u).til c) x.1 x.2
  have hzg := dualLoc_of (Tf.cls D.R.m le_rfl (Or.inr rfl)) (Tf.atT.eV v).1 ((D.fm u).til c) _ hx
  have key := conj_stepA (Tf.atT.eV v).1 _ κ γ.1 hbc x.1
  exact (hF v ((D.fm u).til c) ⟨_, hx⟩ hzg).trans ((congrArg _ ((congrArg _ (Subtype.ext key)).trans (hfix ⟨_, hzx⟩))).trans
    (hF v ((D.fm u).til c) x hzx).symm)

theorem class_injective_holds : ClassMapInjective :=
  class_injective_of_self_dual (fun _ _ _ _ Tf => selfDualP_of_formsTiedSym Tf)

theorem stabiliser_bijective_holds : StabiliserMapBijective :=
  stabiliser_bijective_self_dual (fun _ _ _ _ Tf => selfDualP_of_formsTiedSym Tf) (fun _ _ _ _ Tf => fvStab_holds Tf)

end Formalism.L2.GlobalTheoryTheory.Br
