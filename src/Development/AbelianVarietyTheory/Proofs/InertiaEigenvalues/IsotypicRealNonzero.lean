module

public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeSpacesOrthogonalOfClassSumInnerStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section

namespace GlobalTheory.LiftRefIrr

theorem exists_ne_of_mem_iSup' {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Sort*} (p : ι → Submodule ℂ M)
    (ℓ : M →+ ℂ) {x : M} (hx : x ∈ ⨆ i, p i) (h : ℓ x ≠ 0) : ∃ i, ∃ y ∈ p i, ℓ y ≠ 0 := by
  by_contra H
  push_neg at H
  exact h (Submodule.iSup_induction p (motive := fun z => ℓ z = 0) hx (fun i y hy => H i y hy) (map_zero ℓ)
    (fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero]))

theorem exists_irr_pair {D : D7} {μ : D.what₂.Tup} {j : ℕ} (Mr : MtReal D μ j) (x : D.what₂.Mt μ j) (hx : x ≠ 0) :
    ∃ (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)) (_ : NG.IsIrrRep Mr.wt.ρ S),
      ∃ F ∈ (NG.isoTyp Mr.wt.ρ S).comap Mr.real, inner ℂ F x ≠ 0 := by
  obtain ⟨-, ι, -, S, hirr, -, -, -, -, hsum⟩ := GlobalTheory.T.typeSpaces_orthogonal_of_classSum_inner D.host.E D.R.nV Mr.wt Mr.J Mr.χ Mr.J_open
  let p : ι → Submodule ℂ (D.what₂.Mt μ j) :=
    fun i => (NG.isoTyp Mr.wt.ρ (S i) ⊓ NG.TypeSp Mr.wt.ρ Mr.J Mr.χ).comap Mr.real
  have htop : (⨆ i, p i) = ⊤ := by
    apply Submodule.map_injective_of_injective Mr.real_inj
    rw [Submodule.map_iSup, Submodule.map_top, Mr.real_range]
    conv_rhs => rw [← hsum]
    refine iSup_congr fun i => ?_
    show Submodule.map Mr.real (Submodule.comap Mr.real _) = _
    rw [Submodule.map_comap_eq, Mr.real_range]
    exact inf_eq_right.2 inf_le_right
  have hxm : x ∈ ⨆ i, p i := htop ▸ Submodule.mem_top
  let ℓ : D.what₂.Mt μ j →+ ℂ := AddMonoidHom.mk' (fun F => inner ℂ F x) (fun a b => inner_add_left a b x)
  obtain ⟨i, F, hF, hne⟩ := exists_ne_of_mem_iSup' p ℓ hxm (by
    show inner ℂ x x ≠ 0
    exact inner_self_ne_zero.2 hx)
  exact ⟨S i, hirr i, F, (Submodule.mem_inf.1 hF).1, hne⟩

end GlobalTheory.LiftRefIrr


end
