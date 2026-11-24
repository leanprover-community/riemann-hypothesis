module

public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValOfPowAssociated
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeDeltaInvariantBasisStatement
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem GlobalTheory.NL.p9_statement : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), P9 D HW F := by
  intro D HW F l _ K s LL h T hT hs hl
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  rw [hp] at hl ⊢
  obtain ⟨hc, ⟨π', E', hr⟩, h1⟩ := GlobalTheory.DelParam.torsion_parameters D HW l K s LL h hs hl
  have md := GlobalTheory.T.wachLattice_deltaInvariant_basis D HW F l K s LL h T hT hs hl
  have hpos : 0 < ((HW l).W K s LL h).DelF.card :=
    Finset.card_pos.2 ⟨1, (((HW l).W K s LL h).DelF_def 1).2 ⟨1, one_pos, one_pow _⟩⟩
  have hl1 : 0 < l - 1 := Nat.sub_pos_of_lt (Fact.out : l.Prime).one_lt
  refine ⟨hc, ⟨π', E', hr, md _ _ _ _ (hc ▸ hpos) hr⟩, fun he => ⟨h1 he, md _ _ _ _ hl1 (h1 he)⟩⟩
