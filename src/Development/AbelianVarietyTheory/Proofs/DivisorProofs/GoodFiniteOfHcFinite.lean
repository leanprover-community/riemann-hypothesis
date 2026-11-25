module

public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev
  Formalism.IndefR
open scoped TensorProduct Topology

namespace GlobalTheory.GoodFiniteDim

variable {D : D7}

theorem isOpen_comap_Kg (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (T : Finset (Pl D.host.E)) :
    IsOpen (((Kg D.sp.cm V.gram β T).comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β T] with κ hh
  obtain ⟨h1, h2, h3⟩ := hh
  exact ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩

theorem levFn_eq_one {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {T : Finset (Pl D.host.E)}
    (hg : L.Pg ⊆ T) (hq : L.Q ⊆ T) {x : GL (Fin V.rank) (Lev.EAf D)} (hx : x ∈ Kg D.sp.cm V.gram β T) :
    levFn β L x = 1 := by
  have h3 : ∀ PP ∈ T, redFn β PP x = 1 := by
    have h1 : x ∈ ⨅ PP ∈ T, princAt β PP := hx.2
    exact fun PP hP => (mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h1 PP) hP)).2
  have h4 : rTup β L x = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 x) = 1
    rw [h3 PP.1 (hg PP.2)]; exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levFn
  rw [h4, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hP
    rw [h3 PP (hq hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [h3 PP (hg hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]

theorem exists_open_subgroup (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
      ∀ k ∈ U, k ∈ GfC V → k ∈ (levG V β L : Set (GA D V)) ∧ levChi V β L k = 1 := by
  classical
  refine ⟨_, isOpen_comap_Kg V β (L.Pg ∪ L.Q), fun k hk hf => ⟨⟨hf, ?_⟩, ?_⟩⟩
  · exact Kg_le_lev (D := L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right hk
  · unfold levChi
    rw [levFn_eq_one Finset.subset_union_left Finset.subset_union_right hk, Units.val_one]

end GlobalTheory.GoodFiniteDim
