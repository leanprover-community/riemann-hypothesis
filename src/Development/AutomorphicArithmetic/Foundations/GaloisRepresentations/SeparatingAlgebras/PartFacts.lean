module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenFormEqFiniteSumAutRepEigenFormsStatement
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

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.partFacts_pf :
    UpperTheory.Gal.Gen.PartFacts := by
  intro E _ _ _ a W C P
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨I, F, h1, h2, rfl⟩ := GlobalTheory.T.eigenForm_eq_finite_sum_autRep_eigenForms E a W C 1 f (fun c v g => by simpa using hf c.1 c.2 v g)
    refine Submodule.sum_mem _ fun π hπ => ?_
    have hfix : F π ∈ fixedBy W C := fun k hk v g => by simpa using h2 π hπ ⟨k, hk⟩ v g
    by_cases hP : P π.V
    · exact Submodule.mem_sup_left
        (Submodule.mem_iSup_of_mem π (Submodule.mem_iSup_of_mem hP ⟨h1 π hπ, hfix⟩))
    · exact Submodule.mem_sup_right
        (Submodule.mem_iSup_of_mem π (Submodule.mem_iSup_of_mem hP ⟨h1 π hπ, hfix⟩))
  · exact iSup₂_le fun π _ => inf_le_right
  · intro K hK
    refine iSup₂_mono fun π _ => inf_le_inf_left _ ?_
    intro f hf k hk v g
    exact hf k (hK hk) v g
  · intro x hx f hf
    have hle : part W C P ≤ (part W C P).comap (algRep W x) := by
      refine iSup₂_le fun π hP f hf => ?_
      refine Submodule.mem_iSup_of_mem π (Submodule.mem_iSup_of_mem hP ⟨?_, ?_⟩)
      · exact AutSub.mem_finPart.2 fun v => π.isAut.stable x.1 _ (AutSub.mem_finPart.1 hf.1 v)
      · intro c hc v g
        change f.1 v (g * c * x.1) = f.1 v (g * x.1)
        have e : g * c * x.1 = g * x.1 * (x.1⁻¹ * c * x.1) := by group
        rw [e]
        exact hf.2 _ (hx c hc) v _
    exact hle hf
  · intro G hG
    obtain ⟨F, hF, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp
      (fun π : AutSub E a => ⨆ (_ : P π.V), π.finPart W ⊓ fixedBy W C) G).1 hG
    refine ⟨F.support, F, fun π hπ => ?_, rfl⟩
    have h0 : F π ≠ 0 := Finsupp.mem_support_iff.1 hπ
    have hm : F π ∈ ⨆ (_ : P π.V), π.finPart W ⊓ fixedBy W C := hF π
    by_cases hP : P π.V
    · rw [iSup_pos hP] at hm
      exact ⟨hP, hm.1, hm.2, h0⟩
    · rw [iSup_neg hP] at hm
      exact absurd ((Submodule.mem_bot _).1 hm) h0
