module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
public import CompanionTheory.AutomorphicTheory.SegmentRepresentations.IrreducibleSegments.IsIrreduciblePiTensorSegTerm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodChevalley
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrrRepInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentationIff

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.RgGu.SRC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace SrEasy

theorem isSmooth_prod {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) :
    IsSmooth (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := isSmooth_parInd _ _

theorem hasFiniteLength_prod {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) :
    HasFiniteLength (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := by
  have hρ := CompanionTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ l
  have hsρ : IsSmooth (piTensor (segTerm σ.ρ l)) := isSmooth_piTensor fun a =>
    isSmooth_twist σ.smooth (IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow _))
  exact GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ)

theorem isSmooth_sub {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hπ : IsSmooth π) (S : Subrepresentation π) : IsSmooth S.toRepresentation := by
  intro v
  have : {g : G | S.toRepresentation g v = v} = {g : G | π g v.1 = v.1} := by
    ext g; exact Subtype.ext_iff
  rw [this]; exact hπ v.1

end SrEasy

open SrEasy



theorem exists_irred_le {d l : ℕ} (hd : 0 < d) (hl : 0 < l) (σ : IrrRep (GL (Fin d) k))
    (hσ : IsCuspidal σ.ρ) (T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)))
    (hT : T.toSubmodule ≠ ⊥) :
    ∃ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S'.toRepresentation.IsIrreducible ∧ S'.toSubmodule ≤ T.toSubmodule := by
  let ι : T.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
    ⟨T.toSubmodule.subtype, fun _ => rfl⟩
  have hnt : Nontrivial T.toSubmodule := Submodule.nontrivial_iff_ne_bot.2 hT
  obtain ⟨S, f, hf⟩ := GlobalTheory.T.exists_injective_irreducible_subrepresentation k _ _ _ T.toRepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l))
    (isSmooth_sub (isSmooth_prod σ) T) hnt (IsSubquotient.of_injective ι Subtype.val_injective)
    (hasFiniteLength_prod σ)
  let g : S.ρ.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := ι.comp f
  have hg : Function.Injective g := Subtype.val_injective.comp hf
  have hat : IsAtom g.range := isAtom_range S.irr g hg
  refine ⟨g.range, GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom _ hat, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (f x).2



theorem isIrreducible_segTensor {d : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) :
    (piTensor (segTerm σ.ρ 2)).IsIrreducible :=
  CompanionTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ 2


set_option synthInstance.maxHeartbeats 400000 in
theorem hasFiniteLength_jac_sub {d : ℕ} (hd : 0 < d)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (S : Subrepresentation (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2))) :
    HasFiniteLength (jac (consecBlocks 2 d) S.toRepresentation) := by
  let ι : S.toRepresentation.IntertwiningMap (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)) :=
    ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  have hS : HasFiniteLength S.toRepresentation :=
    GlobalTheory.ProdLength.hasFiniteLength_of_injective ι Subtype.val_injective (hasFiniteLength_prod σ)
  exact GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ (consecBlocks 2 d) _ S.toRepresentation
    (isSmooth_sub (isSmooth_prod σ) S) hS

end CompanionTheory.RgGu.SRC

end
