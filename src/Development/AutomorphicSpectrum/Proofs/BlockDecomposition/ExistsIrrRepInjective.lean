module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodChevalley
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductionFiniteLength
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetQuotientEigenvector
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

noncomputable section

namespace GlobalTheory.CompanionTheory.IrrSub

def subIncl {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (S : Subrepresentation ρ) : S.toRepresentation.IntertwiningMap ρ :=
  ⟨S.toSubmodule.subtype, fun _ => rfl⟩

theorem subIncl_injective {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S : Subrepresentation ρ) : Function.Injective (subIncl S) :=
  Subtype.val_injective

theorem hasFiniteLength_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (h : IsSubquotient σ ρ) (hρ : HasFiniteLength ρ) : HasFiniteLength σ := by
  obtain ⟨T, f, hf⟩ := h
  exact GlobalTheory.JacquetBlocks.hasFiniteLength_of_surjective f hf
    (GlobalTheory.ProdLength.hasFiniteLength_of_injective (subIncl T) (subIncl_injective T) hρ)

theorem exists_isAtom {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} [Nontrivial V] (h : HasFiniteLength ρ) :
    ∃ S : Subrepresentation ρ, IsAtom S := by
  have hbt : (⊤ : Subrepresentation ρ) ≠ ⊥ := by
    intro e
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hmem : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [e] at hmem
    exact hx ((Submodule.mem_bot ℂ).1 hmem)
  obtain ⟨S, hS, -⟩ := GlobalTheory.CompanionTheory.JacExp.exists_atom_le h hbt
  exact ⟨S, hS⟩

theorem exists_irrRep_injective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Representation ℂ (GL (Fin n) k) V) (A₀ : Representation ℂ (GL (Fin n) k) W),
    IsSmooth A → Nontrivial V → IsSubquotient A A₀ → HasFiniteLength A₀ →
    ∃ (S : IrrRep (GL (Fin n) k)) (f : S.ρ.IntertwiningMap A), Function.Injective f := by
  intro k _ _ _ _ n V W _ _ _ _ A A₀ hsm hnt hsub hfl
  obtain ⟨S, hS⟩ := exists_isAtom (hasFiniteLength_of_isSubquotient hsub hfl)
  exact ⟨⟨S.toSubmodule, S.toRepresentation, GlobalTheory.CompanionTheory.JacExp.isSmooth_sub hsm S,
    GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS⟩, subIncl S, subIncl_injective S⟩

end GlobalTheory.CompanionTheory.IrrSub
