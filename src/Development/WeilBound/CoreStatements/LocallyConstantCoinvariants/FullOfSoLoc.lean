module

public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.RightOnto
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaEquivInducedFibre
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ContinuousFinId
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsExtZ
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsFull
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfSurj
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.TopOfMap
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.KCo

section Local

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

def augF (n d : ℕ) (ν α : kˣ →* ℂˣ) : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ) :=
  Submodule.span ℂ {z | ∃ g : GL (Fin n) k, ∃ Φ, Full Φ ∧ z = omB ν α g 1 Φ - Φ}

theorem augF_le {ν α : kˣ →* ℂˣ} : augF n d ν α ≤ aug n d ν α :=
  Submodule.span_mono fun _ ⟨g, Φ, h, e⟩ => ⟨g, Φ, h.1, e⟩

end Local

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip

theorem full_of_soLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (h : IsCMExt F E σ) (hψ : IsStd ψ)
    (hX : X.J.det ≠ 0) (hW : W.J.det ≠ 0) {t : E →ₐ[F] Fv F v} {ι} (hι : M.IsLinBar ψ t 1 1 ι) {φ} (hφ : φ ∈ M.SoLoc ψ t) :
    ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), Y.rank ≠ n → ι φ Y = 0 := by
  obtain ⟨h1, ι', hι', h2⟩ := hφ
  intro Y hY
  obtain ⟨x, hx, h0, rfl⟩ := exists_coB (X := X) (W := W) h t hX hW Y
  exact eigen_kill M h hψ hX hW hι' ((LinearMap.proj (coB σ X W t x)).comp ι) hx h0
    (fun u hu hu1 φ' h' => mult' M hψ hι hu hu1 hx h0 h') h1 (h2 _ hY)

end PositivityTheory.KCo
