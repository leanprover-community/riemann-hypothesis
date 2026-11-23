module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchActOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilOperatorsLinearOneMul
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

theorem _root_.GlobalTheory.T.archimedean_weilOperators_linear_one_mul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) →
    (∀ h ∈ UAt σ W (evI F), ∀ f f' : SInf F (Fin n × Fin d), archOp om h (f + f') = archOp om h f + archOp om h f') ∧
    (∀ h ∈ UAt σ W (evI F), ∀ (c : ℂ) (f : SInf F (Fin n × Fin d)), archOp om h (c • f) = c • archOp om h f) ∧
    (∀ f : SInf F (Fin n × Fin d), archOp om 1 f = f) ∧
    (∀ h ∈ UAt σ W (evI F), ∀ h' ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d),
      archOp om (h * h') f = archOp om h (archOp om h' f)) := by
  first | exact @GlobalTheory.ArchLine.archOp_laws | exact GlobalTheory.ArchLine.archOp_laws | (intros; apply GlobalTheory.ArchLine.archOp_laws <;> assumption)
