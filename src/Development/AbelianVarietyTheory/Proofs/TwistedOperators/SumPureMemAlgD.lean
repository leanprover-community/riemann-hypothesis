module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
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

@[expose] public section

noncomputable section

namespace GlobalTheory.PolKer

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def PolZero (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) : Prop :=
  ∃ T : Finset (Pl F), X.T ⊆ T ∧ ∃ (m : ℕ) (f : Fin m → SInf F (Fin a × Fin (a + a')))
    (φ : Fin m → ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ),
    (∀ i, f i ∈ G.M.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = G.M.vac v) ∧
    Φ = ∑ i, pure (f i) (φ i) ∧
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) = 0

theorem sum_pure_mem_algD {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, EmbOver E w) (T : Finset (Pl F)) {m : ℕ} (f : Fin m → SInf F (Fin n × Fin d))
    (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h : ∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = M.vac v) :
    ∑ i, pure (f i) (φ i) ∈ GlobalTheory.SquareAgree.algD M ψ emb := by
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, φ i, (h i).1, (h i).2.1, ?_, rfl⟩
  filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv
  exact (h i).2.2 v hv

theorem algD_of_polZero (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (h : PolZero B G X R Rf Φ) : Φ ∈ GlobalTheory.SquareAgree.algD G.M B.ψ B.emb := by
  obtain ⟨T, -, m, f, φ, hf, rfl, -⟩ := h
  exact sum_pure_mem_algD G.M B.ψ B.emb T f φ hf

end GlobalTheory.PolKer
