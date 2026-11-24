module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterInUnitaryArchimedeanMaxCompact
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.CompactLine

theorem exists_line_in_kInf_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n : ℕ) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb, ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W, γ (Multiplicative.ofAdd (1 : ℝ)) = k ∧
      ∀ t, γ t ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb := by
  intro F E _ _ _ _ _ σ B n W r s hb hW k hk
  choose A hA hAθ using fun w => GlobalTheory.RealLift.frameEx_holds n r s _ (W.θ w) (hW.sig w) (hW.cartan w)
  have hA1 : ∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf]; exact hA w
  obtain ⟨γ, hγ, Y, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.RealLift.exists_line_of_upq F E σ (Fin n) r s
    B.emb (incM F W.J) Complex.I A W.θ hb.cm hA1 hAθ k hk.1 hk.2
  refine ⟨γ, hγ, hγ1, fun t => ⟨hγ.2 t, fun w => ?_⟩⟩
  obtain ⟨A', hAA⟩ := (hA w).2
  exact commute_of_gen (A w) A' hAA _ _ (Y w) (hKC w) t.toAdd (hAθ w) (hgen t.toAdd w)

end GlobalTheory.CompactLine

end
