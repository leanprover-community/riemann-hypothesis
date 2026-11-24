module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkFacArch
public import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsB
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



section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open UpperTheory.TP
theorem UpperTheory.weilRep_mem_polynomialFock_of_archimedean :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∀ Φ ∈ PolData B M, om (g, h) Φ ∈ PolData B M := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hp g hg h hh Φ hΦ
  obtain ⟨T, hT, hP⟩ := _root_.PositivityTheory.ThKF.A.archOp_k F E σ B n d X W M χX χW om n 0 d 0 hp g hg h hh
  have kg : g ∈ KInf σ X B.emb := ⟨hg, fun w => by
    rw [GlobalTheory.ThK.Dbl.Prs.cartan_one (hp.herm.sig w) (hp.herm.cartan w)]; exact Commute.one_right _⟩
  have kh : h ∈ KInf σ W B.emb := ⟨hh, fun w => by
    rw [GlobalTheory.ThK.Dbl.Prs.cartan_one (hp.skew.sig w) (hp.skew.cartan w)]; exact Commute.one_right _⟩
  refine Submodule.span_induction (p := fun Φ _ => om (g, h) Φ ∈ PolData B M) ?_ (by simp)
    (fun x y _ _ a b => by rw [map_add]; exact add_mem a b)
    (fun c x _ a => by rw [map_smul]; exact Submodule.smul_mem _ c a) hΦ
  rintro _ ⟨f, f1, φ, f2, f3, rfl⟩
  obtain ⟨ξ, hξ, e⟩ := PositivityTheory.ThKG.pure_eq_pureA hp.good φ f2 f3
  rw [e f, hT.1 f ξ hξ, ← e (T f)]
  exact Submodule.subset_span ⟨T f, hP kg kh f f1, φ, f2, f3, rfl⟩
end
